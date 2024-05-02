package com.sequoiareasoner.kernel.context

import com.sequoiareasoner.arrayops.cforeach
import com.sequoiareasoner.kernel.clauses._
import com.sequoiareasoner.kernel.index.{IndexedSequence, NeighborPredClauseIndex, UnprocessedDeque}
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.structural.DLOntology

/** Object containing utility methods for taking a particular clause/clause+predicate and mass-applying a particular inference rule
  * until all possible applications of that rule to that clause have been done in the current state of the context. */

object RuleSaturator {


  /** This method does all possible applications of the Hyper rule for predicate `selectedPredicate` in context clause
    * `clause`. Requires:
    * -The selected predicate `selectedPredicate` of the clause.
    * -The clause itself `clause`
    * -The other context clauses in the context `contextClauses`
    * -The ontology clauses `DLOntology`
    * -The cutting optimisation to be applied (could be `none`).
    * -Whether the context is root.
    * -A buffer for storing derived clauses. */
  private[context] def doHyperInferencesForPredicateInClause(selectedPredicate: Predicate,
                                                             clause: ContextClause,
                                                             contextClauses: ContextClauseIndex,
                                                             ontology: DLOntology,
                                                             ordering: ContextLiteralOrdering,
                                                             cutting: EqualityOptimization,
                                                             isRootContext: Boolean,
                                                             resultsBuffer: UnprocessedDeque,
                                                             debugFlag: Boolean = false,
                                                             onlyHornAxioms: Boolean): Unit = {
    /** Get ontology clauses that have a body literal that can unify with `selectedPredicate` */
    val iterator: Iterator[OntologyClause] = ontology.getRelevantOntologyClauses(selectedPredicate)
    iterator.foreach{ ontologyClause =>
      // if (max.iri.toString.contains("KN_000074") && debugFlag ) System.out.println("Found relevant ontology clause: " + ontologyClause) //DEBUG
      // if (debugFlag ) System.out.println("Found relevant ontology clause: " + ontologyClause) //DEBUG
      /** Try to do all possible applications of the Hyper rule with the given clause and ontology clause */
      // BOBO if (onlyHornAxioms && !ontologyClause.isHorn) {}
      //else
      Rules.Hyper(selectedPredicate, clause, contextClauses.centralUnifiableMaxHeadPredicateLookup, ontologyClause, ordering, cutting, isRootContext, ontology.isNothing, resultsBuffer, debugFlag)
    }
  }

  /** This method carries out the third part of the Pred rule: given a clause `clause` in a context and a predicate
    * `selectedPredicate`, it attempts to apply all possible inferences with a clause of `predClauses`, the set
    * of clauses that have been propagated to (but not added to) the context from successor, and with the other `contextClauses`.
    * Note that there is no need to consider whether the context is root for this, as this method is applied only to
    * non-query predicates.*/
  private[context] def doThirdStepPredInferencesForPredicateInClause(selectedPredicate: Predicate,
                                                                     clause: ContextClause,
                                                                     contextClauses: ContextClauseIndex,
                                                                     predClauses: NeighborPredClauseIndex,
                                                                     ordering: ContextLiteralOrdering,
                                                                     resultsBuffer: UnprocessedDeque): Unit = {
    /** Type check */
    selectedPredicate match {
      case Concept(_,FunctionalTerm(_)) =>
      case Role(_,FunctionalTerm(_),_) | Role(_,_,FunctionalTerm(_)) =>
      case _ => throw new IllegalArgumentException(s"Predicate $selectedPredicate should contain a function term.")
    }
    /** Convenience method that returns all clauses that have a predicate p as maximal, except if this is the selected
      * predicate, in which case it returns the main clause `clause`. */
    def contextClauseLookup(p: Predicate) = if (p == selectedPredicate) IndexedSequence(clause) else contextClauses.maxHeadPredicateLookup(p)
    /** For each relevant predClause, try to do all possible applications of the third part of Pred rule with the given clause and pred clause */
    for (predClause <- predClauses(selectedPredicate)) Rules.Pred(contextClauseLookup, predClause, ordering, resultsBuffer)
  }


  /** This rule is analogous to the one above, but for the rootPred Rule (again, this method is applied to non-query
    * atoms */
  private[context] def doThirdStepRootPredInferencesForPredicateInClause(selectedPredicate: Predicate,
                                                                             clause: ContextClause,
                                                                             contextClauses: ContextClauseIndex,
                                                                             predClauses: NeighborPredClauseIndex,
                                                                             ordering: ContextLiteralOrdering,
                                                                             resultsBuffer: UnprocessedDeque,
                                                                              debug: Boolean = false): Unit = {
    require(selectedPredicate.isRSuccTrigger)
    /** Convenience method that returns all clauses that have a predicate p as maximal, except if this is the selected
      * predicate, in which case it returns the main clause `clause`. */
    def contextClauseLookup(p: Predicate) = if (p == selectedPredicate) IndexedSequence(clause) else contextClauses.maxHeadPredicateLookup(p)
    /** For each relevant predClause, try to do all possible applications of the third part of rootPred rule with the given clause and pred clause */
    for (predClause <- predClauses(selectedPredicate)) {
//      if (debug) {
//        println("Clause identified for RPred:")
//        println(predClause)
//        println(" to be resolved with")
//        println(clause)
//      }
      Rules.Pred(contextClauseLookup, predClause, ordering, resultsBuffer)
    }
  }

  /** This method takes a clause `clause` and a maximal predicate `selectedPredicate` and it carries out all possible
    * inferences with the Eq rule to that predicate. */
  private[context] def doEqInferencesForPredicateInClause(selectedPredicate: Predicate,
                                                          clause: ContextClause,
                                                          contextClauses: ContextClauseIndex,
                                                          ordering: ContextLiteralOrdering,
                                                          cutting: EqualityOptimization,
                                                          isRootContext: Boolean,
                                                          resultsBuffer: UnprocessedDeque): Unit = {

    /** If one of the terms in selectedPredicate is bigger, then we need only apply the method to it.
      *  However, if they are incomparable, we need to apply it to both */
    /** Here we apply it to one of the maximal elements. Note that we do not look for equalities in second-maximal positions
      * of root context clauses, since that would imply there is a query atom as the maximum atom of the clause (but this
      * requires all other atoms in the clause to be in variables x, y, and no such equalities or inequalities are relevant
      * since the reduced term in `selectedPredicate` has to be a function term or a nominal.) */
    val internalPred = selectedPredicate.iri.isInternalIndividual
    for (relevantContextClause <- contextClauses.maxHeadLiteralTermOccurrenceLookup(selectedPredicate.maximalTerms._1))
      /** For each relevant context clause, for each equality on a maximal position that reduces `selectedPredicate`
        * (in particular, a strict equality, since we reduce a functional term or nominal) and contains no variable
        * (this is a safety check, since the maximal term of the selected predicate sould not be a variable), we
        * apply the Eq rule and send the solution to the buffer */
    // Again, cforeach does not respect order when used as anonymous match function, so we need to use a more convoluted form:
    cforeach(relevantContextClause.maxHeadLiterals) { lit => lit match {
        /** Prevent generation of useless atoms O(o) */
        case Equality(t,v: Constant) if internalPred && (selectedPredicate match {
          case Concept(iri,s) if s==t && Term(IRI.nominalConceptUid2NominalIriStringName(iri.uid)) == v => true
          case _ => false}) =>
        case Equality(v: Constant,t) if internalPred && (selectedPredicate match {
          case Concept(iri,s) if s==t && Term(IRI.nominalConceptUid2NominalIriStringName(iri.uid)) == v => true
          case _ => false}) =>
        case equality: Equality if equality.isStrict && equality.maxTerm.contains(selectedPredicate.maximalTerms._1) &&
              equality.maxTerm.exists { case _: Variable => false; case _ => true } =>
          Rules.Eq(selectedPredicate, selectedPredicate.maximalTerms._1, clause, equality, relevantContextClause, ordering, cutting, resultsBuffer)
        case _ =>
      }}

    /** Here we apply it to the second maximal element, if it exists */
      selectedPredicate.maximalTerms._2.foreach(t2 =>
        for (relevantContextClause <- contextClauses.maxHeadLiteralTermOccurrenceLookup(t2))
          cforeach(relevantContextClause.maxHeadLiterals) { lit => lit match {
            case Equality(CentralVariable,v: Constant) if (selectedPredicate match {
              case Concept(iri,_) if iri.isInternalIndividual && Term(IRI.nominalConceptUid2NominalIriStringName(iri.uid)) == v => true
              case _ => false}) =>
            case Equality(v: Constant,CentralVariable) if (selectedPredicate match {
              case Concept(iri,_) if iri.isInternalIndividual && Term(IRI.nominalConceptUid2NominalIriStringName(iri.uid)) == v => true
              case _ => false}) =>
            case equality: Equality if equality.isStrict && equality.maxTerm.contains(t2) &&
              equality.maxTerm.exists { case _: Variable => false; case _ => true } =>
              Rules.Eq(selectedPredicate, t2, clause, equality, relevantContextClause, ordering, cutting, resultsBuffer)
            case _ =>
          }})
  }

  /** This method takes a clause `clause` and a maximal inequality `selectedInequality` and it carries out all possible
    * inferences with the Eq rule to that inequality. */
  private[context] def doEqInferencesForInequalityInClause(selectedInequality: Inequality,
                                                              clause: ContextClause,
                                                              contextClauses: ContextClauseIndex,
                                                              ordering: ContextLiteralOrdering,
                                                              cutting: EqualityOptimization,
                                                              isRootContext: Boolean,
                                                              resultsBuffer: UnprocessedDeque): Unit = {
    if (selectedInequality.s == selectedInequality.t) throw new IllegalStateException("Ineq rule should have been applied immediately after clause generation!")
    /** As above, we will apply the rule to one or two elements of the inequality (this may not be needed, since the
      * inequalities between x or y and a nominal in a root context are regenerated in a nominal context, and those not
      * in a root context will be propagated to a predecessor.) */
    /** Here we apply it to the first */
    for (relevantContextClause <- contextClauses.maxHeadLiteralTermOccurrenceLookup(selectedInequality.maximalTerms._1))
      /** As above, we choose context clauses with relevant equalities in a maximal position */
      /** For the same reason as above we do not need to search for equalities in the second maximal predicates */
      cforeach (relevantContextClause.maxHeadLiterals) {
        case equality: Equality if equality.isStrict && equality.maxTerm.contains(selectedInequality.maximalTerms._1) && equality.maxTerm.exists{ case _: Variable => false; case _ => true }  =>
          Rules.Eq(selectedInequality, selectedInequality.maximalTerms._1, clause, equality, relevantContextClause, ordering, cutting, resultsBuffer)
        case _ =>
      }
    selectedInequality.maximalTerms._2.foreach( t2 =>
      for (relevantContextClause <- contextClauses.maxHeadLiteralTermOccurrenceLookup(t2))
        cforeach (relevantContextClause.maxHeadLiterals) {
          case equality: Equality if equality.isStrict && equality.maxTerm.contains(t2) && equality.maxTerm.exists{ case _: Variable => false; case _ => true } =>
            Rules.Eq(selectedInequality, t2, clause, equality, relevantContextClause, ordering, cutting, resultsBuffer)
          case _ =>
        })
  }


  /** This method takes a clause `clause` and a maximal equality `selectedequality` and it carries out all possible
    * inferences with the Eq rule to that equality. */
  private[context] def doEqInferencesForEqualityInClause(selectedEquality: Equality,
                                                            clause: ContextClause,
                                                            contextClauses: ContextClauseIndex,
                                                            ordering: ContextLiteralOrdering,
                                                            cutting: EqualityOptimization,
                                                            isRootContext: Boolean,
                                                            resultsBuffer: UnprocessedDeque): Unit = {
    if (selectedEquality.s == selectedEquality.t) throw new IllegalStateException("The current clause is redundant!")
    /** Once again, we will apply the rule to one or two elements, depending on whether the equality is strictly ordered */
    /** Here we apply it to the first. Once again, we do not consider places where to apply the equality that are smaller
      * than a query atom, because it would be equalities with variables, and those are not affected by Eq rule */
    for (relevantContextClause <- contextClauses.maxHeadLiteralTermOccurrenceLookup(selectedEquality.maximalTerms._1))
      // cforeach does not work well. On pattern matching, it does not follow the usual order. //
      cforeach(relevantContextClause.maxHeadLiterals) { lit => lit match {
          case Concept(iri, t) if iri.isInternalIndividual && (selectedEquality match {
            case Equality(s, v: Constant) if s == t && Term(IRI.nominalConceptUid2NominalIriStringName(iri.uid)) == v => true
            case Equality(v: Constant, s) if s == t && Term(IRI.nominalConceptUid2NominalIriStringName(iri.uid)) == v => true
            case _ => false
          }) =>
          case _ => if (lit.containsAtRewritePosition(selectedEquality.maximalTerms._1))
            Rules.Eq(lit, selectedEquality.maximalTerms._1, relevantContextClause, selectedEquality, clause, ordering, cutting, resultsBuffer)
        }
      }

    /** Here we apply it to the second */
    selectedEquality.maximalTerms._2.foreach ( t2 =>
      for (relevantContextClause <- contextClauses.maxHeadLiteralTermOccurrenceLookup(t2))
        cforeach (relevantContextClause.maxHeadLiterals) { lit => lit match {
         case Concept(iri,t) if iri.isInternalIndividual && (selectedEquality match {
          case Equality(s,v) if s == t && Term(IRI.nominalConceptUid2NominalIriStringName(iri.uid)) == v  => true
          case Equality(v,s) if s == t && Term(IRI.nominalConceptUid2NominalIriStringName(iri.uid)) == v  => true
          case _ => false }) =>
        case _ => if (lit.containsAtRewritePosition(t2))
            Rules.Eq(lit, t2, relevantContextClause, selectedEquality, clause, ordering, cutting, resultsBuffer)
        } } )
  }

  /** This method takes a predicate `selectedPredicate` of the form R(o,y) occurring maximally in a clause `clause`
    *  and checks if the rule that introduces a new nominal can be applied. */
  private[context] def doNomInferencesForPredicateInClause(selectedPredicate: Predicate,
                                                           clause: ContextClause,
                                                           state: ContextState,
                                                           ontology: DLOntology,
                                                           ordering: ContextLiteralOrdering,
                                                           resultsBuffer: UnprocessedDeque): Unit = {
    //TODO: This can be optimised if instead of searching for the ontology clause, we simply store the corresponding max number for each combination of two predicates
    /** Check that the predicate is of the required form and occurs in the ontology in an atMost restriction */
    ontology.exposeUnaryAtoms4AtMostRestriction.get(selectedPredicate.iri.uid) match  {
      case None =>
      case Some(set: collection.mutable.Set[Int]) if set.isEmpty =>  if (isNotBlocked(clause,selectedPredicate,None,None,state.workedOffClauses,ordering)) {
        val iterator: Iterator[OntologyClause] = ontology.getRelevantOntologyClauses(selectedPredicate)
        iterator.foreach { ontologyClause => if (ontologyClause.isAtMost) Rules.Nom(selectedPredicate, clause, ontologyClause, None, None, ontology, ordering, resultsBuffer) }
      }
      case Some(set: collection.mutable.Set[Int]) => {
        state.hasNomRuleRoleTriggers = true
        for (unaryAtom <- set) {
          state.addNomRuleTrigger(unaryAtom, selectedPredicate.asInstanceOf[Role].s.asInstanceOf[Constant].id, selectedPredicate.asInstanceOf[Role].iri.uid)
          for (auxiliaryClause <- state.workedOffClauses.maxHeadPredicateLookup(Concept(IRI(unaryAtom), selectedPredicate.asInstanceOf[Role].s)(ontology))) {
            if (isNotBlocked(clause, selectedPredicate, Some(auxiliaryClause), Some(Concept(IRI(unaryAtom), selectedPredicate.asInstanceOf[Role].s)(ontology)), state.workedOffClauses, ordering)) {
              val iterator: Iterator[OntologyClause] = ontology.getRelevantOntologyClauses(selectedPredicate)
              iterator.foreach { ontologyClause =>
                if (ontologyClause.isAtMost && ontologyClause.body.contains(Concept(IRI(unaryAtom), CentralVariable)(ontology))) {
                  Rules.Nom(selectedPredicate, clause, ontologyClause, Some(unaryAtom), Some(auxiliaryClause), ontology, ordering, resultsBuffer)
                }
              }
            }
          }
        }
      }
    }
  }

  def isNotBlocked(clause: ContextClause, selectedLiteral1: Literal, auxiliaryClause: Option[ContextClause], selectedLiteral2: Option[Literal], contextClauses: ContextClauseIndex, ordering: ContextLiteralOrdering): Boolean = {
    contextClauses.allPredClauses.exists{ predClause => {
      val prunedHead = predClause.head.filterNot {
        case Equality(CentralVariable, _: Constant) => true
        case Equality(_: Constant, CentralVariable) => true
        case Equality(PredVariable, _: Constant) => true
        case Equality(_: Constant, PredVariable) => true
        case _ => false
      }
      val typeClause: ContextClause = new ContextClause(predClause.body,prunedHead)(ordering)
      val newBody = clause.body ++ auxiliaryClause.foldLeft(Array[Predicate]())( (bod,clau) => bod ++ clau.body)
      val newHead = clause.head.filterNot(lit => lit == selectedLiteral1) ++ auxiliaryClause.foldLeft(Array[Literal]())( (hea,clau) => hea ++ clau.head.filterNot(lit => selectedLiteral2.contains(lit)) )
      typeClause.testStrengthening(new ContextClause(newBody,newHead)(ordering)) == 1
    }}
  }



}
