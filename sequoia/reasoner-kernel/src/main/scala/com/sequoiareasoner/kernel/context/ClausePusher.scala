package com.sequoiareasoner.kernel.context

import com.sequoiareasoner.kernel.clauses._
import com.sequoiareasoner.kernel.index.{ImmutableSet, IndexedSequence}
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.structural.DLOntology

import scala.collection.mutable

/** This object contains the routines that push clauses to nearby contexts */
object ClausePusher {

  /** This method carries out the first part of the Pred rule, pushing clauses derived in last round whose head is made exclusively of
    * ground atoms or predecessor triggers, and therefore can be propagated to a relevant predecessor. Note that it
    * does not apply to clauses that were blocked in this round (clauses that have elements in the body that have not been derived in some
    * predecessor). The clauses propagated by this rule are not added to the predecessor, but they are kept apart as a
    * special kind of clauses, the PredClauses. The second part of the Pred rule will index them, and the third part will
    * resolve context clauses with these PredClauses. */
  private[context] def pushPredClausesDerivedInLastRound(state: ContextState,
                                                         contextStructureManager: ContextStructureManager): Unit = {
    while (state.predClausesOnLastRound.nonEmpty) {
      val clause: ContextClause = state.predClausesOnLastRound.removeFirst
      // if (state.isSelectedCore()) System.out.println("Pushing back: " + clause) //DEBUG

      /** We first add the clause to the set of predhead clauses derived in this context */
      state.workedOffClauses.updatePredIndex(clause, add = true)
      /** If the context is a nominal context and the clause does not contain any role in the body and no variable in the
        * head, we need not propagate it because then the clause is only relevant for root contexts, and it is already
        * propagated to them by the RootPred and Query rules; though it makes life simpler if we propagate clauses with empty head */
      //The check for a PredVariable in the head is unnecessary, since if the body contains no roles, given that the core also contains no roles,
      //variable y cannot appear in the head in any way.
      if (state.isNominalContext && clause.body.forall(_.isInstanceOf[Concept]) && !clause.head.exists(l => l.contains(CentralVariable) ) && !clause.head.isEmpty ) {}
      else {
    //    if (state.isSelectedCore()) System.out.println("Propagating clause " + clause)
        /** For each predecessor, we apply the first part of Pred and push the clause */
        for ((incomingEdge: ContextRunnable, edgeLabel: Term) <- state.getRelevantContextStructurePredecessors(clause.body)) {
     //      if (state.isSelectedCore()) System.out.println("...along edge labelled: " + edgeLabel) //DEBUG
          /** Push the clause to each node; the core of the current context is added for debug purposes; the edgeLabel so that the predecessor knows who sent this message */
          contextStructureManager.messageContext(incomingEdge, PredPush(edgeLabel, state.core, IndexedSequence(clause)))
        }
      }

    }
  }

  /** This method pushes clauses that were already in the context, but there is a new connection along which they
    * can be propagated. */
  private[context] def pushWorkedOffPredClauses(state: ContextState,
                                             contextStructureManager: ContextStructureManager,
                                             contextChannel: ContextRunnable,
                                             edgeLabel: Term,
                                             predicate: Predicate,
                                             parentCore: ImmutableSet[Predicate] = ImmutableSet.empty ): Unit = {
    //TODO: Add check that predecessor context contains all relevant predicates for each pred clause, including the new one.
    /** If the new predicate is part of the core, all clauses should be considered; otherwise, only those clauses
      * that contain such predicate in the body. */
    /** In nominal context, I don't want to propagate PredClauses that have a head exclusively ground; such ground
      * atoms will be taken care of by interactions between Root and Query contexts (Query rule) */
    val predClauses: IndexedSequence[ContextClause] = if (!state.isNominalContext) {
      if (state.core contains predicate) state.workedOffClauses.allPredClauses
        else state.workedOffClauses.bodyPredicateLookupPredClauses(predicate)
    } else {
      if (state.core contains predicate)  state.workedOffClauses.allNonGroundHeadPredClauses
        else state.workedOffClauses.lookupNonGroundHeadPredClauses(predicate)
    }
    /** If we are propagating from a nominal context, we do not need to propagate clauses that will not contain variable `x` once propagated,
      * as these will be propagated by other rules in the root. */
    if (predClauses.nonEmpty) {
      //if (state.isSelectedCore2() && state.isSelectedPredicate(predicate) && state.isSelectedCore(parentCore)) {
      //  for (cl <- predClauses) if (state.isSelectedClause(cl)) System.out.println("[Physiological] Clause " + cl + "can be back-propagated to context with core " + parentCore + " connected through " + edgeLabel)
      // }
      contextStructureManager.messageContext(contextChannel, PredPush(edgeLabel, state.core, predClauses))
    }
  }

  /** This method pushes to the relevant successor all clauses derived in the last round that can trigger a Succ rule
    *  and add clauses to a successor. */
  private[context] def pushSuccClausesDerivedInLastRound(state: ContextState,
                                                      ontology: DLOntology,
                                                      contextStructureManager: ContextStructureManager,
                                                      contextChannel: ContextRunnable): Unit = {
    state.succTriggers.forEachNewTrigger { p =>
     // if (state.isSelectedCore() && state.isSelectedPredicate(p)) System.out.println("[CheyneStokes] Predicate " + p + " triggered Succ!")
      val t = p.maximalTerms._1
      t match {
        case FunctionalTerm(_) =>
        case _ => throw new IllegalStateException(s"Predicate $p given by ContextState.forEachNewSuccPredicate should " +
          s"contain a function symbol as its maximum term.")
      }
      /** Here we do not add the nominal to the next context clause, since if the successor is also a nominal context,
        * the RSucc rule takes care of this. */
      val sigma = new ForwardsInterContextMapping(t,None)
      val pSigma = p.applySubstitution(sigma)
      /* Implementing the Succ rule of the calculus in the generality allowed for in the paper might be too
       * expensive in practice: If the neighbour already exists then one would have to query the neighbour process for
       * whether T -> T are contained in the neighbour for each T in K2 (one communication), and then read the reply
       * (another communication). If the reply is NO, then this process would then query the strategy (one
       * communication), and then read the reply (another communication). In practice, it is likely that the strategy
       * will return the same neighbour as we started with, and it is also quite unlikely that the core of a new
       * neighbour would have been a strict superset of the exiting neighbour (i.e. it is unlikely that any of the
       * predicates in K2 resulted from Horn clauses). It is much cheaper (in terms of inter-process communication) to
       * send one message to the existing neighbour and to not have to wait for any reply.
       * Furthermore, if you get a context with a new core for the term `t` you have to reinitialize the context with
       * the predicates for overloading.
       */
      val edge: ContextRunnable =
        state.getSuccessorOrElseUpdate(t, {
          // Create new successor by communicating with Strategy.
          val K1: ImmutableSet[Predicate] = ontology.getKnownPredicates(t)
          contextStructureManager.getSuccessor(K1)
        })
      // TODO: Undo the addition of the core to the SuccPush message
      contextStructureManager.messageContext(edge, SuccPush(contextChannel, t, pSigma, state.core))
    }
  }

  /** Method for propagating clauses derived in the last round that can trigger the RootSucc rule to propagate a
    * clause to the successor context */
  /** Furthermore, when this happens from nominal o to nominal u, non-ground propagators in nominal o must
  //  be passed to u, as these propagators, which are of the form A(x) -> A(x) with A a unary atom,
  // or R(y,x) -> R(y,x) or R(x,y) -> R(x,y) are the only ORIGINAL clauses in
  // the context of o that cannot be regenerated in the context of u from T -> O(x) -- indeed, all clauses in o
  // are derived from T -> O(x), from non-ground propagators, or ground propagators, but the latter are always automatically
  // derived in each nominal context due to the work ground propagators are propagated through the context structure.*/
  /** Update!! With the new theory of cloud of nominal contexts, we argue differently for completeness, and do not
    * need these propagators */

  private[context] def pushRootSuccClausesDerivedInLastRound(state: ContextState,
                                                          ontology: DLOntology,
                                                          contextStructureManager: ContextStructureManager,
                                                          contextChannel: ContextRunnable): Unit = {
    /* Delaying pushing of RootSucc clauses helps ?? */
    state.rootSuccTriggers.forEachNewTrigger { p => {
      /** Each new root succ predicate can be propagated to as many nominal contexts as nominals appear on it */
      val nominals: (Constant,Option[Constant]) = p match {
        case Concept(_, t: Constant) => (t, None)
        case Role(_, t: Constant, s: Constant) => (t, Some(s))
        case Role(_, t: Constant, CentralVariable) => (t, None)
        case Role(_, CentralVariable, t: Constant) => (t, None)
        case _ => throw new IllegalStateException(s"ContextState.forEachNewRootSuccPredicate iterates over $p, which is not a RootSucc trigger.")
      }
      val v = nominals._1
      val comesFromNominalCore = if (state.isNominalContext) Some(state.core.toSeq.head.asInstanceOf[Concept].iri.uid) else None
      val sigma = new ForwardsInterContextMapping(v,comesFromNominalCore)
      val pSigma = p.applySubstitution(sigma)
      val edge: ContextRunnable =
        state.getSuccessorOrElseUpdate(v, {
          contextStructureManager.getNominalContext(v)
        })
      contextStructureManager.messageContext(edge, SuccPush(contextChannel, v, pSigma, state.core))
      nominals._2.foreach(x => {
        val sigma = new ForwardsInterContextMapping(x,comesFromNominalCore)
        val pSigma = p.applySubstitution(sigma)
        val edge: ContextRunnable =
          state.getSuccessorOrElseUpdate(x, {
            contextStructureManager.getNominalContext(x)
          })
        contextStructureManager.messageContext(edge, SuccPush(contextChannel, x, pSigma, state.core))
      })
      /**THIS SHOULD probably be a push of its own */
      /** This will not activate for derived certain facts; which is good. */
      p match {
        case Concept(_, _: Constant) =>
          for (newEdge <- state.getSuccessors) {
            // if (state.isSelectedCore()) System.out.println("Propagating predicate: " + p + " to a successor")
       //     println("Propagating predicate: " + p + " to a successor from ")
       //     for (a <- state.core) println(a + " ")
            contextStructureManager.messageContext(newEdge, PossibleGroundFactPush(contextChannel, v, p))
          }
        case _ =>
      }
    }
    }
  }

  /** This method propagates, back to a root node that could collapse into a nominal, any clause that has a query head,
    * and such that its body consists of exactly the core of the original root node plus query hooks in that root node. */
  /** This is the equivalent of using the Eq rule in the calculus to reduce an atom of the form A(o) in a query context
    * to an atom of the form A(x), using a clause Gamma -> Delta vee x=o. This is a complement to rule Coll which draws
    * links from query contexts to atomic contexts with x = o */
  //TODO: Modify the Coll and Query clauses: when they happen from nominal o to nominal u, query hooks in nominal o must
  //TODO: be passed to u, as these hooks, which are of the form A(x) -> A(x) with A a query atom, are the only clauses in
  //TODO: the context of o that cannot be regenerated in the context of u from T -> O(x) -- note that other clauses in
  //TODO: the context of o that also cannot be regenerated include y in the body, or are relevant only to propagate to a predecessor of
  //TODO: the nominal node, and as such they are not relevant for the case when a query atom context collapses into a nominal.
  private[context] def pushQueryClausesDerivedInLastRound(state: NominalContextState,
                                                       contextStructureManager: ContextStructureManager): Unit = {
    if (!state.isNominalContext) return
    val nominal: Constant = Term(IRI.nominalConceptUid2NominalIriStringName(state.core.toSeq.head.iri.uid))
    while (state.queryClausesOnLastRound.nonEmpty) {
      val clause: ContextClause = state.queryClausesOnLastRound.removeFirst
      // if (state.isSelectedCore()) System.out.println("Pushing back: " + clause) //DEBUG
      state.workedOffClauses.updateQueryIndex(clause, add = true)
      /** If the body is empty, we must pass it to all predecessors via a core labelled edge */
      if (clause.body.isEmpty) {
        for (incomingEdge <- state.getAllRootPredecessors()) {
          contextStructureManager.messageContext(incomingEdge, QueryPush(nominal, IndexedSequence(clause)))
        }
      } else {
        for (predicate <- clause.body) {
          state.getRootPredecessor(predicate).foreach { incomingEdge =>
            contextStructureManager.messageContext(incomingEdge, QueryPush(nominal, IndexedSequence(clause)))
          }
        }
      }
    }
  }

  private[context] def pushWorkedOffQueryClauses(state: NominalContextState,
                                              contextStructureManager: ContextStructureManager,
                                              contextChannel: ContextRunnable,
                                              edgeLabel: Predicate): Unit = {
    /** Clauses that are relevant are those that contain the edge label (the core of the root context) in the body, and those with empty body */
    val relevantClauses: IndexedSequence[ContextClause] = state.workedOffClauses.bodyPredicateLookupQueryClausesIncludingEmptyBody(edgeLabel)

    val nominal: Constant = Term(IRI.nominalConceptUid2NominalIriStringName(state.core.toSeq.head.iri.uid))
    if (relevantClauses.nonEmpty) {
      //if (state.isSelectedCore2() && state.isSelectedPredicate(predicate) && state.isSelectedCore(parentCore)) {
      //  for (cl <- predClauses) if (state.isSelectedClause(cl)) System.out.println("[Physiological] Clause " + cl + "can be back-propagated to context with core " + parentCore + " connected through " + edgeLabel)
      // }
      contextStructureManager.messageContext(contextChannel, QueryPush(nominal, relevantClauses))
    }
  }


  /** If any collapse into a nominal is detected in a root context, the core must be pushed into the nominal context */
  private[context] def pushRootCollapsesDerivedInLastRound(state: ContextState,
                                                           ontology: DLOntology,
                                                           contextStructureManager: ContextStructureManager,
                                                           contextChannel: ContextRunnable): Unit = {
    state.rootEqualities.forEachNewTrigger { eq =>
      val nominal: Constant = eq match {
        case Equality(CentralVariable, b: Constant) => b
        case Equality(b: Constant, CentralVariable) => b
        case _ => throw new IllegalStateException(s"Equality $eq should contain a central variable and a nominal.")
      }
      val edge: ContextRunnable =
        state.getSuccessorOrElseUpdate(nominal, {
          contextStructureManager.getNominalContext(nominal)
        })
      val core: Predicate = state.core.toSeq.head
      contextStructureManager.messageContext(edge, CollPush(contextChannel, core))
    }
    //This below is no longer necessary, because we propagate already all certain clauses to relevant contexts //
//    /** If the equality is certain and we propagate from a nominal context, it must be propagated as a certain fact top -> A */
//    state.certainRootEqualities.forEachNewTrigger { eq =>
//      val nominal: Constant = eq match {
//        case Equality(CentralVariable, b: Constant) => b
//        case Equality(b: Constant, CentralVariable) => b
//        case _ => throw new IllegalStateException(s"Equality $eq should contain a central variable and a nominal.")
//      }
//      contextStructureManager.contextRoundStarted()
//      val edge: UnboundedChannel[InterContextMessage] =
//        state.getSuccessorOrElseUpdate(nominal, {
//          contextStructureManager.getNominalContext(nominal)
//        })
//      val core: Predicate = state.core.toSeq.head
//      edge ! CollPush(contextChannel, core, state.isNominalContext)
//    }
  }

  private[context] def pushInconsistentOntologyMessage(state: ContextState, manager: ContextStructureManager): Unit = {
    if (state.inconsistencyIsGuaranteed()) manager.flagOntologyAsInconsistent()
  }

  def transform(oldHead: Array[Literal], nominal: Constant, ontology: DLOntology, iri: IRI): Array[Literal] = {
    /** To ensure we avoid repetition, we construct the new head as a set */
    val newHeadBuffer = new mutable.HashSet[Literal]
    for (literal <- oldHead) {
      val newLiteral: Literal = literal match {
        /** We replace `x` by the constant corresponding to the nominal context. If literal of the form x=a, we write O(a),
          * so that it can act in the target context as a selected literal for potential applications of r-Pred in the future. */
        case Concept(b, CentralVariable) => Concept(b, nominal)(ontology)
        case Role(r, CentralVariable, CentralVariable) => Role(r, nominal, nominal)(ontology)
        case Role(r, a: Constant, CentralVariable) => Role(r, a, nominal)(ontology)
        case Role(r, CentralVariable, a: Constant) => Role(r, nominal, a)(ontology)
        case Equality(a: Constant, CentralVariable) => Concept(iri, a)(ontology)
        case Equality(CentralVariable, a: Constant) => Concept(iri, a)(ontology)
        case Inequality(a: Constant, CentralVariable) => if (a.id > nominal.id) Inequality(a, nominal) else Inequality(nominal, a)
        case Inequality(CentralVariable, a: Constant) => if (a.id > nominal.id) Inequality(a, nominal) else Inequality(nominal, a)
        case _ => literal
      }
      newHeadBuffer.add(newLiteral)
    }
    newHeadBuffer.toArray
  }


  //TODO: Unify treatment of CFGs exchange between nominal contexts.
  /** Note: this is only triggered in nominal contexts */
  private[context] def pushCertainGroundClausesDerivedInLastRound(state: NominalContextState, manager:ContextStructureManager, ontology: DLOntology): Unit = {
    val nominal: Constant = Term(IRI.nominalConceptUid2NominalIriStringName(state.getCoreConcept.iri.uid))
    while (state.certainGroundClausesOnLastRound.unprocessedNonEmpty) {
      val unprocessedCGC: ContextClause = state.certainGroundClausesOnLastRound.nextUnprocessed
      val newHead = transform(unprocessedCGC.head,nominal,ontology,state.getCoreConcept.iri)
      /** Send to all relevant contexts that mention this nominal */
      state.constantPredecessors.foreach { edge =>
        manager.messageContext(edge, CGCPush(ContextClause(unprocessedCGC.body, newHead)(state.ordering),state.core))
      }
    }
  }

  /** Note: this is also only triggered in nominal contexts */
  private[context] def pushWorkedOffCertainGroundClauses(state: NominalContextState, manager:ContextStructureManager,
                                                         targetContext: ContextRunnable, ontology: DLOntology): Unit = {
    val nominal: Constant = Term(IRI.nominalConceptUid2NominalIriStringName(state.getCoreConcept.iri.uid))
    for (clause <- state.workedOffCertainGroundClauses) {
      val newHead = transform(clause.head,nominal,ontology,state.getCoreConcept.iri)
      /** Send to all relevant contexts that mention this nominal */
        manager.messageContext(targetContext, CGCPush(ContextClause(clause.body, newHead)(state.ordering),state.core))
    }
  }

 /** This sends a request to a nominal context saying ``I introduced a new constant corresponding to yours; please give
   * me all function-free certain ground clauses */
  private[context] def pushRequestAllCGCsForConstantsIntroducedInLastRound(state: ContextState, manager: ContextStructureManager,
                                              contextChannel: ContextRunnable) {
    val constantsIntroducedInLastRound = state.getAndClearIntroducedConstantsOnLastRound
    for (constant <- constantsIntroducedInLastRound) {
     // if (state.isSelectedCore()) println("Requesting all CGCs in context with core " + state.core + " for constant " + constant)
      manager.messageContext(manager.getNominalContext(constant), ConstantMentionedPush(contextChannel))
      /** To ensure that every nominal context O contains all CGCs that mention `o`, if such CGC is mentioned in another
        * (nominal) context, we propagate it to O. */
      state match {
        case nomState: NominalContextState => {
     //     if (state.isSelectedCore()) println("Also pushing constant exchange message to the same core")
          val coreConstant = nomState.getCoreConstant
          manager.messageContext(manager.getNominalContext(constant), ConstantExchange(contextChannel,coreConstant))
        }
        case _ =>
      }
    }
  }




//COME HERE!! To ensure that if a certain ground clause mentioning o is in context for o (which is what the CGC propagation
  //mechanism assumes; ensure that CGC push is also triggered for each clause in a nominal context with core o mentioning a constant a,
  //to the nominal context a.


}

//  private[context] def pushCertainGroundFactsDerivedInLastRound(state: ContextState, manager: ContextStructureManager, ontology: DLOntology): Unit = {
//
//    // DEACTIVATED // This has been deactivated because each relevant nominal context should store already all ground facts, and propagate them to the relevant contexts.
//    // DEACTIVATED // ** Get all the new facts; these are added to the context structure manager and used exclusively for redundancy checks in all contexts. */
//    // DEACTIVATED // /val newFacts = state.newCertainGroundFacts
//    // DEACTIVATED // / newFacts.foreach { x => manager.addCertainGroundFact(predicate = x, nominal = IRI(IRI.nominalConceptUid2NominalIriStringName(state.getCoreConcept.iri.uid)).uid) }
//    /** We propagate CGCs to the relevant contexts, where they may participate in further inferences */
//
//    /* Unary facts */
//    val newUnaryFacts = state.newUnaryCertainGroundFacts
//    for (fact <- newUnaryFacts) {
//      val transformedFact: Concept = fact match {
//        case Concept(iri, _: Constant) => Concept(iri,CentralVariable)(ontology)
//        case _ => throw new IllegalStateException("We should only propagate certain unary ground facts of the form B(a)")
//      }
//      val constant4TargetContext: Constant = fact match {
//        case Concept(_, v: Constant) => v
//        case _ => throw new IllegalStateException("We should only propagate certain unary ground facts of the form B(a)")
//      }
//      manager.contextRoundStarted()
//      val edge: UnboundedChannel[InterContextMessage] =
//        state.getSuccessorOrElseUpdate(constant4TargetContext, {
//          manager.getNominalContext(constant4TargetContext)
//        })
//      edge ! UnaryCGFPush(transformedFact)
//    }
//
//    /* Binary facts */
//    val newBinaryFacts = state.newBinaryCertainGroundFacts
//    for (fact <- newBinaryFacts) {
//      val transformedFact: Role = fact match {
//        case Role(iri, CentralVariable, v: Constant) => Role(iri, Term(IRI.nominalConceptUid2NominalIriStringName(state.getCoreConcept.iri.uid)), CentralVariable)(ontology)
//        case Role(iri, v: Constant, CentralVariable) => Role(iri, CentralVariable, Term(IRI.nominalConceptUid2NominalIriStringName(state.getCoreConcept.iri.uid)))(ontology)
//        case _ => throw new IllegalStateException("We should only propagate certain binary ground facts of the form R(x,a) or R(a,x)")
//      }
//      val constant4TargetContext: Constant = fact match {
//        case Role(iri, CentralVariable, v: Constant) => v
//        case Role(iri, v: Constant, CentralVariable) => v
//        case _ => throw new IllegalStateException("We should only propagate certain binary ground facts of the form R(x,a) or R(a,x)")
//      }
//      manager.contextRoundStarted()
//      val edge: UnboundedChannel[InterContextMessage] =
//        state.getSuccessorOrElseUpdate(constant4TargetContext, {
//          manager.getNominalContext(constant4TargetContext)
//        })
//      edge ! BinaryCGFPush(transformedFact)
//    }
//
//    /* Equality facts */
//    val newEqualityFacts = state.newEqualityCertainGroundFacts
//    for (fact <- newEqualityFacts) {
//      val transformedFact: Equality = fact match {
//        case Equality(CentralVariable, _: Constant) => Equality(Term(IRI.nominalConceptUid2NominalIriStringName(state.getCoreConcept.iri.uid)),CentralVariable)
//        case Equality(_: Constant, CentralVariable) => Equality(CentralVariable,Term(IRI.nominalConceptUid2NominalIriStringName(state.getCoreConcept.iri.uid)))
//        case Equality(_: Constant, _:Constant) => fact.asInstanceOf[Equality]
//        case _ => throw new IllegalStateException("We should only propagate certain binary ground facts of the form R(x,a) or R(a,x)")
//      }
//      /** In case a == b, we pass it only to nominal context a, for this same rule will pass it to context b */
//      val firstConstant4TargetContext: Constant = fact match {
//        case Equality(CentralVariable, v: Constant) => v
//        case Equality(v: Constant, CentralVariable) => v
//        case Equality(v: Constant, _: Constant) => v
//        case _ => throw new IllegalStateException("We should only propagate certain binary ground facts of the form R(x,a) or R(a,x)")
//      }
//      manager.contextRoundStarted()
//      val edge: UnboundedChannel[InterContextMessage] =
//        state.getSuccessorOrElseUpdate(firstConstant4TargetContext, {
//          manager.getNominalContext(firstConstant4TargetContext)
//        })
//      edge ! EqualityCGFPush(transformedFact)
//    }
//
//    //for (context <- manager.getAllContexts) {
//    //  manager.contextRoundStarted()
//    //  state.core foreach {
//    //    case Concept(iri,_) =>
//    //      context ! CertainGroundFactPush(newFacts, iri.uid)
//    //    case _ =>
//    //  }
//   // }
//  }
