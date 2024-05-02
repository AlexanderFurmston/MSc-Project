/*
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This file is part of Sequoia, an OWL 2 reasoner that supports the SRIQ subset of OWL 2 DL.
 * Copyright 2017 by Andrew Bate <code@andrewbate.com>.
 *
 * This code is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 3 only,
 * as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License version 3 for more details (a copy is
 * included in the LICENSE file that accompanied this code).
 *
 * You should have received a copy of the GNU General Public License
 * version 3 along with this work.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * This file is available under and governed by the GNU General Public
 * License version 3 only, as published by the Free Software Foundation.
 * However, the following notice accompanied the original version of this
 * file:
 *
 * Copyright (c) 2016, Andrew Bate, University of Oxford <andrew.bate@cs.ox.ac.uk>.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in the
 *       documentation and/or other materials provided with the distribution.
 *     * Neither the name of the copyright holder nor the names of its contributors
 *       may be used to endorse or promote products derived from this software
 *       without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package com.sequoiareasoner.kernel.structural

import com.sequoiareasoner.kernel.clauses.Term._
import com.sequoiareasoner.kernel.clauses.{CentralVariable, Concept, Constant, Equality, FunctionalTerm, Inequality, NeighbourVariable, OntologyClause, OriginalIndividual, Predicate, Role, STClause, Substitution, Term, TermSubstitution, Literal => DLLiteral}
import com.sequoiareasoner.kernel.index.{CollectionMakeString, ImmutableSet, IntSet, TotalIRIMultiMap}
import com.sequoiareasoner.kernel.owl.PredefinedOWLClass._
import com.sequoiareasoner.kernel.owl.iri._
import com.sequoiareasoner.kernel.owl.model._
import com.sequoiareasoner.kernel.structural.chains.PreprocessedAxiomCollection
import com.sequoiareasoner.arrayops._

import scala.collection.mutable

object DLOntology {
  /** --------------------------------------- ??? -------------------------------------- */
  //D Seems like this is not used at all.
  //D  @inline def Body(ps: Predicate*) = Array(ps: _*) (D: seems to do nothing)
  //D  @inline def Head(ls: DLLiteral*) = Array(ls: _*)  (D: seems to do nothing)
}

/** Representation of ontology using during algorithm execution. The construction of this object implements
  * structural transformation.
  * @param axioms           the axioms to structurally transform into ontology clauses.
  * @param featureObserver  the observer to call when unsupported logical features are encountered in the input axioms.
  */
class DLOntology(axioms: Iterable[Axiom], featureObserver: UnsupportedFeatureObserver, ignoreABox: Boolean = false) extends CollectionMakeString {
  private[this] implicit val self: DLOntology = this


  /** ------------------------------------- ONTOLOGY INDICES -------------------------------------- */


  /** Indices */

  /** Literal-2-OntologyClause: maps each literal to ontology clauses that contain it in the body **/
  private[this] val makeElementData: Int => Array[OntologyClause] = new Array[OntologyClause](_)
  /** Concept-2-OntologyClause: maps each concept UID C to the set of clauses that contain C(x) in the body. */
  private[this] val conceptClauses = new TotalIRIMultiMap(makeElementData)
  /** ForwardRole-2-OntologyClause: maps each role UID R to the set of clauses that, for some i, contain R(x, z_i) in the body. */
  private[this] val forwardRoleClauses = new TotalIRIMultiMap(makeElementData)
  /** BackwardRole-2-OntologyClause: maps each role UID R to the set of clauses that, for some i, contain R(z_i, x) in the body. */
  private[this] val backwardRoleClauses = new TotalIRIMultiMap(makeElementData)
 /** FunctionSymbol-2-Predicate: maps a function symbol to its *known* predicates: those that are guaranteed to hold for that function symbol i.e.
   * if the symbol is f(x) and it could only have been generated by a clause that has B(f(x)) in the head, then B is one of those predicates. */
  private[this] val functionTermMap = new mutable.LongMap[ImmutableSet[Predicate]]
  /** Constant-2-Predicate: maps a constant to predicates that according to the ontology are guaranteed to hold for that nominal */
  private[this] val individualTermMap = new mutable.LongMap[ImmutableSet[Predicate]]
  /** Ontology clauses with empty body, excluding ABox */
  private[this] val emptyBodyNonGroundClauses = new mutable.HashSet[OntologyClause]
// THIS IS FOR THE DAY WE DO SOMETHING ELSE WITH THE ABOX
//  /** ABox assertions of the form C(o), a = o, a =/= o. Key (int) is the uid of the constant,
//    * value Set[int] is the uid of the corresponding concepts or constant,
//    * first Boolean is true if it is a concept and false if an equation; second Boolean is
//    * true if a concept or equality, and false if an inequality. */
//  private[this] val abox1 = collection.mutable.Map[Int,collection.mutable.Set[(Int,Boolean,Boolean)]]()

  //Uncommenting this for the Kaminsky Optimisation
  private[this] val abox1 = collection.mutable.Map[Int,collection.mutable.Set[(Int)]]()


  //  /** ABox assertions of the form R(o,a), and negation R(o,a). Key (int) is the uid of the constant,
//    * first value Set[int] is the uid of the role, second value Set[int]
//    * is the value of the constant, first Boolean is true iff the key goes first,
//    * and second Boolean is true iff the value is not negated. */
//  private[this] val abox2 = collection.mutable.Map[Int,collection.mutable.Set[(Int,Int,Boolean,Boolean)]]()
//  /** Variable that stores whether facts of the form O(o) have been added */


  /** Accessors and modifiers */

  def isForwardRoleSuccTrigger(r: IRI): Boolean = forwardRoleSuccTriggers(r.uid)
  def isBackwardRoleSuccTrigger(r: IRI): Boolean = backwardRoleSuccTriggers(r.uid)
   /** Returns an iterator over the ontology clauses that contain a predicate in the body that can unify with the
    * specified predicate using a central substitution. This implements some Unification Patterns. */
  def getRelevantOntologyClauses(p: Predicate): Iterator[OntologyClause] =
    p match {
      case Concept(iri, _) => conceptClauses(iri).iterator
      case Role(iri, CentralVariable, CentralVariable) => forwardRoleClauses(iri).iterator ++ backwardRoleClauses(iri).iterator
      case Role(iri, CentralVariable, _)  => forwardRoleClauses(iri).iterator
      case Role(iri, _, CentralVariable) =>  backwardRoleClauses(iri).iterator
      case _ => throw new Exception(s"There is no unification pattern for $p")
    }
  /** Given term t and predicate p, adds p to the list of known predicates for t, which must be a function or constant */
  private[this] def putKnownPredicate(t: Term, p: Predicate): Unit = {
    t match {
      case FunctionalTerm(i) => functionTermMap.put(i, functionTermMap.getOrElse(i,ImmutableSet.empty) + p)
      case OriginalIndividual(i) => individualTermMap.put(i, individualTermMap.getOrElse(i,ImmutableSet.empty) + p)
      case _ => throw new Exception(s"Known predicates can only be stored for functional terms or individuals, but not for $t")
    }
  }
  /** Returns known predicates for a given term t, which must be a function or constant */
  def getKnownPredicates(t: Term): ImmutableSet[Predicate] = {
    val value: Option[ImmutableSet[Predicate]] = t match {
      case FunctionalTerm(i) => functionTermMap.get(i)
      case OriginalIndividual(i) => individualTermMap.get(i)
      case _ =>
        throw new Exception(s"Known predicates can only be stored for functional terms or individuals, but not for $t")
        None
    }
    value.getOrElse(ImmutableSet.empty)
  }
  def getNonGroundClausesWithEmptyBody: Iterator[OntologyClause] = emptyBodyNonGroundClauses.iterator


  /** ------------------------------- SPECIAL PREDICATES AND CLAUSES --------------------------------------- */

  /** Unsatisfiable predicates */

  private[this] val unsatisfiablePredicates = new IntSet
  /** Checks if a given literal is one of the Unsatisfiable Predicates */
  def isNothing(l: DLLiteral): Boolean = l match {
    case p: Predicate => unsatisfiablePredicates contains p.iri.uid
    case _ => false
  }

  /** Rule triggers */

  /** conceptSuccTriggers contains A if A(x) occurs in the body of some clause. */
  private[this] val conceptSuccTriggers = new mutable.BitSet
  def isConceptSuccTrigger(c: IRI): Boolean = conceptSuccTriggers(c.uid)
  /** roleSuccTriggers contains R if, for some i, we have R(x,z_i) occurs in the body of some clause. */
  private[this] val forwardRoleSuccTriggers = new mutable.BitSet
  /** backwardRoleSuccTriggers contains R if, for some i, we have R(z_i,x) occurs in the body of some clause. */
  private[this] val backwardRoleSuccTriggers = new mutable.BitSet
  /** contains, for each S(x,z_i) participating in an at-most restriction, the atoms B(x) - if any - that participate in such restriction */
  private[this] val unaryAtoms4AtMostRestriction: mutable.Map[Int,collection.mutable.Set[Int]] = collection.mutable.Map()
  def exposeUnaryAtoms4AtMostRestriction: mutable.Map[Int,collection.mutable.Set[Int]] = unaryAtoms4AtMostRestriction


  /** Special concepts */

  /** Set of original atomic concepts in the ontology */
  private[this] val atomicConcepts = new mutable.HashSet[Int]
  /** Universal concept */
  private[this] val topConcept = Set(IRI.owlThing.uid)
  /** Set of auxiliar concepts O(x) each corresponding to a nominal o */
  private[this] val nominalConcepts = new mutable.HashSet[Int]
  /** Atomic concepts that must be initialised for classification */
  def getConceptsToClassify: Set[Int] = atomicConcepts.toSet ++ nominalConcepts.toSet ++ topConcept
  /** Atomic concepts that must be initialised for consistency checking */
  def getConceptsForConsistency: Set[Int] = topConcept ++ nominalConcepts.toSet
  def containsNominals: Boolean = nominalConcepts.nonEmpty

  var canABoxProduceInconsistency: Boolean = false
  def getCanABoxProduceInconsistency: Boolean = canABoxProduceInconsistency

  def hasABoxAxioms: Boolean = preProcessedInput.hasABoxAxioms

// THIS SEEMS UNNECESSARY, it is commented out for the moment.
// Kaminsky Optimisation:
  private[this] var trivialABoxAdded: Boolean = false
  /** Method that ensures the trivial ABox has been added and returns the ABox */
  def ensureTrivialFactsAddedAndGetABox: mutable.Map[Int,mutable.Set[Int]] = {
    if (!trivialABoxAdded) {
      for (nominalConcept <- nominalConcepts) {
        abox1.getOrElseUpdate(IRI(IRI.nominalConceptUid2NominalIriStringName(nominalConcept)).uid, mutable.Set[Int]()) += nominalConcept
      }
      trivialABoxAdded = true
    }
    abox1
  }

  /** ---------------------- MAIN ONTOLOGY EDIT AND RETRIEVE METHODS ------------------------------------- */

  /** Adds a clause to this Ontology; indices are updated in the process */
  private[this] def addClauseToOntology(c: OntologyClause): Unit = {
    val body = c.body
    if (!canABoxProduceInconsistency && c.head.isEmpty) {
      canABoxProduceInconsistency = true
    }
    /** If the clause has empty body, we add it to emptyBodyNonGroundClauses */
    if (body.length == 0) {
        /** Check that the ABox has been internalised. */
      assert(c.head.forall(lit => !lit.isGround))
      emptyBodyNonGroundClauses += c
//       THIS CODE CHUNK IS FOR THE DAY I DO SOMETHING DIFFERENT WITH THE ABOX
//      if (c.head.length == 1) {
//        if (c.head(0).isGround) c.head(0) match {
//          case Concept(iri, t) => abox1.getOrElseUpdate(IRI(t.toString).uid, mutable.Set[(Int, Boolean, Boolean)]()) += ((iri.uid, true, true))
//          case Equality(t1, t2) => {
//            abox1.getOrElseUpdate(IRI(t1.toString).uid, mutable.Set[(Int, Boolean, Boolean)]()) += ((IRI(t2.toString).uid, false, true))
//            abox1.getOrElseUpdate(IRI(t2.toString).uid, mutable.Set[(Int, Boolean, Boolean)]()) += ((IRI(t1.toString).uid, false, true))
//          }
//          case Inequality(t1, t2) => {
//            abox1.getOrElseUpdate(IRI(t1.toString).uid, mutable.Set[(Int, Boolean, Boolean)]()) += ((IRI(t2.toString).uid, false, false))
//            abox1.getOrElseUpdate(IRI(t2.toString).uid, mutable.Set[(Int, Boolean, Boolean)]()) += ((IRI(t1.toString).uid, false, false))
//          }
//          case Role(iri, t1, t2) => {
//            abox2.getOrElseUpdate(IRI(t1.toString).uid, mutable.Set[(Int, Int, Boolean, Boolean)]()) += ((iri.uid, IRI(t2.toString).uid, true, true))
//            abox2.getOrElseUpdate(IRI(t2.toString).uid, mutable.Set[(Int, Int, Boolean, Boolean)]()) += ((iri.uid, IRI(t1.toString).uid, false, true))
//          }
//        }
//        else emptyBodyNonGroundClauses += c
//      } else {
//        assert(c.head.forall(lit => !lit.isGround), "Some process tried to add a non-Horn ground clause to the ontology.")
//        emptyBodyNonGroundClauses += c
//      }
    } else {
      /** If the head is empty and the body is a single predicate of form C(x), R(x,z) or R(z,x), the predicate is unsatisfiable */
      /** But not R(x,x), since in that case it may be the case that R is irreflexive, but not empty */
      if (body.length == 1 && c.head.length == 0) {
        body(0) match {
          case Concept(_,_) => unsatisfiablePredicates += body(0).iri.uid
          case Role(_,CentralVariable,NeighbourVariable(_)) => unsatisfiablePredicates += body(0).iri.uid
          case Role(_,NeighbourVariable(_),CentralVariable) => unsatisfiablePredicates += body(0).iri.uid
          case _ =>
        }
      }
      val isAtMostRestriction = c.isAtMost
//      /** Need to search for mentioned nominals due to the way we are treating R(a,b) -- and maybe axioms ObjectHasValue */
//      /** Also, sometimes ObjectOneOf is used alone in the head, so we have to gather those as well */
//      cforeach (c.head) {
//        case p@Concept(iri,_: FunctionalTerm) if iri.isInternalIndividual =>  nominalConcepts += p.iri.uid
//        case p@Concept(iri, CentralVariable) if iri.isInternalIndividual =>  nominalConcepts += p.iri.uid
//        case _ =>
//      }
      /** Check predicates in the body, add them to the corresponding index */
      cforeach (body) {
        case p@Concept(iri, CentralVariable) if iri.isImported =>
          /** Original concepts are added to the list of ``atomic concepts`` used to feed the input for classification.
            * This is an optimisation in disguise: original atomic concepts that do not appear in a body of an ontology
            * clause will just be subclasses of owl:Thing, so we exclude them from classification. */
          atomicConcepts += p.iri.uid
          /** This predicate is a Succ Trigger bc it appears in the body of a clause */
          conceptSuccTriggers(iri.uid) = true
          /** Add to index concept => clauses with that concept in the body */
          conceptClauses.addBinding(iri, c)
        case p@Concept(iri, CentralVariable) if iri.isInternalIndividual =>
          conceptSuccTriggers(iri.uid) = true
          conceptClauses.addBinding(iri,c)
        case Concept(iri, CentralVariable) =>
          conceptSuccTriggers(iri.uid) = true
          conceptClauses.addBinding(iri, c)
        case Role(iri, _: Constant, _) =>
          forwardRoleSuccTriggers(iri.uid) = true
          forwardRoleClauses.addBinding(iri, c)
        case Role(iri, _, _: Constant) =>
          backwardRoleSuccTriggers(iri.uid) = true
          backwardRoleClauses.addBinding(iri, c)
        case Role(iri,CentralVariable,CentralVariable) =>
          forwardRoleSuccTriggers(iri.uid) = true
          forwardRoleClauses.addBinding(iri, c)
          backwardRoleSuccTriggers(iri.uid) = true
          backwardRoleClauses.addBinding(iri, c)
        case Role(iri, CentralVariable, _) =>
          forwardRoleSuccTriggers(iri.uid) = true
          forwardRoleClauses.addBinding(iri, c)
          if (isAtMostRestriction) {
            var existUnaryAtomsInBody = false
            cforeach (body) {
              case Concept(iri2,CentralVariable) => existUnaryAtomsInBody = true ; unaryAtoms4AtMostRestriction.getOrElseUpdate(iri.uid,collection.mutable.Set[Int]()) += iri2.uid
              case _ =>
            }
            /** If the clause is an at-most restriction, but there are no unary atoms, we still need to add it, since later
              * we use keys with emtpty set as value to determine when Nom rule is applicable */
            if (!existUnaryAtomsInBody) unaryAtoms4AtMostRestriction.getOrElseUpdate(iri.uid,collection.mutable.Set[Int]())
          }
        case Role(iri, _, CentralVariable) =>
          backwardRoleSuccTriggers(iri.uid) = true
          backwardRoleClauses.addBinding(iri, c)
        case _ => throw new Error(s"Illegal clause $c. Concepts containing z_i are not allowed to appear in the body.")
      }
    }
  }

  def getOntologyClauses: Iterator[OntologyClause] =
    emptyBodyNonGroundClauses.iterator ++ conceptClauses.valuesIterator ++ forwardRoleClauses.valuesIterator ++ backwardRoleClauses.valuesIterator



 /** ---------------------------- UTILITY METHODS ------------------------------- */


 /** NEIGHBOUR VARIABLE AND FUNCTION SYMBOL MANAGER  */

  private[this] var varIdCount: Int = 1
  private[this] var functionCount: Int = 1
  /** Return a fresh z neighbour variable */
  private def zFresh(): Term = {
    val zIndex = varIdCount
    varIdCount += 1
    z(zIndex)
  }
  /** Return an array of fresh z neighbour variables */
  private def zFresh(num: Int): Array[Term] = {
    val zIndex = varIdCount
    varIdCount += 1
    cyield (0, num) {  i => z(zIndex + i) }
  }
  /** Return an array of fresh terms of the form f(x) where f is a fresh symbol */
  private def fFresh(num: Int): Array[Term] = {
    val fIndex = functionCount
    functionCount += num
    cyield (0, num) { i => f(fIndex + i) }
  }


  /** TERRIBLE TRIFECTA MONITOR */

  /** This monitors the occurrence of a nominal in an inverse role restricted by an at-Most number quantifier */
  private[this] var havocFlag: Boolean = false
  def havocTriggered: Boolean = havocFlag
  def setHavocFlag(value: Boolean) : Unit = havocFlag = value


  /** PRINT ONTOLOGY AS STRING */

  override def toString: String = addString(new StringBuilder, "DLOntology[\n", "\n", "\n]").result

  def addString(b: StringBuilder, start: String, sep: String, end: String): StringBuilder = {
    var first = true
    def append(clause: OntologyClause) =
      if (first) {
        b append clause
        first = false
      } else {
        b append sep
        b append clause
      }
    b append start
    for (clause <- emptyBodyNonGroundClauses) append(clause)
    val seen = new mutable.HashSet[OntologyClause]
    for (clause <- conceptClauses.valuesIterator) if (seen.add(clause)) append(clause)
    for (clause <- forwardRoleClauses.valuesIterator) if (seen.add(clause)) append(clause)
    for (clause <- backwardRoleClauses.valuesIterator) if (seen.add(clause)) append(clause)
    b append end
    b
  }



  /** --------------------------------  * * * ONTOLOGY PROCESSING * * * -------------------------------------- */

  /** A fragment of a clause, where the first element belongs to the body, and the second element belongs to the head */
  private type ClauseFragment = (Seq[Predicate], Seq[DLLiteral])

  private[this] val clauseTransformer = new STClauseToOntologyClauseTransformer

   /** Methods for adding STClauses to Clauses, first transforming them to Clauses if required */
  private[this] def addSTClauseToOntology(c: STClause): Unit = {
    val result = clauseTransformer.transform(c)
    val result2 = (for (c <- result) yield clauseTransformer.transform2(c)).flatten
    for (c <- result2) addClauseToOntology(c)
  }
  private[this] def addSTClausesToOntology(cs: Iterable[STClause]): Unit = {
    val result = clauseTransformer.transform(cs)
    for (c <- result) addClauseToOntology(c)
  }

  /** Given an object property expression and a term z, obtain the corresponding role in first-order syntax,
    * i.e. R(x,z) or R(z,x), accordingly. This method does not construct the encoding of the property chains using the
    * automaton, and hence it is intended to be used only when handling exact, min and max cardinality expressions. */
  private[this] def getRole(term: Term)(ope: ObjectPropertyExpression): Role =
    ope match {
      case ObjectProperty(iri) =>
        Role(iri, x, term)
      case ObjectInverseOf(ObjectProperty(iri)) =>
        Role(iri, term, x)
    }

  /** Put together clause fragments in the same clause, possibly doing a cross product. */
  private[this] def combine(doCrossProduct: Boolean)(l: Set[ClauseFragment], r: Set[ClauseFragment]): Set[ClauseFragment] =
    if (doCrossProduct)
      for ((lBody, lHead) <- l; (rBody, rHead) <- r) yield (lBody ++ rBody, lHead ++ rHead)
    else
      l ++ r

  /** Apply a given substituton to a given literal  */
  //TODO: What is the purpose of these methods? It looks like one can directly use the applySubstitution methods.
  private[this] def predicateSubstitution(sigma: Substitution)(l: Predicate): Predicate = l applySubstitution sigma
  private[this] def literalSubstitution(sigma: Substitution)(l: DLLiteral): DLLiteral = l applySubstitution sigma

  /** Returns whether a given literal contains no neighbour variables */
  private[this] def noNeighbourTerm(l: DLLiteral): Boolean = l match {
    case Concept(_, CentralVariable) | Concept(_,_: Constant)  => true
    case Role(_, CentralVariable, CentralVariable) | Role(_, _: Constant, _: Constant) |
    Role(_, CentralVariable, _: Constant) | Role(_, _: Constant, CentralVariable) => true
    case _ => false
  }

  /** -----   -----   ----   ----- INITIALISATION -----   ------   -----   ------   -------*/


  /** -------------------------STEP 1: Preprocessing */

  /** The pre-processing step does some steps such as rejecting unsupported axioms, encoding away property chains,
    * and producing some indices for optimisation.
    * The result is a PreprocessedAxiomCollection, which contains the axioms in several internal buffers, from where
    * they can be picked from. */
  private[this] val preProcessedInput: PreprocessedAxiomCollection = new PreprocessedAxiomCollection(axioms, featureObserver, ignoreABox)

  /** ------------------------ STEP 2: Clausification */

  /** The clausification step transforms all axioms generated in the pre-processing phase to DL rules and writes them in
    * the Ontology. Note below that the main clausification method can produce clauses that are of type STClause. These
    * clauses may not be valid ontology clauses (type Clause) due to having concepts of the form C(zi) in the body.
    * Therefore, the method that adds such clauses to the ontology will first convert them
    * from STClause to a set of (ontology) Clauses.
    *
    * This method also rejects axioms unsupported by Sequoia that have not been flagged in the preprocessing step */

  /** This is a cache for the method normalising class expressions */
  private[this] val interning = new mutable.AnyRefMap[ClassExpression, Set[ClauseFragment]]

  /** Generates a universal corresponding to a _simple_ object property expression.
    * * * A -> \forall R . C  becomes  A(x) \wedge R(x,z1) -> C(z1) */
  private[this] def forAll(ope: ObjectPropertyExpression, ce: ClassExpression): Set[ClauseFragment] = {
    val zSymbol: Term = zFresh()
    val role: Predicate = getRole(zSymbol)(ope)
    val fragmentsFromFiller: Set[ClauseFragment] = normalise(ce)

    val canInlineFiller = fragmentsFromFiller forall {
      case (body, head) => body.forall(noNeighbourTerm) && head.forall(noNeighbourTerm)
    }

    if (canInlineFiller) {
      // Optimization.
      val sigma = new TermSubstitution(zSymbol)
      for ((body, head) <- fragmentsFromFiller) yield {
        val sigmaBody: Seq[Predicate] = body map predicateSubstitution(sigma)
        val sigmaHead: Seq[DLLiteral] = head map literalSubstitution(sigma)
        (role +: sigmaBody, sigmaHead)
      }

    } else {

      // Generate auxiliary clauses.
      val auxIri = IRI.all()
      val auxConceptNeighbour: Predicate = Concept(auxIri, zSymbol)

      val auxConceptCentral = Concept(auxIri, x)
      // Try to reduce the total number of disjuncts in the set of clauses.
      val negateAux = fragmentsFromFiller forall { case (_, head) => head.isEmpty }

      if (negateAux)
        for ((body, head) <- fragmentsFromFiller)
          addSTClauseToOntology(STClause(body, auxConceptCentral +: head))
      else
        for ((body, head) <- fragmentsFromFiller)
          addSTClauseToOntology(STClause(auxConceptCentral +: body, head))

      val fragment: ClauseFragment =
        if (negateAux) (Seq(role, auxConceptNeighbour), Nil)
        else (Seq(role), Seq(auxConceptNeighbour))

      Set(fragment)
    }
  }

  /**  A -> <= n R . C     becomes  A(x) \bigwedge_{i=0}n (R(x,z_i) \wedge C(z_i)) -> \bigvee_{0<=i<j<=n} z_i = z_j
    *
    * PRECONDITION: `ope` is a simple object property expression. */
  private[this] def atMost(n: Int,
                           ope: ObjectPropertyExpression,
                           ce: ClassExpression): Set[ClauseFragment] = {
    require(n >= 0)

    val zSymbols: Array[Term] = zFresh(n + 1)

    val roles: Seq[Predicate] =
      cyield (0, n + 1) { i => getRole(zSymbols(i))(ope) }.toSeq
    val equalities: Seq[Equality] =
      cyield (0, n + 1, {i => i + 1}, {_ => n + 1}) { (i, j) => Equality(zSymbols(i), zSymbols(j)) }.toSeq

    val fragmentsFromFiller: Set[ClauseFragment] = ce match {
      case cr: OWLClass                     => normalise(ObjectComplementOf(cr))
      case ObjectComplementOf(cr: OWLClass) => normalise(cr)
      case _                                => throw new AssertionError(s"$ce is not in a valid normal form.")
    }

    val zFragments: Seq[Set[ClauseFragment]] =
      cyield (0, n + 1) { i =>
        val sigma = new TermSubstitution(zSymbols(i))
        for ((body, head) <- fragmentsFromFiller) yield {
          val sigmaBody: Seq[Predicate] = body map predicateSubstitution(sigma)
          val sigmaHead: Seq[DLLiteral] = head map literalSubstitution(sigma)
          (sigmaBody, sigmaHead)
        }
      }

    zFragments reduce combine(doCrossProduct = true) map {
      case (body, head) => (body ++ roles, head ++ equalities)
    }

  }

  /**  A -> \exists R . C  becomes  A(x) -> R(x,f(x))  and  A(x) -> C(f(x))
    * A -> >= n R . C     becomes  A(x) -> R(x,f_i(x))  and  A(x) -> C(f_i(x)) for 1 <= i <= n
    *                     and      A(x) -> f_i(x) \neq f_j(x) for 1 <= i < j <= n */
  /** Furthermore, we replace C by an auxiliar atomic concept A_c, and add the transformation of A_c(x) -> C(x) */
  private[this] def atLeast(n: Int,
                            ope: ObjectPropertyExpression,
                            ce: ClassExpression): Set[ClauseFragment] = {
    require(n > 0)

    /** Create n new function symbols */
    val funSymbols: Array[Term] = fFresh(n)

    /** Generate a clause fragment for each inequality */
    val inequalities: Seq[ClauseFragment] =
      cyield (0, n, {i => i + 1}, {_ => n}) { (i, j) => (Nil, Seq(Inequality(funSymbols(j), funSymbols(i)))) }.toSeq

    val fragmentsFromFiller: Set[ClauseFragment] = normalise(ce)

    lazy val auxFillerSuccessor = Concept(IRI.some(), x)

    val allFillers = new mutable.HashSet[Concept]

    for (fragment <- fragmentsFromFiller) fragment match {
      case (Nil, Seq(c @ Concept(iri, CentralVariable)))  =>
        crange (0, n) { i =>
          putKnownPredicate(funSymbols(i), c)
          allFillers += Concept(iri, funSymbols(i))
        }
      case (body, head) =>
        addSTClauseToOntology(STClause(auxFillerSuccessor +: body, head))
        crange (0, n) { i =>
          putKnownPredicate(funSymbols(i), auxFillerSuccessor)
          allFillers += auxFillerSuccessor.applySubstitution(new TermSubstitution(funSymbols(i)))
        }
    }

    val (existentialRoles: Seq[ClauseFragment], knownRole: Role) = ope match {
      case ObjectProperty(iri) =>
        (cyield (0, n) { i => (Nil, Seq(Role(iri, x, funSymbols(i)))) }.toSeq, Role(iri, y, x))
      case ObjectInverseOf(ObjectProperty(iri)) =>
        (cyield (0, n) { i => (Nil, Seq(Role(iri, funSymbols(i), x))) }.toSeq, Role(iri, x, y))
    }

    crange (0, n) { i => putKnownPredicate(funSymbols(i), knownRole) }

    val existentialFillers: Set[ClauseFragment] = allFillers.toSet map {
      c: Concept => (Nil, Seq(c))
    }

    existentialFillers ++ existentialRoles ++ inequalities
  }

  /** This method normalises a class expression and rejects unsupported class expressions */
  /** Funnily enough, negative parts are put to the left of the clause, while positive parts
    * are put to the right. This deals away with the problem of things being negated. */
  private[this] def normalise(ce: ClassExpression): Set[ClauseFragment] = {

    interning.getOrElseUpdate(ce, ce match {

      case OWLClass(iri) =>
        // TODO: add tests for this case
        if (iri.isNothing) Set((Nil, Nil))
        else if (iri.isThing) Set.empty
        else Set((Nil, Seq(Concept(iri, x))))

      case ObjectComplementOf(OWLClass(iri)) =>
        // Since `ce` is in NNF, ObjectComplementOf can only occur immediately before a OWLClass.dde
        if (iri.isNothing) Set.empty
        else if (iri.isThing) Set((Nil, Nil))
        else Set((Seq(Concept(iri, x)), Nil))

      case ObjectComplementOf(ObjectHasSelf(ObjectProperty(iri))) =>
        Set((Seq(Role(iri, x, x)), Nil))

      case ObjectComplementOf(ObjectHasSelf(ObjectInverseOf(ObjectProperty(iri)))) =>
        Set((Seq(Role(iri, x, x)), Nil))

      case ObjectComplementOf(ObjectOneOf(individuals)) =>
        if (individuals.isEmpty) Set.empty
        else {
          /** Recall: due to being in NNF, this OOO has only one individual */
          assert(individuals.size == 1)
          val conceptForNominal = IRI.nominalConcept(individuals.head.getName)
          if (nominalConcepts.add(conceptForNominal.uid)) {
            /** It does not need additional transformation, so we add it directly */
            addClauseToOntology(OntologyClause(Seq(Concept(conceptForNominal, CentralVariable)), Seq(Equality(CentralVariable, Term(individuals.head.getName)))))
          }
          Set((Seq(Concept(conceptForNominal,CentralVariable)),Nil))
          }

      case ObjectIntersectionOf(ces) =>
        if (ces.isEmpty) Set.empty
        else
        {
          val cesNormalised: Set[Set[ClauseFragment]] = ces map normalise
          cesNormalised reduce {
            (fragments1: Set[ClauseFragment], fragments2: Set[ClauseFragment]) =>
              combine(doCrossProduct = false)(fragments1, fragments2)
          }
        }

      case ObjectUnionOf(ces) =>
        if (ces.isEmpty) Set((Nil,Nil))
        else
        {
          val cesNormalised: Set[Set[ClauseFragment]] =
            ces map {
              ce: ClassExpression =>
                val fragments: Set[ClauseFragment] = normalise(ce)
                val shouldInline = fragments.size <= 1 || fragments.forall {
                  case (_, head) => head.isEmpty
                }
                if (shouldInline) {
                  fragments
                } else {
                  val aux = Concept(IRI.disjunct(), x)
                  fragments map {
                    case (body, head) =>
                      addSTClauseToOntology(STClause(aux +: body, head))
                      (Nil, Seq(aux)): ClauseFragment
                  }
                }
            }
          cesNormalised reduce {
            (fragments1: Set[ClauseFragment], fragments2: Set[ClauseFragment]) =>
              combine(doCrossProduct = true)(fragments1, fragments2)
          }
        }

      case ObjectSomeValuesFrom(ope, cex) =>
        atLeast(1, ope, cex)

      case ObjectAllValuesFrom(ope, cex) =>
        forAll(ope, cex)

      case ObjectExactCardinality(n, ope, cex) if n > 0 =>
        val fragments1 = atLeast(n, ope, cex)
        val fragments2 = atMost(n, ope, cex)
        combine(doCrossProduct = false)(fragments1, fragments2)

      case ObjectMaxCardinality(n, ope, cex) =>
        atMost(n, ope, cex)

      case ObjectMinCardinality(n, ope, cex) if n > 0 =>
        atLeast(n, ope, cex)

      case ObjectHasSelf(ObjectProperty(iri)) =>
        Set((Nil, Seq(Role(iri, x, x))))

      case ObjectHasSelf(ObjectInverseOf(ObjectProperty(iri))) =>
        Set((Nil, Seq(Role(iri, x, x))))

      case ObjectOneOf(individuals) =>
        if (individuals.isEmpty) Set((Nil,Nil))
        else {
          val ces = for (individual <- individuals) yield {
            val conceptForNominal = IRI.nominalConcept(individual.getName)
            if (nominalConcepts.add(conceptForNominal.uid)) {
            /** It does not need additional transformation, so we add it directly to the ontology */
              addClauseToOntology(OntologyClause(Seq(Concept(conceptForNominal, CentralVariable)), Seq(Equality(CentralVariable, Term(individual.getName)))))
            }
            OWLClass(conceptForNominal)
          }
          normalise(ObjectUnionOf(ces.asInstanceOf[Set[ClassExpression]]))
        }

      case ObjectHasValue(ope, individual) => {
        val conceptForNominal = IRI.nominalConcept(individual.getName)
        if (nominalConcepts.add(conceptForNominal.uid)) {
          /** It does not need additional transformation, so we add it directly to the ontology */
          addClauseToOntology(OntologyClause(Seq(Concept(conceptForNominal, CentralVariable)), Seq(Equality(CentralVariable, Term(individual.getName)))))
        }
        atLeast(1, ope, OWLClass(conceptForNominal))
      }

      case _: DataExactCardinality =>
        featureObserver.reportUnsupported(ce)

        normalise(owlThing)

      case _: DataMaxCardinality =>
        featureObserver.reportUnsupported(ce)

        normalise(owlThing)

      case _: DataMinCardinality =>
        featureObserver.reportUnsupported(ce)

        normalise(owlThing)

      case _: DataAllValuesFrom =>
        featureObserver.reportUnsupported(ce)

        normalise(owlThing)

      case _: DataHasValue =>
        featureObserver.reportUnsupported(ce)

        normalise(owlThing)

      case _: DataSomeValuesFrom =>
        featureObserver.reportUnsupported(ce)
        normalise(owlThing)

      case _ =>
        throw new AssertionError(s"$ce is not in a valid normal form.")
    })
  }

  /** --------------- Here is where Step 2 actually happens -------------------- */

  /** As noted in PreprocessedAxiomCollection.scala, preprocessed axioms are partitioned in the following disjoint buffers:
    * -Internalised axioms
    * -Asymmetric OPE axioms
    * -Reflexive OPE axioms
    * -Disjoint OPEs axioms
    * -Simple SubObjectProperty axioms
    * Therefore, we must clausify the axioms in each of these sets. */
  for ((lhs: ClassExpression, rhs: ClassExpression) <- preProcessedInput.getInternalizedAxioms) {
    val lhsFragments: Set[ClauseFragment] = normalise(lhs)
    val rhsFragments: Set[ClauseFragment] = normalise(rhs)
    val clauses: Set[STClause] =
      for ((body, head) <- combine(doCrossProduct = true)(lhsFragments, rhsFragments)) yield
        STClause(body, head)
    addSTClausesToOntology(clauses)
  }
  for (AsymmetricObjectPropertyAxiom(ope) <- preProcessedInput.getAsymmetricProperties) {
    val z = zFresh()
    val role = getRole(z)(ope)
    addClauseToOntology(OntologyClause(Seq(role, role.inverse), Nil))
  }
  for (ReflexiveObjectPropertyAxiom(ope) <- preProcessedInput.getReflexiveProperties) {
    val role = getRole(x)(ope)
    addClauseToOntology(OntologyClause(Nil, Seq(role)))
  }
  for (SubObjectPropertyOfAxiom(lhs, rhs) <- preProcessedInput.getSimpleSubProperties) {
    val z = zFresh()
    val lhsRole = getRole(z)(lhs)
    val rhsRole = getRole(z)(rhs)
    addClauseToOntology(OntologyClause(Seq(lhsRole), Seq(rhsRole)))
  }
  for (DisjointObjectPropertiesAxiom(properties) <- preProcessedInput.getDisjointProperties) {
    val prop: Array[ObjectPropertyExpression] = properties.toArray
    val z = zFresh()
    val ps: Array[Role] = cmap (prop) (getRole(z))
    crange (0, ps.length) { i =>
      crange (i + 1, ps.length) { j => addClauseToOntology(OntologyClause(Seq(ps(i), ps(j)), Nil)) }
    }
  }

  //THE CODE CHUNK BELOW IS FOR A DAY I DECIDE TO TREAT THE ABOX DIFFERENTLY THAN JUST INTERNALISING
//  for (axiom <- preProcessedInput.getABoxAxioms) {
//    axiom match {
//      /** Here the idea is to normalise top->C(x); this will create a bunch of clauses
//        * of the form top-> blah, and some ontology clauses of the form A(x)->B(x)... that are just structural transf clauses,
//        * so no worries about introducing unsound clauses to the ontology. With the remaining clauses,
//        * make sure o holds for them. */
//      case ClassAssertionAxiom(ce,individual) => {
//        val fragments = normalise(ce)
//        for ((body,head) <- fragments) {
//          addClauseToOntology(OntologyClause(Concept(IRI.nominalConcept(individual.getName), CentralVariable) +: body, head))
//        }
//          /** Possible optimisation, now disabled: If just one atom in head (most will be, since the form for
//        * clauses of the form top -> C(x) is top -> A1(x) v A2(x) v ...), we add it as top -> A1(o), so that
//        * it can later be added to our ABox buffer. Otherwise, we just use the nominal concept O and add O(x) ^ gamma => delta
//         */
////         if (body.isEmpty && (head.size == 1)) {
////            head(0) match {
////              case Concept(iri,_) => addClauseToOntology(OntologyClause(Nil,Seq(Concept(iri,Term(individual.getName)))))
////              case _ => addClauseToOntology(OntologyClause(Concept(IRI.nominalConcept(individual.getName),CentralVariable) +: body,head))
////              }
////          } else {
////            addClauseToOntology(OntologyClause(Concept(IRI.nominalConcept(individual.getName),CentralVariable) +: body,head))
////          }
//      }
//      case ObjectPropertyAssertionAxiom(ope,indiv1,indiv2) => {
//        val conceptForIndividual1 = IRI.nominalConcept(indiv1.getName)
//        val conceptForIndividual2 = IRI.nominalConcept(indiv2.getName)
//        ope match {
//           case ObjectProperty(iri) => addClauseToOntology(OntologyClause(Nil,Seq(Role(iri,Term(indiv1.getName),Term(indiv2.getName)))))
//           case ObjectInverseOf(ObjectProperty(iri)) => addClauseToOntology(OntologyClause(Nil,Seq(Role(iri,Term(indiv2.getName),Term(indiv1.getName)))))
//         }
//      }
//      case NegativeObjectPropertyAssertionAxiom(ope,indiv1,indiv2) =>
//      case SameIndividualAxiom(individuals) => addClauseTo
//      case DifferentIndividualsAxiom(individuals) =>
//    }
//  }

}
