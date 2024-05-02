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

package com.sequoiareasoner.kernel.structural.chains

import com.sequoiareasoner.kernel.graph.MutableGraph
import com.sequoiareasoner.kernel.index.AnyRefUnionFind
import com.sequoiareasoner.kernel.owl.PredefinedOWLClass._
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.owl.model._
import com.sequoiareasoner.kernel.structural.UnsupportedFeatureObserver
import com.sequoiareasoner.kernel.structural.chains.AutomatonBuilder._
import com.sequoiareasoner.arrayops._
import com.sequoiareasoner.kernel.clauses.Equality

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/** Carries out some pre-processing steps on a collection of Sequoia Axioms. */

class PreprocessedAxiomCollection(axioms: Iterable[Axiom], featureObserver: UnsupportedFeatureObserver, ignoreABox: Boolean) {

  private[this] var theABoxIsEmpty: Boolean = true
  def hasABoxAxioms: Boolean = !theABoxIsEmpty

  // FIXME: handle owl:topObjectProperty

  /** STEP 1: Creates an object that can be used to check later the restrictions of non-simple roles specified by OWL 2 */

  private[this] val simplicityChecker = new SimplePropertyRestrictionValidator(axioms)


  /** STEP 2: Process the input axioms to build the Property Inclusion Graph. This step eliminates axioms of the form
    *  EquivalentObjectPropertiesAxiom, InverseObjectPropertiesAxiom and SymmetricObjectPropertyAxiom, since they are
    *  only needed to build the graph. This step also removes declaration and annotation axioms. The remaining axioms
    *  are piped out to a new buffer, _filteredAxioms_ */

  private[this] val filteredAxioms = new ArrayBuffer[Axiom]
  /** `knownPropertyInclusionGraph` has an edge from `A` to `B` if `B` is a known super property expression of `A`. */
  private[this] val knownPropertyInclusionGraph = new MutableGraph[ObjectPropertyExpression]
  for (ax <- axioms) ax match {
    case EquivalentObjectPropertiesAxiom(properties) =>
      val propertiesSeq = properties.toArray
      val length = propertiesSeq.length
      crange (0, length) { i => crange(i + 1, length) { j =>
        knownPropertyInclusionGraph.addEdge(propertiesSeq(i), propertiesSeq(j))
        knownPropertyInclusionGraph.addEdge(propertiesSeq(i).inverse, propertiesSeq(j).inverse)
        knownPropertyInclusionGraph.addEdge(propertiesSeq(j), propertiesSeq(i))
        knownPropertyInclusionGraph.addEdge(propertiesSeq(j).inverse, propertiesSeq(i).inverse)
      } }
    case InverseObjectPropertiesAxiom(first, second) =>
      knownPropertyInclusionGraph.addEdge(first, second.inverse)
      knownPropertyInclusionGraph.addEdge(first.inverse, second)
      knownPropertyInclusionGraph.addEdge(second, first.inverse)
      knownPropertyInclusionGraph.addEdge(second.inverse, first)
    case SubObjectPropertyOfAxiom(lhs: ObjectPropertyExpression, rhs) =>
      knownPropertyInclusionGraph.addEdge(lhs, rhs)
      knownPropertyInclusionGraph.addEdge(lhs.inverse, rhs.inverse)
      filteredAxioms += ax
    case SymmetricObjectPropertyAxiom(ope) =>
      knownPropertyInclusionGraph.addEdge(ope, ope.inverse)
      knownPropertyInclusionGraph.addEdge(ope.inverse, ope)
    case _: DeclarationAxiom =>
      // Declarations do not affect reasoning, so discard.
    case _: AnnotationAxiom =>
      // Annotations do not affect reasoning, so discard.
    case _ =>
      filteredAxioms += ax
  }
  /** Contains a partitioned set, where every partition is one of the object properties */
  /** If asked to get a representative for a property that is not in the graph (this may happen, for instance,  with
    * transitive properties with no other participation in the RBox, we add a new class for this property and return it.*/
  private[this] val equivalentProperties: AnyRefUnionFind[ObjectPropertyExpression] =
    knownPropertyInclusionGraph.stronglyConnectedComponents



  /** STEP 3: Build the automaton for encoding away transitivity and role chains. This eliminates all axioms of
    * the form SubObjectPropertyOf (which are encoded in the automaton, or stored in _simpleSubProperties_, and
    * also Chain and Transitive axioms, which are always encoded in the automaton. The remaining axioms are sent
    * to buffer _remainingAxioms_ */

  /** Contains all axioms that are simple SubObjectProperty axioms, which do not need to be processed in this step. */
  private[this] val simpleSubProperties = new ArrayBuffer[SubObjectPropertyOfAxiom[ObjectPropertyExpression]]
  /** Role inclusion axioms in the ontology */
  private[this] val riasForAutomatonBuilder = new ArrayBuffer[RoleInclusionAxiom]
  /** Axioms that are neither of the two above, which will be filtered and internalised later */
  private[this] val remainingAxioms = new ArrayBuffer[Axiom]

  /** Given an object property expression, returns the canonical element of the equivalentProperties partition */
  private[this] def canonical(ope: ObjectPropertyExpression): ObjectPropertyExpression = {
    val opeRep: ObjectPropertyExpression = equivalentProperties.getRepresentative(ope)
    val opeInvRep: ObjectPropertyExpression = equivalentProperties.getRepresentative(ope.inverse)
    val opeRepIri: IRI = opeRep.namedProperty.iri
    val opeRepInvIri: IRI = opeInvRep.namedProperty.iri
    if (opeRepIri <= opeRepInvIri) opeRep else opeInvRep.inverse
  }
  /** Returns `true` iff `ope1` and `ope2` are equivalent in the reflexive-transitive closure of the property hierarchy. */
  private[this] def areEquivalent(ope1: ObjectPropertyExpression, ope2: ObjectPropertyExpression): Boolean = {
    val ope1Rep = equivalentProperties.getRepresentative(ope1)
    val ope2Rep = equivalentProperties.getRepresentative(ope2)
    ope1Rep == ope2Rep
  }
  /** Returns `true` iff `op` is found to be symmetric in the reflexive-transitive closure of the property hierarchy. */
  private[this] def isSymmetric(op: ObjectProperty): Boolean = areEquivalent(op, op.inverse)

  for (ax <- filteredAxioms) ax match {
    case SubObjectPropertyOfAxiom(ope1: ObjectPropertyExpression, ope2) =>
      if (!areEquivalent(ope1, ope2)) {
        if (simplicityChecker.isSimple(ope2))
          simpleSubProperties += SubObjectPropertyOfAxiom(canonical(ope1), canonical(ope2))
        else
          riasForAutomatonBuilder += RoleInclusionAxiom(Seq(canonical(ope1)), canonical(ope2))
      }
    case SubObjectPropertyOfAxiom(ObjectPropertyChain(chain), ope) =>
      riasForAutomatonBuilder += RoleInclusionAxiom(chain map canonical, canonical(ope))
    case TransitiveObjectPropertyAxiom(property) =>
      riasForAutomatonBuilder += RoleInclusionAxiom(Seq(canonical(property), canonical(property)), canonical(property))
    case _ =>
      remainingAxioms += ax
  }

  /** Finally, we construct the automaton that can encode away Transitivity and Chains. */
  private[this] val builder = new AutomatonBuilder(riasForAutomatonBuilder, isSymmetric)



  /** STEP 4 : Final processing. The remaining axioms are taken and, after filtering those which are unsupported by
    * Sequoia, we perform the Structural Transformation and replace object properties by their corresponding
    * encoding given by the automaton build in the previous step. The result is an RBox divided in three for
    * AsymmetricProperty, ReflexiveProperty, and DisjointProperty axioms, and a TBox containing all other
    * axioms, in the form T -> Not C v D, stored as (C,D), where in each tuple,
    * the first element is the NNF of Not-C, and the second is the NNF of D. */

  private[this] val internalizedAxioms = new ArrayBuffer[(ClassExpression,ClassExpression)]
  private[this] val asymmetricProperties = new ArrayBuffer[AsymmetricObjectPropertyAxiom]
  private[this] val reflexiveProperties = new ArrayBuffer[ReflexiveObjectPropertyAxiom]
  private[this] val disjointProperties = new ArrayBuffer[DisjointObjectPropertiesAxiom]
  // This is for not internalising the ABox: private[this] val aBoxAxioms = new ArrayBuffer[AssertionAxiom]


  /** This checks if the automaton for a role is the kind of automaton obtained when the only restriction on
    * the role is that it is transitive (and it is not symmetric). This automata has only two states, and an
    * edge labelled R from initial state to final state, and a self-loop labelled R in the final state. */
  private[this] def isTransitivityOnlyAutomaton(ope: ObjectPropertyExpression): Boolean = {
    val nfa: NFA = builder.getAutomaton(canonical(ope))
    nfa.delta forall{
      case Transition(source, r, sink) if source.isInitial => sink.isTerminal && r == ope.namedProperty
      case Transition(source, r, sink) if source.isTerminal => sink.isTerminal && r == ope.namedProperty
      case _ => false
    }
  }


  /** Returns the encoding of a property that may occur on the right of a property chain.
    *
    * Given the non-deterministic finite automaton A = (states, symbols, transition, initials, terminals) that
    * corresponds to an object property expression, the set of clauses is constructed as follows:
    * For each transition (u, R, v), we introduce the clause:
    *   AUX_u -> \ForAll R AUX_v
    *
    * Each initial state i corresponds to the negative concept AUX_i, and each terminal state t corresponds to the
    * positive concept AUX_t.
    *
    * @param ope
    * @param ce a class expression that has _already_ been transformed
    * @return
    */
  private[this] def rewriteForAll(ope: ObjectPropertyExpression,
                                  ce: ClassExpression): ClassExpression = {
    /* OPEs in RIAs are replaced with representatives of the equivalence class, so get the NFA for the representative,
     * but we do not need to get the canonical OPEs for transition labels since they were substituted before. */
    /** Each role has a corresponding automaton, as described in `The Even More Irresistible SROIQ' */
    val nfa: NFA = builder.getAutomaton(canonical(ope))

    /** Delta is the transition function, its elements are off the form Transition(source,label,sink) */
    // true if the auxiliary concept that corresponds to an initial state would only occur negatively if generated.
    /** Namely, true iff there is no incoming edge into an initial state */
    val canInlineInitialStates = nfa.delta forall {
      case Transition(_, _, sink) => !sink.isInitial
    }

    /** Similarly, true iff the final state has no outgoing edge */
    // true if the auxiliary concept that corresponds to a terminal state would only occur positively if generated.
    val canInlineTerminalStates = nfa.delta forall {
      case Transition(source, _, _) => !source.isTerminal
    }

    /** This simply determines if we should generate auxiliary for a given state. The answer is no only for
      * initial states when they can be inlined, and final states when they can be inlined. */
    @inline def genAuxForState(s: State): Boolean =
      (s.isInitial && !canInlineInitialStates) ||
      (s.isTerminal && !canInlineTerminalStates) ||
      (!s.isInitial && !s.isTerminal)

    val flipPolarityOfAux = true

    /** Constructs a map from states to the auxiliary concept for the state, if one exists */
    val stateMap = new mutable.AnyRefMap[State, OWLClass]
    for (s: State <- nfa.states)
      if (genAuxForState(s)) stateMap.put(s, OWLClass(IRI.all()))

    /** Class expression for inlined final state is the original, otherwise return complement of
      * auxiliary concept if negativePolarity, or auxiliary concept otherwise. */
    @inline def ceForState(s: State, negativePolarity: Boolean): ClassExpression =
      if (s.isTerminal && canInlineTerminalStates) ce
      else if (negativePolarity ^ flipPolarityOfAux) ObjectComplementOf(stateMap(s))
      else stateMap(s)

    /** This will contain the initial transitions */
    val classExpressions = new ArrayBuffer[ClassExpression]

    for (Transition(source, label, sink) <- nfa.delta) {
      /** Class expression for the transition: V R.A , with R the transition label, A the auxiliary for sink */
      val expressionForTransition =
        if (label ne null) ObjectAllValuesFrom(label, ceForState(sink, false))
        else ceForState(sink, false)

      /** If the source is initial and we can inline the initial state, we just add the expression for transition
        *  to classExpressions, otherwise we add the auxiliary concept for the source. */
      if (source.isInitial) {
        if (canInlineInitialStates)
          classExpressions += expressionForTransition
        else
          classExpressions += ceForState(source, false)
      }

      /** If the source is not initial, or if the source is initial but we cannot inline initial state, we
        * add a new axiom, NOT auxiliary for state => expression for transition. */
      if (!source.isInitial || !canInlineInitialStates)
        internalizedAxioms += ((ceForState(source, true), expressionForTransition))
    }

    /** If we cannot inline the terminal state, we add an extra axiom from the auxiliary for terminal, to the terminal class expression */
    if (!canInlineTerminalStates)
      for (s: State <- nfa.terminals)
        internalizedAxioms += ((ceForState(s, true), ce))

    // Conjunction over the initial transitions.
    ObjectIntersectionOf(classExpressions.toSet)
  }

  /** ObjectMaxCardinality(n R A) will be transformed into clauses as
    * NOT(R(x, z0)) OR ... OR NOT(R(x, zn)) OR NOT(A(z0)) OR ... OR NOT(A(zn))
    * and thus the filler will be complemented. This will introduce universal quantifiers if existential quantifiers
    * occur in `ce`. */
  private[this] def atMost(n: Int, ope: ObjectPropertyExpression, ce: ClassExpression): ClassExpression =
    ce match {
      case cr: OWLClass =>
        ObjectMaxCardinality(n, canonical(ope), cr)
      case oco @ ObjectComplementOf(_: OWLClass) =>
        ObjectMaxCardinality(n, canonical(ope), oco)
      case _ =>
        val aux = OWLClass(IRI.all())
        internalizedAxioms += ((transform(ce.nnfComplement), aux))
        ObjectMaxCardinality(n, canonical(ope), aux)
    }

  /** Given a class expression in negation-normal form, returns a class expression in negation-normal form which has the
    * property inclusions encoded.
    *
    * Note that even if the input class expression is in conjunctive-normal form, the result is not guaranteed to be in
    * conjunctive-formal form. */

  private[this] def transform(ceNNF: ClassExpression): ClassExpression = ceNNF match {
    case cr: OWLClass =>
      cr
    case oco @ ObjectComplementOf(_: OWLClass) =>
      oco
    case oco @ ObjectComplementOf(_: ObjectHasSelf) =>
      oco
    case oco @ ObjectComplementOf(_: ObjectOneOf) =>
      oco
    case ObjectAllValuesFrom(ope, ce) =>
      rewriteForAll(ope, transform(ce))
    case ObjectExactCardinality(n, ope, ce) =>
      ObjectIntersectionOf(Set(ObjectMinCardinality(n, canonical(ope), transform(ce)), atMost(n, ope, ce)))
    case ObjectIntersectionOf(ces) =>
      ObjectIntersectionOf(ces map transform)
    case ObjectMaxCardinality(n, ope, ce) =>
      atMost(n, ope, ce)
    case ObjectMinCardinality(n, ope, ce) =>
      ObjectMinCardinality(n, canonical(ope), transform(ce))
    case ObjectSomeValuesFrom(ope, ce) =>
      ObjectSomeValuesFrom(canonical(ope), transform(ce))
    case ObjectUnionOf(ces) =>
      ObjectUnionOf(ces map transform)
    case ohs: ObjectHasSelf =>
      ohs
    case ObjectHasValue(ope, individual) =>
      ObjectHasValue(canonical(ope), individual)
    case ooo: ObjectOneOf => ooo
    case dav: DataAllValuesFrom => dav
    case dec: DataExactCardinality => dec
    case dhv: DataHasValue => dhv
    case dmc: DataMaxCardinality => dmc
    case dmc: DataMinCardinality => dmc
    case dsv: DataSomeValuesFrom => dsv
    case ce: ObjectComplementOf =>
      throw new AssertionError(s"$ce is not in NNF.")
  }

  /** Given an axiom, it:
    * 1) Checks it verifies the restrictions on non-simple properties.
    * 2) Checks it is supported by Sequoia.
    * 3) Does Structural Transformation and encodes object properties using the automaton.
    * 4) Stores RBox axioms in one of three buffers (Asymmetric properties, Reflexive properties, Disjoint properties)
    * 5) Stores the remaining internalised axioms in _internalizedAxioms_ */

  private[this] def internalize(axiom: Axiom): Unit = {
    axiom match {
      case DisjointClassesAxiom(ces) =>
        simplicityChecker.isValid(axiom)
        // For each class expression that is repeated, that class expression is equivalent to owl:Nothing.
        val repetitions: Set[ClassExpression] = ces.groupBy(identity).collect{ case (x, ys) if ys.size > 1 => x }.toSet
        // Otherwise, transform Disjoint(A B) as A \wedge B -> \bottom for each pair A and B in ces -- repetitions.
        val others: Array[ClassExpression] = (ces.toSet -- repetitions).toArray
        for (ce <- repetitions)
          internalizedAxioms += ((transform(ce.nnfComplement), owlNothing))
        crange (0, others.length) { i => crange(i + 1, others.length) { j =>
          internalizedAxioms += ((transform(others(i).nnfComplement), transform(others(j).nnfComplement)))
        } }
      case DisjointUnionAxiom(definedClass, ces) =>
        simplicityChecker.isValid(axiom)
        internalize(DisjointClassesAxiom(ces))
        internalize(EquivalentClassesAxiom(Set(definedClass,ObjectUnionOf(ces.toSet))))
      case EquivalentClassesAxiom(ces) =>
        simplicityChecker.isValid(axiom)
        val prop: Array[ClassExpression] = ces.toArray
        if (prop.length > 1)
          for (i <- prop.indices) {
            val lhs = prop(i)
            val rhs = prop((i + 1) % prop.length)
            internalizedAxioms += ((transform(lhs.nnfComplement), transform(rhs.nnf)))
          }
      case HasKeyAxiom(ce, opes, dpes) =>
        simplicityChecker.isValid(axiom)
        featureObserver.reportUnsupported(HasKeyAxiom(ce,opes,dpes))
      /** Why is this case treated differently ?
        * Answer: no idea, so commenting out for the moment.  */
//      case SubClassOfAxiom(ObjectOneOf(individuals),ce) =>
//        simplicityChecker.isValid(axiom)
//        for (individual <- individuals)
//          internalizedAxioms += ((transform(OWLClass(IRI.nominalConcept(individual.getName)).nnfComplement), transform(ce.nnf)))
      case SubClassOfAxiom(lhs, rhs) =>
        simplicityChecker.isValid(axiom)
        internalizedAxioms += ((transform(lhs.nnfComplement), transform(rhs.nnf)))
      case ObjectPropertyDomainAxiom(ope, domain) =>
        simplicityChecker.isValid(axiom)
        //if (isTransitivityOnlyAutomaton(ope)) internalizedAxioms += (( owlNothing, ObjectUnionOf(Set(transform(domain.nnf), ObjectAllValuesFrom(ope, owlNothing))) ))
     //   else
       internalizedAxioms += ((transform(domain.nnf), rewriteForAll(ope, owlNothing)))
      case ObjectPropertyRangeAxiom(ope, range) =>
        simplicityChecker.isValid(axiom)
        /** Optimisation: if the automaton only encodes transitivity, the reduction is not necessary in this case */
        if (isTransitivityOnlyAutomaton(ope)) internalizedAxioms += ((owlNothing, ObjectAllValuesFrom(ope, transform(range.nnf))))
        else internalizedAxioms += ((owlNothing, rewriteForAll(ope, transform(range.nnf))))
      case FunctionalObjectPropertyAxiom(ope) =>
        simplicityChecker.isValid(axiom)
        internalizedAxioms += ((owlNothing, ObjectMaxCardinality(1, canonical(ope))))
      case InverseFunctionalObjectPropertyAxiom(ope) =>
        simplicityChecker.isValid(axiom)
        internalizedAxioms += ((owlNothing, ObjectMaxCardinality(1, canonical(ope.inverse))))
      case AsymmetricObjectPropertyAxiom(ope) =>
        simplicityChecker.isValid(axiom)
        asymmetricProperties += AsymmetricObjectPropertyAxiom(canonical(ope))
      case ReflexiveObjectPropertyAxiom(ope) =>
        simplicityChecker.isValid(axiom)
        reflexiveProperties += ReflexiveObjectPropertyAxiom(canonical(ope))
      case DisjointObjectPropertiesAxiom(opes) =>
        simplicityChecker.isValid(axiom)
        disjointProperties += DisjointObjectPropertiesAxiom(opes map canonical)
      case IrreflexiveObjectPropertyAxiom(ope) =>
        simplicityChecker.isValid(axiom)
        internalizedAxioms += ((ObjectComplementOf(ObjectHasSelf(canonical(ope))),owlNothing))
      /** Datatypes are yet UNSUPPORTED by Sequoia */
      case ax: DatatypeDefinitionAxiom =>
        simplicityChecker.isValid(axiom)
        featureObserver.reportUnsupported(ax)
      case ax: DataPropertyDomainAxiom =>         // UNSUPPORTED
        simplicityChecker.isValid(axiom)
        featureObserver.reportUnsupported(ax)
      case ax: DataPropertyAxiom =>               // UNSUPPORTED
        featureObserver.reportUnsupported(ax)
      /** Axioms with individuals */
      case ClassAssertionAxiom(ce, individual) => if (!ignoreABox) {
          simplicityChecker.isValid(axiom)
          theABoxIsEmpty = false
          // internalizedAxioms +=  ((transform(individual2nominal(individual).nnfComplement),transform(ce.nnf)))
          // internalizedAxioms += ((transform(OWLClass(IRI.nominalConcept(individual.getName)).nnfComplement),transform(ce.nnf)))
          // This is for not internalising the ABox: aBoxAxioms += ClassAssertionAxiom(transform(ce.nnf),individual)
          internalizedAxioms += ((ObjectOneOf(Set(individual)).nnfComplement, transform(ce.nnf)))
        }
      case ObjectPropertyAssertionAxiom(ope,indiv1,indiv2) => if (!ignoreABox) {
        simplicityChecker.isValid(axiom)
        theABoxIsEmpty = false
//        internalizedAxioms += ( (transform(OWLClass(IRI.nominalConcept(indiv1.getName)).nnfComplement),
//           transform( ObjectSomeValuesFrom(ope,OWLClass(IRI.nominalConcept(indiv2.getName))).nnf )  ) )
        internalizedAxioms += (( ObjectOneOf(Set(indiv1)).nnfComplement,
                 transform( ObjectSomeValuesFrom(ope,ObjectOneOf(Set(indiv2))) )  ) )
       //  This is for not internalising the ABox: aBoxAxioms += ObjectPropertyAssertionAxiom(canonical(ope),indiv1,indiv2)
      }
      case NegativeObjectPropertyAssertionAxiom(ope, indiv1, indiv2) => if (!ignoreABox) {
        simplicityChecker.isValid(axiom)
        theABoxIsEmpty = false
        internalizedAxioms += ((transform(ObjectIntersectionOf(Set(ObjectOneOf(Set(indiv1)),
          ObjectSomeValuesFrom(ope, ObjectOneOf(Set(indiv2))).nnfComplement))), owlNothing))
        //        internalizedAxioms += (( transform(ObjectIntersectionOf(Set(OWLClass(IRI.nominalConcept(indiv1.getName)),
        //          ObjectSomeValuesFrom(ope,OWLClass(IRI.nominalConcept(indiv2.getName))).nnfComplement))), owlNothing ))
        // This is for not internalising the ABox: aBoxAxioms += NegativeObjectPropertyAssertionAxiom(canonical(ope),indiv1,indiv2)
      }
      case SameIndividualAxiom(indivs) => if (!ignoreABox) {
        simplicityChecker.isValid(axiom)
        //        indivs.drop(1).foreach( o2 => {
        //          indivs.headOption.foreach( o1 => {
        //            internalizedAxioms += ((transform(OWLClass(IRI.nominalConcept(o1.getName)).nnfComplement),
        //              transform(OWLClass(IRI.nominalConcept(o2.getName)).nnf)))
        //            internalizedAxioms += ((transform(OWLClass(IRI.nominalConcept(o2.getName)).nnfComplement),
        //              transform(OWLClass(IRI.nominalConcept(o1.getName)).nnf)))
        //          }) })
        theABoxIsEmpty = false
        indivs.drop(1).foreach(o2 => {
          indivs.headOption.foreach(o1 => {
            internalizedAxioms += ((ObjectOneOf(Set(o1)).nnfComplement, ObjectOneOf(Set(o2))))
            internalizedAxioms += ((ObjectOneOf(Set(o2)).nnfComplement, ObjectOneOf(Set(o1))))
          })
        })
      }
       // This is for not internalising the ABox: aBoxAxioms += SameIndividualAxiom(indivs)
      case DifferentIndividualsAxiom(indivs) => if (!ignoreABox) {
        //        simplicityChecker.isValid(axiom)
        //        indivs.drop(1).foreach( o2 => {
        //          indivs.headOption.foreach( o1 => {
        //            internalizedAxioms += ((transform(ObjectIntersectionOf(Set(OWLClass(IRI.nominalConcept(o1.getName)),
        //              OWLClass(IRI.nominalConcept(o2.getName)))).nnfComplement),owlNothing))
        //          }) })
        simplicityChecker.isValid(axiom)
        theABoxIsEmpty = false
        indivs.drop(1).foreach(o2 => {
          indivs.headOption.foreach(o1 => {
            internalizedAxioms += ((ObjectIntersectionOf(Set(ObjectOneOf(Set(o1)), ObjectOneOf(Set(o2)))).nnfComplement, owlNothing))
          })
        })
      }
       //This is for not internalising the ABox: aBoxAxioms += DifferentIndividualsAxiom(indivs)
      case ax: AssertionAxiom =>
        throw new Error(s"AssertionAxiom $ax should have been processed already. Perhaps a case test is missing in the implementation?")
      case ax: DeclarationAxiom =>
        throw new Error(s"DeclarationAxiom $ax should have been discarded by Step 1 in the preprocessing phase.")
      case ax: AnnotationAxiom =>
        throw new Error(s"AnnotationAxiom $ax should have been discarded by Step 1 in the preprocessing phase.")
      case ax: EquivalentObjectPropertiesAxiom =>
        throw new Error(s"EquivalentObjectPropertiesAxiom $ax should have been handled by Step 2 in the preprocessing phase.")
      case ax: InverseObjectPropertiesAxiom =>
        throw new Error(s"InverseObjectPropertiesAxiom $ax should have been handled by Step 2 in the preprocessing phase.")
      case ax: SubObjectPropertyOfAxiom[_] =>
        throw new Error(s"SubObjectPropertyOfAxiom $ax should have been handled by Step 3 in the preprocessing phase.")
      case ax: SymmetricObjectPropertyAxiom =>
        throw new Error(s"SymmetricObjectPropertyAxiom $ax should have been handled by Step 3 in the preprocessing phase.")
      case ax: TransitiveObjectPropertyAxiom =>
        throw new Error(s"TransitiveObjectPropertyAxiom $ax should have been handled by Step 3 in the preprocessing phase.")
    }
  }

  /** Here is where Step 4 ACTUALLY happens */

  for (ax <- remainingAxioms) internalize(ax)


  /** --------------------------------------- Preprocessing complete --------------------------------------- */


  /** In accordance with the previous descriptions,
    * after the preprocessing phase, the preprocessed ontology is stored partitioned into the following disjoint sets:
    *
    * -internalizedAxioms
    * -asymmetricProperties
    * -reflexiveProperties
    * -disjointProperties
    * -simpleSubProperties
    *
    * The following methods allow us to recover these partitions. Note that the preprocessing is carried out on the
    * creation of this instance of PreprocessedAxiomCollection, so these methods always return the preprocessed axioms.
    */

  /** Returns the internalised axioms (normalised, transformed(Trans and Chains encoded away), and supported axioms except RBox axioms) */
  def getInternalizedAxioms: Iterator[(ClassExpression, ClassExpression)] = internalizedAxioms.iterator

  /** Return the transformed asymmetric object property axioms */
  def getAsymmetricProperties: Iterator[AsymmetricObjectPropertyAxiom] = asymmetricProperties.iterator

  /** Return the transformed reflexive object property axioms  */
  def getReflexiveProperties: Iterator[ReflexiveObjectPropertyAxiom] = reflexiveProperties.iterator

  /** Return the transformed disjoint object properties axioms of the input ontology */
  def getDisjointProperties: Iterator[DisjointObjectPropertiesAxiom] = disjointProperties.iterator

  /** Returns the transformed simple sub object property inclusions of the input ontology. These are object property
    *  inclusions of the form OPE1 -> OPE2, where both OPE1 and OPE2 are simple object property expressions. */
  def getSimpleSubProperties: Iterator[SubObjectPropertyOfAxiom[ObjectPropertyExpression]] = simpleSubProperties.iterator

  // This is for not internalising the ABox:
//  /** Return the transformed ABox */
//  def getABoxAxioms: Iterator[AssertionAxiom] = aBoxAxioms.iterator

  override def toString: String = knownPropertyInclusionGraph.toString

}
