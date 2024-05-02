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

package com.sequoiareasoner.kernel

import java.io.PrintWriter

import com.sequoiareasoner.kernel.clauses.{Concept, OntologyClause}
import com.sequoiareasoner.kernel.context._
import com.sequoiareasoner.kernel.index._
import com.sequoiareasoner.kernel.logging.Logger
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.owl.model._
import com.sequoiareasoner.kernel.reasoner.{FreshEntitiesException, ReasonerConfiguration, UnsupportedReasoningTaskException}
import com.sequoiareasoner.kernel.structural.{DLOntology, UnsupportedFeatureObserver}
import com.sequoiareasoner.kernel.taxonomy.{Taxonomy, TaxonomyNode, TaxonomyNodeSet}
import org.semanticweb.owlapi.model.OWLNamedIndividual

import scala.collection.mutable.ArrayBuffer

/** The main class for querying the results of reasoning for a given ontology.
  *
  * The reasoner is configured as described by the [[ReasonerConfiguration]] object. This configuration cannot change
  * over the lifetime of the reasoner---the system is optimized for a particular configuration.
  *
  * @author Andrew Bate <code@andrewbate.com>
  *
  * @define FreshEntitiesException            [[FreshEntitiesException]]
  * @define TaxonomyNode                      [[TaxonomyNode]]
  * @define TaxonomyNodes                     [[TaxonomyNode]]s
  * @define OWLClass                          [[com.sequoiareasoner.kernel.owl.model.OWLClass]]
  * @define ClassExpression                   [[com.sequoiareasoner.kernel.owl.model.ClassExpression]]
  * @define TaxonomyNodeSet                   [[TaxonomyNodeSet]]
  * @define UnsupportedReasoningTaskException [[UnsupportedReasoningTaskException]]
  *
  * @param config  the object describing the reasoner configuration.
  */
class Reasoner(config: ReasonerConfiguration,
               logger: Logger,
               unsupportedFeatureObserver: UnsupportedFeatureObserver) {
  // TODO: use the progress monitor in the configuration to report progress.


  /** MULTITHREADING */

  //D if (!config.enableMultithreading) io.cso.runtime.Scheduler.setNumWorkerThreads(1)
  io.cso.runtime.Scheduler.setNumWorkerThreads(1)


  /** ------------------------ AXIOMS IN DL FORM [SEQUOIA API, not OWL API] ------------- */

  /** This contains the original axioms, before processing them */
  private[this] val axiomBuffer = new ArrayBuffer[Axiom]
  def addAxiom(axiom: Axiom): Unit = axiomBuffer += axiom
  def getDLAxioms: Iterator[Axiom] = axiomBuffer.iterator

  /** FLAGS */
 // val testHorn : Boolean = false
 // var horn: Boolean = true

  /** ----------------------- ONTOLOGY  DL Clausal Frorm -------------------------------- */

  /** This contains the ontology axioms used in the algorithm execution */
  private[this] var dlOntology: DLOntology = _
  private[this] var dlOntologyTBoxOnly: DLOntology = _
  def ontologyContainsNominals: Boolean = dlOntologyTBoxOnly.containsNominals
  def ontologyABoxIsEmpty: Boolean = !dlOntology.hasABoxAxioms


  def processAxiomsAndLoadAsOntology(): Unit = {
    logger.info("Starting ontology processing...")
    require(dlOntology eq null, "Sequoia does not support axiom changes.")
    dlOntology = new DLOntology(axiomBuffer, unsupportedFeatureObserver)
    dlOntologyTBoxOnly = new DLOntology(axiomBuffer, unsupportedFeatureObserver, ignoreABox = true)

//   if (testHorn) for (clause: OntologyClause <- dlOntology.getOntologyClauses.toSet) {
//       if (!clause.isHorn) {
//       }
//     }

    val printOntology = false
    if (printOntology) for (clause: OntologyClause <- dlOntology.getOntologyClauses.toSet)
    //        if (clause.head.exists {
//        case Concept(iri, _) if (iri.toString.contains("IntrinsicallyPathologicalBodyProcess") | (iri.toString.contains("all:231"))) => true
//        case _ => false
//      })
      System.out.println("ONTOLOGY CLAUSE: " + clause) // DEBUG
   // logger.info("Done ontology processing.")
  }
  def getOntologyClauses: Iterator[OntologyClause] = dlOntology.getOntologyClauses
  def ontologyIsHorn: Boolean = {
    require(dlOntology ne null, "The structural transformation has not been computed yet, so the Reasoner's ontology is empty.")
    dlOntology.getOntologyClauses.toSet forall { clause => clause.isHorn }
  }
  def ontologyContainsEquality: Boolean = {
    require(dlOntology ne null, "The structural transformation has not been computed yet, so the Reasoner's ontology is empty.")
    dlOntology.getOntologyClauses.toSet exists { clause => clause.hasEquality }
  }

  /** --------------------------- CONTEXT STRUCTURE FOR TAXONOMIES -------------------------- */
  /** Currently, the context structure manager just initialises computing the
    * class taxonomy including nominal concepts. Future versions will allow to
    * initialise the manager with a single consistency check, then add stuff to
    * it as new queries are required. */
  private[this] lazy val contextStructureForTaxonomies: ContextStructureManager = {
    def getRedundancyIndex: ContextClauseRedundancyIndex =
      if (config.enableTrieRedundancyIndex) new TrieContextClauseRedundancyIndex
      else new BasicContextClauseRedundancyIndex
    def getEqualityOptimization: EqualityOptimization =
//D      if (config.enableEqualitySimplifyReflect) new SimplifyReflectEqualityOptimization
//D      else EqualityOptimizationDisabled
          EqualityOptimizationDisabled
    // Here query set is empty. Instead, the query should be the set of internal atomic concepts for each atomic concept.
    //: To compensate for this, the order has a "is internal iri" test that makes unary internal atoms smaller.
//    val query = dlOntology.getConceptsToClassify.zipAll(Set[Set[Int]](), 0, Set[Int]()).toMap
    // Optimisation v29
    val selectedOntology = if (dlOntologyTBoxOnly.containsNominals || dlOntology.getCanABoxProduceInconsistency) dlOntology else dlOntologyTBoxOnly
    val result = new ContextStructureManager(selectedOntology, getRedundancyIndex, config.enableEqualityReasoning,
      getEqualityOptimization, ExpansionStrategies.safeCentralStrategy, selectedOntology.getConceptsToClassify, logger)
    _isTaxonomyPrecomputed = true
    result
  }
  private[this] var _isTaxonomyPrecomputed = false
  def isTaxonomyPrecomputed: Boolean = _isTaxonomyPrecomputed


  /** ------------------------------- TAXONOMIES -------------------------------- */

  /** Taxonomy that stores final reasoning results. */
  private[this] lazy val classTaxonomy: Taxonomy[OWLClass] = contextStructureForTaxonomies.getClassesTaxonomy
  private[this] lazy val individualTaxonomy: Taxonomy[NamedIndividual] = contextStructureForTaxonomies.getIndividualsTaxonomy


  /** Return the inferred taxonomy of the named classes for the loaded ontology. */
  def getClassesTaxonomy: Taxonomy[OWLClass] = classTaxonomy
  def getIndividualsTaxonomy: Taxonomy[NamedIndividual] = individualTaxonomy


  /** ----------------------- CONSISTENCY FLAG ----------------------------- */

  /** `true` if the current ontology is inconsistent */
  private[this] lazy val inconsistentOntology: Boolean = {
    def getRedundancyIndex: ContextClauseRedundancyIndex =
      if (config.enableTrieRedundancyIndex) new TrieContextClauseRedundancyIndex
      else new BasicContextClauseRedundancyIndex
    def getEqualityOptimization: EqualityOptimization = EqualityOptimizationDisabled
    //D      if (config.enableEqualitySimplifyReflect) new SimplifyReflectEqualityOptimization
    //D      else EqualityOptimizationDisabled
    //DO: Set query to be empty
//    val query = dlOntology.getConceptsForConsistency.foldLeft(Map[Int,Set[Int]]()){ (z,x) => z + ((x,Set.empty))}
    val manager = new ContextStructureManager(dlOntology, getRedundancyIndex, config.enableEqualityReasoning, getEqualityOptimization,
      ExpansionStrategies.safeCentralStrategy, dlOntology.getConceptsForConsistency, logger)
    val result = manager.getClassesTaxonomy.getTopNode.equivalentObjects.contains(IRI.owlNothing)
    _isConsistencyPrecomputed = true
    if (manager.contradictionHasBeenDerived) true
    else result
  }
  private[this] var _isConsistencyPrecomputed = false
  def isConsistencyPrecomputed: Boolean = _isConsistencyPrecomputed
  /** Return `true` if the ontology is inconsistent (i.e. unsatisfiable). This is done by checking consistency
     * of `owl:Thing` and of all individuals occurring in the ontology. */
  def isInconsistent: Boolean = inconsistentOntology



  /** OTHER REASONING TASKS */

  /** Returns the $TaxonomyNode for the given $OWLClass. If the given $OWLClass does not occur in the ontology
    * and fresh entities are not allowed, a $FreshEntitiesException will be thrown.
    *
    * Calling this method will trigger the computation of the taxonomy if it has not yet been computed.
    *
    * @param iri  an $OWLClass for which to find a $TaxonomyNode
    * @return the $TaxonomyNode for the given $OWLClass
    */
  def getClassNode(iri: IRI): TaxonomyNode[OWLClass] =  {
    require(iri.isImported)
    if (config.allowFreshEntities) {
      getClassesTaxonomy.node(iri, allowFreshEntities = true)
    } else try {
      getClassesTaxonomy.node(iri)
    } catch {
      case _: NoSuchElementException => throw FreshEntitiesException(OWLClass(iri))
    }
  }

  def getIndividualNode(iri: IRI): TaxonomyNode[NamedIndividual] = {
    require(iri.isImported)
    getIndividualsTaxonomy.node(iri)
  }


  /** Return the (direct or indirect) subclasses of the given $ClassExpression as specified by the parameter. Currently,
    * only instances of $OWLClass are supported. If called with other objects, an $UnsupportedReasoningTaskException will
    * be thrown.
    *
    * This method returns a $TaxonomyNodeSet (a collection implementing a set of $TaxonomyNode objects). Each taxonomy
    * node in the returned set represents an equivalence class of subclasses.
    *
    * Calling this method will trigger the computation of the taxonomy if it has not yet been computed.
    *
    * @param classExpression  the $ClassExpression for which to return the subclass $TaxonomyNodes
    * @param direct           `true` to return only direct subclasses
    * @return the set of $TaxonomyNodes for (either direct or indirect) subclasses of the given $ClassExpression
    */
  def getSubClasses(classExpression: ClassExpression, direct: Boolean): TaxonomyNodeSet[OWLClass] =
    classExpression match {
      case OWLClass(iri) if iri.isImported =>
        val node = getClassNode(iri)
        if (direct) node.directSubNodes
        else node.allSubNodes
      case OWLClass(iri) if iri.isInternal =>
        throw new IllegalArgumentException
      case _ =>
        throw UnsupportedReasoningTaskException("Sequoia does not support computation of subclasses for complex class expressions.")
    }


    def getSubIndividuals(individual: Individual, direct: Boolean): TaxonomyNodeSet[NamedIndividual] =
     individual match {
      case NamedIndividual(iri) if iri.isImported =>
        val node = getIndividualNode(iri)
        if (direct) node.directSubNodes
        else node.allSubNodes
      case NamedIndividual(iri) if iri.isInternal =>
        throw new IllegalArgumentException
      case _ =>
        throw UnsupportedReasoningTaskException("Sequoia does not support computation of which individuals are identical to a given fresh individual.")
    }


//COME HERE, see what you do for the instance retrieval thingy. Remember, you can write methods in the context structure manager. Its possibly quicker
  // to, given a class, just iterate over all nominals and see if they contain it.
  // Or, since you will need the individual hierarchy anyway, do this; for each individual, take those that have C as super.
// Seems like you have to do this the horrible way: scan the verifiedQueries for each nominal context to see if they satisfy o -> C; for each such o,
  // then add the corresponding node to the nodeset.
  /** Return all (direct and indirect) nominal concept subclasses of the given $ClassExpression.  Currently,
    * only instances of $OWLClass are supported. If called with other objects, an $UnsupportedReasoningTaskException will
    * be thrown. Calling this method will trigger the computation of the taxonomy if it has not yet been computed. */
//  def getNominalSubClasses(classExpression: ClassExpression): TaxonomyNodeSet =
  //    classExpression match {
//        //COME HERE!! Define new method which retrieves all conceptNominal nodes, and checks for superclasses (indirect) whether C is in it. Then, call to subIndividuals... possibly rename THIS method, which does not seem super-useful.
//      case OWLClass(iri) if iri.isImported =>
//        val node = getClassNode(iri)
//        node.allSubNodes
//      case OWLClass(iri) if iri.isInternal =>
//        throw new IllegalArgumentException
//      case _ =>
//        throw UnsupportedReasoningTaskException("Sequoia does not support computation of instances for complex class expressions.")
//    }



  /** Returns the (direct or indirect) superclasses of the given class expression.
    *
    * Only instances of $OWLClass are supported. If called with other objects, an $UnsupportedReasoningTaskException will be thrown.
    *
    * This method returns a $TaxonomyNodeSet (a collection implementing a set of $TaxonomyNode objects). Each taxonomy
    * node in the returned set represents an equivalence class of superclasses.
    *
    * Calling this method will trigger the computation of the taxonomy if it has not yet been computed.
    *
    * @param classExpression  the $ClassExpression for which to return the superclass $TaxonomyNodes
    * @param direct           `true` to return only direct superclasses
    * @return the set of $TaxonomyNodes for (either direct or indirect) superclasses of the given $ClassExpression
    */
  def getSuperClasses(classExpression: ClassExpression, direct: Boolean): TaxonomyNodeSet[OWLClass] =
    classExpression match {
      case OWLClass(iri) if iri.isImported =>
        val node = getClassNode(iri)
        if (direct) node.directSuperNodes
        else node.allSuperNodes
      case OWLClass(iri) if iri.isInternal =>
        throw new IllegalArgumentException
      case _ =>
        throw UnsupportedReasoningTaskException("Sequoia does not support computation of superclasses for complex class expressions.")
    }

  /** Returns `true` if and only if the given class expression is satisfiable (i.e., the given class expression is not
    * equivalent to `owl:Nothing`). A satisfiable $ClassExpression is also called consistent or coherent.
    *
    * Only instances of $OWLClass are supported. If called with other objects, an $UnsupportedReasoningTaskException will be thrown.
    *
    * Calling this method will trigger the computation of the taxonomy if it has not yet been computed.
    *
    * @param classExpression  the class expression for which to check satisfiability
    * @return `true` if the given input is satisfiable, `false` otherwise
    * @throws UnsupportedReasoningTaskException if the result cannot be computed
    */
  def isSatisfiable(classExpression: ClassExpression): Boolean =
    classExpression match {
      case OWLClass(iri) if iri.isImported =>
        val classNode = getClassNode(iri)
        !classNode.equivalentObjects.contains(IRI.owlNothing)
      case OWLClass(iri) if iri.isInternal =>
        throw new IllegalArgumentException
      case _ =>
        throw UnsupportedReasoningTaskException("Sequoia does not support satisfiability checking for unnamed class expressions.")
    }


  /** AUXILIARY METHODS */


  def havocTriggered: Boolean = dlOntology.havocTriggered
  /** Requests that the reasoner aborts the currently running reasoning task. */
  def interrupt: Unit = ???
  /** Shuts down the reasoner. Return `true` if the operation was successful. */
  def shutdown: Boolean = io.cso.shutdown

}
