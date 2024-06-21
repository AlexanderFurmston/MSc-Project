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

package com.sequoiareasoner.kernel.context

import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicInteger

import akka.actor.ActorSystem
import akka.actor.ActorRef
import akka.actor.Props

import com.sequoiareasoner.kernel.clauses._
import com.sequoiareasoner.kernel.index.{ArrayBuilders, ImmutableSet, NeighborPredClauseIndex, TotalIRIMultiMap, _}
import com.sequoiareasoner.kernel.logging.Logger
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.owl.model.{NamedIndividual, OWLClass}
import com.sequoiareasoner.kernel.structural.DLOntology
import com.sequoiareasoner.kernel.taxonomy.Taxonomy
import org.semanticweb.owlapi.model.OWLNamedIndividual

import scala.collection.mutable

/** Class that manages the context structure, including the introducing of new contexts according to a supplied strategy
  * function, and the termination of the procedure once all contexts have completed saturation. */

 /** IMPORTANT INFORMATION: Currently, the Context Structure Manager is hardcoded to, on creation, run only once,
   * and check all atomic queries of the form A(x) -> B(x), for A(x) an OWLClass in the input ontology
   * this includes auxiliary classes for nominals.
   * In the future, we will implement a more fine degree of control of which queries have been checked,
   * to allow for shorter computations and incremental reasoning. */

final class ContextStructureManager(ontology: DLOntology,
                                    redundancyIndex: => ContextClauseRedundancyIndex,
                                    enableEqualityReasoning: Boolean,
                                    equalityOptimization: => EqualityOptimization,
                                    strategy: ImmutableSet[Predicate] => ImmutableSet[Predicate],
                                    targetConcepts: Set[Int],
                                    logger: Logger) {

   if (ontology eq null) throw new NullPointerException

 //  require(query.keys.forall( x => IRI(x).isImported || IRI(x).isInternalIndividual || IRI(x).isThing))
//  require(query.values.flatten.forall( x => IRI(x).isImported || IRI(x).isInternalIndividual || IRI(x).isThing))


  /**------------------------- Context Structure fields and methods------------------------ */


  /** This map provides, for each set of predicates, a channel to the context that has that set as its core */
  val contexts = new mutable.AnyRefMap[ImmutableSet[Predicate], ActorRef]
  private val actorSystem = ActorSystem.create("ContextStructureManager")

  /** This map provides, for each nominal context O(x), the set of (other) contexts that mention o */
  private[this] val constantIndex = new mutable.AnyRefMap[Constant,collection.mutable.Set[ImmutableSet[Predicate]]]
  /** Add a context to the index mapping each constant to the list of contexts that mention it */
  def addToConstantIndex(individual: Constant, core: ImmutableSet[Predicate]) = synchronized {
    constantIndex.getOrElseUpdate(individual, collection.mutable.Set[ImmutableSet[Predicate]]()) += core
    Unit
  }

  /** `superConcepts(a)` collects subsumption relations between  all the (direct and non-direct) super concepts of `a`. */
  private[this] val provedAtomicQueries = new TotalIRIMultiMap[IRI](ArrayBuilders.iriArrayBuilder)

  /** This records whether a contradiction clause has been derived.  */
  //TODO: stop reasoner whenever inconsistency has been derived
  var contradictionDerived = false
  def flagOntologyAsInconsistent(): Unit = synchronized { contradictionDerived = true }
  def contradictionHasBeenDerived: Boolean = synchronized { contradictionDerived }


   /**-------------------------- Flow Control --------------------------*/


  private[this] var beginTime: Long = 0L
  private[this] var totalTime: Long = 0L
  private[this] var hornPhaseActive: Boolean = true
  /** Counts the number of contexts that are currently active */
  /** THIS IS A HACK: this is automatically initialised with the number of classes to be classified */
  val activeCount = new AtomicInteger(targetConcepts.size) // !!! TODO : make private again
  /** Latch used for awaiting for and terminating the process that constructs the saturated context structure */
  //TODO: Make latch private again;
  val latch = new CountDownLatch(1)
  val secondLatch = new CountDownLatch(1)
  def activeLatch = {
    if (hornPhaseActive) latch; else secondLatch
  }
  protected[context] def contextRoundStarted(): Unit =  activeCount.incrementAndGet
  protected[context] def contextRoundFinished(): Unit = {
    val count = activeCount.decrementAndGet
    if (count < 0) throw new IllegalStateException
    if (count == 0) {
      totalTime = System.currentTimeMillis - beginTime
      logger.info(s"Saturation completed in $totalTime.")
      activeLatch.countDown()
    }
  }
  /** Wait until the Context structure is saturated */
  def waitForSaturation: Unit = {
 // HORN OPTIMISATION  /** Horn phase */
    latch.await()
//    /** Non-horn phase */
    println("surely we get here")
    synchronized { hornPhaseActive = false }
    println("synced")
    activeCount.set(contexts.values.size)
    for (context <- getAllContexts) {
      context ! StartNonHornPhase()
    }
    secondLatch.await()
    println("past the 2nd latch")
 }
  /** Stop ASAP the construction of the context structure */
  def interrupt(): Unit = synchronized {
    if (ontology.havocTriggered) {
      while (activeLatch.getCount > 0) activeLatch.countDown()
    }
  }



   // Uncommenting for the Kaminsky optimisation
   private[this] val certainFacts: mutable.Map[Int,mutable.Set[Int]] = ontology.ensureTrivialFactsAddedAndGetABox
   def addCertainGroundFact(predicate: Int, nominal: Int) = synchronized {
     certainFacts.getOrElseUpdate(nominal, collection.mutable.Set[Int]()) += predicate
   }
//   private[this] val derivedNewCertainGroundFacts = collection.immutable.HashSet[Predicate]()
   def getCertainFacts(nominal: Int) = synchronized {
     certainFacts(nominal)
   }
//   def getCertainGroundFacts(ordering: ContextLiteralOrdering): Seq[ContextClause] = synchronized {
//     (for ( (k,v) <- certainFacts.iterator; pred <- v) yield ContextClause(Array[Predicate](),
//       Array[Literal](Concept(IRI(pred),Term(IRI.importedIriUid2IriNameString(k)))(ontology)))(ordering)).toSeq
//   }

  /** -------------------------- Operations on the context structure -------------------*/


  private[this] def buildContext(queryConcepts: Set[Int],
                                 core: ImmutableSet[Predicate],
                                 rootContext: Boolean,
                                 workedOffClauseIndex: ContextClauseIndex,
                                 ordering: ContextLiteralOrdering,
                                 hornPhaseActive: Boolean): ActorRef = {
   // Ignore this parameter for the moment. Require(ordering.verifyQuery(queryConcepts))
    val state = if (core.toSeq.head.iri.isInternalIndividual) {
      new NominalContextState(queryConcepts, core, rootContext, workedOffClauseIndex,
        new NeighborPredClauseIndex, equalityOptimization, redundancyIndex, hornPhaseActive,ordering,ontology, contextStructureManager = this)
    } else {
      new ContextState(queryConcepts, core, rootContext, workedOffClauseIndex, new NeighborPredClauseIndex,
        equalityOptimization, redundancyIndex, hornPhaseActive, ordering, ontology, contextStructureManager = this)
    }
    actorSystem.actorOf(Props(classOf[Context], state, ontology, enableEqualityReasoning, ordering, this))
  }

  def getAllContexts = synchronized { contexts.values }

  /** Given a conjunction of known predicates, this method identifies the successor given by the _strategy_ of this
    * context structure, and then retrieves it or creates it; in the latter case, it initialises the first round */
  def getSuccessor(K1: ImmutableSet[Predicate]): ActorRef = synchronized {
    val core: ImmutableSet[Predicate] = strategy(K1)
    if (core.isEmpty) logger.warn(s"WARNING: trivial context is active! (K1 = $K1)")
    contexts.getOrElseUpdate(core, {
      /** If we create the context, then it is not a root context so the Index is a standard ContextClauseIndex */
      val contextIndex = new ContextClauseIndex
      /** Since this is not a root context, the query is empty */
      val ordering = ContextLiteralOrdering(Set[Int]())
      contextRoundStarted()
      buildContext(Set[Int](), core, rootContext = false, contextIndex, ordering, hornPhaseActive)
    })
  }
  /** Given a constant, retrieve or create the nominal context corresponding to that constant. If it is created,
    * the initialisation round is started.*/
  protected[context] def getNominalContext(individual: Constant): ActorRef = synchronized {
    implicit val theOntology = ontology
    val core: ImmutableSet[Predicate] = ImmutableSet(Concept(IRI.nominalConcept(individual.toString),CentralVariable))
    contexts.getOrElseUpdate(core, {
      // System.out.println("NOMINAL NODE CREATED for core " + core + " !!")
      /** Since each nominal context is a root context, we introduce a root context index */
      val contextIndex = new RootContextClauseIndex(provedAtomicQueries.addKey(IRI.nominalConcept(individual.toString)))
      /** Since nominal contexts have no query, the query is empty */
      val ordering = ContextLiteralOrdering(Set[Int]())
      contextRoundStarted()
      buildContext(Set[Int](), core, rootContext = true, contextIndex, ordering, hornPhaseActive)
    })
  }
  protected[context] def getContextsWithNominal(individual: Constant): Iterable[ImmutableSet[Predicate]] = synchronized {
    constantIndex(individual)
  }


  /** ------------------------------ Output Methods -------------------------------------- */

  def getClassesTaxonomy: Taxonomy[OWLClass] = {
    val classHierarchy = new TotalIRIMultiMap[IRI](ArrayBuilders.iriArrayBuilder)
    provedAtomicQueries.foreachKeys(key => {
//      println("provedAtomicQuery key: ")
//      println(key)
//      println("Values")
//      provedAtomicQueries(key).foreach( iri => println(iri))
//      println("Is empty?: " + provedAtomicQueries(key).isEmpty)
      if (key.isImported) provedAtomicQueries(key).foreach(value => classHierarchy.addBinding(key, value))
    })
    Taxonomy[OWLClass](classHierarchy, Some(IRI.owlNothing), Some(IRI.owlThing))
  }

  def getIndividualsTaxonomy: Taxonomy[NamedIndividual] = {
    val individualHierarchy = new TotalIRIMultiMap[IRI](ArrayBuilders.iriArrayBuilder)
    provedAtomicQueries.foreachKeys(key => {
      if (key.isInternalIndividual) provedAtomicQueries(key).foreach(value =>
        individualHierarchy.addBinding(IRI(IRI.nominalConceptUid2NominalIriStringName(key.uid)), value))
    })
    Taxonomy[NamedIndividual](individualHierarchy)
  }

  /** -------------------- Saturation of the Context Structure (ON CREATION) ------------------- */


  synchronized {
    beginTime = System.currentTimeMillis
    /** This process creates a context for each relevant concept, and initialises such concepts) */
    implicit val theOntology = ontology
    for (concept <- targetConcepts) {
      val core: ImmutableSet[Predicate] = ImmutableSet(Concept(IRI(concept),CentralVariable))
      contexts.put(core, {
        /** Creates the context index, which is a special case since these contexts are query contexts. */
        val contextIndex = new RootContextClauseIndex(provedAtomicQueries.addKey(IRI(concept)))
        buildContext(queryConcepts = Set.empty[Int], core, rootContext = true, contextIndex,
          ContextLiteralOrdering(), hornPhaseActive)
      })
    }
  }
   waitForSaturation
   println("gothere")
}



