file://<WORKSPACE>/sequoia/reasoner-kernel/src/main/scala/com/sequoiareasoner/kernel/context/ContextStructureManager.scala
### scala.reflect.internal.FatalError: no context found for source-file://<WORKSPACE>/sequoia/reasoner-kernel/src/main/scala/com/sequoiareasoner/kernel/context/ContextStructureManager.scala,line-14,offset=676

occurred in the presentation compiler.

presentation compiler configuration:
Scala version: 2.13.12
Classpath:
<HOME>/.cache/coursier/v1/https/repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.12/scala-library-2.13.12.jar [exists ]
Options:



action parameters:
offset: 676
uri: file://<WORKSPACE>/sequoia/reasoner-kernel/src/main/scala/com/sequoiareasoner/kernel/context/ContextStructureManager.scala
text:
```scala
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
 * GNU General Public License version 3 for more details (a c@@opy is
 * included in the LICENSE file that accompanied this code).
 *
 * You should have received a copy of the GNU General Public License
 * version 3 along with this work.  If not, see <http://www.gnu.org/licenses/>.
 */

package com.sequoiareasoner.kernel.context

import com.sequoiareasoner.kernel.clauses._
import com.sequoiareasoner.kernel.index.{ArrayBuilders, ImmutableSet, NeighborPredClauseIndex, TotalIRIMultiMap, _}
import com.sequoiareasoner.kernel.logging.Logger
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.owl.model.{NamedIndividual, OWLClass}
import com.sequoiareasoner.kernel.structural.DLOntology
import com.sequoiareasoner.kernel.taxonomy.Taxonomy
import org.semanticweb.owlapi.model.OWLNamedIndividual

import scala.collection.mutable
import scala.collection.JavaConverters._
import java.util.concurrent.ForkJoinPool
import java.util.concurrent.Callable

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
  private[this] val contexts = new mutable.AnyRefMap[ImmutableSet[Predicate], ContextRunnable]
  // private[this] val contextExecutor = new ForkJoinPool() // Defaults to number of processors -1
  private[this] val contextExecutor = new ActorExecutionService()
  def messageContext(context: ContextRunnable, message: InterContextMessage): Unit = {
    val task: Runnable = () => { context.reSaturateUponMessage(message) }
    contextExecutor.executeWithPartition(task, context.state.core.toString)
  }

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
  
  /** Stop ASAP the construction of the context structure */
  def interrupt(): Unit = synchronized {
    if (ontology.havocTriggered) contextExecutor.shutdownNow()
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
                                 hornPhaseActive: Boolean): Callable[ContextRunnable] = () => {
   // Ignore this parameter for the moment. Require(ordering.verifyQuery(queryConcepts))
    val state = if (core.toSeq.head.iri.isInternalIndividual) {
      new NominalContextState(queryConcepts, core, rootContext, workedOffClauseIndex,
        new NeighborPredClauseIndex, equalityOptimization, redundancyIndex, hornPhaseActive,ordering,ontology, contextStructureManager = this)
    } else {
      new ContextState(queryConcepts, core, rootContext, workedOffClauseIndex, new NeighborPredClauseIndex,
        equalityOptimization, redundancyIndex, hornPhaseActive, ordering, ontology, contextStructureManager = this)
    }
    new ContextRunnable(state, ontology, enableEqualityReasoning, ordering, contextStructureManager = this)
  }

  def getAllContexts: Iterable[ContextRunnable] = synchronized { contexts.values }

  /** Given a conjunction of known predicates, this method identifies the successor given by the _strategy_ of this
    * context structure, and then retrieves it or creates it; in the latter case, it initialises the first round */
  def getSuccessor(K1: ImmutableSet[Predicate]): ContextRunnable = synchronized {
    val core: ImmutableSet[Predicate] = strategy(K1)
    if (core.isEmpty) logger.warn(s"WARNING: trivial context is active! (K1 = $K1)")
    contexts.getOrElseUpdate(core, {
      /** If we create the context, then it is not a root context so the Index is a standard ContextClauseIndex */
      val contextIndex = new ContextClauseIndex
      /** Since this is not a root context, the query is empty */
      val ordering = ContextLiteralOrdering(Set[Int]())
      val createNewContext: Callable[ContextRunnable] = buildContext(Set[Int](), core, rootContext = false, contextIndex, ordering, hornPhaseActive)
      val context: ContextRunnable = contextExecutor.submit(createNewContext).get
      contextExecutor.submit(context.saturateAndPush())
      context
    })
  }
  /** Given a constant, retrieve or create the nominal context corresponding to that constant. If it is created,
    * the initialisation round is started.*/
  protected[context] def getNominalContext(individual: Constant) : ContextRunnable = synchronized {
    implicit val theOntology = ontology
    val core: ImmutableSet[Predicate] = ImmutableSet(Concept(IRI.nominalConcept(individual.toString),CentralVariable))
    contexts.getOrElseUpdate(core, {
      // System.out.println("NOMINAL NODE CREATED for core " + core + " !!")
      /** Since each nominal context is a root context, we introduce a root context index */
      val contextIndex = new RootContextClauseIndex(provedAtomicQueries.addKey(IRI.nominalConcept(individual.toString)))
      /** Since nominal contexts have no query, the query is empty */
      val ordering = ContextLiteralOrdering(Set[Int]())
      val createNewContext: Callable[ContextRunnable] = buildContext(Set[Int](), core, rootContext = true, contextIndex, ordering, hornPhaseActive)
      val context: ContextRunnable = contextExecutor.submit(createNewContext).get
      contextExecutor.submit(context.saturateAndPush())
      context
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


  beginTime = System.currentTimeMillis
  
  /** Create jobs to create a context for each target concept, then run those jobs */
  implicit val theOntology = ontology

  val contextCreationJobs: Set[Callable[ContextRunnable]] = targetConcepts.map(concept => {
    val core: ImmutableSet[Predicate] = ImmutableSet(Concept(IRI(concept),CentralVariable))
    /** Creates the context index, which is a special case since these contexts are query contexts. */
    val contextIndex = new RootContextClauseIndex(provedAtomicQueries.addKey(IRI(concept)))
    buildContext(queryConcepts = Set.empty[Int], core, rootContext = true, contextIndex,
      ContextLiteralOrdering(), hornPhaseActive)
  })
  val cs = contextExecutor.invokeAll(contextCreationJobs.asJava).asScala.map(x => x.get())
  for (c <- cs) contexts.put(c.state.core, c)
  println("creation jobs done")

  /** Saturate every concept, starting with the Horn phase */
  val saturationJobs = cs.map(c => c.saturateAndPush())
  contextExecutor.invokeAll(saturationJobs.asJava)
  while (!contextExecutor.isQuiescent() || contextExecutor.getActiveThreadCount() > 0) {}
  println("saturation jobs done")

  /** Non-Horn phase */
  hornPhaseActive = false
  val nonHornJobs = getAllContexts.toList.map(c =>
    (() => c.reSaturateUponMessage(StartNonHornPhase())): java.util.concurrent.Callable[Unit]
  )
  contextExecutor.invokeAll(nonHornJobs.asJava)
  while (!contextExecutor.isQuiescent() || contextExecutor.getActiveThreadCount() > 0) {}
  println("non horn jobs done")

}




```



#### Error stacktrace:

```
scala.tools.nsc.interactive.CompilerControl.$anonfun$doLocateContext$1(CompilerControl.scala:100)
	scala.tools.nsc.interactive.CompilerControl.doLocateContext(CompilerControl.scala:100)
	scala.tools.nsc.interactive.CompilerControl.doLocateContext$(CompilerControl.scala:99)
	scala.tools.nsc.interactive.Global.doLocateContext(Global.scala:114)
	scala.meta.internal.pc.PcDefinitionProvider.definitionTypedTreeAt(PcDefinitionProvider.scala:151)
	scala.meta.internal.pc.PcDefinitionProvider.definition(PcDefinitionProvider.scala:68)
	scala.meta.internal.pc.PcDefinitionProvider.definition(PcDefinitionProvider.scala:16)
	scala.meta.internal.pc.ScalaPresentationCompiler.$anonfun$definition$1(ScalaPresentationCompiler.scala:386)
```
#### Short summary: 

scala.reflect.internal.FatalError: no context found for source-file://<WORKSPACE>/sequoia/reasoner-kernel/src/main/scala/com/sequoiareasoner/kernel/context/ContextStructureManager.scala,line-14,offset=676