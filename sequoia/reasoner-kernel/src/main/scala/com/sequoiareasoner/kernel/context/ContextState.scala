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

import com.sequoiareasoner.kernel.clauses._
import com.sequoiareasoner.kernel.index._
import com.sequoiareasoner.arrayops._
import com.sequoiareasoner.kernel.context.inferenceRule._
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.structural.DLOntology

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

import akka.actor.ActorRef

/** Class that combines all data structures used to maintain the state of the derivation within a context.
  * In particular, this class holds both the unprocessed queue of clauses and the set of worked off clauses for a
  * single context. */


/** The required arguments for creating a context state are:
  * --The set of query contexts for that concept
  * --The core of the context
  * --The index for clauses in this context
  * --The index for clauses that have been pushed back from a successor.
  * --A redundancy intex for clauses in this context.
  * */

class ContextState(val queryConcepts: Set[Int],
                   val core: ImmutableSet[Predicate],
                   val isRootContext: Boolean,
                   val workedOffClauses: ContextClauseIndex,
                   val neighborIndex: NeighborPredClauseIndex,
                   val cutting: EqualityOptimization,
                   redundancyIndex: ContextClauseRedundancyIndex,
                   val hornPhaseActiveAtCreation: Boolean,
                   val ordering: ContextLiteralOrdering,
                   val ontology: DLOntology,
                   val contextStructureManager: ContextStructureManager) {

  /** This checks that the definition of core from the technical report is adhered to. */
  require { core forall { l => l.isLegalInContextClauseBody } }

  /** CLASS VARIABLE */

  var hornPhaseActive: Boolean = hornPhaseActiveAtCreation


  /** CORE INFO METHODS */ //-----------------------------------------------------------

  val isNominalContext: Boolean = core.toSeq.head.iri.isInternalIndividual
  def getCoreConcept: Predicate = {
    assert(isNominalContext)
    core.toSeq.head
  }
  def getUnaryCoreConcept: Predicate = {
    assert(core.size == 1)
    core.toSeq.head
  }

  /** STORED SETS OF CLAUSES */ //----------------------------------------------------------

  /** The set of unprocessed clauses derived in this context. */
  val todo = new UnprocessedClauses
  /** The set of clauses propagated from the successor contexts in the last round. */
  val predClausesOnLastRound = new UnprocessedDeque
  /** The set of clauses propagated, in a query context, from the nominal contexts in the last round via QueryPush */
  val queryClausesOnLastRound = new UnprocessedDeque
  /** The buffer into which rule conclusion results are collected. Reusing a single buffer avoids object churn. */
  val resultsBuffer = new UnprocessedDeque
//  /** Set of unprocessed clauses stored for the Horn phase **/
//  val stored4NonHorn = new UnprocessedClauses
//  /** Set of unprocessed ground facts (?? what are these ??) */
//  val certainGroundFacts = new mutable.HashSet[Int]
//  /** Set of unprocessed binary ground facts */
//  val certainBinaryGroundFacts = new mutable.HashSet[Role]
//  /** Set of unprocessed unary ground facts */
//  val certainUnaryGroundFacts = new mutable.HashSet[Concept]
//  /** Set of unprocessed equality ground facts */
//  val certainEqualityGroundFacts = new mutable.HashSet[Equality]
//  /** Sets of certain ground clauses, only relevant in nominal contexts. */
//  val certainGroundClausesOnLastRound = new UnprocessedClauses
//  val workedOffGroundClauses = new mutable.HashSet[ContextClause]()

 /** STORED SET OF MENTIONED CONSTANTS */ //-------------------------------------------

 val introducedConstantsOnLastRound = new mutable.ListBuffer[Constant]
 val mentionedConstants = new mutable.HashSet[Constant]()
  //For the Kaminski optimisation
 val mentionedNominals = new mutable.HashSet[Constant]()
 def addConstantToMentionedConstantSet(ind: Constant): Boolean = mentionedConstants.add(ind)
 def getAndClearIntroducedConstantsOnLastRound: List[Constant] = {
   val output = introducedConstantsOnLastRound.toList
   introducedConstantsOnLastRound.clear()
   output
 }

  /** TRIGGER SETS */ //-----------------------------------------------------------------------

  /** Set of all predicates that can trigger rule Succ */
  val succTriggers = new TriggerSet[Predicate]
  /** Set of all predicates that can trigger rule RootSucc  */
  val rootSuccTriggers = new TriggerSet[Predicate]
  /** Set of all equalities that can trigger rule Coll */
  val rootEqualities = new TriggerSet[Equality]
//  /** Same, but records only certain equalities */
//  val certainRootEqualities = new TriggerSet[Equality]
//  /** The set of all singleton ground clauses that have been derived */
//  val singletGroundPredicates = new TriggerSet[Predicate]

  /** NOM RULE TRIGGERS */ //-----------------------------------------------------------------------

  val nomRuleRoleTriggers = new collection.mutable.HashMap[(Int,Int),collection.mutable.Set[Int]]()
  def addNomRuleTrigger(concept: Int, nominal: Int, role: Int) {
    nomRuleRoleTriggers.getOrElseUpdate((concept,nominal),collection.mutable.Set[Int]()) += role
  }
  def getRolesForNomRuleTrigger(concept:Int, nominal:Int): collection.mutable.Set[Int] = {
    nomRuleRoleTriggers.getOrElse((concept,nominal), collection.mutable.Set[Int]())
  }
  var hasNomRuleRoleTriggers = false

  /** INCONSISTENCY REGISTER */ //--------------------------------------------------------------------

  var inconsistencyGuaranteed = false
  def inconsistencyIsGuaranteed(): Boolean = inconsistencyGuaranteed

  /** SUCCESSOR OPERATIONS */  //--------------------------------------------------------------------------

  /** This stores the successors of the context: for each function symbol f, we can get the edge channel to the corresponding successor." */
  private[this] val successors = new mutable.LongMap[ActorRef]
  private[this] val nominalCollapseSuccessors = new mutable.LongMap[ActorRef]
  /** Gets a successor corresponding to a given function term, creating it if required. Needs a function that specifies how
    * to create this new successor when required. */
  def getSuccessorOrElseUpdate(t: Term, default: => ActorRef): ActorRef = t match {
    case FunctionalTerm(f) => successors.getOrElseUpdate(f, default)
    case OriginalIndividual(o) => nominalCollapseSuccessors.getOrElseUpdate(o,default)
    case o: ArtificialIndividual => nominalCollapseSuccessors.getOrElseUpdate(o.id,default)
    case _ => throw new IllegalArgumentException(s"Term $t is neither a functional term nor a constant.")
  }
  /** Gets all successors. */
  def getSuccessors: Vector[ActorRef] =
     successors.values.toVector
  /** Get nominal successors of a root context where the root context may collapse into that nominal i.e. successor via
    * rule Coll */
  def getNominalCollapseSuccessors: Vector[ActorRef] =
    nominalCollapseSuccessors.values.toVector


  /** CLAUSE BLOCKING MANAGER */ //------------------------------------------------

  /** Index of all the clauses that could be resolved with elements in a particular predecessor */
  private[this] val blockedClauseIndex = new BlockedContextClauseIndex

  /** Block newly derived clauses that are not useful (due to, for the moment, us not being able to propagate back
    * any conclusion generated using this clause */
  private[this] def blockIfNotUseful(clause: ContextClause): Boolean = {
    if (clause.body.length > 1) {
      /** To be useful, there must exist a predecessor which contains all atoms of the body as maximal, selected literals.
        * Since predecessors are stored by context and function symbol, we need to find one pair (context,f) that contains all
        * atoms in the body that are not ground, plus pairs (context,a) for each ground atom C(a) */
      val isUseful = predecessors.keys.exists { pair => clause.body.forall {
        /** This first case covers usefulness both for Pred and RootPred, since for RootPred, an incoming edge with label o, and relevant
          * atoms B(o) in the predecessor will have been propagated as B(x) -> B(x) here */
        case p: Predicate if !p.isGround => predecessors.getOrElse((pair._1,pair._2),collection.mutable.Set[Predicate]()).contains(p)
        case p@Concept(_, v: Constant) => predecessors.keys.toSet.contains(pair._1,v) && predecessors.getOrElse((pair._1,v),
          collection.mutable.Set[Predicate]()).contains(p)
        case _ =>  false
      }
      }
      if (!isUseful) {
        blockedClauseIndex.add(clause)
        return true
      }
    }
    false
  }


  /** PREDECESSOR OPERATIONS */  //--------------------------------------------------------------------------

//  def getRootPredecessor(p: Predicate): Option[UnboundedChannel[InterContextMessage]] = rootPredecessors.get(p)
//  def getAllRootPredecessors(): Iterable[UnboundedChannel[InterContextMessage]] = rootPredecessors.values
 /** A list of predecessor context, together with the predicates that may be relevant for the Pred rule */
  private[this] val predecessors = new mutable.AnyRefMap[(ActorRef, Term), mutable.Set[Predicate]]
//  private[this] val rootPredecessors = new mutable.AnyRefMap[Predicate, UnboundedChannel[InterContextMessage]]
  /** Method for obtaining all incoming edge labels */
  def predecessorsGetAllEdgeLabels(targetEdge: ActorRef): Iterable[Term] = {
    for { (edge, label) <- predecessors.keys if edge == targetEdge } yield label
  }
  /** Method for obtaining all predecessor contexts that have clauses with maximal predicates for all the predicates in the body of the given clause*/
  def getRelevantContextStructurePredecessors(body: Array[Predicate]): Iterable[(ActorRef, Term)] = {
/// Here if we use collect, scala chooses the wrong collect, and it messes everything up like uncle Tom on Thanksgiving dinner, so we need to use filter instead
   predecessors.keys.filter {
     case (context, term) if body.forall {
        case p: Predicate if !p.isGround => predecessors.getOrElse((context,term),collection.mutable.Set[Predicate]()).contains(p)
        case p@Concept(_, v: Constant) => predecessors.keys.toSet.contains(context, v) && predecessors.getOrElse((context, v), collection.mutable.Set[Predicate]()).contains(p)
        case _ => false
      } => true
     case _ => false
   }
   // predecessors collect {
   //   case (pair, atoms) => pair // if body.forall {
   //     case p: Predicate if !p.isGround => atoms.contains(p)
   //     case p@Concept(_, v: Constant) => predecessors.keys.toSet.contains(pair._1, v) && predecessors.getOrElse((pair._1, v), collection.mutable.Set[Predicate]()).contains(p)
   //     case _ => true
   //   } => pair
   // }
  }

  /** Updates _predecessors_ with a new predicate in a (new or existing) predecessor */
  def addContextStructurePredecessor(incomingEdge: ActorRef, edgeLabel: Term,
                                     p: Predicate, receivedCore: ImmutableSet[Predicate] = ImmutableSet.empty ): Boolean = {
    /** Sanity check */
    edgeLabel match {
      case FunctionalTerm(_) =>
      case _: Constant =>
      case _ => throw new IllegalArgumentException(s"Term $edgeLabel is not a valid label")
    }
    /** Update predecessors and available predicates in each predecessor */
    val predicates = predecessors.getOrElseUpdate((incomingEdge, edgeLabel),
     { new mutable.HashSet[Predicate]})
    predicates += p

    /** Unblock clauses in the current context that may be pushed back to a predecessor due to the new information that
      * a particular predicate is in a predecessor. */
    var hasUnblocked = false

    blockedClauseIndex.retrieveAndRemoveClauses(predicates.toArray, {
      clause => {
        val isRedundant: Boolean = redundancyIndex.isClauseSubsumed(clause)
        if (!isRedundant) addClauseToContextAndUpdateEndOfRoundPushes(clause)
        // v30: Remove - seems redundant updatePredSuccTodo(clause)
        hasUnblocked = !isRedundant || hasUnblocked
      }
    })
    hasUnblocked
  }
//  def addRootPredecessor(incomingEdge: UnboundedChannel[InterContextMessage], edgeLabel: Predicate): Unit = {
//    rootPredecessors.getOrElseUpdate(edgeLabel, incomingEdge)
//  }



 /** CERTAIN CLAUSE EXTRACTOR */ //-------------------------------------------------------------------------


//  def toSetAndClear[T <: Any](originalSet: mutable.HashSet[T]): Set[T] = {
//    val output = originalSet.toSet
//    originalSet.clear()
//    output
//  }
  // def newCertainGroundFacts: Set[Int] = toSetAndClear[Int](certainGroundFacts)
  //def newBinaryCertainGroundFacts: Set[Role] = toSetAndClear[Role](certainBinaryGroundFacts)
  //def newUnaryCertainGroundFacts: Set[Concept] = toSetAndClear[Concept](certainUnaryGroundFacts)
  //def newEqualityCertainGroundFacts: Set[Equality] = toSetAndClear[Equality](certainEqualityGroundFacts)
//  def getAndClearMentionedConstantsOnLastRound: ListBuffer[Constant] = {
//   val output = mentionedConstantsOnLastRound.clone()
//   mentionedConstantsOnLastRound.clear()
//   output
//  }


  /** PROCESSING DERIVED CLAUSES */ //-------------------------------------------------------------------------

  /** Adds a newly derived clause to the set of unprocessed clauses, unless there is a strengthening of the clause
    * in the context already. If the clause is added, weaker clauses in the context are removed */
  protected[this] def addClauseToContextAndUpdateEndOfRoundPushes(clause: ContextClause, skipRemovals: Boolean = false): Boolean = {
    // if (isSelectedClause(clause)) System.out.println("Attention, using clause... " + clause )
//    if (isSelectedCore()) println("Checking redundancy for clause " + clause)

    /** Remove redundant clauses first */

    if (!skipRemovals) {
      if (clause.isEmpty) {
        redundancyIndex.removeAllClauses()
        workedOffClauses.removeAllClauses()
        //    workedOffGroundClauses.clear()
        succTriggers.clear
        rootSuccTriggers.clear
        rootEqualities.clear
        redundancyIndex.add(clause)
        preparePushesForEndOfRound(clause)
        cutting.clauseDerived(clause)
        return true
      }
      redundancyIndex.removeSubsumedClauses(clause) { subsumedClause =>
      // redundancyIndex contains clauses in both the unprocessed queue and the worked off clauses.
      workedOffClauses.remove(subsumedClause)
      // Update Pred index
      if (subsumedClause.isClauseHeadForPred) workedOffClauses.updatePredIndex(subsumedClause, add = false)
      // Update XPred index
      if (subsumedClause.isClauseHeadForQuery) workedOffClauses.updateQueryIndex(subsumedClause, add = false)
      // Update Succ index
      cforeach(subsumedClause.maxHeadPredicates) { p => if (p.isSuccTrigger) succTriggers.decTriggerCount(p) }
      cforeach(subsumedClause.maxHeadPredicates) { p => if (p.isRSuccTrigger) rootSuccTriggers.decTriggerCount(p) }
      cforeach(subsumedClause.maxHeadLiterals) {
        case eq: Equality if eq.isXEquality && this.isRootContext => //if (subsumedClause.isFact) certainRootEqualities.decTriggerCount(eq) else rootEqualities.decTriggerCount(eq)
            rootEqualities.decTriggerCount(eq)
        case _ =>
      }
      // cforeach(subsumedClause.maxHeadPredicates) { p => if (p.isGround) singletGroundPredicates.decTriggerCount(p) }
      }
    }




    /** Add clause */

    // Adding this for the Kaminski Optimisation: if a certain ground fact is derived in a nominal context,
    // it is sent to the context manager.
    if (isNominalContext && clause.isCertainFunctionFreeGroundClause && clause.isHorn && !clause.head.isEmpty) clause.head(0) match {
      case Concept(iri, CentralVariable) => contextStructureManager.addCertainGroundFact(iri.uid,
        IRI(IRI.nominalConceptUid2NominalIriStringName(this.getCoreConcept.iri.uid)).uid)
      case _ =>
    }

    redundancyIndex.add(clause)
    preparePushesForEndOfRound(clause)
    cutting.clauseDerived(clause)
    true
  }

  /** Given a newly (for sure) derived clause, we prepare all clauses that must be pushed to
    * other contexts at the end of the round. */
  private[context] def preparePushesForEndOfRound(clause: ContextClause): Unit = {
    /** predClausesOnLastRound will be empty at the start of the round, but it is not true that it won't contain
      * redundant clauses at the end of the round, because a stronger clause might be added later. so at the end of the round,
      * predClausesOnLastRound will only contain non-redundant clauses. */

    /** Auxiliary method */
    def checkAndProcessConstant(o: Constant)  {
      if (!mentionedConstants.contains(o)) {
        /** Add to lists of mentioned constants */
        mentionedConstants.add(o)
        /** Update context structure with relevant links */
        contextStructureManager.addToConstantIndex(o, core)
        /** Prepare request push for corresponding nominal concept */
        introducedConstantsOnLastRound.append(o)
      }
    }

    /** First, if any of the new head literals contains a new constant, we add the relevant link and prepare a trigger
      * to the relevant nominal context: ``give me your CGCs'' */
    //TODO: perhaps it would be more efficient to do this within each inference rule
    cforeach (clause.maxHeadLiterals) { p => {
      p.constants._1.foreach { o => checkAndProcessConstant(o) }
      p.constants._2.foreach { o => checkAndProcessConstant(o) }
    } }
    /** Next, update Pred to do */
    if (clause.isClauseHeadForPred) {
      predClausesOnLastRound.removeRedundant(clause)
      predClausesOnLastRound.addLast(clause)
    }
    /** Next, update Query to do, if the clause head consists exclusively of query atoms or conceptFor for nominals */
    if (clause.isClauseHeadForQuery) {
      queryClausesOnLastRound.removeRedundant(clause)
      queryClausesOnLastRound.addLast(clause)
    }
    /** Update triggers for Succ rule */
    cforeach(clause.maxHeadPredicates) { p => if (p.isSuccTrigger) succTriggers.incTriggerCount(p) }
    /** Update triggers for RSucc rule */
    cforeach(clause.maxHeadPredicates) { p => if (p.isRSuccTrigger) rootSuccTriggers.incTriggerCount(p) }
    /** Update triggers for Coll rule */
    cforeach(clause.maxHeadLiterals) {
      case eq: Equality if eq.isXEquality && this.isRootContext => //  if (clause.isFact) certainRootEqualities.incTriggerCount(eq) else rootEqualities.incTriggerCount(eq) case _ =>
        rootEqualities.incTriggerCount(eq)
      case _ =>
    }
    // cforeach (clause.maxHeadPredicates) { p => if (p.isGround) singletGroundPredicates.incTriggerCount(p) }
//    /** If this is a nominal context, we update the set of CGCs, and we prepare a propagation to all relevant contexts
//      * of any new clause. */
//    if (isNominalContext && clause.isCertainFunctionFreeGroundClause) {
//      certainGroundClausesOnLastRound.addUnprocessedClause(clause)
//      workedOffGroundClauses.add(clause)
//    }



      // /** First, the certain ground facts used only for redundancy checks */
      //      case Concept(iri,CentralVariable) => certainGroundFacts += iri.uid
      //      /** Then, the CGFs exchanged between nominal contexts */
      //      case Role(iri,CentralVariable,_: Constant) => certainBinaryGroundFacts += clause.head(0).asInstanceOf[Role]
      //      case Role(iri,_: Constant,CentralVariable) => certainBinaryGroundFacts += clause.head(0).asInstanceOf[Role]
      //      /** No roles will have two constants, and those that have two x's don't need to go anywhere */
      //      case Concept(iri,_: Constant) => certainUnaryGroundFacts += clause.head(0).asInstanceOf[Concept]
      //        /** Same with equalities */
      //      case Equality(CentralVariable,_: Constant) | Equality(_: Constant,CentralVariable) | Equality( _: Constant, _: Constant) =>
      //        certainEqualityGroundFacts += clause.head(0).asInstanceOf[Equality]
      //      case _ =>
      //    }
//      /** If the following happens, the ontology must be inconsistent. For original nominals, this is clear. For
//        * artificial individuals, we will never derive a clause of the form top -> A(o), because those clauses
//        * are only derived from ABox axioms (indeed, only ABox axioms can add clauses of the form Top -> ... to
//        * the root context(s); in this implementation, the only exception is \top to conceptFor(o), but such concept
//        * never appears on the LHS of an axiom, so no problem. */
//    if (isNominalContext && clause.isFact && clause.head.isEmpty) {
//        inconsistencyGuaranteed = true
//    }

    }

      /** This methods shows what to do with candidate inferences obtained from rule applications
        * (they must be ran against the redundancy indices and added to other relevant indices if necessary.) */
    def processCandidateConclusion(clause: ContextClause, inferenceRuleType: InferenceRule): Boolean = {


      // Uncommenting for Kaminski Optimisation
    /** If the clause contains a constant, we unblock any certain ground facts that mention that constant and immediately add them,
      * to make sure that if the clause is redundant, it will not be added. */
    /** This optimisation is only activated after the Horn Phase, when Horn, simple certain ground facts have been derived,
      * and we still do not have the big, redundant disjunctions that actually cause the issue */
      if (!hornPhaseActive) for (literal <- clause.head) {
        if (literal.constants._1.exists(x => mentionedNominals.add(x))) {
          val o = IRI(literal.constants._1.get.toString).uid
          contextStructureManager.getCertainFacts(o).foreach { uid =>
            redundancyIndex.add(ContextClause(Array[Predicate](), Array[Literal](Concept(IRI(uid),
              Term(IRI.importedIriUid2IriNameString(o)))(ontology)))(ordering))
          }
        }
        if (literal.constants._2.exists(x => mentionedNominals.add(x))) {
          val o = IRI(literal.constants._2.get.toString).uid
          contextStructureManager.getCertainFacts(o).foreach { uid =>
            redundancyIndex.add(ContextClause(Array[Predicate](), Array[Literal](Concept(IRI(uid),
              Term(IRI.importedIriUid2IriNameString(o)))(ontology)))(ordering))
          }
        }
    }


      /** Sanity check for Core and Certain Ground Fact; ALSO blocking clauses that are not useful */
      inferenceRuleType match {
        case Core => require(clause.isHornAndBodyIsEmpty)
        case Hyper | Nom | Pred | Eq => if (clause.isHeadTautology || blockIfNotUseful(clause)) return false
        case Query | CertainGroundClause => if (clause.isHeadTautology) return false
        case _ =>
      }
      /** Perform the redundancy check (which, if the clause is not redundant, adds the clause to the redundancy index
        * and eliminates from the index any clauses it subsumes); it also adds it to indices for propagation to neighbour
        * contexts. */
      val isNotRedundant: Boolean = inferenceRuleType match {
        /** Optimisation: rather than calling addIfNoStrengthening as usual, we directly give the relevant commands */
        case Core => addClauseToContextAndUpdateEndOfRoundPushes(clause,skipRemovals = true) ; true
        case Succ | Coll | PossibleGroundFact | Hyper | Nom | Pred | Query | Eq | CertainGroundClause =>
          if (redundancyIndex.isClauseSubsumed(clause)) return false
          else addClauseToContextAndUpdateEndOfRoundPushes(clause); true
//        /** Certain ground facts are only added to redundancy index, but they dont need to be added to set of predecessors,
//          * or pushed by pred, since they are in every clause and only appear on heads */
//        case CertainGroundFact => {
//          redundancyIndex.add(clause)
//          return true
//        }
      }
      /** If the clause is not redundant, add it to the set of clauses to be processed in this round.  */
      if (isNotRedundant) todo.addUnprocessedClause(clause)
//      /** Some extra sanity checks */ ~ Now skipped because this seems like too many extra operations.
//      if (isNotRedundant) inferenceRuleType match {
//        case Hyper => assert(cforall(clause.head) { l: Literal => !ccontains(clause.body, l) })
//        case Pred => assert(cforall(clause.head) { l: Literal => !ccontains(clause.body, l) })
//        case Eq => assert(cforall(clause.head) { l: Literal => !ccontains(clause.body, l) })
//        case _ =>
//      }
      /** Return whether the clause was redundant */
      isNotRedundant
    }





    /** DEBUG METHODS **/
    //---------------------------------------------------------------------------------------

    // This is a debug function that allows you to print debug derivations only for one particular set of cores.
    def isSelectedCore(): Boolean = {
      return false
//      {
//        val coreString = "http://example.org/a"
//        //val coreString = "A"
//        // val coreString2 = "conceptFor:http://example.org/o3"
//        (core.size == 1) && core.exists {
//          case Concept(iri, _) if iri.toString.contains(coreString) => true
//          case Role(iri, _, _) if iri.toString.contains(coreString) => true
//          //case Concept(iri, _) if iri.toString.contains(coreString2)=> true
//          case _ => false
//        } // DEBUG
//      }
    }

    // Same as above, but takes an argument.
    def isSelectedCore(receivedCore: ImmutableSet[Predicate]): Boolean = {
     true  // THIS IS THE DEFAULT VALUE; SET IT TO TRUE FOR NORMAL BEHAVIOUR
      //    (receivedCore.size == 1)  &&
      //      receivedCore.exists {
      //        case Concept(iri,_) if iri.toString.contains("PositiveChargedAminoAcid") => true
      //        // case Concept(iri,_) if iri.toString.contains("galen#pathological") => true
      //        // case Concept(iri,_) if iri.toString.contains("galen#physiological") => true
      //        case _ => false
      //      }
    }

    //Now applied to a particular predicate
    def isSelectedPredicate(p: Predicate): Boolean = p match {
      case Concept(iri, CentralVariable) if iri.toString.contains("galen#pathological") => true
      case Concept(iri, t) if iri.toString.contains("galen#pathological") && t.toString.contains("f38") => true
      case Role(iri, PredVariable, CentralVariable) if iri.toString.contains("galen#hasIntrinsicPathologicalStatus") => true
      case Role(iri, _, t) if iri.toString.contains("galen#hasIntrinsicPathologicalStatus") && t.toString.contains("f38") => true
      case _ => false
    }

    def coreToIndividual(): Option[Constant] = {
      core.toSeq.headOption.flatMap(x => x match {
        case Concept(_, nom: Constant) => Some(nom)
        case _ => None
      })
    }

    def isSelectedClause(clause: ContextClause): Boolean = {
      clause.head.exists {
        case Concept(iri, a: Constant) if iri.toString.contains("<MD_DataTypeCode>") && a.toString.contains("interfaceClass") => true
        case _ => false
      }
    }

  }

