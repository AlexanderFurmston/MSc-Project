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
import com.sequoiareasoner.kernel.structural.DLOntology
import com.sequoiareasoner.arrayops._
import com.sequoiareasoner.kernel.logging.DerivationObserver
import com.sequoiareasoner.kernel.owl.iri.IRI

import scala.language.postfixOps
import com.sequoiareasoner.kernel.context.RuleSaturator._
import com.sequoiareasoner.kernel.context.ClausePusher._
import com.sequoiareasoner.kernel.context.inferenceRule._

import akka.actor.ActorRef
import akka.actor.ActorSystem
import akka.actor.Props
import akka.actor.UntypedActor

/** Class implementing saturation for a context.
  *
  * @author Andrew Bate <code@andrewbate.com>
  */
class Context(
  state: ContextState,
  ontology: DLOntology,
  isEqualityReasoningEnabled: Boolean,
  order: ContextLiteralOrdering,
  contextStructureManager: ContextStructureManager) extends UntypedActor {

  def actorRef: ActorRef = this.contextStructureManager.contexts.get(state.core).get

  private[this] def processResultsBuffer(state: ContextState, inferenceRuleType: InferenceRule): Unit = {
    while (state.resultsBuffer.nonEmpty) {
              val conclusion = state.resultsBuffer.removeFirst
              val fired = state.processCandidateConclusion(conclusion, inferenceRuleType)
              /** For debugging */
              if (fired && state.isSelectedCore()) inferenceRuleType match {
                  case Hyper => DerivationObserver.hyperFired(state.core,conclusion)
                  case Pred => DerivationObserver.predFired(state.core,conclusion)
                  case Eq => DerivationObserver.eqFired(state.core,conclusion)
                  case Nom => DerivationObserver.nomFired(state.core,conclusion)
                  case _ =>
                }
              }
  }


  private[this] def applyIntracontextRulesToClause(clause: ContextClause, state: ContextState, ontology: DLOntology,
                                                   isEqualityReasoningEnabled: Boolean, ordering:ContextLiteralOrdering,
                                                   hornPhase: Boolean): Unit = {
      /* The Hyper rule will not be applicable if max == C(y) since C(z_i) occurs in neither the body of an ontology
       * clause nor the body of a context clause. */
    cforeach(relevantLiterals(clause,state.isRootContext)) {
        case p: Predicate =>
         //  if (state.isSelectedCore) System.out.println("Literal " + p + " has been selected as maximal in clause " + clause) // DEBUG
          // Since Predicate is the most common case, it is at the top of the match for efficiency.
          /** If the literal is a predicate with variable x, we produce all relevant inferences by Hyper */
          /** Note that no other inferences by Hyper are possible */
          if (p.hasCentralVariable) {
            doHyperInferencesForPredicateInClause(p, clause, state.workedOffClauses, ontology, ordering,
              state.cutting, state.isRootContext, state.resultsBuffer,state.isSelectedCore(),hornPhase)
            processResultsBuffer(state,Hyper)
          }
          /** If the predicate contains a function term, we apply the third part of the Pred rule */
          if (p.containsFunctionalTerm) {
            doThirdStepPredInferencesForPredicateInClause(p, clause, state.workedOffClauses, state.neighborIndex, ordering, state.resultsBuffer)
            processResultsBuffer(state,Pred)
          }
          /** If the predicate is a RSuccTrigger, we apply the third part of the RootPred rule */
          if (p.isRSuccTrigger) {
            doThirdStepRootPredInferencesForPredicateInClause(p, clause, state.workedOffClauses,
              state.neighborIndex, ordering, state.resultsBuffer, state.isSelectedCore())
            /** We mark this inference as Pred() instead of RootPred() because the effect is the same */
            processResultsBuffer(state,Pred)
          }
          /** If the predicate contains a function term or nominal, we apply also the Eq rule */
          if (isEqualityReasoningEnabled && (p.containsFunctionalTerm || p.containsConstant)) {
            doEqInferencesForPredicateInClause(p, clause, state.workedOffClauses, ordering, state.cutting, state.isRootContext, state.resultsBuffer)
            processResultsBuffer(state,Eq)
          }
          /** If the predicate is of the form R(o,x), we attempt to apply the Nom rule */
          // OPTIMISATION: Do not apply the rule in nominal contexts, bc it is never applied there, and with this optimisation
          // we avoid making lots of checks for atoms from ABox assertions of the form R(a,b)
          if (!state.isNominalContext && (p match { case Role(_, _: Constant,CentralVariable) => true; case _ => false })) {
            doNomInferencesForPredicateInClause(p, clause, state, ontology, ordering, state.resultsBuffer)
            processResultsBuffer(state,Nom)
          }
          /** If the predicate is of the form B(o), we also attempt to apply the Nom rule */
          //Optimisation: since most ontologies do not have these triggers, we add a Boolean to reject these tests in most ontologies.
          if (!state.isNominalContext && state.hasNomRuleRoleTriggers) {
            p match {
              case Concept(iri,o: Constant) => for (role <- state.getRolesForNomRuleTrigger(iri.uid,o.id)) {
                val rolePredicate = Role(IRI(role),o,CentralVariable)(ontology)
                for (roleClause <- state.workedOffClauses.maxHeadPredicateLookup(rolePredicate)) {
                  doNomInferencesForPredicateInClause(rolePredicate,roleClause,state,ontology,ordering,state.resultsBuffer)
                  processResultsBuffer(state,Nom)
                }
              }
              case _ =>
            }
          }
        case lit: Equality =>
          /** If the literal is a strict equality, where the maximal term is not a variable, we apply the Eq rule */
          // if (state.isSelectedCore()) System.out.println("Resolving with equality " + lit)
          if (isEqualityReasoningEnabled && lit.isStrict && lit.maxTerm.exists{ case _: Variable => false; case _ => true }) {
            doEqInferencesForEqualityInClause(lit, clause, state.workedOffClauses, ordering, state.cutting, state.isRootContext,state.resultsBuffer)
            processResultsBuffer(state,Eq)
          }
        /** If the literal is a strict inequality, where the maximal term is not a variable, we apply the Eq rule */
        case lit: Inequality =>
          if (isEqualityReasoningEnabled) {
            doEqInferencesForInequalityInClause(lit, clause, state.workedOffClauses, ordering, state.cutting, state.isRootContext, state.resultsBuffer)
            processResultsBuffer(state,Eq)
          }
      }
  }

  /** Takes the stack of unprocessed clauses, and for each clause, and for each selected literal in that clause,
    * (maximal, or maximal and second maximal if it is a clause in a ground context with a query atom as a maximum),
    * it tries all possible inferences by rules:
    * -Hyper
    * -Third part of Pred (hyperresolve a clause with a functional term in maximal position with the Pred clauses
    *  back-propagated from a successor, as well as other context clauses)
    * -Third part of RootPred (analogous)
    * -Eq
    * -Nom
    * that apply to that clause, and adds any non-redundant, non-blocked conclusion to the stack of unprocessed clauses.
    * All newly derived clauses are added to both the redundancy index and; if the clause should propagate info to
    * another context, we add it to an index of clauses that will propagate info to neighbour contexts at the end of
    * this round. We finally add this clause to the set `state.workedOffClauses` of clauses that have been processed.
    * Note that the Elim rule is applied immediately after each clause is derived and is not implemented as a separate rule.
    * Note also that this method must be called before all `pushClauses` methods, which push clauses derived in this round */
  private[this] def rulesToSaturation(state: ContextState,
                                      ontology: DLOntology,
                                      isEqualityReasoningEnabled: Boolean,
                                      ordering: ContextLiteralOrdering,
                                      hornPhase: Boolean): Unit = {
      while (state.todo.unprocessedHornNonEmpty || (!hornPhase && state.todo.unprocessedNonEmpty) ) {
        val unprocessedClause: ContextClause = state.todo.nextUnprocessed
        applyIntracontextRulesToClause(unprocessedClause, state, ontology, isEqualityReasoningEnabled, ordering, hornPhase)
        state.workedOffClauses.add(unprocessedClause)
      }
  }

  /** Applies all rules of the algorithm, until the context is saturated, and pushing relevant clauses to neighbours */

 @inline def saturateAndPush(state: ContextState, ontology: DLOntology, isEqualityReasoningEnabled: Boolean,
                             order: ContextLiteralOrdering, contextStructureManager: ContextStructureManager,
                             hornPhase: Boolean) {
    rulesToSaturation(state, ontology, isEqualityReasoningEnabled, order, hornPhase = hornPhase)
    // if (ontology.havocTriggered) contextStructureManager.interrupt
    /** Push certain ground clauses to all relevant contexts */
    state match {
      case nomState: NominalContextState => pushCertainGroundClausesDerivedInLastRound(nomState, contextStructureManager, ontology)
      case _ =>
    }
    pushInconsistentOntologyMessage(state,contextStructureManager)
    pushPredClausesDerivedInLastRound(state, contextStructureManager)
    state match {
      case nomState: NominalContextState => pushQueryClausesDerivedInLastRound(nomState, contextStructureManager)
      case _ =>
    }
    pushSuccClausesDerivedInLastRound(state, ontology, contextStructureManager, actorRef)
    pushRootSuccClausesDerivedInLastRound(state, ontology, contextStructureManager, actorRef)
    if (state.isRootContext) pushRootCollapsesDerivedInLastRound(state,ontology,contextStructureManager,actorRef)
    pushRequestAllCGCsForConstantsIntroducedInLastRound(state,contextStructureManager,actorRef)
  }




  /** --------------------------------------------- CONTEXT CREATOR -------------------------------------*/

    //    /** Step 0: Import all certain ground facts derived so far clauses; add them straight to the redundancy index set */
    //    if (!state.isNominalContext) for (clause <- contextStructureManager.getCertainGroundFacts(order)) {
    //      state.processCandidateInference(clause,inferenceRule.Hyper)
    //    }

        //DEBUG
    //   println("Creating context with core: ")
    //    for (cu <- state.core) {
    //      println(cu)
    //    }

    /** Initialisation Phase */

    /** Step 1: apply the Core rule */
    if (state.core.exists( p => ontology.isNothing(p) )) {
      state.processCandidateConclusion(ContextClause(ArrayBuilders.emptyPredicateArray, ArrayBuilders.emptyLiteralArray)(order), inferenceRule.Core)
      if (state.isNominalContext) {
        System.out.println("WARNING: Inconsistent Ontology!")
        contextStructureManager.interrupt()
      }
    }
    else {
      for (p <- state.core) {
        val fired = state.processCandidateConclusion(ContextClause(ArrayBuilders.emptyPredicateArray, Array(p))(order), inferenceRule.Core)
        /** For debugging: */
        if (fired && state.isSelectedCore()) DerivationObserver.coreFired(state.core,p)
      }
    }

    /** Step 2: apply Hyper rule on clauses from the ontology with an empty body.  Since the body is empty,
      *  the head cannot contain any neighbour variables. */
    for (OntologyClause(body, head) <- ontology.getNonGroundClausesWithEmptyBody) {
      if (state.hornPhaseActive && head.length > 1) {}
      else {
        val fired = state.processCandidateConclusion(ContextClause(ArrayBuilders.emptyPredicateArray, head)(order), inferenceRule.Hyper)
        /** For debugging: */
        if (fired && state.isSelectedCore()) DerivationObserver.hyperFired(state.core, OntologyClause(body, head), new IdentitySubstitution,
          Seq.empty[ContextClause], ContextClause(ArrayBuilders.emptyPredicateArray, head)(order)) // DEBUG
      }
    }

    /** Step 3: perform all remaining inferences */
    saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, state.hornPhaseActive)

    /** Step 4: mark the context as in sleeping mode */
    contextStructureManager.contextRoundFinished()

    /** Step 5: wake the context up if a new message is received, and start a new saturation round*/
    def onReceive(message: Any): Unit = { // Although message: Any, it should actually be an InterContextMessage
      message match {
        case EndNonHornPhase() => {
          println("tryna end") //!!! todo: remove
        }

        case StartNonHornPhase() => {
          /** When the Horn Phase optimisation is activated, this message reactivates contexts and kickstarts the non-Horn phase */
          state.hornPhaseActive = false

          /** Step 0 and 1 should have been done already */
          for (OntologyClause(body, head) <- ontology.getNonGroundClausesWithEmptyBody if head.length > 1) {
            val fired = state.processCandidateConclusion(ContextClause(ArrayBuilders.emptyPredicateArray, head)(order), inferenceRule.Hyper)
            /** For debugging: */
            if (fired && state.isSelectedCore()) DerivationObserver.hyperFired(state.core, OntologyClause(body, head), new IdentitySubstitution,
              Seq.empty[ContextClause], ContextClause(ArrayBuilders.emptyPredicateArray, head)(order))
          }

          /** We directly saturate; new clauses added in the step just above, and old, non-Horn ones in the todo.nonHornUnprocessed should now be processed */
          saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, state.hornPhaseActive)
        }


        /** Message received: SuccPush - a clause pushed from a predecessor context.  */
        case SuccPush(contextChannel: ActorRef,
        edgeLabel: Term,
        predicate: Predicate, parentCore: ImmutableSet[Predicate]) =>
          //if (state.isSelectedCore2() && state.isSelectedPredicate(predicate) && state.isSelectedCore(parentCore)) {
          //System.out.println("[Physiological] Received succ predicate: " + predicate + " from context with core " + parentCore + " connected by edge with label " + edgeLabel)
          //  System.out.println("Now attempting to see if this unblocks blocked clauses")
          // }
          /** This is awful! It looks like we define a value, but actually this might unblock pred
            *  clauses already in the context and process them, adding them to todo */
          val hasUnblocked = state.addContextStructurePredecessor(contextChannel, edgeLabel, predicate, parentCore)
          // if (state.isSelectedCore2() && state.isSelectedPredicate(predicate) && state.isSelectedCore(parentCore)) System.out.println("And the answer is: " + hasUnblocked)
          // Succ rule conclusion generation
          val fired = state.processCandidateConclusion(ContextClause(Array(predicate), Array(predicate))(order), inferenceRule.Succ)
          // if (clauseAdded && state.isSelectedCore2() && state.isSelectedClause(ContextClause(Array(predicate),Array(predicate))(order)))
          //  System.out.println("[Physiological] Derived clause: " + ContextClause(Array(predicate),Array(predicate))(order))
          if (fired && state.isSelectedCore()) DerivationObserver.succFired(state.core, ContextClause(Array(predicate), Array(predicate))(order))
          if (!fired) {
            /** This optimisation is tricky as F*CK.
              * TL;DR We need to pushWorkedOffPredClauses here always; however, if !fired, we can guarantee that pushing off
              * these clauses is unnecessary.
              * Whenever we add a new edge from a predecessor to this context with
              * mention that a predicate A appears in a maximal position in a clause, we want to ensure that all applications
              * of Pred that involve this edge and this predicate are performed. To ensure this, we need to ensure 1) that all pred clauses
              * that already mention this predicate in the body are propagated back to the predecessor context. This includes
              * all current workedoff pred clauses with explicitly A in the body, if A is not part of the core of current context, or ALL workedoff
              * pred clauses if A is part of the core of the current context (because implicitly is in the body), and 2)
              * in the future, if we derive a clause with head purely of predTriggers that has A in the body, it will automatically be
              * propagated to the predecessor context. 2) Is ensured because of how candidate consequences are processed. 1) can be ensured by
              * propagating workedOffClauses. HOWEVER, if A -> A has been added, this is a guarantee that A IS NOT PART OF THE CORE,
              * AND THERE WAS NO CLAUSE WITH A IN THE BODY BEFORE, because any A in the body appears only via A -> A. This
              * ensures that propagating workedofff clauses at this point would be irrelevant, because none of them would match the required
              * condition.
              *
              * Incidentally, this is what Andrew said: Push the worked off pred clauses first before
              * pushPredClausesDerivedInLastRound to avoid repetition.
              * Doesn't seem to be avoid repetition here, but just skipping an unnecessary step.
               */
            // if (state.isSelectedCore2() && state.isSelectedPredicate(predicate) && state.isSelectedCore(parentCore))
            //  System.out.println("[Physiological] Attempting to push worked off pred clauses to context with core" + parentCore + " across edge " + edgeLabel + "containing predicate " + predicate)
            pushWorkedOffPredClauses(state, contextStructureManager, contextChannel, edgeLabel, predicate, parentCore)
          }
          if (fired || hasUnblocked) {
            saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, state.hornPhaseActive)
          }

        /** Message received: PredPush - a clause pushed from a successor, which can be resolved with clauses in this
          * context. */
        case PredPush(edgeLabel: Term, neighbourCore: ImmutableSet[Predicate],
        predClauses: IndexedSequence[ContextClause]) =>
          predClauses foreach { clause =>
            /** Generate corresponding PredClause after doing substitution */
            val nominalCore = if (state.isNominalContext) Some(state.core.toSeq.head.asInstanceOf[Concept].iri.uid) else None
  //          if (state.isSelectedCore() )  System.out.println("Received clause: " + clause + " from context with core " + neighbourCore)
            val predClause: PredClause = state.neighborIndex.transformAndAdd(edgeLabel, neighbourCore, nominalCore, clause)
  //          if (state.isSelectedCore() )  System.out.println("Transformed clause to: " + predClause)
            Rules.Pred(state.workedOffClauses.maxHeadPredicateLookup, predClause, order, state.resultsBuffer)
            processResultsBuffer(state,Pred)
          }
          saturateAndPush(state, ontology, isEqualityReasoningEnabled, order,
            contextStructureManager, state.hornPhaseActive)

        case QueryPush(nominal: Constant, queryClauses: IndexedSequence[ContextClause]) =>
          queryClauses foreach { clause =>
 //           if (state.isSelectedCore()) System.out.println("Received Query Push : " + clause) // DEBUG
            val queryClause: PredClause = state.neighborIndex.transformQueryHeadAndAdd(nominal, clause)
 //           if (state.isSelectedCore()) println("Transformed version of incoming clause: " + queryClause)
            Rules.Close(state.workedOffClauses.maxHeadEqualityLookup, state.workedOffClauses.maxHeadPredicateLookup,
              state.getUnaryCoreConcept.iri, queryClause, nominal, order, state.resultsBuffer)
            processResultsBuffer(state,Query)
          }
          saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager,
            state.hornPhaseActive)

        /** Message received: A(o) -> A(o) from a predecessor context.  */
        case PossibleGroundFactPush(contextChannel: ActorRef, edgeLabel: Term,
        predicate: Predicate) =>
          predicate match {
            /** Let us exclude propagations of type conceptFor:a(a), since these may not always be prevented by the optimisation,
            * and are always unnecessary */
            case Concept(iri, v) if iri.isInternalIndividual &&
              (Term(IRI.nominalConceptUid2NominalIriStringName(iri.uid)) == v) =>
            case _ =>
              /** Predicate has not been transformed, it is a ground fact C(o); we store this in the predecessor index */
              val hasUnblocked = state.addContextStructurePredecessor(contextChannel, edgeLabel, predicate)
              /** If this is a nominal context with core conceptFor:o, and the predicate contains
                *  the constant o, we then replace it by x */
              val transformedPredicate = if (!state.isNominalContext) predicate else predicate match {
                case Concept(iri, v) if v == Term(IRI.nominalConceptUid2NominalIriStringName(state.getCoreConcept.iri.uid))
                => Concept(iri, CentralVariable)(ontology)
                case _ => predicate
              }
              val clauseAdded = state.processCandidateConclusion(ContextClause(Array(transformedPredicate),
                Array(transformedPredicate))(order), inferenceRule.Succ)
              if (clauseAdded && state.isSelectedCore()) DerivationObserver.allSuccFired(state.core,
                ContextClause(Array(transformedPredicate), Array(transformedPredicate))(order))
              if (!clauseAdded) {
                pushWorkedOffPredClauses(state, contextStructureManager, contextChannel, edgeLabel, transformedPredicate)
              }
              if (clauseAdded || hasUnblocked) {
                saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager,
                  state.hornPhaseActive)
              }
          }

         /** If a potential collapse to a nominal `o` is detected in a query context with core A(x), we push the
            * clause A(x) -> A(x) to the corresponding nominal context for `o`, and add an edge labelled `A(x)` from
            * that query context, to the nominal context for `o`. This is the detection of such push in a nominal context. */
        case CollPush(contextChannel: ActorRef, edgeLabel: Predicate) => {
          state match {
            case nomState: NominalContextState => {
              /** The corresponding root predecessor is added */
              nomState.addRootPredecessor(contextChannel, edgeLabel)
              /** We consider the addition of the relevant clause A(x) -> A(x) */
              val clauseAdded = state.processCandidateConclusion(ContextClause(Array(edgeLabel), Array(edgeLabel))(order), inferenceRule.Coll)
              /** If the clause is added, we need to update indices and start round */
              if (clauseAdded) {
                if (state.isSelectedCore()) DerivationObserver.eqSuccFired(state.core, ContextClause(Array(edgeLabel), Array(edgeLabel))(order)) //DEBUG
                saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, state.hornPhaseActive)
              } else {
              /** If no clause is added, we need to see if we can propagate anything back, except if certain fact, which does not propagate */
                pushWorkedOffQueryClauses(nomState, contextStructureManager, contextChannel, edgeLabel)
              }
            }
            case _ =>
          }
        }

        case CGCPush(clause,originCore) => {
          // if (state.isSelectedCore()) {println("CGC clause pushed!"); println(clause)}
          /** If we are in a nominal context with core O(x), we replace any mention of o in the input clause by x */
          val processedClause = if (state.isNominalContext) {
            val nominal = Term(IRI.nominalConceptUid2NominalIriStringName(state.getCoreConcept.iri.uid))
            val sigma = new NominalAbstractionSubstitution(nominal)
            clause.applySubstitution(sigma)
          } else clause
          val clauseAdded = state.processCandidateConclusion(processedClause, CertainGroundClause)
          if (clauseAdded) {
            if (state.isSelectedCore())  DerivationObserver.cgcFired(state.core,clause,originCore)
            saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, state.hornPhaseActive)
          }
        }

        /** We are a nominal context and receive a message from some other context: ``I mention your constant'',
          * so we add the context to the relevant list and propagate all existing certain ground clauses. */
        case ConstantMentionedPush(originContext) => {
         // if (state.isSelectedCore()) println("Received mentioned constant push in context with core " + state.getCoreConcept)
          state match {
            case nomState: NominalContextState => {
              nomState.constantPredecessors.add(originContext)
              /** Next line includes the contextRoundStarted */
              pushWorkedOffCertainGroundClauses(nomState,contextStructureManager,originContext,ontology)
            }
            case _ =>
          }
        }

        case ConstantExchange(originContext,coreConstant) => {
          /** If the constant corresponding to the core of the origin constant has not been mentioned yet,
            * we update the set of mentioned constants, and send a request to `originContext` to send all
            * relevant CGCs */
       //   if (state.isSelectedCore()) println("Received constant exchange message from nominal context for " + coreConstant)
          state match {
            /** Optimisation: if target and core contexts are the same, just do nothing */
            case nomState: NominalContextState if nomState.getCoreConstant.id == coreConstant.id =>
            case _ => {
              if (state.addConstantToMentionedConstantSet(coreConstant)) {
                contextStructureManager.contextRoundStarted()
                originContext ! ConstantMentionedPush(actorRef)
              }
            }
          }
        }

         /** This is for debug only. If received, print the core */
      // case RevealCore() => {
       //   System.out.println("REVEALING CORE: " + state.core)
      //    contextStructureManager.contextRoundStarted()
        //  }

//        case CertainGroundFactPush(predicates: Set[Int], origin: Int) => {
//          /** If the context mentions the nominal, we add it as usual */
//         if (state.mentionedNominals.contains(IRI(IRI.concept2Nominal(origin)).uid)) {
//            for (predicate <- predicates) {
//              val headPredicate = Concept(IRI(predicate), Term(IRI.concept2Nominal(origin)))(ontology)
//              val clause = ContextClause(Array[Predicate](), Array[Literal](headPredicate))(order)
//              val fired = state.processCandidateInference(clause, inferenceRule.CertainGroundFact)
//              if (fired && state.isSelectedCore()) DerivationObserver.certainGroundFactFired(state.core, clause)
//            }
//          } else {
//            state.blockedCertainGroundFacts.getOrElseUpdate(IRI(IRI.concept2Nominal(origin)).uid, collection.mutable.Set[Int]()) ++= predicates
//          }
//        }
      }
      contextStructureManager.contextRoundFinished()
    }


}
///** Receving CGFs from nominal contexts (this should only be received by nominal contexts */
//
//case BinaryCGFPush(role: Role) =>
///** Don't need to keep track of predecessors since this will not backpropagate */
//val fired = state.processCandidateInference(ContextClause(Array(), Array(role))(order), inferenceRule.Succ)
//// if (clauseAdded && state.isSelectedCore2() && state.isSelectedClause(ContextClause(Array(predicate),Array(predicate))(order)))
////  System.out.println("[Physiological] Derived clause: " + ContextClause(Array(predicate),Array(predicate))(order))
//if (fired && state.isSelectedCore()) DerivationObserver.succFired(state.core,ContextClause(Array(), Array(role))(order))
//if (fired) saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, incoming, state.hornPhaseActive )
//
//case UnaryCGFPush(concept: Concept) =>
///** Don't need to keep track of predecessors since this will not backpropagate */
//val fired = state.processCandidateInference(ContextClause(Array(), Array(concept))(order), inferenceRule.Succ)
//// if (clauseAdded && state.isSelectedCore2() && state.isSelectedClause(ContextClause(Array(predicate),Array(predicate))(order)))
////  System.out.println("[Physiological] Derived clause: " + ContextClause(Array(predicate),Array(predicate))(order))
//if (fired && state.isSelectedCore()) DerivationObserver.succFired(state.core,ContextClause(Array(), Array(concept))(order))
//if (fired) saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, incoming, state.hornPhaseActive )
//
//case EqualityCGFPush(equality: Equality) =>
///** Don't need to keep track of predecessors since this will not backpropagate */
//val fired = state.processCandidateInference(ContextClause(Array(), Array(equality))(order), inferenceRule.Succ)
//// if (clauseAdded && state.isSelectedCore2() && state.isSelectedClause(ContextClause(Array(predicate),Array(predicate))(order)))
////  System.out.println("[Physiological] Derived clause: " + ContextClause(Array(predicate),Array(predicate))(order))
//if (fired && state.isSelectedCore()) DerivationObserver.succFired(state.core,ContextClause(Array(), Array(equality))(order))
//if (fired) saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, incoming, state.hornPhaseActive )