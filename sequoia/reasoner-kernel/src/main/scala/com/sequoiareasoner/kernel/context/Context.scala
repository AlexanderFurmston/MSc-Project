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

/** Class implementing saturation for a context.
  *
  * @author Andrew Bate <code@andrewbate.com>
  */
object Context {

  def processResultsBuffer(state: ContextState, inferenceRuleType: InferenceRule): Unit = {
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
                             incoming: ContextRunnable, hornPhase: Boolean )  {
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
    pushSuccClausesDerivedInLastRound(state, ontology, contextStructureManager, incoming)
    pushRootSuccClausesDerivedInLastRound(state, ontology, contextStructureManager, incoming)
    if (state.isRootContext) pushRootCollapsesDerivedInLastRound(state,ontology,contextStructureManager,incoming)
    pushRequestAllCGCsForConstantsIntroducedInLastRound(state,contextStructureManager,incoming)
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