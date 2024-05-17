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

import java.util.concurrent.Callable

class ContextRunnable(
    val state: ContextState,
    val ontology: DLOntology,
    val isEqualityReasoningEnabled: Boolean,
    val order: ContextLiteralOrdering,
    val contextStructureManager: ContextStructureManager) {

    /** Do contextRoundStarted here so we don't need to do it in lots of other places */
    // contextStructureManager.contextRoundStarted()

    println("ContextRunnable creation")

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

    println("ContextRunnable creation finished")

    def saturateAndPush(): Callable[Unit] = () => {
      /** Step 3: perform all remaining inferences */
      Context.saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, this, state.hornPhaseActive)

      /** Step 4: mark the context as in sleeping mode */
      contextStructureManager.contextRoundFinished()
    }


    /** Step 5: Separated into a separate method - receive a message and start a new saturation round */
    def reSaturateUponMessage(message: InterContextMessage): Unit = {
      contextStructureManager.contextRoundStarted()

      message match {
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
          Context.saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, this, state.hornPhaseActive)
        }


        /** Message received: SuccPush - a clause pushed from a predecessor context.  */
        case SuccPush(contextChannel: ContextRunnable,
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
            Context.saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, this, state.hornPhaseActive)
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
            Context.processResultsBuffer(state,Pred)
          }
          Context.saturateAndPush(state, ontology, isEqualityReasoningEnabled, order,
            contextStructureManager, this, state.hornPhaseActive)

        case QueryPush(nominal: Constant, queryClauses: IndexedSequence[ContextClause]) =>
          queryClauses foreach { clause =>
 //           if (state.isSelectedCore()) System.out.println("Received Query Push : " + clause) // DEBUG
            val queryClause: PredClause = state.neighborIndex.transformQueryHeadAndAdd(nominal, clause)
 //           if (state.isSelectedCore()) println("Transformed version of this clause: " + queryClause)
            Rules.Close(state.workedOffClauses.maxHeadEqualityLookup, state.workedOffClauses.maxHeadPredicateLookup,
              state.getUnaryCoreConcept.iri, queryClause, nominal, order, state.resultsBuffer)
            Context.processResultsBuffer(state,Query)
          }
          Context.saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager,
            this, state.hornPhaseActive)

        /** Message received: A(o) -> A(o) from a predecessor context.  */
        case PossibleGroundFactPush(contextChannel: ContextRunnable, edgeLabel: Term,
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
                Context.saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager,
                  this, state.hornPhaseActive)
              }
          }

         /** If a potential collapse to a nominal `o` is detected in a query context with core A(x), we push the
            * clause A(x) -> A(x) to the corresponding nominal context for `o`, and add an edge labelled `A(x)` from
            * that query context, to the nominal context for `o`. This is the detection of such push in a nominal context. */
        case CollPush(contextChannel: ContextRunnable, edgeLabel: Predicate) => {
          state match {
            case nomState: NominalContextState => {
              /** The corresponding root predecessor is added */
              nomState.addRootPredecessor(contextChannel, edgeLabel)
              /** We consider the addition of the relevant clause A(x) -> A(x) */
              val clauseAdded = state.processCandidateConclusion(ContextClause(Array(edgeLabel), Array(edgeLabel))(order), inferenceRule.Coll)
              /** If the clause is added, we need to update indices and start round */
              if (clauseAdded) {
                if (state.isSelectedCore()) DerivationObserver.eqSuccFired(state.core, ContextClause(Array(edgeLabel), Array(edgeLabel))(order)) //DEBUG
                Context.saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, this, state.hornPhaseActive)
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
            Context.saturateAndPush(state, ontology, isEqualityReasoningEnabled, order, contextStructureManager, this, state.hornPhaseActive)
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
                contextStructureManager.messageContext(originContext, ConstantMentionedPush(this))
              }
            }
          }
        }
      }

      contextStructureManager.contextRoundFinished()
    }
}