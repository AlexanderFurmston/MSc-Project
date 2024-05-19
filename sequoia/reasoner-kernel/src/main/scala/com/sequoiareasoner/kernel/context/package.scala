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

package com.sequoiareasoner.kernel

import com.sequoiareasoner.kernel.clauses._
import com.sequoiareasoner.kernel.index.{ImmutableSet, IndexedSequence}

/** Package containing relevant methods for the entire package context. */
package object context {

  /** Given a context clause, and an indicator of whether the context is a root context,
    * this determines the literals that are selected in the clause for participation in inferences. */
  def relevantLiterals(clause: ContextClause, isRootContext: Boolean): Array[Literal] =
    if (isRootContext) clause.maxAndSecondMaxHeadLiterals else clause.maxHeadLiterals

  /** ---------------------------- INTERCONTEXT MESSAGES ---------------------------------- */


  /** Trait for inter-context messages sent during the application of rules of the calculus. */
  sealed trait InterContextMessage extends Any

  /** A message to notify a context that it must apply the second part of the Pred rule to each clause in a set `clauses`.
    * This requires:
    * -A set of clauses `clauses` is passed to a predecessor.
    * -The term `edgeLabel` of the form f(x) labelling the edge.
    * -The core of the successor (this is added to the body of clauses in `clauses`, even though this should be useless
    *  since the core of a successor is always a fragment of K1(f), the certain set of f in the predecessor. */
  final case class PredPush(edgeLabel: Term,
                            core: ImmutableSet[Predicate],
                            clauses: IndexedSequence[ContextClause]) extends InterContextMessage

  /** A message to propagate a binary certain ground atom i.e. of the form top -> R(a,b) - represented R(a,x), where a
    * is the origin nominal context and x stands for the destination nominal context */
  final case class BinaryCGFPush(role: Role) extends InterContextMessage


  /** A message to propagate a unary certain ground atom i.e. of the form top -> B(a) - represented B(x), where a
    * is the destination nominal context */
  final case class UnaryCGFPush(concept: Concept) extends InterContextMessage

  /** A message to propagate an equality certain ground atom i.e. of the form top -> a = b - represented a=x or x=b or a=b */
  final case class EqualityCGFPush(equality: Equality) extends InterContextMessage

  /** Message to notify a root context that may collapse into a nominal, that such circumstance leads to
    * deriving query clauses. This requires:
    * -The set `clauses` of derived query clauses.
    * -The constant `nominal` */
  final case class QueryPush(nominal: Constant, clauses: IndexedSequence[ContextClause]) extends InterContextMessage


  /** Message to notify a context that the second part of the Succ rule must be applied to a predicate `predicate`
    * in predecessor `contextChannel` with label `edgeLabel`. This requires:
    * -The edge `contextChannel` to update the index of predecessors in the successor context.
    * -The label `edgeLabel` to update the index of relevant predecessor predicates in the successor context (this is
    * probably unnecessary, as the label can be deduced from the predicate).
    * -The predicate `predicate` to which the rule is applied.
    * -The `core` of the predecessor, for debugging purposes (and consequently we pass the empty one by default). */
  final case class SuccPush(contextChannel: ContextRunnable,
                            edgeLabel: Term,
                            predicate: Predicate,
                            core: ImmutableSet[Predicate] = ImmutableSet.empty) extends InterContextMessage

  final case class MiniSuccPush(contextChannel: ContextRunnable, predicate: Predicate) extends InterContextMessage

  /** Message to notify a context that a set of certain ground fact `clauses` has been derived */
  final case class CertainGroundFactPush(predicates: Set[Int], origin: Int) extends InterContextMessage

  final case class StartNonHornPhase() extends InterContextMessage

  final case class EndNonHornPhase() extends InterContextMessage

 /** Message to notify a context that it must add a tautology with a ground fact `predicate` and update so that its
   * predecessor `contextChannel` with edge `edgeLabel` also has this fact. This requires:
   * -The predicate itself `predicate`
   * -The edge to the predecessor `contextChannel` for updating the index of predecessors.
   * -The edge label of the predecessor for updating the index of predecessors. */
  final case class PossibleGroundFactPush(contextChannel: ContextRunnable,
                                          edgeLabel: Term,
                                          predicate: Predicate) extends InterContextMessage


  /** Message to notify a nominal context that some root context `contextChannel` may collapse into it,
    *  so the core of that root context `edgeLabel` must be added as a tautology (and the index updated). */
  final case class CollPush(contextChannel: ContextRunnable,
                            edgeLabel: Predicate) extends InterContextMessage
 /** This clause propagates certain, function-free ground clauses from nominal contexts to other contexts that mention
   * the nominal corresponding to this context. */
  final case class CGCPush(clause: ContextClause, core: ImmutableSet[Predicate]) extends InterContextMessage

  /** This rule propagates certain, function-free ground clauses from nominal contexts to other contexts that mention
   * the nominal corresponding to this context. */
  final case class ConstantMentionedPush(originContext: ContextRunnable) extends InterContextMessage

  /** This message is sent from a nominal context with core `O`, which mentions constant `a`, to nominal context `A`,
    * and tells it that it should act as if `o` had been mentioned in `A`. */
  final case class ConstantExchange(originContext: ContextRunnable, originConstant: Constant) extends InterContextMessage


  /** FOR DEBUGGING. A message to notify a context that it should print its core. */
  final case class RevealCore() extends InterContextMessage
}
