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

package com.sequoiareasoner.kernel.index

import com.sequoiareasoner.kernel.clauses._
import com.sequoiareasoner.kernel.owl.iri.IRI

import scala.collection.mutable

/** Maintains an index of the clauses that can participate in the Pred rule for a single context and that have been
  * pushed back from successor context.
  *
  * @author Andrew Bate <code@andrewbate.com>
  */
class NeighborPredClauseIndex {

  private[this] val conceptIndex = new LongIndexedSequenceMap[PredClause](8, ArrayBuilders.predClauseArrayBuilder)
  private[this] val forwardsRoleIndex = new LongIndexedSequenceMap[PredClause](8, ArrayBuilders.predClauseArrayBuilder)
  private[this] val backwardsRoleIndex = new LongIndexedSequenceMap[PredClause](8, ArrayBuilders.predClauseArrayBuilder)
  // private[this] val equalityIndex = new LongIndexedSequenceMap[PredClause](8, ArrayBuilders.predClauseArrayBuilder)


  private val term2Int = new mutable.AnyRefMap[Term,Int]()
  private var nextInt: Int = 1
  def getOrElseUpdate(t: Term): Int = {
    term2Int.getOrElseUpdate(t, {
      nextInt = nextInt + 1
      nextInt - 1
    })
  }

  private[this] def compoundKey(iri: IRI, t: Term): Long = iri.uid.toLong << 32 | getOrElseUpdate(t).toLong
  // private[this] def compoundKey(term1: Term, term2: Term): Long = term1.xid.toLong << 32  | term2.xid.toLong

  import com.sequoiareasoner.arrayops._


  /** Takes a clause propagated via Pred from a successor context, and transforms it to the correct form,
    * and maybe does something else too. */
  def transformAndAdd(t: Term, neighbourCore: ImmutableSet[Predicate], nominalCore: Option[Int], c: ContextClause): PredClause = {
    /** Sanity check */
    t match {
      case FunctionalTerm(_) | _: Constant =>
      case _ => throw new IllegalArgumentException
    }
    val sigma = new BackwardsInterContextSubstitution(t,nominalCore)
    /** If backpropagating from a nominal context, we don't need the core O(x), as it is a tautology, and we can assume
      * O(o) is, virtually, in every context. This line assumes nominals appear alone in cores (i.e. no core B(x) ^ O(x)) */
    val neighbourCoreSeq: Seq[Predicate] = if (neighbourCore.forall( p => p.iri.isInternalIndividual)) Set[Predicate]().toSeq else neighbourCore.toSeq
    val clauseBodyLength: Int = c.body.length
    val newBody: Array[Predicate] = new Array[Predicate](clauseBodyLength + neighbourCoreSeq.size)
    crange(0, newBody.length) { i =>
      newBody(i) =
        if (i < clauseBodyLength) c.body(i).applySubstitution(sigma)
        else neighbourCoreSeq(i - clauseBodyLength).applySubstitution(sigma)
    }
    val newHead: Array[Literal] = cmap (c.head) {_.applySubstitution(sigma)}
    val predClause: PredClause = PredClause(newBody, newHead)
    cforeach (newBody) {
      case Concept(iri, s: FunctionalTerm) =>
        conceptIndex.addBinding(compoundKey(iri, s), predClause)
      case Concept(iri, s: Constant) =>
        conceptIndex.addBinding(compoundKey(iri, s), predClause)
      case Concept(iri, CentralVariable) =>
        conceptIndex.addBinding(compoundKey(iri, CentralVariable), predClause)
      case Role(iri, CentralVariable, s: FunctionalTerm) =>
        forwardsRoleIndex.addBinding(compoundKey(iri, s), predClause)
      case Role(iri, CentralVariable, s: Constant) =>
        forwardsRoleIndex.addBinding(compoundKey(iri, s), predClause)
      case Role(iri, s1: FunctionalTerm, CentralVariable)  =>
        backwardsRoleIndex.addBinding(compoundKey(iri, s1), predClause)
      case Role(iri, s1: Constant, CentralVariable)  =>
        backwardsRoleIndex.addBinding(compoundKey(iri, s1), predClause)
    }
    predClause
  }

  /** Takes a clause propagated via Query (from a nominal context) and transforms the body to ground form;
    * also, it DOES NOT YET eliminate the atom of the form B(o), where B(x) is the core of the context we just propagated to,
    * as it will do this as part of the Close rule, for otherwise we add unsound PredClauses to the index */
  def transformQueryHeadAndAdd(constant: Constant, c: ContextClause): PredClause = {
    val sigma = new TermSubstitution(constant)
    //val clauseBodyLength: Int = if (c.body.isEmpty) c.body.length; else c.body.length - 1
    val clauseBodyLength: Int = c.body.length
    val newBody: Array[Predicate] = new Array[Predicate](clauseBodyLength)
    // var foundAtomToRemove: Boolean = false
    crange(0, newBody.length) { i =>
      //      if (foundAtomToRemove) newBody(i-1) = c.body(i).applySubstitution(sigma)
      //      else if (c.body(i).iri == core) {
      //        foundAtomToRemove = true
      //      } else {
      newBody(i) = c.body(i).applySubstitution(sigma) // }
    }
    /** The head of this clause has query form; i.e. atoms of the form C(x) v D(x) v ... so it stays like this; no subs */
    val newHead: Array[Literal] = c.head
    val predClause: PredClause = PredClause(newBody, newHead)
    cforeach (newBody) {
      case Concept(iri, s: Constant) =>
        conceptIndex.addBinding(compoundKey(iri, s), predClause)
      case _ =>
    }
    predClause
  }

  /** Given a literal, returns a sequence of all pred clauses that contain the literal in the body. */
  def apply(p: Literal): IndexedSequence[PredClause] = {
    p match {
      case Concept(iri, t: FunctionalTerm) =>
        conceptIndex(compoundKey(iri, t))
      case Concept(iri, c: Constant) =>
        conceptIndex(compoundKey(iri,c))
      case Role(iri, CentralVariable, t: FunctionalTerm) =>
        forwardsRoleIndex(compoundKey(iri, t))
      case Role(iri, CentralVariable, t: Constant) =>
        forwardsRoleIndex(compoundKey(iri, t))
      case Role(iri, t: FunctionalTerm, CentralVariable) =>
        backwardsRoleIndex(compoundKey(iri, t))
      case Role(iri, t: Constant, CentralVariable) =>
        backwardsRoleIndex(compoundKey(iri, t))
    }}

  override def toString: String = {
    val builder = new StringBuilder
    builder.append("NeighborPredClauseIndex[\n")
    def buildString(k: Long, vs: IndexedSequence[PredClause]): Unit =
      vs.addString(builder.append(k), " -> [", ", ", "]\n")
    conceptIndex foreach buildString
    forwardsRoleIndex foreach buildString
    backwardsRoleIndex foreach buildString
    builder.append("]")
    builder.result
  }

}
