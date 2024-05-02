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

import com.sequoiareasoner.kernel.index.UnprocessedDeque
import com.sequoiareasoner.kernel.clauses.ContextClause

/** Maintains a multi-level queue of unprocessed clauses.
  *
  * @author Andrew Bate <code@andrewbate.com>
  */
final class UnprocessedClauses {

  // The facts that have not yet been used as the primary clause in any rule instance.
  private[this] val unprocessedHornAndEmptyBody = new UnprocessedDeque
  // The Horn clauses that are consequences of rule applications, but have not yet been used as the primary clause in any rule instance.
  private[this] val unprocessedHorn = new UnprocessedDeque
  // The non-Horn clauses that are consequences of rule applications, but have not yet been used as the primary clause in any rule instance.
  private[this] val unprocessedNonHorn = new UnprocessedDeque // TODO: consider sorting by disjunction length.

  def unprocessedNonEmpty: Boolean = unprocessedHornAndEmptyBody.nonEmpty || unprocessedHorn.nonEmpty || unprocessedNonHorn.nonEmpty

  def unprocessedHornNonEmpty: Boolean = unprocessedHornAndEmptyBody.nonEmpty || unprocessedHorn.nonEmpty

  def nextUnprocessed: ContextClause =
    if (unprocessedHornAndEmptyBody.nonEmpty) unprocessedHornAndEmptyBody.removeFirst
    else if (unprocessedHorn.nonEmpty) unprocessedHorn.removeFirst
    else unprocessedNonHorn.removeFirst

//  def nextUnprocessedHorn: ContextClause =
//    if (unprocessedHornAndEmptyBody.nonEmpty) unprocessedHornAndEmptyBody.removeFirst
//    else unprocessedHorn.removeFirst

  /** Adds a clause that is a fact to the set of unprocessed clauses, without first checking for redundancy.
    */
  def enqueueUnprocessedHornAndEmptyBody(clause: ContextClause): Unit = {
    require(clause.isHornAndBodyIsEmpty)
    unprocessedHornAndEmptyBody.addLast(clause)
  }

  /** If an existing unprocessed clause does not make the given clause redundant, then adds the given clause to the
    * queue of unprocessed clauses.
    */
  def addUnprocessedClause(clause: ContextClause): Unit = {
    // System.out.println("Derived clause: " + clause)
    val isHorn = clause.isHorn
    val isHornAndEmptyBody = clause.isHornAndBodyIsEmpty
    // Clauses that are facts never subsume other facts in the unprocessed queue.
    if (isHorn) unprocessedHorn.removeRedundant(clause)
    unprocessedNonHorn.removeRedundant(clause)
    if (isHornAndEmptyBody) unprocessedHornAndEmptyBody.addLast(clause)
    else if (isHorn) unprocessedHorn.addLast(clause)
    else unprocessedNonHorn.addLast(clause)
  }

}
