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

import com.sequoiareasoner.arrayops._

/** Package providing the implementation of predicates, equations, literals, clauses, and ordering.
  *
  * @author Andrew Bate <code@andrewbate.com>
  */
package object clauses {


  //TODO: Add requirement that clauses cannot have repeated elements, and optimise algorithms accordingly.


  /** STRUCTURAL TRANSFORMATION CLAUSE */

  /** Clause used during structural transformation. */
  final case class STClause(body: Seq[Predicate], head: Seq[Literal]) {
    require {
      body forall {
        case Concept(_, _: Variable) => true
        case Role(_, _: Variable, _: Variable) => true
        case _ => false
      }
    }

    override def toString = s"STClause[${body mkString " AND "} -> ${head mkString " OR "}]"
  }


  /** ONTOLOGY CLAUSE */

  /** Clause from the normalised ontology, which is used for algorhithm execution */
  final case class OntologyClause private(body: Array[Predicate], head: Array[Literal]) {
    require(isLegal, s"$this is illegal!")

    def toContextClause(ordering: ContextLiteralOrdering): ContextClause = ContextClause(body, head)(ordering)

    def isHorn: Boolean = head.length <= 1

    def hasEquality: Boolean =
      cexists(head) {
        case _: Equality => true
        case _ => false
      }

    /** This method verifies that:
      * -Every concept in the body has x as its inner term.
      * -Every neighbour variable occurring in the head also occurs within a role in the body. */
    private[this] def isLegal: Boolean = {
      def termUsageIsLegal(t: Term): Boolean = t match {
        case NeighbourVariable(_) => cexists(body) {
          case Role(_, l, r) => l == t || r == t
          case _ => false
        }
        case _ => true
      }
      cforall(body) {
        case Concept(_, CentralVariable) => true
        case Concept(_, _) => false
        case _ => true
      } && cforall(head) {
        case Role(_, s, t) => termUsageIsLegal(s) && termUsageIsLegal(t)
        case Concept(_, v) => termUsageIsLegal(v)
        case Equality(s, t) => termUsageIsLegal(s) && termUsageIsLegal(t)
        case Inequality(s, t) => termUsageIsLegal(s) && termUsageIsLegal(t)
      }
    }

    /** Check if an ontology clause is an ``at most`` restriction: all elements of the head must be equalities z_i = z_j,
      * and the head cannot be empty. */
    def isAtMost: Boolean =
      !head.isEmpty && head.forall {
        case Equality(NeighbourVariable(_),NeighbourVariable(_)) => true
        case _ => false
      }

    override def toString = s"OntologyClause[${body mkString " AND "} -> ${head mkString " OR "}]"
  }

  /** Companion object */
  object OntologyClause {
    def apply(body: Set[Predicate], head: Set[Literal]): OntologyClause =
      OntologyClause(body.toArray, head.toArray)

    def apply(body: Seq[Predicate], head: Seq[Literal]): OntologyClause =
    //TODO: Need to remove duplicates before constructing the ontology clause.
      OntologyClause(body.toSet.toArray, head.toSet.toArray)

    def apply(body: Predicate, head: Literal): OntologyClause =
      OntologyClause(Array(body), Array(head))
  }


  /** CONTEXT CLAUSE */

  /** Represents a context clause (i.e. a clause derived within a context). */
  final case class ContextClause(body: Array[Predicate], head: Array[Literal])(ordering: ContextLiteralOrdering) {
    /** Check that Ineq rule has been applied eagerly */
    require {
      cforall(head) {
        case Inequality(s, t) if s == t => false
        case _ => true
      }
    }

    def isHorn: Boolean = head.length <= 1

    def isEmpty: Boolean = head.length == 0 && body.length == 0

    def isFunctionFree: Boolean = head.forall( lit => lit.isFunctionFree )

    def applySubstitution(sigma: Substitution): ContextClause = {
      val newBody: Array[Predicate] = for (atm <- body) yield atm.applySubstitution(sigma)
      val newHead: Array[Literal] = for (lit <- head) yield lit.applySubstitution(sigma)
      ContextClause(newBody,newHead)(ordering)
    }


    /** Convenience method */

    def isCertainFunctionFreeGroundClause: Boolean = {
    //  body.forall {
    //    case Concept(_, CentralVariable) => true
    //    case Concept(_, _: Constant) => true
    //    case Role(_, CentralVariable, CentralVariable) => true
    //    case Role(_, _: Constant, CentralVariable) => true
    //    case Role(_, CentralVariable, _: Constant) => true
    //    case Role(_, _: Constant, _: Constant) => true
    //    case _ => false
    //  } && {
        body.isEmpty && head.forall {
        case Concept(_, CentralVariable) => true
        case Concept(_, _: Constant) => true
        case Role(_, CentralVariable, CentralVariable) => true
        case Role(_, _: Constant, CentralVariable) => true
        case Role(_, CentralVariable, _: Constant) => true
        case Role(_, _: Constant, _: Constant) => true
        case Equality(CentralVariable, CentralVariable) => true
        case Equality(_: Constant, CentralVariable) => true
        case Equality(CentralVariable, _: Constant) => true
        case Equality(_: Constant, _: Constant) => true
        case Inequality(CentralVariable, CentralVariable) => true
        case Inequality(_: Constant, CentralVariable) => true
        case Inequality(CentralVariable, _: Constant) => true
        case Inequality(_: Constant, _: Constant) => true
        case _ => false
        }
    //  }
    }

    def isHornAndBodyIsEmpty: Boolean = body.length == 0 && head.length <= 1

    def headContainsConstant(o: Constant): Boolean = {
      head.exists( _.contains(o))
    }

    /** Head literals that are not dominated by any other literal in the head */
    val maxHeadLiterals: Array[Literal] =
      cfilter(head) { l: Literal => cforall(head) { k => k == l || !ordering.lteq(l, k) } }
    /** Head predicates that are not dominated by any other literal in the head */
    val maxHeadPredicates: Array[Predicate] = ccollect[Predicate, Literal](maxHeadLiterals)

    // For OPTIMISATION ORDER
    val maxAndSecondMaxHeadLiterals: Array[Literal] = if ((maxHeadLiterals.size == 1) && (
      maxHeadLiterals(0) match {
        case Concept(iri, CentralVariable) if iri.isImported || iri.isInternalIndividual => true
        case _ => false
      })) {
      maxHeadLiterals ++: otherHeadLiteral.find( l => otherHeadLiteral.forall ( k => k == l || !ordering.lteq(l, k) ) ).toArray
      }
    else maxHeadLiterals

     val maxAndSecondMaxHeadPredicates: Array[Predicate] = ccollect[Predicate, Literal](maxAndSecondMaxHeadLiterals)

    /** Head literals that ARE dominated by some other literal in the head */
    private[this] def otherHeadLiteral: Array[Literal] = cfilterNot(head) { l => ccontains(maxHeadLiterals, l) }


    override def equals(that: Any): Boolean = this eq that.asInstanceOf[AnyRef]

    /** Returns `true` if and only if the head of this clause is a tautology, i.e., there exist terms s and t such that
      * `Equality(s, s) ∈ head` or `{Equality(s, t), Inequality(s, t)} ⊆ head`. */
    def isHeadTautology: Boolean =
      cexists(head) {
        case Equality(s, t) => s == t || cexists(head) {
          case Inequality(`s`, `t`) => true
          case Inequality(`t`, `s`) => true
          case _ => false
        }
        case _ => false
      }

    /** Determines the strengthening relationship between this clause and the one passed as argument.
      *
      * @param that the clause to test against
      * @return -1 if `this` is a strengthening of `that` (or `this` and `that` are equal),
      *         +1 if `that` is a proper strengthening of `this`, or
      *         0 is neither is a strengthening of the other.
      */
    def testStrengthening(that: ContextClause): Int = {
      val thisBody = this.body; val thatBody = that.body
      val thisHead = this.head; val thatHead = that.head
      if (isSubsetOf(thisBody, thatBody) && isSubsetOf(thisHead, thatHead)) -1
      else if (isSubsetOf(thatBody, thisBody) && isSubsetOf(thatHead, thisHead)) +1
      else 0
    }

    /** Is a rule whose head means that the Pred rule can be triggered */
    def isClauseHeadForPred: Boolean = cforall(head) { x => x.isPredTrigger || x.isGround }

    def isClauseHeadForQuery: Boolean = cforall(head) {
      case Concept(iri, CentralVariable) if iri.isImported || iri.isInternalIndividual || iri.isNothing => true
      case _ => false
    }

    override def toString: String =
      if (otherHeadLiteral.isEmpty)
        s"ContextClause[${body mkString " AND "} -> [${maxHeadLiterals mkString " OR "}]]"
      else
        s"ContextClause[${body mkString " AND "} -> [${maxHeadLiterals mkString " OR "}] OR ${otherHeadLiteral mkString " OR "}]"

  }

  /** The type of a pred clause with the substitution already applied. */
  final case class PredClause(body: Array[Predicate], head: Array[Literal]) {
    override def toString = s"PredClause[${body mkString " AND "} -> [${head mkString " OR "}]]"
  }


  /** Returns `true` if each element in arr1 is contained in arr2. */
  private[this] def isSubsetOf[L <: Literal](arr1: Array[L], arr2: Array[L]): Boolean = {
    arr1.toSet.subsetOf(arr2.toSet)
//    val length1 = arr1.length
//    val length2 = arr2.length
//    if (length1 > length2) return false
//    /** The invariant here is that the literal 1 is always bigger or equal than that of 2, otherwise the answer is no */
//    var i, j = 0
//    while (i < length1 && j < length2) {
//      val comparison = arr1(i) compare arr2(j)
//      /** If the literal in array 1 is bigger than the one in array 2, move to the next one in array 2 */
//      if (comparison > 0) {
//        j += 1
//      }
//
//      /** If they are the same, we move on to the next literal */
//      else if (comparison == 0) {
//        i += 1
//        j += 1
//      }
//
//      /** If the literal in array 2 is bigger than the one in array 1, the invariant is broken and hence the answer is negative */
//      else {
//        return false
//      }
//    }
//    /** When the loop is over, one of the two indices is at the end of their respective literal. The reply is positive
//      * iff we have recached the end of literal 1 */
//    return i == length1
  }

}
