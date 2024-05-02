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

package com.sequoiareasoner.kernel.clauses

import com.sequoiareasoner.kernel.owl.iri.IRI

import scala.collection.mutable

/** Trait representing a term, which can be of any of the following forms:
  *
  * -Central Variable x.
  * -Predecessor Variable y.
  * -Neighbour Variable z_i.
  * -Functional Term f_i(x).
  * -Original Individual o_i.
  * -Artificial Individual (o_i,rho).
  *
  */

sealed trait Term {

  type T <: Term

  /** Terms in a context can be compared according to the following partial order:
    * - y is smaller than x
    * - x is smaller than z_i
    * - z_i is smaller than z_j iff i < j
    * - o_i is smaller than o_j iff i < j
    * - x is smaller than f(x)
    * - o_i is smaller than (o_j, rho)
    * - (o_i,rho) is smaller than (o_j,rho') according to the lexicographic order between the two.
    *
    * For neigbhour variables, we invert the order since the original sequoia uses negative numbers for it, but we don't.
    *
    */
  @inline def <(that: Term): Boolean = {
    this match {
      case CentralVariable => that match {
          case NeighbourVariable(_) => true
          case FunctionalTerm(_) => true
          case _ => false
        }
      case OriginalIndividual(i) => that match {
        case OriginalIndividual(j) => i < j
        case FunctionalTerm(_) => true
        case ArtificialIndividual(_) => true
        case _ => false
      }
      case PredVariable => that match {
        case PredVariable => false
        case _: Constant => false
        case _ => true
      }
      case FunctionalTerm(i) => that match {
        case FunctionalTerm(j) => i < j
        case _ => false
      }
      case NeighbourVariable(i) => that match {
        case NeighbourVariable(j) => i > j
        case _ => false
      }
        // See below for explanation
      case ArtificialIndividual(i) => that match {
        case ArtificialIndividual(j) => i < j
        case FunctionalTerm(_) => true
        case _ => false
      }
//      case ArtificialIndividual(i,rho1,n1) => that match {
//        case ArtificialIndividual(j,rho2,n2) =>
//          if (rho1.length < rho2.length) true
//          else if (rho2.length > rho1.length) false
//          else if (i > j) true
//          else if (i < j) false
//          // TODO: ADD order taking into account the IntList
//          else rho1.zip(rho2).filterNot(x => x._1 == x._2).headOption.exists(x => x._1.uid > x._2.uid)
//        case FunctionalTerm(_) => true
//        case _ => false
//      }
      case _ => throw new IllegalArgumentException(s"Term $this could not be matched to any known term pattern.")
    }
  }

  @inline def <=(that:Term): Boolean = this < that || this == that


  @inline def >(that: Term): Boolean = {
    this match {
      case CentralVariable => that match {
        case PredVariable => true
        case _ => false
      }
      case OriginalIndividual(i) => that match {
        case OriginalIndividual(j) => i > j
        case _ => false
      }
      case PredVariable => false

      case FunctionalTerm(i) => that match {
        case CentralVariable => true
        case PredVariable => true
        case _: Constant => true
        case FunctionalTerm(j) => i > j
        case _ => false
      }
      case NeighbourVariable(i) => that match {
        case NeighbourVariable(j) => i < j
        case CentralVariable => true
        case PredVariable => true
        case _ => false
      }
        // See comments below for explanation
      case ArtificialIndividual(i) => that match {
        case OriginalIndividual(_) => true
        case ArtificialIndividual(j) => i > j
        case _ => false
      }
//      case ArtificialIndividual(i,rho1,n1) => that match {
//        case ArtificialIndividual(j,rho2,n2) =>
//          if (rho1.length > rho2.length) true
//          else if (rho2.length < rho1.length) false
//          else if (i < j) true
//          else if (i > j) false
//          // TODO: ADD order taking into account the IntList
//          else rho1.zip(rho2).filterNot(x => x._1 == x._2).headOption.exists(x => x._1.uid < x._2.uid)
//        case OriginalIndividual(_) => true
//        case _ => false
//      }

      case _ => false
    }
  }

//  @inline def <=(that: Term): Boolean = !(this > that)
//  @inline def ~=(that:Term): Boolean = !(this > that) && !(that > this)

  /** Given two terms, if one is strictly greater than the other, this method should return it */
  @inline def max(that: Term): Option[Term] = if (this < that) Some(that); else if (this > that) Some(this); else None

  /** Given two terms, if one is strictly smaller than the other, this method should return it */
  @inline def min(that: Term): Option[Term] = if (this > that) Some(that); else if (this < that) Some(this); else None

  /** Returns a string representing the term. */
  override def toString: String

}

/** Trait representing a variable: x, y, or z_i */
sealed trait Variable extends Term {
  override type T <: Variable
}

case object CentralVariable extends Variable {
  override type T = CentralVariable.type

  override def toString: String = "x"
}

case object PredVariable extends Variable {
  override type T = PredVariable.type

  override def toString: String = "y"
}

final case class NeighbourVariable(id: Int) extends Variable {
  require (id > 0)
  override type T = NeighbourVariable

  override def toString: String = s"z$id"
}

final case class FunctionalTerm(id: Int) extends Term {
  require (id > 0)
  override type T = FunctionalTerm

  override def toString: String = s"f$id(x)"
}

sealed trait Constant extends Term {
  override type T <: Constant
  def id: Int

  // def next(iri: IRI, n: Int): ArtificialIndividual

}

final case class OriginalIndividual(id: Int) extends Constant {
  require (id > 0)
  override type T = OriginalIndividual

  override def toString: String = s"${Term.getName(id)}"

  //def next(iri: IRI,n: Int) =  ArtificialIndividual(id,List(iri),List(n))

}

final case class ArtificialIndividual(id: Int) extends Constant {
  require (id > 0)
  override type T = ArtificialIndividual

  //TODO: Replace this toString method with a recursive function to print the name and all the roles, concepts, and numbers.
  override def toString: String = "ArtificialNominal" + id
}

object Term {

  def x: CentralVariable.type = CentralVariable
  def y: PredVariable.type = PredVariable
  def z(i: Int): Term = NeighbourVariable(i)
  def f(i: Int): Term = FunctionalTerm(i)
  def o(i: Int): Term = OriginalIndividual(i)

  private[this] val artificialIndividualIndex = new mutable.HashMap[(Int,Int,Int,Int),Int]
  private[this] val name2Id = new mutable.HashMap[String, Int]
  private[this] val id2Name = new mutable.HashMap[Int,String]
  private[this] var nextIndividualId: Int = 1

  def apply(name: String): OriginalIndividual = {
     val id = name2Id.getOrElseUpdate(name, {
       val i = nextIndividualId
       id2Name.put(i, name)
       nextIndividualId += 1
       i
     })
     OriginalIndividual(id)
  }
  def getName(id: Int): String = id2Name(id)
  def getId(name: String): Int = name2Id(name)
  def getArtificialNominalFor(baseUid: Int, role: Int, concept: Int, number: Int): ArtificialIndividual = {
   // Continuing the use of numbers from the last originalIndividual id ensures that artificial individuals are bigger.
   // The order of creation also ensures that deeper artificial individuals are bigger than their shallower fragments
    ArtificialIndividual(artificialIndividualIndex.getOrElseUpdate((baseUid,role,concept,number),{ val i = nextIndividualId; nextIndividualId += 1; i }))
  }

}

