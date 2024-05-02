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

import com.sequoiareasoner.arrayops.cmap
import Term._
import com.sequoiareasoner.kernel.owl.iri.IRI


/** This trait does not correspond to substitutions in the usual sense, but to restricted mappings between terms.
  * Therefore, some terms may not be present in the domain of a substitution. Moreover, we can map constants to variables
  */
sealed trait Substitution {
  self =>
//  def add(i: Term, o: Term): Boolean
  /** Apply this substitution to a term, or throws an exception if `v` is not in the domain of the substitution. */
  def apply(v: Term): Term
  /** Apply the subsitution to an array of literals*/
  final def apply(in: Array[Literal]): Array[Literal] = cmap (in) { _.applySubstitution(self) }
}





/** Forward-context mapping */

/** Given a term `fx` or `o`, this class provides the term-to-term mapping {`o` or `fx` -> x, x -> y}.*/
/** If called from a nominal context with core `a`, we change x->y for x->a*/
final class ForwardsInterContextMapping(t: Term, nominalCore: Option[Int]) extends Substitution {
    /** Sanity check */
  t match {
    case FunctionalTerm(_) | _: Constant =>
    case _ => throw new IllegalArgumentException(s"$t is neither a function symbol nor an individual")
  }
  override def apply(v: Term): Term = {
    v match {
      case _ if v == t => x
      case CentralVariable => if (nominalCore.isDefined) Term(IRI.nominalConceptUid2NominalIriStringName(nominalCore.get)).asInstanceOf[Constant] else y
      case v: Constant => v
      case PredVariable | FunctionalTerm(_) => throw new IllegalArgumentException(s"Substitution $toString should not be applied to clauses with variable `y` or non-variable symbols other than `$t`")
      case _ => throw new IllegalArgumentException(s"Unexpected type: $v is not a context term.")
    }
  }
  //TODO: update this with case nominalCore = true.
  override def toString: String = s"{$t -> $x, $x -> $y}"
}



/** Backward-context mapping */

/** Given a term `fx` or `o`, this class provides the substitution {x -> `fx` or `o`, y -> x}. */
/** If called FROM a nominal context with core concetFor:a, we replace x by a.  */
final class BackwardsInterContextSubstitution(t: Term, nominalCore: Option[Int]) extends Substitution {
  t match {
    case FunctionalTerm(_) | _: Constant =>
    case _ => throw new IllegalArgumentException(s"$t is neither a function symbol nor an Constant")
  }
  val nomi: Option[Constant] = nominalCore.map{x => Term(IRI.nominalConceptUid2NominalIriStringName(x)).asInstanceOf[Constant]}
//  override def add(i: Term, o: Term): Boolean =
//    (i == y && o == x) || (i == x && o == t)
  override def apply(v: Term): Term =
    v match {
      case PredVariable => x
      case CentralVariable => t
        /** A constant a in the context with core conceptFora will become x */
      case v: Constant => if (nominalCore.isEmpty) v; else if (nomi.exists{ x => x.id == v.id}) CentralVariable; else v
      case FunctionalTerm(_) => throw new IllegalArgumentException(s"Substitution $toString should not be applied to clauses with function symbols.")
      case _ => throw new IllegalArgumentException(s"Unexpected type: $v is not a context term.")
    }
  override def toString: String = s"{$x -> $t, $y -> $x}"
}



/** Central substitution */

/** This class provides a substitution that maps x to itself */

final class CentralSubstitution (s: scala.collection.mutable.Map[Term,Term]) extends Substitution {
   def extend(input: Term, output: Term): CentralSubstitution = {
     input match {
      case CentralVariable | FunctionalTerm(_)  => return this
      case _ =>
     }
     new CentralSubstitution(s + (input -> output))
   }
  /** Apply this substitution to a term. (Note that x and f(x) will always map to x and f(x), respectively.)
    * Throws a [[NoSuchElementException]] is the term is not in the domain of the substitution. */
  override def apply(v: Term): Term = {
    v match {
      case CentralVariable | FunctionalTerm(_) => v
      case v: Constant => v
      case _ => s(v)
    }
  }
  /** Extends the substitution if it is possible, and returns whether such extension was successful. */
  def addIfPossible(input: Term, output: Term): Boolean = {
    if (s.get(input).contains(output)) true
    else if (s.get(input).isDefined) false
    else { s += ((input,output)) ; true}
  }
  override def toString: String = if (s.isEmpty) s"{$x -> $x}" else s"{$x -> $x, ${s mkString ", "}}"
}



/** Swap mapping */

/** A substitution to swap the variables `x` and `t`. */
final class VariableSwapSubstitution(t: Term) extends Substitution {
  t match {
    case _: Variable =>
    case _ => throw new IllegalArgumentException(s"$t is not a variable")
  }
//  override def add(i: Term, o: Term): Boolean =
//    (i == x && o == v) || (i == v && o == x)
  override def apply(v: Term): Term = {
    v match {
      case CentralVariable => t
      case _ if v == t  => x
   //   case FunctionalTerm(_) if t == CentralVariable => v
      case _ => throw new IllegalArgumentException(s"Substitution $toString should not be applied to clauses with terms other than variables $x and $t")
    }
  }
  override def toString: String = s"{$x -> $t, $t -> $x}"
}



/** Term mapping */

/** Given a term `t`, this class provides the substitution {`x` -> `t`}. */
final class TermSubstitution(t: Term) extends Substitution {
//  override def add(i: Term, o: Term): Boolean = i == x && o == t
  override def apply(v: Term): Term =
    v match {
      case CentralVariable => t
      case _ => throw new IllegalArgumentException(s"Substitution $toString should not be applied to clauses with terms other than $x")
    }
  override def toString: String = s"{$x -> $t}"
}


/** Nominal Context abstraction */

/** Given a term `t` and a nominal `a`, this class provides the substitution `a`->`x` and `t` -> `t` for any other term */
final class NominalAbstractionSubstitution(nominal: Constant) extends Substitution {
  override def apply(v: Term): Term =
    v match {
      case o: Constant => if (o.id == nominal.id) CentralVariable else o
      case _ => v
    }
  override def toString: String = s"{$nominal -> $x}"
}



/** Identity mapping */

final class IdentitySubstitution extends Substitution {

// override def add(i:Term, o: Term): Boolean = false
 override def apply(v: Term): Term = v
 override def toString: String = s"{}"
}
