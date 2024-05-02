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

package com.sequoiareasoner.kernel.structural

import com.sequoiareasoner.kernel.clauses._
import com.sequoiareasoner.kernel.owl.iri.IRI

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/** Class to convert [[STClause]] clauses to [[OntologyClause]] ontology clauses. */
class STClauseToOntologyClauseTransformer(implicit dlOntology: DLOntology) {

  import Term._
  private[this] val intern = new mutable.AnyRefMap[(Set[Predicate], Boolean), IRI]
  private[this] val z1 = z(1)
  private[this] val sigma = new VariableSwapSubstitution(z1)
  private[this] def predicateSubstitution(sigma: Substitution)(l: Predicate): Predicate = l applySubstitution sigma

  /** This method takes a conjunction of predicates appearing in some clause body which all contain v,
    * where v is some neighbour variable of the form zi, and a boolean flag determining whether this
    * variable appears in the head of the original clause. It generates two things: a predicate that will replace the
    * conjunction in the original clause (a role if v appears in the head of the original clause, a concept otherwise),
    * and a new auxiliary clause that can generate this auxiliary predicate from a suitable body (which consists in
    * swapping variables x and v in the original conjunction, so v does not appear in any predicate of the form C(v)) */
  private[this] def getAuxiliary(conjunction: Seq[Predicate], useRole: Boolean, v: NeighbourVariable): (Predicate, OntologyClause) = {
    /** First, map the variable v to the variable z1 used for all auxiliary clauses so the lookup works. */
    val standardize = new CentralSubstitution(scala.collection.mutable.Map(v -> z1))
    /** Second, apply this substitution to the conjunction. */
    val standardizedConjunction = conjunction map predicateSubstitution(standardize)
    val standardizedConjunctionSet = standardizedConjunction.toSet
    /** Get the auxiliary elements using the cache or creating a new predicate and updating the cache */
    intern.get((standardizedConjunctionSet, useRole)) match {
      case Some(auxIri) =>
        val predicate = if (useRole) Role(auxIri, x, v) else Concept(auxIri, x)
        (predicate, null)
      case None =>
        val auxIri: IRI = intern.getOrElseUpdate((standardizedConjunctionSet, useRole), IRI.all())
        val predicate = if (useRole) Role(auxIri, x, v) else Concept(auxIri, x)
        val clause = OntologyClause(standardizedConjunction map predicateSubstitution(sigma), Seq(if (useRole) Role(auxIri, z1, x) else Concept(auxIri, z1)))
        (predicate, clause)
    }
  }

  /** Analogous to the case above, but converts a predicate R(z_i,z_i) into C(z_i) and clause C(x) -> R(x,x). Uses
    * the IRIs for universal restriction filler since this happens when a HasSelf is such filler. */
  private[this] def getAuxiliary2(predicate: Predicate, v: NeighbourVariable): (Predicate, OntologyClause) = {
    /** First, map the variable v to the variable z1 used for all auxiliary clauses so the lookup works. */
    val standardize = new CentralSubstitution(scala.collection.mutable.Map(v -> CentralVariable))
    /** Second, apply this substitution to the conjunction. */
    val standardizedPredicate = predicateSubstitution(standardize)(predicate)
    val standardizedPredicateSet = Set(standardizedPredicate)
    /** Get the auxiliary elements using the cache or creating a new predicate and updating the cache */
    intern.get((standardizedPredicateSet, false)) match {
      case Some(auxIri) => (Concept(auxIri,v), null)
      case None =>
        val auxIri: IRI = intern.getOrElseUpdate((standardizedPredicateSet, false), IRI.all())
        val newConcept = Concept(auxIri, v)
        val clause = OntologyClause(Seq(Concept(auxIri, CentralVariable)), Seq(standardizedPredicate))
        (newConcept, clause)
    }
  }

  /** Transforms a clause that results from structural transformation into a collection of clauses that satisfy the
    * additional restrictions of ontology clauses.  */
  def transform(c: STClause): Seq[OntologyClause] = {
    /** If there are no body clauses of the form C(z), then there is no need to do any transformation */
    /** BUG!! This is no longer true with reflexivity! Added below a quick fix with transform 2 */
    if (c.body forall {
      case Concept(_, CentralVariable) => true
      case Concept(_, _: NeighbourVariable) => false
      case _ => true
    }) return Seq(OntologyClause(c.body, c.head)) // The new nominal clauses verify this, so there is no need to add further transformation.
    /** Collect variables zi that appear in literals of the form C(zi) in the body */
    val conceptNeighbourVars: Set[Term] = c.body.collect {
      case Concept(_, v: NeighbourVariable)  => v
    }.toSet
    /** Collect the conjunction of predicates in the body that contain zi, for each such variable detected above */
    val conjunctionsToHoist: Map[Term, Seq[Predicate]] = c.body.groupBy {
      case Concept(_, v) => v
      case Role(_, CentralVariable, v) => if (conceptNeighbourVars contains v) v else CentralVariable
      case Role(_, v, CentralVariable) => if (conceptNeighbourVars contains v) v else CentralVariable
      case _ => throw new AssertionError(s"Illegal clause $c generated during clausification.")
    }
    /** (Auxiliary method) */
    @inline def occursInHead(v: Term): Boolean = c.head.exists {
      case Concept(_, t) => t == v
      case Role(_, s, t) => s == v || t == v
      case Equality(s, t) => s == v || t == v
      case Inequality(s, t) => s == v || t == v
    }
    val predicates = new ArrayBuffer[Predicate]
    val clauses = new ArrayBuffer[OntologyClause]
    /** For each zi, generate the corresponding auxiliary clause, and predicate to replace the conjunction in the original clause */
    for ((v, conjunction) <- conjunctionsToHoist) { v match {
      case CentralVariable =>
      case v : NeighbourVariable =>
        val (p, clause) = getAuxiliary(conjunction, occursInHead(v), v)
        predicates += p
        if (clause ne null) clauses += clause
      }}
    Seq(OntologyClause(predicates ++ conjunctionsToHoist.getOrElse(x, Nil), c.head)) ++ clauses
  }

  /** This one transforms clauses with R(z,z) in the head */
  def transform2(c: OntologyClause): Seq[OntologyClause] = {
    val clauses = new ArrayBuffer[OntologyClause]
    val newHead = c.head.map{
      case lit@Role(_, v: NeighbourVariable, _: NeighbourVariable) => {
        val (p, clause) = getAuxiliary2(lit, v)
        if (clause ne null) clauses += clause
        p
      }
      case lit@_ => lit
    }
    Seq(OntologyClause(c.body,newHead)) ++ clauses
  }


  /** Transforms a collection of clauses that result from structural transformation into a collection of clauses that
    * satisfy the additional restrictions of ontology clauses. */
  def transform(cs: Iterable[STClause]): Iterable[OntologyClause] = {cs flatMap transform} flatMap transform2

}
