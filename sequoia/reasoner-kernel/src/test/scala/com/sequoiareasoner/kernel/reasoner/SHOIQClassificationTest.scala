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

package com.sequoiareasoner.kernel.reasoner

import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.owl.model._
import com.sequoiareasoner.kernel.owl.model
import com.sequoiareasoner.kernel.{CommonNames, OWLAxiomBuilder}
import org.scalatest.{FunSuite, RandomTestOrder}
import sun.awt.geom.AreaOp.SubOp

/** Tests to check that the computed taxonomy is both correct and complete for SHOIQ ontologies.
  *
  * Some test cases are adapted from the HermiT reasoner.
  *
  */


//class SHOIQClassificationTest extends FunSuite with RandomTestOrder {
class SHOIQClassificationTest extends FunSuite  {
  import ClassificationTestUtils._
  import CommonNames._
  import OWLAxiomBuilder._

  /** --------------------- AUXILIARY METHODS ------------------------ */

  def taxonomyContains(input: Set[_ <: Axiom],expected: Set[_ <: Axiom]) = {
    computeTaxonomy(input) match {
      case None =>
        fail("Ontology found to be inconsistent")
      case Some(actual) =>
        assert(expected.forall{subsumption => isContainedModuloEquivalences(subsumption,actual)}, "Computed taxonomy does not contain known subsumption.")
    }
  }
  def taxonomyEquals(input: Set[_ <: Axiom],expected: Set[_ <: Axiom]) = {
    computeTaxonomy(input) match {
      case None =>
        fail("Ontology found to be inconsistent")
      case Some(actual) =>
        assert(decorate(expected) === decorate(actual), "Computed taxonomy does not contain known subsumption.")
    }
  }
  def consistency(input: Set[_ <: Axiom]) = {
    computeTaxonomy(input) match {
      case None =>
        fail("Ontology found to be inconsistent")
      case Some(_) =>
        assert(true)
    }
  }
 def inconsistency(input: Set[_ <: Axiom]) = {
    computeTaxonomy(input) match {
      case None =>
        assert(true)
      case Some(_) =>
        fail("Ontology found to be consistent")
    }
  }

 def mandanga: Unit = {
   Thread.sleep(100000)
 }


  /** --------------------- TESTS ----------------------------- */

  test( "testReflexiveAndSameAs [from HermiT]") {
    val input = Set(
     EquivalentClassesAxiom(ObjectOneOf(Set(a)),A),
     EquivalentClassesAxiom(ObjectOneOf(Set(b)),B),
     ReflexiveObjectPropertyAxiom(R),
     ObjectPropertyAssertionAxiom(R,a,b),
     SameIndividualAxiom(Set(a,b))
    )
    val expected = Set(
      EquivalentClassesAxiom(A , B)
    )
    taxonomyContains(input,expected)
  }

  test( "testEquivalentClassInstances [from HermiT]") {
    val Car = OWLClass(IRI(p,"Car"))
    val Automobile = OWLClass(IRI(p,"Automobile"))
    val car = NamedIndividual(IRI(p,"car"))
    val auto = NamedIndividual(IRI(p,"auto"))
    val input = Set(
      EquivalentClassesAxiom(A,ObjectOneOf(Set(car))),
      EquivalentClassesAxiom(B,ObjectOneOf(Set(auto))),
      EquivalentClassesAxiom(Car,Automobile),
      ClassAssertionAxiom(Car,car),
      ClassAssertionAxiom(Automobile,auto),
    )
    val expected = Set(
      SubClassOfAxiom(A,Automobile),
      SubClassOfAxiom(B,Car)
    )
    taxonomyContains(input,expected)
  }

  test ("testNegativeObjectPropertyAssertionWithNonSimple [from HermiT]") {
    val input = Set(
      SubClassOfAxiom(A, ObjectSomeValuesFrom(T, ObjectSomeValuesFrom(T, ObjectOneOf(Set(b))))),
      TransitiveObjectPropertyAxiom(T),
      SubObjectPropertyOfAxiom(T, ObjectInverseOf(R)),
      ClassAssertionAxiom(A, a),
      NegativeObjectPropertyAssertionAxiom(R, b, a)
    )
    inconsistency(input)
  }

  test("testSameAs [from HermiT]")  {
    val input = Set(
      ClassAssertionAxiom(A, a1),
      SameIndividualAxiom(Set(a1,a2)),
      EquivalentClassesAxiom(A2,ObjectOneOf(Set(a2)))
    )
    val expected = Set(
      SubClassOfAxiom(A2,A)
    )
    taxonomyContains(input,expected)
  }

  test( "textIndividualRetrievalBug [from HermiT]") {
    val input = Set(
      EquivalentClassesAxiom(D,ObjectSomeValuesFrom(R,ObjectOneOf(Set(d)))),
      EquivalentClassesAxiom(C,ObjectOneOf(Set(c))),
      ClassAssertionAxiom(A,d),
      ObjectPropertyAssertionAxiom(R,c,d),
    )
    val expected = Set(
      SubClassOfAxiom(C,D)
    )
    taxonomyContains(input,expected)
  }

 test( "testIndividualRetrieval [from HermiT]") {
   val input = Set(
     FunctionalObjectPropertyAxiom(S),
     SameIndividualAxiom(Set(a,b)),
     ObjectPropertyAssertionAxiom(S,a,c),
     ObjectPropertyAssertionAxiom(S,a,d),
     SubClassOfAxiom(D,C),
     SubClassOfAxiom(E,C),
     ClassAssertionAxiom(E,b),
     ClassAssertionAxiom(C,c),
     ClassAssertionAxiom(ObjectUnionOf(F,D),e),
     EquivalentClassesAxiom(C1,ObjectSomeValuesFrom(S,ObjectOneOf(Set(c)))),
     EquivalentClassesAxiom(D1,ObjectSomeValuesFrom(S,ObjectOneOf(Set(d)))),
     EquivalentClassesAxiom(A1,ObjectOneOf(Set(a))),
     EquivalentClassesAxiom(B1,ObjectOneOf(Set(b))),
   )
   val expected = Set(
     SubClassOfAxiom(A1,C1),
     SubClassOfAxiom(A1,D1),
     SubClassOfAxiom(B1,C1),
     SubClassOfAxiom(B1,D1)
   )
   taxonomyContains(input,expected)
 }


  test ("testReflexivity [from HermiT]") {
    val input = Set(
      ReflexiveObjectPropertyAxiom(R),
      ClassAssertionAxiom(ObjectAllValuesFrom(R,Nothing),a),
      ClassAssertionAxiom(Thing,a)
    )
    inconsistency(input)
  }

  test ("testNegProperties [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R,a,b),
      ObjectPropertyAssertionAxiom(R,b,c),
      TransitiveObjectPropertyAxiom(R),
      NegativeObjectPropertyAssertionAxiom(R,a,a)
    )
    inconsistency(input)
  }

  test("testIrreflexivity [from HermiT]") {
    val input = Set(
      IrreflexiveObjectPropertyAxiom(R),
      ObjectPropertyAssertionAxiom(R,a,a)
    )
    inconsistency(input)
  }


  test( "testRoleDisjointness_1 [from HermiT]") {
    val input = Set(
      DisjointObjectPropertiesAxiom(List(R,S)),
      ObjectPropertyAssertionAxiom(R,a,b),
      ObjectPropertyAssertionAxiom(S,a,b)
    )
    inconsistency(input)
  }

  test("testRoleDisjointness2 [from HermiT]") {
    val input = Set(
      DisjointObjectPropertiesAxiom(List(R,S)),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R, Thing), a),
      ClassAssertionAxiom(ObjectSomeValuesFrom(S, Thing), a),
      ClassAssertionAxiom(C,a),
      SubClassOfAxiom(C, ObjectMaxCardinality(1,T)),
      SubObjectPropertyOfAxiom(R,T),
      SubObjectPropertyOfAxiom(S,T)
    )
    inconsistency(input)
  }

  test( "testExistsSelf1 [from HermiT]") {
    val input = Set(
      ClassAssertionAxiom(ObjectAllValuesFrom(R,Nothing),a),
      ClassAssertionAxiom(ObjectHasSelf(R),a)
    )
    inconsistency(input)
  }

  test( "textExistsSelf2 [from HermiT]") {
    val input = Set(
      SubClassOfAxiom(B1, ObjectSomeValuesFrom(R, C2)),
      SubClassOfAxiom(C2, ObjectSomeValuesFrom(R, B2)),
      SubClassOfAxiom(B2, ObjectSomeValuesFrom(R, C1)),
      SubClassOfAxiom(C1, ObjectSomeValuesFrom(R, B1)),
      ClassAssertionAxiom(C1,a),
      ClassAssertionAxiom(ObjectAllValuesFrom(R,ObjectHasSelf(R)),a)
    )
    consistency(input)
  }

  test( "testAsymmetry [from HermiT]") {
    val input = Set(
      AsymmetricObjectPropertyAxiom(S),
      SubObjectPropertyOfAxiom(R,S),
      ObjectPropertyAssertionAxiom(S,b,a),
      ObjectPropertyAssertionAxiom(R,a,b)
    )
    inconsistency(input)
  }

  test( "testSatisfiability1 [from HermiT]") {
    val input = Set(
      ClassAssertionAxiom(C,a),
      ClassAssertionAxiom(ObjectComplementOf(C),a),
    )
    inconsistency(input)
  }

 test( "testSatisfiability2 [from HermiT]") {
   val input = Set(
     SubClassOfAxiom(Thing, C),
     SubClassOfAxiom(Thing, ObjectComplementOf(C))
   )
   inconsistency(input)
 }

  test("testSatisfiability3 [from HermiT]") {
    val Person = OWLClass(IRI(p, "Person"))
    val hasParent = ObjectProperty(IRI(p, "hasParent"))
    val Grandchild = OWLClass(IRI(p, "Grandchild"))
    val peter = NamedIndividual(IRI(p,"peter"))
    val input = Set(
      SubClassOfAxiom( Person, ObjectSomeValuesFrom( hasParent, Person)),
      SubClassOfAxiom(ObjectSomeValuesFrom(hasParent, ObjectSomeValuesFrom(hasParent, Person)),Grandchild),
      ClassAssertionAxiom(Person,peter),
      ClassAssertionAxiom(ObjectComplementOf(Grandchild), peter)
    )
    inconsistency(input)
  }

  test ("testSatisfiability4 [from HermiT]") {
    val input = Set(
      FunctionalObjectPropertyAxiom(R),
      ObjectPropertyAssertionAxiom(R,a,b),
      SubClassOfAxiom(Thing, ObjectSomeValuesFrom(R,C)),
      ClassAssertionAxiom(ObjectComplementOf(C),b)
    )
    inconsistency(input)
  }

  test ("testNominals1 [from HermiT]") {
    val input = Set(
      ClassAssertionAxiom(A,a),
      ClassAssertionAxiom(A,b),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(R,A)),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n))))
    )
    consistency(input)
  }

  test( "testNominals2 [from HermiT]") {
    val input = Set(
      ClassAssertionAxiom(A,a),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(R,A)),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      ClassAssertionAxiom(B,b),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(R,B)),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      DisjointClassesAxiom(A,B),
      ClassAssertionAxiom(ObjectMaxCardinality(5, ObjectInverseOf(S)), n)
    )
    consistency(input)
  }

  test ("testNominals2.5") {
    val input = Set(
      ClassAssertionAxiom(A,a),
      ClassAssertionAxiom(B,b),
      SubClassOfAxiom(A, ObjectHasValue(S,n)),
      SubClassOfAxiom(B, ObjectHasValue(S,n)),
      SubObjectPropertyOfAxiom(S,ObjectInverseOf(invS)),
      ClassAssertionAxiom(ObjectMaxCardinality(1, invS), n),
      SubClassOfAxiom(ObjectSomeValuesFrom(invS,ObjectIntersectionOf(A,B)),desc),
      EquivalentClassesAxiom(N,ObjectOneOf(Set(n)))
    )
    val expected = Set(
      SubClassOfAxiom(N,desc)
    )
    taxonomyContains(input,expected)
  }


  // We ignore it for the moment, as this has to do with the Nom rule, which is quite irrelevant to the evaluation.
  ignore("testNominals3 [from HermiT]") {
    val input = Set(
      SubClassOfAxiom(A, ObjectSomeValuesFrom(R,A)),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R,A),a),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(R,B)),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R,B), b),
      EquivalentObjectPropertiesAxiom(Set(ObjectInverseOf(S),invS)),
      ClassAssertionAxiom(ObjectMaxCardinality(1, invS), n),
      //EquivalentClassesAxiom(desc,ObjectSomeValuesFrom(invS,ObjectIntersectionOf(A,B,ObjectSomeValuesFrom(R,ObjectIntersectionOf(A,B))))),
      EquivalentClassesAxiom(desc,ObjectSomeValuesFrom(invS,ObjectIntersectionOf(A,B))),
      EquivalentClassesAxiom(N,ObjectOneOf(Set(n)))
    )
    val expected = Set(
      EquivalentClassesAxiom(N,desc)
    )
    taxonomyContains(input,expected)
  }


  // MAY FAIL due to bug in OWL API, apparently
  ignore("testNominals4 [from HermiT]") {
    val input = Set (
      DisjointClassesAxiom(A,B),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(R,A)),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R, A), a),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(R, B)),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R,B), b),
      ClassAssertionAxiom(ObjectMaxCardinality(2, ObjectInverseOf(S)),n),
      EquivalentClassesAxiom(descA,ObjectSomeValuesFrom(ObjectInverseOf(S),ObjectIntersectionOf(A,ObjectSomeValuesFrom(R,A)))),
      EquivalentClassesAxiom(descB,ObjectSomeValuesFrom(ObjectInverseOf(S),ObjectIntersectionOf(B,ObjectSomeValuesFrom(R,B)))),
      EquivalentClassesAxiom(N,ObjectOneOf(Set(n)))
    )
    val expected = Set(
      SubClassOfAxiom(N,descA),
      SubClassOfAxiom(N,descB)
    )
    taxonomyContains(input,expected)
  }

 //MAY FAIL DUE TO BUG IN OWL API
  ignore ( "testNominals5 [from HermiT]")  {
    val input = Set(
      DisjointClassesAxiom(A,B),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(R,A)),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R, A), a),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(R, B)),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R,B), b),
      ClassAssertionAxiom(ObjectMaxCardinality(2, ObjectInverseOf(S)),n),
      EquivalentClassesAxiom(desc,ObjectMinCardinality(2, ObjectInverseOf(S), ObjectUnionOf(A,B))),
      EquivalentClassesAxiom(N,ObjectOneOf(Set(n)))
    )
    val expected = Set(
      EquivalentClassesAxiom(N,desc)
    )
    taxonomyContains(input,expected)
  }


  //MAY FAIL DUE TO BUG IN OWL API
  ignore("testNominals6 [from HermiT]") {
    val input = Set(
      DisjointClassesAxiom(A,B),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(R,A)),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R, A), a),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(R, B)),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(S, ObjectOneOf(Set(n)))),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R,B), b),
      ClassAssertionAxiom(ObjectMaxCardinality(2, ObjectInverseOf(S)),n),
      EquivalentClassesAxiom(descA,ObjectMinCardinality(1, ObjectInverseOf(S), ObjectComplementOf(A))),
      EquivalentClassesAxiom(ObjectComplementOf(descB),ObjectMinCardinality(2, ObjectInverseOf(S), ObjectComplementOf(A))),
      EquivalentClassesAxiom(N,ObjectOneOf(Set(n)))
    )
    val expected = Set(
      SubClassOfAxiom(N,descA),
      SubClassOfAxiom(N,descB)
    )
    taxonomyContains(input,expected)
  }

  test( "testNovelNominals [from HermiT]") {
    val input = Set(
       ClassAssertionAxiom(C,a),
      EquivalentClassesAxiom(desc,ObjectIntersectionOf(ObjectOneOf(Set(a)),ObjectComplementOf(C)))
    )
    val expected = Set(
      EquivalentClassesAxiom(desc,Nothing)
    )
    taxonomyContains(input,expected)
  }

  test( "testNominalMerging [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(S,a,a),
      ClassAssertionAxiom(ObjectSomeValuesFrom(R,B),a),
      SubClassOfAxiom(B, ObjectSomeValuesFrom(R,C)),
      SubClassOfAxiom(C, ObjectSomeValuesFrom(S,D)),
      SubClassOfAxiom(D, ObjectOneOf(Set(a))),
      InverseFunctionalObjectPropertyAxiom(S)
    )
    consistency(input)
  }

  // Ignore for the moment as it involves Nom
  ignore ("testNIRuleBlockingWithUnraveling [from HermiT]") {
   val input = Set(
     ClassAssertionAxiom(A,a),
     ClassAssertionAxiom(ObjectSomeValuesFrom(R,B),a),
     SubClassOfAxiom(ObjectSomeValuesFrom(R,A), Nothing),
     SubClassOfAxiom(B, ObjectSomeValuesFrom(R,B)),
     SubClassOfAxiom(B, ObjectHasValue(S,a)),
     InverseFunctionalObjectPropertyAxiom(R),
     InverseObjectPropertiesAxiom(S, invS),
     SubClassOfAxiom(Thing,ObjectMaxCardinality(3, invS, Thing))
   )
   inconsistency(input)
  }

  test ("testSatisfiabilityWithRIAs1 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R1,a,b),
      ObjectPropertyAssertionAxiom(R1,b,c),
      ObjectPropertyAssertionAxiom(R2,c,d),
      ObjectPropertyAssertionAxiom(R2,d,e),
      ObjectPropertyAssertionAxiom(R3,e,g),
      SubObjectPropertyOfAxiom(R1, S),
      SubObjectPropertyOfAxiom(R2, S),
      SubObjectPropertyOfAxiom(S,R),
      ClassAssertionAxiom(ObjectAllValuesFrom(R,C), g),
      ClassAssertionAxiom(ObjectComplementOf(C), a),
      TransitiveObjectPropertyAxiom(R1),
      TransitiveObjectPropertyAxiom(R2),
      TransitiveObjectPropertyAxiom(S),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(S, R3), ObjectInverseOf(R))
    )
    inconsistency(input)
  }

  test ("testSatisfiabilityWithRIAs2 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R1, a, b),
      ObjectPropertyAssertionAxiom(T3, b, c),
      ObjectPropertyAssertionAxiom(T2, c, d),
      ObjectPropertyAssertionAxiom(T1, d, e),
      ObjectPropertyAssertionAxiom(R2, e, g),
      InverseObjectPropertiesAxiom(S, T),
      InverseObjectPropertiesAxiom(S1, T1),
      InverseObjectPropertiesAxiom(S2, T2),
      InverseObjectPropertiesAxiom(S3, T3),
      ClassAssertionAxiom(ObjectComplementOf(C), a),
      ClassAssertionAxiom(ObjectAllValuesFrom(R, C), g),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(S1, S2, S3), S),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(R1, T, R2), ObjectInverseOf(R))
    )
    inconsistency(input)
  }

  test ("testSatisfiabilityWithRIAs3 [from HermiT]") {
     val input = Set(
       ObjectPropertyAssertionAxiom(R1,a,b),
       ObjectPropertyAssertionAxiom(R2,b,c),
       InverseObjectPropertiesAxiom(R,invR),
       ClassAssertionAxiom(ObjectComplementOf(C),a),
       ClassAssertionAxiom(ObjectAllValuesFrom(R, C),c),
       SubObjectPropertyOfAxiom(ObjectPropertyChain(R1, R2), invR),
       SubObjectPropertyOfAxiom(ObjectPropertyChain(R3,R4), R)
     )
     inconsistency(input)
  }

  test("testSatisfiabilityWithRIAs4 [from HermiT]") {
    val input = Set(
      SubObjectPropertyOfAxiom(ObjectPropertyChain(R2, R3), R),
      EquivalentObjectPropertiesAxiom(Set(R, R2)),
      EquivalentObjectPropertiesAxiom(Set(R,R3)),
      ObjectPropertyAssertionAxiom(R2,a,b),
      ObjectPropertyAssertionAxiom(R3,b,c),
      ClassAssertionAxiom(ObjectComplementOf(C),c),
      ClassAssertionAxiom(ObjectAllValuesFrom(R,C),a)
    )
    inconsistency(input)
  }

  test("testSatisfiabilityWithRIAs5 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R1,a,b),
      ObjectPropertyAssertionAxiom(R2,b,c),
      ClassAssertionAxiom(ObjectComplementOf(C), a),
      ClassAssertionAxiom(ObjectAllValuesFrom(ObjectInverseOf(R), C), c),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(R1, R2), R)
    )
    inconsistency(input)
  }

  test("testSatisfiabilityWithRIAs6 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R1,a,b),
      ObjectPropertyAssertionAxiom(R2,b,c),
      ClassAssertionAxiom(ObjectComplementOf(C),a),
      ClassAssertionAxiom(ObjectAllValuesFrom(R,C),c),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(R1,R2), ObjectInverseOf(R))
    )
    inconsistency(input)
  }

  test("testSatisfiabilityWithRIAs7 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R1,a,b),
      ObjectPropertyAssertionAxiom(R2,b,c),
      ClassAssertionAxiom(ObjectComplementOf(C),a),
      ClassAssertionAxiom(ObjectAllValuesFrom(R,C), c),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(ObjectInverseOf(R2), ObjectInverseOf(R1)), R)

    )
  }

  test("testSatisfiabilityWithRIAs8 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R1,a,b),
      ObjectPropertyAssertionAxiom(S1,b,c),
      ObjectPropertyAssertionAxiom(S2,c,d),
      ObjectPropertyAssertionAxiom(S1,d,e),
      ObjectPropertyAssertionAxiom(S2,e,g),
      TransitiveObjectPropertyAxiom(S),
      ClassAssertionAxiom(ObjectComplementOf(C),a),
      ClassAssertionAxiom(ObjectAllValuesFrom(R, C), g),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(ObjectInverseOf(S2), ObjectInverseOf(S1)), S),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(S, ObjectInverseOf(R1)), R)
    )
    inconsistency(input)
 }

  test("testSatisfiabilityWithRIAs9 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R, a, b),
      TransitiveObjectPropertyAxiom(R),
      SymmetricObjectPropertyAxiom(R),
      ClassAssertionAxiom(ObjectComplementOf(C),a),
      ClassAssertionAxiom(ObjectAllValuesFrom(R,C),a)
    )
   inconsistency(input)
  }

 test("testSatisfiabilityWithRIAs10 [from HermiT]") {
   val input = Set(
     ObjectPropertyAssertionAxiom(R1,a,b),
     ObjectPropertyAssertionAxiom(R2,b,c),
     ObjectPropertyAssertionAxiom(R1,c,d),
     ObjectPropertyAssertionAxiom(R2,d,e),
     SymmetricObjectPropertyAxiom(R),
     TransitiveObjectPropertyAxiom(ObjectInverseOf(R)),
     ClassAssertionAxiom(ObjectComplementOf(C),e),
     ClassAssertionAxiom(ObjectAllValuesFrom(R, C), a),
     SubObjectPropertyOfAxiom(ObjectPropertyChain(R1, R2), ObjectInverseOf(R))
   )
   inconsistency(input)
 }

  test("testSatisfiabilityWithRIAs11 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R1,a,b),
      ObjectPropertyAssertionAxiom(R2,b,c),
      ObjectPropertyAssertionAxiom(R1,c,d),
      ObjectPropertyAssertionAxiom(R2,d,e),
      SymmetricObjectPropertyAxiom(R),
      TransitiveObjectPropertyAxiom(R),
      ClassAssertionAxiom(ObjectComplementOf(C),e),
      ClassAssertionAxiom(ObjectAllValuesFrom(ObjectInverseOf(R), C), a),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(R1, R2), R)
    )
    inconsistency(input)
  }

  test("testSatisfiabilituWithRIAs11b [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R1,a,b),
      ObjectPropertyAssertionAxiom(R2,b,c),
      ObjectPropertyAssertionAxiom(R1,c,d),
      ObjectPropertyAssertionAxiom(R2,d,e),
      SymmetricObjectPropertyAxiom(ObjectInverseOf(R)),
      TransitiveObjectPropertyAxiom(ObjectInverseOf(R)),
      ClassAssertionAxiom(ObjectComplementOf(C),a),
      ClassAssertionAxiom(ObjectAllValuesFrom(R, C), e),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(R1, R2), R)
    )
    inconsistency(input)
  }

  test("testSatisfiabilityWithRIAs12 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R1,a,b),
      ObjectPropertyAssertionAxiom(R2,b,c),
      ObjectPropertyAssertionAxiom(R1,c,d),
      ObjectPropertyAssertionAxiom(R2,d,e),
      TransitiveObjectPropertyAxiom(R),
      ClassAssertionAxiom(ObjectComplementOf(C), e),
      ClassAssertionAxiom(ObjectAllValuesFrom(ObjectInverseOf(R),C),a),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(R1, R2), ObjectInverseOf(R))
    )
    inconsistency(input)
  }

  test( "testSatisfiabilityWithRIAs13 [from HermiT]") {
    val input = Set(
      ObjectPropertyAssertionAxiom(R2, b, a),
      ObjectPropertyAssertionAxiom(P1,b,c),
      ObjectPropertyAssertionAxiom(P2,c,d),
      InverseObjectPropertiesAxiom(R1, S),
      ClassAssertionAxiom(ObjectComplementOf(C),a),
      ClassAssertionAxiom(ObjectAllValuesFrom(R, C), d),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(P1, P2), S),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(T, T ), R1),
      SubObjectPropertyOfAxiom(ObjectPropertyChain(R1,R2), R)
    )
    inconsistency(input)
  }

  test( "testELHOCalculus [from the Practical Reasoning with Nominals... paper]" ) {
    val input = Set(
      SubClassOfAxiom(A, ObjectSomeValuesFrom(R,ObjectIntersectionOf(B, ObjectOneOf(Set(o))))),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(S,ObjectOneOf(Set(o)))),
      SubClassOfAxiom(ObjectSomeValuesFrom(S,B), B)
    )
    val expected = Set(
      SubClassOfAxiom(A,B)
    )
    taxonomyContains(input,expected)
  }

  test( "testELHOCalculus2 [from the Practical Reasoning with Nominals... paper]" ) {
    val input = Set(
      SubClassOfAxiom(A, ObjectSomeValuesFrom(R,ObjectIntersectionOf(B, ObjectOneOf(Set(o))))),
      SubClassOfAxiom(A, ObjectSomeValuesFrom(S,ObjectOneOf(Set(o)))),
      SubClassOfAxiom(ObjectSomeValuesFrom(S,B), B),
      SubClassOfAxiom(C,ObjectSomeValuesFrom(R,A))
    )
    val expected = Set(
      SubClassOfAxiom(A,B)
    )
    taxonomyContains(input,expected)
  }

 test ("testDavidOriginal")  {
     val input = Set(
     SubClassOfAxiom(A,ObjectSomeValuesFrom(R,D)),
     SubClassOfAxiom(D,ObjectSomeValuesFrom(R,B1)),
     SubClassOfAxiom(A,ObjectSomeValuesFrom(R,B2)),
     SubClassOfAxiom(ObjectSomeValuesFrom(R, C),F),
     SubClassOfAxiom(ObjectSomeValuesFrom(R, F),F),
     SubClassOfAxiom(ObjectIntersectionOf(B1,B2),C),
     SubClassOfAxiom(ObjectIntersectionOf(B1,B3),C),
     SubClassOfAxiom(ObjectIntersectionOf(B2,B3),C),
     SubClassOfAxiom(B1,ObjectOneOf(Set(o1,o2))),
     SubClassOfAxiom(B2,ObjectOneOf(Set(o1,o2))),
     SubClassOfAxiom(B3,ObjectOneOf(Set(o1,o2))),
     ClassAssertionAxiom(B3,a),
   )
   val expected = Set(
     SubClassOfAxiom(A,F)
   )
   taxonomyContains(input,expected)
 }


  test( "testDavidOriginalSimplified") {
    val input = Set(
      SubClassOfAxiom(A,ObjectSomeValuesFrom(R,D)),
      SubClassOfAxiom(D,ObjectSomeValuesFrom(R,B1)),
      SubClassOfAxiom(A,ObjectSomeValuesFrom(R,B2)),
      SubClassOfAxiom(ObjectSomeValuesFrom(R, C),F),
      SubClassOfAxiom(ObjectSomeValuesFrom(R, F),F),
      SubClassOfAxiom(ObjectIntersectionOf(B1,B2),C),
      SubClassOfAxiom(ObjectIntersectionOf(B1,B3),C),
      SubClassOfAxiom(ObjectIntersectionOf(B2,B3),C),
      SubClassOfAxiom(B1,ObjectOneOf(Set(o1))),
      SubClassOfAxiom(B2,ObjectOneOf(Set(o2))),
      SubClassOfAxiom(B3,ObjectOneOf(Set(o1,o2))),
      ClassAssertionAxiom(B3,o3),
    )
    val expected = Set(
      SubClassOfAxiom(A,F)
    )
    taxonomyContains(input,expected)
  }
// TIMES OUT
//    test( "testNikoo1simplified") {
//      val input = Set(
//        SubClassOfAxiom(A,ObjectSomeValuesFrom(R,D)),
//        SubClassOfAxiom(D,ObjectSomeValuesFrom(R,B1)),
//        SubClassOfAxiom(A,ObjectSomeValuesFrom(R,B2)),
//        SubClassOfAxiom(ObjectSomeValuesFrom(R, C),F),
//        SubClassOfAxiom(ObjectSomeValuesFrom(R, F),F),
//        SubClassOfAxiom(ObjectIntersectionOf(B1,B2),C),
//        SubClassOfAxiom(ObjectIntersectionOf(B1,B3),C),
//        SubClassOfAxiom(ObjectIntersectionOf(B2,B3),C),
//        SubClassOfAxiom(B1,ObjectOneOf(Set(o1,o2))),
//        SubClassOfAxiom(B2,ObjectOneOf(Set(o1,o2))),
//        SubClassOfAxiom(B3,ObjectOneOf(Set(o1,o2))),
//        ClassAssertionAxiom(B3,o4),
//        ClassAssertionAxiom(B3,o5),
//        SubClassOfAxiom(ObjectIntersectionOf(ObjectOneOf(Set(o4)),ObjectOneOf(Set(o5))),Nothing),
//      )
//      val expected = Set(
//        SubClassOfAxiom(A,F)
//      )
//      taxonomyContains(input,expected)
//    }


//TIMES OUT
// test( "testNikoo1") {
//    mandanga
//   val input = Set(
//     SubClassOfAxiom(A,ObjectSomeValuesFrom(R,D)),
//     SubClassOfAxiom(D,ObjectSomeValuesFrom(R,B1)),
//     SubClassOfAxiom(A,ObjectSomeValuesFrom(R,B2)),
//     SubClassOfAxiom(ObjectSomeValuesFrom(R, C),F),
//     SubClassOfAxiom(ObjectSomeValuesFrom(R, F),F),
//     SubClassOfAxiom(ObjectIntersectionOf(B1,B2),C),
//     SubClassOfAxiom(ObjectIntersectionOf(B1,B3),C),
//     SubClassOfAxiom(ObjectIntersectionOf(B2,B3),C),
//     SubClassOfAxiom(B1,ObjectOneOf(Set(o1,o2,o3))),
//     SubClassOfAxiom(B2,ObjectOneOf(Set(o1,o2,o3))),
//     SubClassOfAxiom(B3,ObjectOneOf(Set(o1,o2,o3))),
//     ClassAssertionAxiom(B3,o4),
//     ClassAssertionAxiom(B3,o5),
//     SubClassOfAxiom(ObjectIntersectionOf(ObjectOneOf(Set(o4)),ObjectOneOf(Set(o5))),Nothing),
//   )
//   val expected = Set(
//     SubClassOfAxiom(A,F)
//   )
//   taxonomyContains(input,expected)
// }

 test( "testNikoo2") {
   val input = Set(
     SubClassOfAxiom(ObjectIntersectionOf(A,ObjectOneOf(Set(o))),Nothing),
     SubClassOfAxiom(A,ObjectOneOf(Set(o))),
   )
   consistency(input)
 }

  test("testNikoo3") {
    val input = Set(
   //   SubClassOfAxiom(A,ObjectUnionOf(ObjectMinCardinality(2,S,C),X)),

      SubClassOfAxiom(A,ObjectMinCardinality(2,S,C)),
  //    SubClassOfAxiom(A,ObjectUnionOf(ObjectMaxCardinality(1,S,D),E)),
      SubClassOfAxiom(A,ObjectMaxCardinality(1,S,D)),
//      SubClassOfAxiom(X,G),
//      SubClassOfAxiom(E,G),
      SubClassOfAxiom(C,ObjectSomeValuesFrom(S,ObjectOneOf(Set(o)))),
      SubClassOfAxiom(ObjectSomeValuesFrom(S,B),D),
      SubClassOfAxiom(A,ObjectSomeValuesFrom(R,F)),
      SubClassOfAxiom(F,ObjectOneOf(Set(o))),
      SubClassOfAxiom(F,B)
    )
    val expected = Set(
     // SubClassOfAxiom(A,G)
      EquivalentClassesAxiom(A,Nothing)
    )
    taxonomyContains(input,expected)
  }

 test ( "testDavid1") {
   val input = Set(
     SubClassOfAxiom(A,B),
     SubClassOfAxiom(A,ObjectSomeValuesFrom(R,C)),
     SubClassOfAxiom(B,ObjectSomeValuesFrom(R,D)),
     FunctionalObjectPropertyAxiom(R),
     SubClassOfAxiom(ObjectIntersectionOf(C,D),Nothing)
   )
   val expected = Set(
     EquivalentClassesAxiom(A,Nothing)
   )
  taxonomyContains(input,expected)
 }

 test ( "testDavid2") {
   val input = Set(
     EquivalentClassesAxiom(A, ObjectOneOf(Set(o,u))),
     ClassAssertionAxiom(B,o),
     ClassAssertionAxiom(B,u),
   )
   val expected = Set(
     SubClassOfAxiom(A,B)
   )
   taxonomyContains(input,expected)
 }

 test ("testDavid3") {
   val input = Set(
     EquivalentClassesAxiom(ObjectOneOf(Set(b)),B),
     ObjectPropertyDomainAxiom(R,C),
     ClassAssertionAxiom(ObjectHasValue(R,a),b)
   )
   val expected = Set(
     SubClassOfAxiom(B,C)
   )
   taxonomyContains(input,expected)
 }

//  test("mondongo") {
//    mandanga
//    assert(true)
//  }
}
