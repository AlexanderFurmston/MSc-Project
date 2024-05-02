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

package com.sequoiareasoner.kernel.owl.iri

import com.sequoiareasoner.kernel.owl.model.{AnnotationSubject, AnnotationValue}

import scala.collection.mutable

object IRI {
  /* An IRI is either an imported IRI (i.e. it originates from an input ontology), or it is an internal IRI (i.e. an
   * IRI that was introduced during structural transformation). An internal IRI is introduced for each quantifier
   * (either universal or existential), and for each class expression in a disjunction, and for each individual.
   * (It is assumed that class expressions are in negation normal form.) Each IRI is uniquely identified by an integer.
   * In order to quickly determine the type of an IRI, the following convention on the bit pattern of UIDs is used:
   *  (0|1)^29 111  can be used to represent an imported IRI;
   *  (0|1)^29 001  can be used to represent an internal IRI introduced by an existential quantifier;
   *  (0|1)^29 011  can be used to represent an internal IRI introduced by a universal quantifier;
   *  (0|1)^29 010  can be used to represent an internal IRI introduced by a disjunct.
   *  (0|1)^29 000  can be used to represent an internal IRI introduced by an individual (but represents the concept).
   * Furthermore, the first few imported IRI UIDs are reserved for IRIs that are predefined in the OWL 2 specification.
   */

  /**------ STRING <--> UID for imported IRIs-------- */

  /** Registry mapping iri names to their UID */
  private[this] val iriString2Uid = new mutable.HashMap[String, Int]
  /** Maps UIDs to iri names */
  private[this] val uid2IriString = new mutable.LongMap[String]

  /** ------CREATION AND RETRIEVAL---------- **/

  /** Variable pointing to the number for the next uid of an iri of a particular kind. We do not do this for
    * nominal concepts since we produce their iri uid based on the individual uid. */
  private[this] var nextImportedIriUid: Int = 0
  private[this] var nextInternalExistentialUid: Int = 0
  private[this] var nextInternalDisjunctionUid: Int = 0
  private[this] var nextInternalUniversalUid: Int = 0
  /** Creates an IRI by concatenating a prefix with a suffix. This method is not thread safe.
    * @param prefix
    * @param localName
    * @return the IRI whose full String consists of the specified prefix followed by the localName.
    */
  def apply(prefix: Prefix, localName: String): IRI = apply(prefix.iri.fullIriAsString + localName)
  /** Returns an IRI to be used by an auxiliary predicate representing an existential quantifier filler.
    * This method is not thread safe.
    *
    * @return an IRI to be used by an auxiliary predicate representing an existential quantifier filler.
    */
  def some(): IRI = {
    val uid = (nextInternalExistentialUid << 3) + 1 // Internal existential IRI UIDs end in 001.
    nextInternalExistentialUid += 1
    require(uid >= 0)
    new IRI(uid)
  }
  /** Returns an IRI to be used by an auxiliary predicate representing an disjunct.
    * This method is not thread safe.
    *
    * @return an IRI to be used by an auxiliary predicate representing an disjunct.
    */
  def disjunct(): IRI = {
    val uid = (nextInternalDisjunctionUid << 3) + 2 // Internal disjunction IRI UIDs end in 010.
    nextInternalDisjunctionUid += 1
    require(uid >= 0)
    new IRI(uid)
  }
  /** Returns an IRI to be used by an auxiliary predicate representing a universal quantifier filler.
    * This method is not thread safe.
    *
    * @return an IRI to be used by an auxiliary predicate representing a universal quantifier filler.
    */
  def all(): IRI = {
    val uid = (nextInternalUniversalUid << 3) + 3 // Internal universal IRI UIDs end in 011.
    nextInternalUniversalUid += 1
    require(uid >= 0)
    new IRI(uid)
  }
  /** Returns an IRI corresponding to the nominal concept for a given individual IRI string */
  def nominalConcept(fullIri: String): IRI = { // TODO: add assertion that IRI is legal (e.g. "<http://www.example.com>" with < and > is illegal.
    /** First, create the IRI for the nominal, and get corresponding nominal UID */
    val uid = IRI(fullIri).uid
    /** Then produce corresponding uid for the concept */
    new IRI(uid & (~7))  // Nominal concept UIDs end in 000, but otherwise they are equal to the imported nominal uid.
  }
  /** Create IRI given the full IRI as a string. This SHOULD ONLY BE USED to create iris from IMPORTED iris*/
  def apply(fullIri: String): IRI = { // TODO: add assertion that IRI is legal (e.g. "<http://www.example.com>" with < and > is illegal.
    val uid = iriString2Uid.getOrElseUpdate(fullIri, {
      val uid = (nextImportedIriUid << 3) + 7 // Imported IRI UIDs end in 111.
      nextImportedIriUid += 1
      uid2IriString.put(uid, fullIri)
      uid
    })
    require(uid >= 0)
    new IRI(uid)
  }
  /** Create IRI from UID, usable for all kinds of IRIs */
  def apply(uid: Int): IRI = {
    new IRI(uid)
  }

  /** ---------------- RETRIEVER OF IRI names -------------------*/

  /** Given the UID of an imported IRI (including IRIs predefined in the OWL 2 specification), returns the full IRI as a
    * string. */
  def importedIriUid2IriNameString(uid: Int): String = {
    /** Make sure it ends in 111 */
    require((~uid & 7) == 0)
    uid2IriString(uid)
  }

  /** Given the uid of a nominalconcept, returns the fullIRI string name of the corresponding nominal */
  def nominalConceptUid2NominalIriStringName(uid: Int): String = {
    require(IRI(uid).isInternalIndividual)
    /** The uid is the same, but replacing 000 at the end (code for nominal concepts) by 000 (code for imported iris) */
    uid2IriString(uid | 7)
  }

  /** ------------- PREDEFINED IRIS ---------------- */

  /** The predefined IRI `http://www.w3.org/2002/07/owl#Thing`. */
  final val owlThing                = apply("http://www.w3.org/2002/07/owl#Thing")
  /** The predefined IRI `http://www.w3.org/2002/07/owl#Nothing`. */
  final val owlNothing              = apply("http://www.w3.org/2002/07/owl#Nothing")
  /** The predefined IRI `http://www.w3.org/2002/07/owl#topObjectProperty`. */
  final val owlTopObjectProperty    = apply("http://www.w3.org/2002/07/owl#topObjectProperty")
  /** The predefined IRI `http://www.w3.org/2002/07/owl#bottomObjectProperty`. */
  final val owlBottomObjectProperty = apply("http://www.w3.org/2002/07/owl#bottomObjectProperty")
  /** The predefined IRI `http://www.w3.org/2002/07/owl#topDataProperty`. */
  final val owlTopDataProperty      = apply("http://www.w3.org/2002/07/owl#topDataProperty")
  /** The predefined IRI `http://www.w3.org/2002/07/owl#bottomDataProperty`. */
  final val owlBottomDataProperty   = apply("http://www.w3.org/2002/07/owl#bottomDataProperty")
  /** The predefined IRI `http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral`. */
  final val rdfPlainLiteral         = apply("http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral")
  /** The predefined IRI `http://www.w3.org/2000/01/rdf-schema#Literal`. */
  final val rdfsLiteral             = apply("http://www.w3.org/2000/01/rdf-schema#Literal")
}

/** Represents International Resource Identifiers.
  *
  * @author Andrew Bate <code@andrewbate.com>
  *
  * @param uid a unique identifier generated from `fullIriAsString`
  */
class IRI /*private*/ (val uid: Int) extends AnyVal with AnnotationSubject with AnnotationValue { // FIXME: add an apply local to kernel for this constructor

  /** These tests implement the convention on UIDs described above. */
  @inline def isImported: Boolean = (~uid & 7) == 0
  @inline def isInternal: Boolean = ((uid >>> 2) & 1) == 0
  @inline def isInternalExistential: Boolean = (uid & 7) == 1
  @inline def isInternalUniversal: Boolean = (uid & 7) == 3
  @inline def isInternalDisjunct: Boolean = (uid & 7) == 2
  @inline def isInternalIndividual: Boolean = (uid & 7) == 0

  @inline def <(that: IRI): Boolean = { this.uid < that.uid}

  /** return the full IRI as a string */
  def fullIriAsString: String =
    if (isImported) IRI.importedIriUid2IriNameString(uid)
    else if (isInternalExistential) "some:" + (uid >> 3)
    else if (isInternalUniversal) "all:" + (uid >> 3)
    else if (isInternalDisjunct) "disjunct:" + (uid >> 3)
    else if (isInternalIndividual) "conceptFor:" + IRI.nominalConceptUid2NominalIriStringName(uid)
    else "ERROR"

  /** Returns `true` if this IRI is equal to `owl:Thing`. */
  @inline def isThing: Boolean =
    this == IRI.owlThing
  /** Returns `true` if this IRI is equal to `owl:Nothing`. */
  @inline def isNothing: Boolean =
    this == IRI.owlNothing
  /** Returns `true` if this IRI is equal to `rdf:PlainLiteral`. */
  @inline def isPlainLiteral: Boolean =
    this == IRI.rdfPlainLiteral
  /** Returns `true` if this IRI is equal to `rdfs:Literal`. */
  @inline def isRDFSLiteral: Boolean =
    this == IRI.rdfsLiteral


  /** Compares this IRI with the specified IRI for order.
    *
    * The order implemented is the following: `iri1 <= iri2` if and only if one of the following conditions hold:
    * $ - `iri1` is an internal IRI and `iri2` is an imported IRI;
    * $ - `iri1` is an internal disjunct IRI and `iri2` either an internal existential IRI or an internal universal IRI or an internal individual IRI;
    * $ - `iri1` is an internal existential IRI and `iri2` is an internal universal IRI or an internal individual IRI;
    * $ - `iri1` is an internal universal IRI and `iri2` is an internal individual IRI;
    * $ - `iri1` and `iri2` are both imported IRIs and `iri1.uid <= iri2.uid`;
    * $ - `iri1` and `iri2` are both internal individual IRIs and `ir1.uid <= iri2.uid`;
    * $ - `iri1` and `iri2` are both internal universal IRIs and `iri1.uid <= iri2.uid`;
    * $ - `iri1` and `iri2` are both internal existential IRIs and `iri1.uid <= iri2.uid`;
    * $ - `iri1` and `iri2` are both internal disjunct IRIs and `iri1.uid <= iri2.uid`.
    * Read explanation of this in the paper.
    *
    */
  def <=(that: IRI): Boolean =
    if (that.isImported) {
      this.isInternal || this.uid - that.uid <= 0
    } else if (that.isInternalIndividual) {
      this.isInternal && (!this.isInternalIndividual || this.uid - that.uid <= 0)
    } else if (that.isInternalUniversal) {
      (this.isInternalExistential || this.isInternalDisjunct) || (this.isInternalUniversal && this.uid - that.uid <= 0)
    } else if (that.isInternalExistential) {
      this.isInternalDisjunct || (this.isInternalExistential && this.uid - that.uid <= 0)
    } else  {
      assert(that.isInternalDisjunct)
      this.isInternalDisjunct && this.uid - that.uid <= 0
    }

  override def toString: String = "<" + fullIriAsString + ">"

}
