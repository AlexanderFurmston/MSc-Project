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

package com.sequoiareasoner.kernel.taxonomy

import com.sequoiareasoner.kernel.index.{IndexedSequence, TotalIRIMultiMap}
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.owl.model.{DataProperty, OWLClass, OWLObject, ObjectProperty}

import scala.annotation.tailrec
import scala.collection.mutable





object Taxonomy {





  /** An optimized representation for immutable sets of size 1.
    *
    * @param elem  the UID of the IRI.
    */
  private[this] final class SingletonImmutableIRISet(elem: Int) extends ImmutableIRISet {
    override def representative: IRI = new IRI(elem)
    override def contains(elem: IRI): Boolean = this.elem == elem.uid
    override def size: Int = 1
    override def isEmpty: Boolean = false
    override def iterator: Iterator[IRI] = Iterator(new IRI(elem))
    override def hashCode: Int = elem
    override def equals(that: Any): Boolean = that match {
      case that: ImmutableIRISet => that.size == 1 && that.contains(new IRI(elem))
      case _ => false
    }
    override def addString(b: StringBuilder, start: String, sep: String, end: String): StringBuilder =
      b ++= start ++= new IRI(elem).toString ++= end
  }

  /** An immutable IRI set implemented using an array of IRI UIDs to avoid boxing.
    * The array passed to the constructor will be sorted in place and is assumed to *not contain repetitions*.
    *
    * @param elems  the array of IRI UIDs.
    */
  private[this] final class ArrayBackedImmutableIRISet(private val elems: Array[Int]) extends ImmutableIRISet {
    java.util.Arrays.sort(elems)
    override def representative: IRI =
      if (elems.length == 0) throw new NoSuchElementException
      else new IRI(elems(0))
    override def contains(elem: IRI): Boolean = {
      @tailrec def binarySearch(from: Int, to: Int): Boolean =
        if (to == from) false else {
          val idx = from + (to - from - 1) / 2
          val cmp = elem.uid - elems(idx)
          if (cmp < 0) {
            binarySearch(from, idx)
          } else if (cmp > 0) {
            binarySearch(idx + 1, to)
          } else {
            true
          }
        }
      binarySearch(0, elems.length)
    }
    override def size: Int = elems.length
    override def isEmpty: Boolean = elems.length > 0
    override def iterator: Iterator[IRI] = elems.iterator map { uid => new IRI(uid) } // TODO: remove boxing
    override def hashCode: Int = {
      @tailrec def sum(acc: Int, idx: Int): Int =
        if (idx == elems.length) acc
        else sum(acc + elems(idx), idx + 1)
      sum(0, 0)
    }
    override def equals(that: Any): Boolean = that match {
      case that: ArrayBackedImmutableIRISet =>
        // Optimized case when we know that arrays can be compared directly.
        java.util.Arrays.equals(this.elems, that.elems)
      case that: ImmutableIRISet =>
        var canBeEqual = this.size == that.size
        var i = 0
        while (canBeEqual && i < elems.length) {
          canBeEqual = that.contains(new IRI(elems(i)))
          i += 1
        }
        canBeEqual
      case _ =>
        false
    }
    override def addString(b: StringBuilder, start: String, sep: String, end: String): StringBuilder =
      iterator.addString(b, start, sep, end)
  }

  /** A fresh TaxonomyNode containing an OWLObject that does not occur in a taxonomy.
    * Such nodes are returned to queries when FreshEntityPolicy is set to ALLOW.
    */
  private final class FreshTaxonomyNode[X <: OWLObject](member: IRI, taxonomy: Taxonomy[X]) extends TaxonomyNode[X] {
    require(member.isImported)
    override def equivalentObjects: ImmutableIRISet = new SingletonImmutableIRISet(member.uid)
    override def directSuperNodes = TaxonomyNodeSetImpl(taxonomy.getTopNode)
    override def allSuperNodes = TaxonomyNodeSetImpl(taxonomy.getTopNode)
    override def directSubNodes = TaxonomyNodeSetImpl(taxonomy.getBottomNode)
    override def allSubNodes = TaxonomyNodeSetImpl(taxonomy.getBottomNode)
  }

  /** Stores information about an OWLObject for the purpose of hierarchy creation. It is read-only for
    * public access but provides package-private ways of modifying it.
    *
    * @param equivalentObjects  the set of equivalent $OWLClass objects
    */
  private[this] final class TrueTaxonomyNode[X <: OWLObject](override val equivalentObjects: ImmutableIRISet) extends TaxonomyNode[X] {
    /** OWLObject nodes, except for the bottom node, whose members are direct sub-classes of the members of this node. */
    override val directSubNodes: TaxonomyNodeSet[X] = new TaxonomyNodeSetImpl[X]
    /** OWLObject nodes whose members are direct super-classes of the members of this node. */
    override val directSuperNodes: TaxonomyNodeSet[X] = new TaxonomyNodeSetImpl[X]

    /** Notice that this is a class definition. The vals above start empty, but they can be filled. They are mutable objects. */
    private[this] def allNodes(sub: Boolean): TaxonomyNodeSet[X] = {
      val result = new TaxonomyNodeSetImpl[X]
      val todo = new mutable.ArrayStack[TaxonomyNode[X]]
      val init = if (sub) directSubNodes else directSuperNodes
      init foreach { n => todo += n }
      while (todo.nonEmpty) {
        val next = todo.pop
          if (result add next) {
            val toPush = if (sub) next.directSubNodes else next.directSuperNodes
            toPush foreach { n => todo += n }
          }
        }
      result
    }
    override def allSubNodes: TaxonomyNodeSet[X] = allNodes(sub = true)
    override def allSuperNodes: TaxonomyNodeSet[X] = allNodes(sub = false)
  }





  // equivalents must not contain repetitions.
  private[this] def createImmutableIRISet(equivalents: Seq[Int]): ImmutableIRISet =
    if (equivalents.size == 1) new SingletonImmutableIRISet(equivalents.head)
    else new ArrayBackedImmutableIRISet(equivalents.toArray)


///** Given an OWLObject which is an OWLClass, OWLObjectProperty, or OWLDataProperty, returns the corresponding
//      * bottom object. Otherwise, it does not return anything. */
//    def getBottomEntity(entity: OWLObject): Option[IRI] = {
//     entity match {
//       case _: OWLClass => Some(IRI.owlNothing)
//       case _: ObjectProperty => Some(IRI.owlBottomObjectProperty)
//       case _: DataProperty => Some(IRI.owlBottomDataProperty)
//       case _ => None
//     }
//    }
///** Given an OWLObject which is an OWLClass, OWLObjectProperty, or OWLDataProperty, returns the corresponding
//      * top object. Otherwise, it does not return anything. */
//    def getTopEntity(entity: OWLObject): Option[IRI] = {
//     entity match {
//       case _: OWLClass => Some(IRI.owlThing)
//       case _: ObjectProperty => Some(IRI.owlTopObjectProperty)
//       case _: DataProperty => Some(IRI.owlTopDataProperty)
//       case _ => None
//     }
//    }

/** This method returns a Sequoia taxonomy given a set of subsumption relations between OWL entities, and optionally a top
    * and bottom entities to put in the top and bottom nodes, respectively.
    *
    * The input set of subsumption relations `superConcepts` must be transitively closed. However, reflexivity is not required.
    *
    * The method also creates a dummy top node and a bottom top node if none are provided.
    */

  def apply[X <: OWLObject](allSupers: TotalIRIMultiMap[IRI], bottomEntity: Option[IRI] = None, topEntity: Option[IRI] = None): Taxonomy[X] = {


//    println("Input to taxonomy builder: ")
//    println("Supers: ")
//    allSupers.foreachKeys( key => {
//      allSupers(key).foreach( kosi => println(key + " -> " + kosi)) })
//    println("Bottom")
//    bottomEntity.foreach(enti => println(enti))
//    println("Top")
//    topEntity.foreach(enti => println(enti))


    // The map from object IRIs to object nodes (LongMap is significantly faster than HashMap).
    val taxonomyNodes = new mutable.LongMap[TaxonomyNode[X]]
    // Objects to be put in the bottom node.
    val bottomEquivalents = new mutable.ListBuffer[Int]
    bottomEntity.foreach( iri => bottomEquivalents += iri.uid)
    // Objects to be put at the top node.
    val topEquivalents = new mutable.ListBuffer[Int]
    topEntity.foreach( iri => topEquivalents += iri.uid)
    // directSupers(a) returns all the direct super concepts of a. Note that line below is just the initialisation, not
    // the final value.
    val directSupers = allSupers.copy
    // The set of IRI UIDs that have a subEntity.
    val hasSubEntity = new mutable.BitSet

    /** Two sets are used: superConcepts, which has the list of all (direct and indirect) superconcepts, and
      * directSupers, which has the list of all direct superconcepts. Both start equal to superConcepts.
      * Then, for each concept _conceptA_, we just need to make sure we remove those bindings (A,B) where
      * B is not a direct superconcept of A, as well as remove any other concept B equivalent to A that has
      * not been considered yet; we just add it to a list of equivalents of A, except if B is owl:Nothing or
      * owl:Thing, in we remove A. */
    allSupers.foreachKeys { entityA =>

      // if (entityA.toString.contains("AminoAcid")) superConcepts.foreach(entityA) ( x => System.out.println("(" + entityA.toString + " ," + x + ")")) // DEBUG
      assert(entityA.isImported || entityA.isInternalIndividual)
      /** If entityA is equivalent to the topEntity, then any direct superconcept must be made a topEquivalent */
      /** Note that we eliminate equivalent topEntities from the set of keys of directSupers(A), since it should have none */
      if (topEntity.contains(entityA)) {
        directSupers.foreach(entityA) { entityB => { topEquivalents += entityB.uid; directSupers.removeKey(entityB) }}
        directSupers.removeKey(entityA)
      } else if (bottomEntity.exists{ p: IRI => directSupers(entityA) contains p}) {
        /** If entityA has bottomEntity as a superentity, we make it a bottomEquivalent and remove any binding where it appears as a subclass */
        bottomEquivalents += entityA.uid
        directSupers.removeKey(entityA)
        allSupers.removeKey(entityA)
      } else {
        /** Create a list of elements that will turn out to be identical to A */
        val equivalents = new mutable.ListBuffer[Int]
        /** Add A to the list if equivalents of A */
        equivalents += entityA.uid
        /** Take each superentity B and:
          *  1) Remove (A,A) from the taxonomy.
          *  2) If B is subentity of A, add B to list of equivalents of A, and remove B from taxonomy and from the
          *  list of entities to consider.
          *  3) Remove (A,C) from directSupers if C is a super of B.
          */
        // Only consider directSupers which is needed to correctly handle cycles.
        directSupers.foreach(entityA){ entityB =>
          if (entityA == entityB) {
            directSupers.removeBinding(entityA, entityB)
            allSupers.removeBinding(entityA, entityB)
          } else if (allSupers(entityB) contains entityA) {
            equivalents += entityB.uid
            directSupers.removeKey(entityB)
            allSupers.removeKey(entityB)
            directSupers.removeBinding(entityA, entityB)
            allSupers.removeBinding(entityA, entityB)
            allSupers.removeKey(entityB)
          } else {
            hasSubEntity += entityB.uid
            allSupers.foreach(entityB) { conceptC =>
              if (entityB != conceptC) directSupers.removeBinding(entityA, conceptC)
            }
          }
        }
        val nodeForA = new TrueTaxonomyNode[X](createImmutableIRISet(equivalents))
        for (iriUID <- equivalents) taxonomyNodes.put(iriUID, nodeForA)
      }
    }

    val bottomImmutableEquivalents: ImmutableIRISet = createImmutableIRISet(bottomEquivalents)
    val bottomNode = new TrueTaxonomyNode[X](bottomImmutableEquivalents)
    for (iriUID <- bottomEquivalents) taxonomyNodes.put(iriUID, bottomNode)

    val topImmutableEquivalents: ImmutableIRISet = createImmutableIRISet(topEquivalents)
    val topNode = new TrueTaxonomyNode[X](topImmutableEquivalents)
    for (iriUID <- topEquivalents) taxonomyNodes.put(iriUID, topNode)

    directSupers foreachKeys { a =>
      val subNode: TaxonomyNode[X] = taxonomyNodes(a.uid)
      // If an iri has no sub-entities, we add its node as a supernode of the bottom node.
      if (!hasSubEntity.contains(a.uid)) {
        bottomNode.directSuperNodes.add(subNode)
        subNode.directSubNodes.add(bottomNode)
      }
      val supers: IndexedSequence[IRI] = directSupers(a)
      if (supers.isEmpty) {
        // If this node does not have any superentities, we add as its supernode the top node.
        subNode.directSuperNodes.add(topNode)
        topNode.directSubNodes.add(subNode)
      } else {
        supers foreach { sup =>
          val superNode: TaxonomyNode[X] = taxonomyNodes.getOrElseUpdate(sup.uid, {
            val newNode = new TrueTaxonomyNode[X](new SingletonImmutableIRISet(sup.uid))
            // If this new super node does not exist as a key, it only has the trivial superclass owl:Thing.
            newNode.directSuperNodes.add(topNode)
            topNode.directSubNodes.add(newNode)
            newNode
          })
          superNode.directSubNodes.add(subNode)
          subNode.directSuperNodes.add(superNode)
        }
      }
    }

    if (bottomNode.directSuperNodes.isEmpty) {
      assert(topNode.directSubNodes.isEmpty)
      bottomNode.directSuperNodes.add(topNode)
      topNode.directSubNodes.add(bottomNode)
    }
//
//   var number = 1
//   taxonomyNodes.foreachKey( key => {
//    println("Node " + number)
//     number += 1
//     for (iri <- taxonomyNodes(key).equivalentObjects.iterator) println(iri)
//   })
//println("The Bottom Node: ")
//   for (iri <- bottomNode.equivalentObjects.iterator ) println(iri)

    new Taxonomy[X](taxonomyNodes, bottomNode, topNode)
  }




}


/** A taxonomy in the form of a lattice of TaxonomyNodes. For each OWLObject, the taxonomy holds a TaxonomyNode object
  * from which direct sub- and super-nodes can be retrieved.
  *
  * The input should be transitively reduced.
  *
  * */
class Taxonomy[X <: OWLObject] private (nodes: mutable.LongMap[TaxonomyNode[X]], bottomNode: TaxonomyNode[X] , topNode: TaxonomyNode[X]) {

    //* Verify that this is a lattice */
    val toProcess = new mutable.Queue[TaxonomyNode[X]]
    toProcess += bottomNode
    val visited = new mutable.HashSet[TaxonomyNode[X]]
    while (toProcess.nonEmpty) {
      val current = toProcess.dequeue
      if (visited add current) {
        val directSuperNodes = current.directSuperNodes
        if (directSuperNodes.isEmpty) assert(current.equivalentObjects.equals(topNode.equivalentObjects),"Not a lattice")
        directSuperNodes foreach { elem => toProcess += elem }
      }
    }

  /** Returns the [[TaxonomyNode]] containing the given ($OWLObject with imported IRI) as a member.  */
  def node(iri: IRI, allowFreshEntities: Boolean = false): TaxonomyNode[X] = {
    require(iri.isImported)
    val node: TaxonomyNode[X] = nodes.getOrNull(iri.uid)
    if (node eq null) {
      if (allowFreshEntities) new Taxonomy.FreshTaxonomyNode(iri, this)
      else throw new NoSuchElementException
    } else {
      node
    }
  }

  def getBottomNode: TaxonomyNode[X] = bottomNode
  def getTopNode: TaxonomyNode[X] = topNode
  def getAllNodes: Iterable[TaxonomyNode[X]] = nodes.values

  /** Applies a pair of functions to the equivalent objects and superEntity relationships respectively.
    *
    * @param f1  the function to invoke for each set of equivalent objects
    * @param f2  the function to invoke for each pair of IRIs in a subEntity relationship
    */
  def foreach[U1, U2](f1: ImmutableIRISet => U1, f2: (IRI, IRI) => U2): Unit = {
    val toProcess = new mutable.Queue[TaxonomyNode[X]]
    toProcess += bottomNode
    val visited = new mutable.HashSet[TaxonomyNode[X]]
    while (toProcess.nonEmpty) {
      val current = toProcess.dequeue
      if (visited add current) {
        val equivalentObjects: ImmutableIRISet = current.equivalentObjects
        f1(equivalentObjects)
        val currentRepresentative: Option[IRI] = try {
          Some(equivalentObjects.representative)
        } catch {
          case _: Throwable => None
        }
        val directSuperNodes = current.directSuperNodes
        for (n <- directSuperNodes) {
          val superRepresentative: Option[IRI] = try {
            Some(n.equivalentObjects.representative)
          } catch {
            case _: Throwable => None
          }
          currentRepresentative.foreach(x => superRepresentative.foreach( y => f2(x,y)))
        }
        directSuperNodes foreach { elem => toProcess += elem }
      }
    }
  }

  /** Returns a pretty printed string of the taxonomy. */
  override def toString: String = {

    val builder = new StringBuilder
    def f1(equivalentObjects: ImmutableIRISet): Unit =
      if (equivalentObjects.size > 1)
        equivalentObjects.addString(builder, "EquivalentObjects(", " ", ")\n")
    def f2(sub: IRI, sup: IRI): Unit = {
      //if (sub != bottomIRI && sup != topIRI) { // Skip trivial subsumptions.
        builder.append("SubEntityOf(")
        builder.append(sub)
        builder.append(' ')
        builder.append(sup)
        builder.append(')')
        builder.append('\n')
      }
    foreach(f1, f2)
    builder.result
  }

}
