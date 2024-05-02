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

package com.sequoiareasoner.owlapi

import com.sequoiareasoner.kernel.taxonomy.{ImmutableIRISet, TaxonomyNode, TaxonomyNodeSet}
import com.sequoiareasoner.owlapi.util.WeakIdentityMap
import com.sequoiareasoner.owlapi.wrapper.OWLConverter
import org.semanticweb.owlapi.model._
import org.semanticweb.owlapi.reasoner.{Node, NodeSet}
import java.util.{AbstractSet => jAbstractSet, Collection => jCollection, Iterator => jIterator, Set => jSet}

import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.reasoner.{SequoiaException, SequoiaRuntimeException}
import com.sequoiareasoner.owlapi.impl.OWLNamedIndividualImpl
import com.sequoiareasoner.kernel.owl.model.{OWLClass => SequoiaOWLClass}
import com.sequoiareasoner.kernel.owl.model.{NamedIndividual => SequoiaOWLNamedIndividual}


/** Converter from Sequoia OWL to OWL API.
  *
  * Facade class for conversion from Sequoia objects to OWL API objects.
  *
  * @author Andrew Bate <code@andrewbate.com>
  */
object TaxonomyNodeConverter {
  // This class implements wrapper classes to efficiently redirect calls to their Sequoia counterparts.
  // This also means that changes to the underlying collections are reflected in these views.

  private[this] val cache = new WeakIdentityMap[TaxonomyNode[SequoiaOWLClass], Node[OWLClass]]
  private[this] val cache2 = new WeakIdentityMap[TaxonomyNode[SequoiaOWLNamedIndividual], Node[OWLNamedIndividual]]

  private[this] final class OWLClassSetWrapper(peer: ImmutableIRISet) extends jAbstractSet[OWLClass] {
    override def size: Int = peer.size
    override def contains(o: Any): Boolean = o match {
      case o: OWLClass => peer.contains(OWLConverter.convert(o.getIRI))
      case _ => false
    }
    override def iterator: jIterator[OWLClass] = new jIterator[OWLClass] {
      private[this] val underlying = peer.iterator
      override def next: OWLClass = EntityConverter.toOWLClass(underlying.next)
      override def hasNext: Boolean = underlying.hasNext
    }
    override def remove(o: Any) = throw new UnsupportedOperationException
    override def removeAll(c: jCollection[_]) = throw new UnsupportedOperationException
    override def add(e: OWLClass) = throw new UnsupportedOperationException
    override def addAll(c: jCollection[_ <: OWLClass]) = throw new UnsupportedOperationException
    override def clear = throw new UnsupportedOperationException
    override def retainAll(c: jCollection[_]) = throw new UnsupportedOperationException
    // Safe to cache hashCode for performance because peer is immutable.
    private[this] var hashCodeCached: Int = 0
    override def hashCode: Int = {
      if (hashCodeCached == 0) hashCodeCached = super.hashCode
      hashCodeCached
    }
  }
  private[this] final class OWLNamedIndividualSetWrapper(peer: ImmutableIRISet) extends jAbstractSet[OWLNamedIndividual] {
    override def size: Int = peer.size
    override def contains(o: Any): Boolean = o match {
      case o: OWLNamedIndividual => peer.contains(OWLConverter.convert(o.getIRI))
      case _ => false
    }
    override def iterator: jIterator[OWLNamedIndividual] = new jIterator[OWLNamedIndividual] {
      private[this] val underlying = peer.iterator
      override def next: OWLNamedIndividual = EntityConverter.toOWLNamedIndividual(underlying.next)
      override def hasNext: Boolean = underlying.hasNext
    }
    override def remove(o: Any) = throw new UnsupportedOperationException
    override def removeAll(c: jCollection[_]) = throw new UnsupportedOperationException
    override def add(e: OWLNamedIndividual) = throw new UnsupportedOperationException
    override def addAll(c: jCollection[_ <: OWLNamedIndividual]) = throw new UnsupportedOperationException
    override def clear = throw new UnsupportedOperationException
    override def retainAll(c: jCollection[_]) = throw new UnsupportedOperationException
    // Safe to cache hashCode for performance because peer is immutable.
    private[this] var hashCodeCached: Int = 0
    override def hashCode: Int = {
      if (hashCodeCached == 0) hashCodeCached = super.hashCode
      hashCodeCached
    }
  }
  // PRECONDITION: peer.contains(exclude)
  private[this] class OWLClassSetExcludeWrapper(peer: ImmutableIRISet, exclude: IRI) extends jAbstractSet[OWLClass] {
    override def size: Int = peer.size - 1
    override def contains(o: Any): Boolean = o match {
      case o: OWLClass =>
        val iri: IRI = OWLConverter.convert(o.getIRI)
        iri != exclude && peer.contains(iri)
      case _ => false
    }
    override def iterator: jIterator[OWLClass] = new jIterator[OWLClass] {
      private[this] val underlying = peer.iterator
      private[this] var seen: Int = 0
      override def next: OWLClass = {
        val elem: IRI = underlying.next
        seen += 1
        val res = if (elem == exclude) underlying.next else elem
        EntityConverter.toOWLClass(res)
      }
      override def hasNext: Boolean = seen < size
    }
    override def remove(o: Any) = throw new UnsupportedOperationException
    override def removeAll(c: jCollection[_]) = throw new UnsupportedOperationException
    override def add(e: OWLClass) = throw new UnsupportedOperationException
    override def addAll(c: jCollection[_ <: OWLClass]) = throw new UnsupportedOperationException
    override def clear = throw new UnsupportedOperationException
    override def retainAll(c: jCollection[_]) = throw new UnsupportedOperationException
    // Safe to cache hashCode for performance because both peer and excluded value are immutable.
    private[this] var hashCodeCached: Int = 0
    override def hashCode: Int = {
      if (hashCodeCached == 0) hashCodeCached = super.hashCode
      hashCodeCached
    }
  }
// PRECONDITION: peer.contains(exclude)
  private[this] class OWLNamedIndividualSetExcludeWrapper(peer: ImmutableIRISet, exclude: IRI) extends jAbstractSet[OWLNamedIndividual] {
    override def size: Int = peer.size - 1
    override def contains(o: Any): Boolean = o match {
      case o: OWLNamedIndividual =>
        val iri: IRI = OWLConverter.convert(o.getIRI)
        iri != exclude && peer.contains(iri)
      case _ => false
    }
    override def iterator: jIterator[OWLNamedIndividual] = new jIterator[OWLNamedIndividual] {
      private[this] val underlying = peer.iterator
      private[this] var seen: Int = 0
      override def next: OWLNamedIndividual= {
        val elem: IRI = underlying.next
        seen += 1
        val res = if (elem == exclude) underlying.next else elem
        EntityConverter.toOWLNamedIndividual(res)
      }
      override def hasNext: Boolean = seen < size
    }
    override def remove(o: Any) = throw new UnsupportedOperationException
    override def removeAll(c: jCollection[_]) = throw new UnsupportedOperationException
    override def add(e: OWLNamedIndividual) = throw new UnsupportedOperationException
    override def addAll(c: jCollection[_ <: OWLNamedIndividual]) = throw new UnsupportedOperationException
    override def clear = throw new UnsupportedOperationException
    override def retainAll(c: jCollection[_]) = throw new UnsupportedOperationException
    // Safe to cache hashCode for performance because both peer and excluded value are immutable.
    private[this] var hashCodeCached: Int = 0
    override def hashCode: Int = {
      if (hashCodeCached == 0) hashCodeCached = super.hashCode
      hashCodeCached
    }
  }


  private[this] class OWLClassNodeImpl(private val peer: TaxonomyNode[SequoiaOWLClass]) extends Node[OWLClass] {
    private[this] val entities = new OWLClassSetWrapper(peer.equivalentObjects)
    override def getSize: Int = peer.equivalentObjects.size
    override def isSingleton: Boolean = peer.equivalentObjects.size == 1
    override def isBottomNode: Boolean = peer.equivalentObjects.contains(IRI.owlNothing)
    override def isTopNode: Boolean = peer.equivalentObjects.contains(IRI.owlThing)
    override def contains(entity: OWLClass): Boolean = entities.contains(entity)
    override def getRepresentativeElement: OWLClass = EntityConverter.toOWLClass(peer.equivalentObjects.representative)
    override def getEntities: jSet[OWLClass] = entities
    override def getEntitiesMinus(e: OWLClass): jSet[OWLClass] =
      if (contains(e)) new java.util.HashSet(new OWLClassSetExcludeWrapper(peer.equivalentObjects, OWLConverter.convert(e.getIRI))) else entities // WORKAROUND for Protege bug.
    override def getEntitiesMinusBottom: jSet[OWLClass] =
      if (isBottomNode) new java.util.HashSet(new OWLClassSetExcludeWrapper(peer.equivalentObjects, IRI.owlNothing)) else entities // WORKAROUND for Protege bug.
    override def getEntitiesMinusTop: jSet[OWLClass] =
      if (isTopNode) new java.util.HashSet(new OWLClassSetExcludeWrapper(peer.equivalentObjects, IRI.owlThing)) else entities // WORKAROUND for Protege bug.
    override def iterator: jIterator[OWLClass] = new jIterator[OWLClass] {
      private[this] val underlying = peer.equivalentObjects.iterator
      override def next: OWLClass = EntityConverter.toOWLClass(underlying.next)
      override def hasNext: Boolean = underlying.hasNext
    }
    override def equals(o: Any): Boolean = o match {
      case that: OWLClassNodeImpl =>
        this.peer.equivalentObjects == that.peer.equivalentObjects
      case that: Node[_] =>
        this.getSize == that.getSize && this.getEntities == that.getEntities
      case _ => false
    }
    override def hashCode: Int = entities.hashCode // For compatibility with the OWL API.
  }
private[this] class OWLNamedIndividualNodeImpl(private val peer: TaxonomyNode[SequoiaOWLNamedIndividual]) extends Node[OWLNamedIndividual] {
    private[this] val entities = new OWLNamedIndividualSetWrapper(peer.equivalentObjects)
    override def getSize: Int = peer.equivalentObjects.size
    override def isSingleton: Boolean = peer.equivalentObjects.size == 1
    override def isBottomNode: Boolean = peer.equivalentObjects.contains(IRI.owlNothing)
    override def isTopNode: Boolean = peer.equivalentObjects.contains(IRI.owlThing)
    override def contains(entity: OWLNamedIndividual): Boolean = entities.contains(entity)
    override def getRepresentativeElement: OWLNamedIndividual = EntityConverter.toOWLNamedIndividual(peer.equivalentObjects.representative)
    override def getEntities: jSet[OWLNamedIndividual] = entities
    override def getEntitiesMinus(e: OWLNamedIndividual): jSet[OWLNamedIndividual] =
      if (contains(e)) new java.util.HashSet(new OWLNamedIndividualSetExcludeWrapper(peer.equivalentObjects, OWLConverter.convert(e.getIRI))) else entities // WORKAROUND for Protege bug.
    override def getEntitiesMinusBottom: jSet[OWLNamedIndividual] =
      if (isBottomNode) new java.util.HashSet(new OWLNamedIndividualSetExcludeWrapper(peer.equivalentObjects, IRI.owlNothing)) else entities // WORKAROUND for Protege bug.
    override def getEntitiesMinusTop: jSet[OWLNamedIndividual] =
      if (isTopNode) new java.util.HashSet(new OWLNamedIndividualSetExcludeWrapper(peer.equivalentObjects, IRI.owlThing)) else entities // WORKAROUND for Protege bug.
    override def iterator: jIterator[OWLNamedIndividual] = new jIterator[OWLNamedIndividual] {
      private[this] val underlying = peer.equivalentObjects.iterator
      override def next: OWLNamedIndividual = EntityConverter.toOWLNamedIndividual(underlying.next)
      override def hasNext: Boolean = underlying.hasNext
    }
    override def equals(o: Any): Boolean = o match {
      case that: OWLNamedIndividualNodeImpl =>
        this.peer.equivalentObjects == that.peer.equivalentObjects
      case that: Node[_] =>
        this.getSize == that.getSize && this.getEntities == that.getEntities
      case _ => false
    }
    override def hashCode: Int = entities.hashCode // For compatibility with the OWL API.
  }


  def convertClassNode(node: TaxonomyNode[SequoiaOWLClass]): Node[OWLClass] = cache.getOrElseUpdate(node, new OWLClassNodeImpl(node))
  def convertNamedIndividualNode(node: TaxonomyNode[SequoiaOWLNamedIndividual]): Node[OWLNamedIndividual] =  cache2.getOrElseUpdate(node, new OWLNamedIndividualNodeImpl(node))


  private[this] class OWLClassNodeSetWrapper(peer: TaxonomyNodeSet[SequoiaOWLClass]) extends jAbstractSet[Node[OWLClass]] {
    override def size: Int = peer.size
    override def isEmpty: Boolean = peer.isEmpty
    override def contains(o: Any): Boolean =
      try {
        val set = o.asInstanceOf[Node[OWLClass]]
        val targetSize = set.getSize
        peer.exists( node => node.equivalentObjects.size == targetSize && {
          val it = set.iterator
          var res = true
          while (res && it.hasNext) res = node.equivalentObjects.contains(OWLConverter.convert(it.next.getIRI))
          res
        })
      } catch { case _: ClassCastException => false }
    override def iterator: jIterator[Node[OWLClass]] = new jIterator[Node[OWLClass]] {
      private[this] val underlying = peer.iterator
      override def next: Node[OWLClass] = convertClassNode(underlying.next())
      override def hasNext: Boolean = underlying.hasNext
    }
    override def add(e: Node[OWLClass]): Boolean = throw new UnsupportedOperationException
    override def clear: Unit = throw new UnsupportedOperationException
    override def addAll(c: jCollection[_ <: Node[OWLClass]]): Boolean = throw new UnsupportedOperationException
    override def retainAll(c: jCollection[_]): Boolean = throw new UnsupportedOperationException
    override def remove(o: Any): Boolean = throw new UnsupportedOperationException
    override def removeAll(c: jCollection[_]): Boolean = throw new UnsupportedOperationException
    // Safe to cache hashCode for performance because both peer will not be mutated.
    private[this] var hashCodeCached: Int = 0
    override def hashCode: Int = {
      if (hashCodeCached == 0) hashCodeCached = super.hashCode
      hashCodeCached
    }
  }

  private[this] class OWLNamedIndividualNodeSetWrapper(peer: TaxonomyNodeSet[SequoiaOWLNamedIndividual]) extends jAbstractSet[Node[OWLNamedIndividual]] {
    override def size: Int = peer.size
    override def isEmpty: Boolean = peer.isEmpty
    override def contains(o: Any): Boolean =
      try {
        val set = o.asInstanceOf[Node[OWLNamedIndividual]]
        val targetSize = set.getSize
        peer.exists( node => node.equivalentObjects.size == targetSize && {
          val it = set.iterator
          var res = true
          while (res && it.hasNext) res = node.equivalentObjects.contains(OWLConverter.convert(it.next.getIRI))
          res
        })
      } catch { case _: ClassCastException => false }
    override def iterator: jIterator[Node[OWLNamedIndividual]] = new jIterator[Node[OWLNamedIndividual]] {
      private[this] val underlying = peer.iterator
      override def next: Node[OWLNamedIndividual] = convertNamedIndividualNode(underlying.next())
      override def hasNext: Boolean = underlying.hasNext
    }
    override def add(e: Node[OWLNamedIndividual]): Boolean = throw new UnsupportedOperationException
    override def clear: Unit = throw new UnsupportedOperationException
    override def addAll(c: jCollection[_ <: Node[OWLNamedIndividual]]): Boolean = throw new UnsupportedOperationException
    override def retainAll(c: jCollection[_]): Boolean = throw new UnsupportedOperationException
    override def remove(o: Any): Boolean = throw new UnsupportedOperationException
    override def removeAll(c: jCollection[_]): Boolean = throw new UnsupportedOperationException
    // Safe to cache hashCode for performance because both peer will not be mutated.
    private[this] var hashCodeCached: Int = 0
    override def hashCode: Int = {
      if (hashCodeCached == 0) hashCodeCached = super.hashCode
      hashCodeCached
    }
  }

  private[this] class FlattenedOWLClassNodeSet(nodeSet: TaxonomyNodeSet[SequoiaOWLClass]) extends jAbstractSet[OWLClass] {
    override val size: Int = nodeSet.iterator.foldLeft(0){ (acc, node) => acc + node.equivalentObjects.size }
    override def isEmpty: Boolean = size == 0
    override def contains(o: Any): Boolean = o match {
      case o: OWLClass => nodeSet exists { node => node.equivalentObjects contains OWLConverter.convert(o.getIRI)}
      case _ => false
    }
    override def iterator: jIterator[OWLClass] = new jIterator[OWLClass] {
      private[this] val iterators: Iterator[TaxonomyNode[SequoiaOWLClass]] = nodeSet.iterator
      private[this] var currentIterator: Iterator[IRI] =
        if (!iterators.hasNext) Iterator.empty
        else iterators.next.equivalentObjects.iterator
      // Call this before next and hasNext to ensure that the current iterator is not exhausted.
      private[this] def updateCurrentIterator: Unit =
        while (!currentIterator.hasNext && iterators.hasNext) {
          currentIterator = iterators.next.equivalentObjects.iterator
        }
      def hasNext: Boolean = {
        updateCurrentIterator
        currentIterator.hasNext
      }
      def next: OWLClass = {
        updateCurrentIterator
        EntityConverter.toOWLClass(currentIterator.next)
      }
    }
    override def add(e: OWLClass): Boolean = throw new UnsupportedOperationException
    override def addAll(c: jCollection[_ <: OWLClass]): Boolean = throw new UnsupportedOperationException
    override def clear: Unit = throw new UnsupportedOperationException
    override def remove(o: Any): Boolean = throw new UnsupportedOperationException(s"Cannot remove $o.")
    override def removeAll(c: jCollection[_]): Boolean = throw new UnsupportedOperationException
    override def retainAll(c: jCollection[_]): Boolean = throw new UnsupportedOperationException
    // Safe to cache hashCode for performance because both peer will not be mutated.
    private[this] var hashCodeCached: Int = 0
    override def hashCode: Int = {
      if (hashCodeCached == 0) hashCodeCached = super.hashCode
      hashCodeCached
    }
  }

  private[this] class FlattenedOWLNamedIndividualNodeSet(nodeSet: TaxonomyNodeSet[SequoiaOWLNamedIndividual]) extends jAbstractSet[OWLNamedIndividual] {
    override val size: Int = nodeSet.iterator.foldLeft(0){ (acc, node) => acc + node.equivalentObjects.size }
    override def isEmpty: Boolean = size == 0
    override def contains(o: Any): Boolean = o match {
      case o: OWLNamedIndividual=> nodeSet exists { node => node.equivalentObjects contains OWLConverter.convert(o.getIRI)}
      case _ => false
    }
    override def iterator: jIterator[OWLNamedIndividual] = new jIterator[OWLNamedIndividual] {
      private[this] val iterators: Iterator[TaxonomyNode[SequoiaOWLNamedIndividual]] = nodeSet.iterator
      private[this] var currentIterator: Iterator[IRI] =
        if (!iterators.hasNext) Iterator.empty
        else iterators.next.equivalentObjects.iterator
      // Call this before next and hasNext to ensure that the current iterator is not exhausted.
      private[this] def updateCurrentIterator: Unit =
        while (!currentIterator.hasNext && iterators.hasNext) {
          currentIterator = iterators.next.equivalentObjects.iterator
        }
      def hasNext: Boolean = {
        updateCurrentIterator
        currentIterator.hasNext
      }
      def next: OWLNamedIndividual = {
        updateCurrentIterator
        EntityConverter.toOWLNamedIndividual(currentIterator.next)
      }
    }
    override def add(e: OWLNamedIndividual): Boolean = throw new UnsupportedOperationException
    override def addAll(c: jCollection[_ <: OWLNamedIndividual]): Boolean = throw new UnsupportedOperationException
    override def clear: Unit = throw new UnsupportedOperationException
    override def remove(o: Any): Boolean = throw new UnsupportedOperationException(s"Cannot remove $o.")
    override def removeAll(c: jCollection[_]): Boolean = throw new UnsupportedOperationException
    override def retainAll(c: jCollection[_]): Boolean = throw new UnsupportedOperationException
    // Safe to cache hashCode for performance because both peer will not be mutated.
    private[this] var hashCodeCached: Int = 0
    override def hashCode: Int = {
      if (hashCodeCached == 0) hashCodeCached = super.hashCode
      hashCodeCached
    }
  }

    /** This class is the impliementation of  NodeSet[OWLClass] */
  private[this] class OWLClassNodeSetImpl(private val peer: TaxonomyNodeSet[SequoiaOWLClass]) extends NodeSet[OWLClass] {
    private[this] val nodes = new OWLClassNodeSetWrapper(peer)
    override def isEmpty: Boolean = peer.isEmpty
    override def isSingleton: Boolean = peer.size == 1
    override def isTopSingleton: Boolean = isSingleton && peer.exists(node => node.equivalentObjects.contains(IRI.owlThing))
    override def isBottomSingleton: Boolean = isSingleton && peer.exists(node => node.equivalentObjects.contains(IRI.owlNothing))
    override def containsEntity(e: OWLClass): Boolean = peer.exists(node => node.equivalentObjects.contains(OWLConverter.convert(e.getIRI)))
    override def getNodes: jSet[Node[OWLClass]] = nodes
    override def getFlattened: jSet[OWLClass] = new java.util.HashSet(new FlattenedOWLClassNodeSet(peer)) // WORKAROUND for Protege bug.
    override def iterator: jIterator[Node[OWLClass]] = getNodes.iterator
    override def equals(o: Any): Boolean = o match {
      case that: OWLClassNodeSetImpl => this.peer == that.peer
      case that: NodeSet[_] => nodes == that.getNodes
      case _ => false
    }
    override def hashCode: Int = nodes.hashCode // For compatibility with the OWL API.
  }

  /** This class is the implementation of  NodeSet[OWLNamedIndividual] */
  private[this] class OWLNamedIndividualNodeSetImpl(private val peer: TaxonomyNodeSet[SequoiaOWLNamedIndividual]) extends NodeSet[OWLNamedIndividual] {
    private[this] val nodes = new OWLNamedIndividualNodeSetWrapper(peer)
    override def isEmpty: Boolean = peer.isEmpty
    override def isSingleton: Boolean = peer.size == 1
    override def isTopSingleton: Boolean = false
    override def isBottomSingleton: Boolean = false
    override def containsEntity(e: OWLNamedIndividual): Boolean = {
      val nominalConcept: IRI =  IRI.nominalConcept(OWLConverter.convert(e.getIRI).fullIriAsString)
      peer.exists(node => node.equivalentObjects.contains(nominalConcept))
    }
    override def getNodes: jSet[Node[OWLNamedIndividual]] = nodes
    override def getFlattened: jSet[OWLNamedIndividual] = new java.util.HashSet(new FlattenedOWLNamedIndividualNodeSet(peer)) // WORKAROUND for Protege bug.
    override def iterator: jIterator[Node[OWLNamedIndividual]] = getNodes.iterator
    override def equals(o: Any): Boolean = o match {
      case that: OWLNamedIndividualNodeSetImpl => this.peer == that.peer
      case that: NodeSet[_] => nodes == that.getNodes
      case _ => false
    }
    override def hashCode: Int = nodes.hashCode // For compatibility with the OWL API.
  }


  def convertClassNodes(nodeSet: TaxonomyNodeSet[SequoiaOWLClass]): NodeSet[OWLClass] = new OWLClassNodeSetImpl(nodeSet)
  def convertIndividualNodes(nodeSet: TaxonomyNodeSet[SequoiaOWLNamedIndividual]): NodeSet[OWLNamedIndividual] = new OWLNamedIndividualNodeSetImpl(nodeSet)

  def convert(e: SequoiaException): OWLRuntimeException = ExceptionConverter.convert(e)

  def convert(e: SequoiaRuntimeException): OWLRuntimeException = ExceptionConverter.convert(e)

}