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

import com.sequoiareasoner.kernel.index._
import com.sequoiareasoner.kernel.clauses.{CentralVariable, _}
import com.sequoiareasoner.arrayops._
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.structural.DLOntology

import scala.annotation.tailrec

/** Provides an implementation of the Hyper, Nom, Pred and Eq rules from the calculus, independent of any particular context. */

object Rules {

  /** ----------------------------- UTILITY METHODS ------------------------------------------- */

  /** Method to remove duplicates in an array of literals, but only until index _toIndex_ */
  @inline private[this] def removeConsecutiveDuplicates[L <: Literal](arr: Array[L], toIndex: Int, @inline builder: Int => Array[L]): Array[L] = {
    arr.take(toIndex).distinct // ++ arr.drop(toIndex)
  }

  /** Method to sort an array up to certain index. Generally used because some elements of the array at the end will be
    * nulls. */
  private[this] def sortUnique[L <: Literal](arr: Array[L], toIndex: Int, @inline builder: Int => Array[L]): Array[L] = {
    java.util.Arrays.sort(arr.asInstanceOf[Array[AnyRef]], 0, toIndex)
    removeConsecutiveDuplicates(arr, toIndex, builder)
  }

  /** Determine whether there is a Central Substitution that applied to p1 produces p2 */
  private[this] def canUnify(p1: Predicate, p2: Predicate): Boolean = (p1, p2) match {
    case (Concept(iri1, CentralVariable), Concept(iri2, CentralVariable)) =>
      iri1 == iri2
    case (Role(iri1, s1, t1), Role(iri2, s2, t2)) =>
      iri1 == iri2 && {
        (s1, s2) match {
          case (CentralVariable, CentralVariable) => true
          case (CentralVariable, _) => false
          case _ => true
        }
      } && {
        (t1, t2) match {
          case (CentralVariable, CentralVariable) => true
          case (CentralVariable, _) => false
          case _ => true
        }
      }
    case _ => false
  }

  /** Returns true iff sigma is either such that or can be extended so that `p1 \sigma = p2` holds. */
  private[this] def unify(sigma: CentralSubstitution, p1: Predicate, p2: Predicate): Boolean = (p1, p2) match {
    case (Concept(iri1, CentralVariable), Concept(iri2, CentralVariable)) =>
      iri1 == iri2
    case (Role(iri1, s1, t1), Role(iri2, s2, t2)) =>
      /* TODO: an ordering on neighbour variables to avoid repetition in the case of, for example,
       * R(x, z1) AND R(x, z2) -> z1 == z2.
       * We assume that if an ontology clause contains repeated predicates in the body, then the clause is symmetric in
       * the variables occurring in those predicates.
       */
      iri1 == iri2 && sigma.addIfPossible(s1, s2) && sigma.addIfPossible(t1, t2)
    case _ => false
  }

  /** ------------------------------------- CALCULUS RULES -------------------------------------- */


  /* Here we use the assumption that each ontology clause is symmetric in neighbour variables (*).
   * To see why this invariant exists, consider the following clauses:
   *
   *                         -> R(x, f(x))  (1)
   *                         -> R(x, g(x))  (2)
   *   R(x, z1) AND R(x, z2) -> C(z2)       (3)
   *                         -> C(f(x))     (4)
   *                         -> C(g(x))     (5)
   *
   * Clause (3) is not symmetric in neighbour variables, and thus violates (*). To derive (4) and (5) from (1), (2) and
   * (3), the head predicate of (1) must be a candidate for unification at both the first and second predicate in the
   * body of (3) even though a match is found at the first predicate. (Similarly for the head predicate of (2).)
   * However, if each clause is symmetric in neighbour variables, then unification tests between a head predicate and
   * the body predicates of another clause can stop after the first match is found.
   */

  def Nom(max: Predicate,
          sideConditionToUse: ContextClause,
          ontologyClause: OntologyClause,
          unaryAtomPredicate: Option[Int],
          auxiliaryClause: Option[ContextClause],
          ontology: DLOntology,
          ordering: ContextLiteralOrdering,
          resultsBuffer: UnprocessedDeque): Unit = {
    /** Find out maximum number restriction in predicate */
    val maxNumber = ontologyClause.body.foldLeft(0: Int) { (n: Int, p: Predicate) =>
      p match {
        case Role(_, _, NeighbourVariable(i)) => n max i
        case _ => throw new IllegalStateException(s"There should be no predicates other than roles of the form S(x,z_i) in the body of the clause")
      }
    }
    /** Generate new clause */
    val newBody = sideConditionToUse.body ++ auxiliaryClause.foldLeft(Array[Predicate]())((bod, clau) => bod ++ clau.body)
    val equalities: Array[Literal] = {
      (for (i <- (1 until maxNumber).toArray) yield Equality(CentralVariable, Term.getArtificialNominalFor(
        max.asInstanceOf[Role].s.asInstanceOf[Constant].id, max.asInstanceOf[Role].iri.uid, unaryAtomPredicate.getOrElse(0), i))).toArray
    }
    val newHead = sideConditionToUse.head.filterNot(lit => lit == max) ++
      auxiliaryClause.foldLeft(Array[Literal]())((hea, clau) => hea ++ clau.head.filterNot(lit => unaryAtomPredicate.exists { x => lit == Concept(IRI(x), max.asInstanceOf[Role].s)(ontology) })) ++ equalities

    val conclusion = ContextClause(newBody, newHead)(ordering)
    if (resultsBuffer.removeRedundant(conclusion)) resultsBuffer.addFirst(conclusion)
  }

  /** Implementation of the Hyper rule from the calculus, with predicate _max_ selected on context clause
    * _sideConditionToUse_, _ontologyClause_ selected as the ontology clause to be applied, and
    * _contextClauseLookup_ to retrieve the other clauses in the context. */
  def Hyper(max: Predicate,
            sideConditionToUse: ContextClause,
            contextClauseLookup: Predicate => IndexedSequence[ContextClause],
            ontologyClause: OntologyClause,
            ordering: ContextLiteralOrdering,
            cutting: EqualityOptimization,
            rootContext: Boolean = false,
            isNothing: Literal => Boolean,
            resultsBuffer: UnprocessedDeque,
            debugFlag: Boolean = false): Unit = {


    /** This is for debugging */
    def isSelectedPredicate(predicate: Predicate): Boolean =
      predicate match {
        case Concept(iri, _) if iri.toString.contains("galen#pathological") => true
        case _ => false
      }

    def selectedPredicates(clause: ContextClause) = if (rootContext) clause.maxAndSecondMaxHeadPredicates else clause.maxHeadPredicates

    /** Step 1: Identify and index all possible applications of Hyper rule given the initial conditions */

    val ontologyClauseBodyLength = ontologyClause.body.length
    val sideConditionIndexedSequence = IndexedSequence(sideConditionToUse)
    var haveUsedSideCondition = false
    /** The following array contains an entry for each predicate in the body of the ontology clause. Each such entry
      * contains every possible clause in the context that can be resolved with the ontology clause.
      */
    val arrayContextClauses = new Array[IndexedSequence[ContextClause]](ontologyClauseBodyLength)
    crange(0, ontologyClauseBodyLength) { i =>

      /** For each body predicate in the Ontology clause, check if we can use the main context clause (called
        * `side condition`). */
      val useSideCondition = !haveUsedSideCondition && canUnify(ontologyClause.body(i), max)
      if (useSideCondition) {
        arrayContextClauses(i) = sideConditionIndexedSequence
        haveUsedSideCondition = true
      } else {
        /** If we do not use the `side condition`, then we fill the `arrayContextClauses` with all possible candidates. */
        val candidates: IndexedSequence[ContextClause] = contextClauseLookup(ontologyClause.body(i))
        // if (debugFlag && isSelectedPredicate(max)) for (candidate <- candidates) System.out.println("Candidate identified: " + candidate) //DEBUG
        if (candidates.isEmpty) return
        arrayContextClauses(i) = candidates
      }
    }
    if (!haveUsedSideCondition) throw new AssertionError


    /** Step 2, apply rule for each candidate  */

    //TODO: REDO THIS IMPLEMENTATION IN A FUNCTIONAL WAY

    /** The following two counters, with the increment functions, essentially range over all possible groups of clauses
      * that are candidates for an application of the Hyper rule */

    /** Outer counter is an array where the k-th element ranges over the set of candidate context clauses
      * that can resolve with predicate in position k in the body of the ontology clause */
    val outerCounter = new Array[Int](ontologyClauseBodyLength)
    /** Inner counter is an array where the k-th element ranges over the set of maximal predicates in the k-position
      * candidate context clause that currently the k-th pointer in outerCounter is pointing at. */
    val innerCounter = new Array[Int](ontologyClauseBodyLength)

    /** This method increases the counter at k-th index by 1, unless the resulting value would
      * surpass the number of context clause candidates for position k, in which the counter is reset and we call this
      * function on the k+1-th counter. */
    @inline
    @tailrec def incOuterCounter(k: Int = 0): Boolean =
      (k < ontologyClauseBodyLength) && {
        (outerCounter(k) + 1 < arrayContextClauses(k).length && {
          outerCounter(k) += 1; true
        }) || {
          outerCounter(k) = 0; incOuterCounter(k + 1)
        }
      }

    /** Same as above, but now the counter is bounded by the number of predicates in a context clause stored in position
      * outerCounter(k) of the array */
    @inline
    @tailrec def incInnerCounter(k: Int = 0): Boolean =
      (k < ontologyClauseBodyLength) && {
        (innerCounter(k) + 1 < selectedPredicates(arrayContextClauses(k)(outerCounter(k))).length && {
          innerCounter(k) += 1; true
        }) || {
          innerCounter(k) = 0; incInnerCounter(k + 1)
        }
      }

    do {

      do {
        val sigma = new CentralSubstitution(scala.collection.mutable.Map[Term, Term]())
        /** Setp 1: Check if the current candidate unifies with the ontology clause */
        val isUnifiable =
          cforall(0, ontologyClauseBodyLength) { i: Int =>
            val contextClauseMax: Predicate = if (rootContext) arrayContextClauses(i)(outerCounter(i)).maxAndSecondMaxHeadPredicates(innerCounter(i))
            else arrayContextClauses(i)(outerCounter(i)).maxHeadPredicates(innerCounter(i))
            val bodyCandidate: Predicate = ontologyClause.body(i)
            unify(sigma, bodyCandidate, contextClauseMax)
          }

        /** If _isUnifiable_ is false, move to the next candiate */
        if (isUnifiable) {
          /** Buffer for head of the derived clause */
          val headBufferLength: Int =
            ontologyClause.head.length + csum(0, ontologyClauseBodyLength) { i => arrayContextClauses(i)(outerCounter(i)).head.length - 1 }
          val headBuffer = new Array[Literal](headBufferLength)

          /** Step 2: fill the first part of the buffer, with the head of the ontology clause. */

          var w = 0
          /** Variable determining if the derived clause is tautological */
          var isRedundant: Boolean = false
          /* All literals are predicates in the case of the Pred rule so contextual literal cutting cannot apply, and
           * nor can the clause be redundant due to equations in the head. */
          var i = 0
          while (!isRedundant && i < ontologyClause.head.length) {
            val literal: Literal = ontologyClause.head(i)
            // System.out.println("Applying substitution " + sigma + " to literal " + literal ) // DEBUG
            val literalSigma: Literal = literal.applySubstitution(sigma)
            if (literalSigma.isValidEquation) {
              isRedundant = true
            } else if (!literalSigma.isInvalidEquation && !cutting.shouldCut(literalSigma) && !isNothing(literalSigma)) {
              headBuffer(w) = literalSigma
              w += 1
            }
            i += 1
          }

          /** Continue only if the tautological clause is not redundant. */

          /** Step 3: fill the remainder of the buffer, with the heads of the context clauses */

          if (!isRedundant) {
            crange(0, ontologyClauseBodyLength) { i =>
              val j = outerCounter(i)
              val k = innerCounter(i)
              val head = arrayContextClauses(i)(j).head
              cforeach(head) { literal =>
                if (rootContext) {
                  if (arrayContextClauses(i)(j).maxAndSecondMaxHeadPredicates(k).compare(literal) != 0) {
                    headBuffer(w) = literal
                    w += 1
                  }
                } else {
                  if (arrayContextClauses(i)(j).maxHeadPredicates(k).compare(literal) != 0) {
                    headBuffer(w) = literal
                    w += 1
                  }
                }
              }
            }
            val newHead = sortUnique(headBuffer, w, ArrayBuilders.literalArrayBuilder)

            /** Step 4: build the body for the newly derived clause */

            val bodyBufferLength: Int = csum(0, ontologyClauseBodyLength) { i => arrayContextClauses(i)(outerCounter(i)).body.length }
            val bodyBuffer = new Array[Predicate](bodyBufferLength)
            w = 0
            crange(0, ontologyClauseBodyLength) { i =>
              val j = outerCounter(i)
              cforeach(arrayContextClauses(i)(j).body) { predicate =>
                bodyBuffer(w) = predicate
                w += 1
              }
            }
            val newBody = sortUnique(bodyBuffer, w, ArrayBuilders.predicateArrayBuilder)

            /** Step 5: Add clause to a buffer of results if it is not redundant (and remove clauses made reundant). */

            val conclusion = ContextClause(newBody, newHead)(ordering)
            if (resultsBuffer.removeRedundant(conclusion)) {
              // if (debugFlag && isSelectedPredicate(max)) System.out.println("Conclusion obtained: " + conclusion)
              resultsBuffer.addFirst(conclusion)
            }

          }
        }

      } while (incInnerCounter())

    } while (incOuterCounter())
  }


  /** Implementation of the second part of Pred rule from the calculus, where a clause _predClause_ has been
    * propagated from a successor by the first part of the Pred rule */
  def Pred(contextClauseLookup: Predicate => IndexedSequence[ContextClause],
           predClause: PredClause,
           ordering: ContextLiteralOrdering,
           resultsBuffer: UnprocessedDeque): Unit = {
    val predClauseBodyLength = predClause.body.length
    /** Because the substitution has been already applied in the pred clause body, no unification is required. */
    val arrayContextClauses = new Array[IndexedSequence[ContextClause]](predClauseBodyLength)
    crange(0, predClauseBodyLength) { i =>
      val candidates = contextClauseLookup(predClause.body(i))
      arrayContextClauses(i) = candidates
      if (candidates.isEmpty) return
    }

    val outerCounter = new Array[Int](predClauseBodyLength)

    @inline
    @tailrec def incOuterCounter(k: Int = 0): Boolean =
      (k < predClauseBodyLength) && {
        (outerCounter(k) + 1 < arrayContextClauses(k).length && {
          outerCounter(k) += 1; true
        }) || {
          outerCounter(k) = 0; incOuterCounter(k + 1)
        }
      }

    do {
      // Set the buffer to the maximum length of the head of the new clause.
      val headBufferLength: Int =
        predClause.head.length + csum(0, predClauseBodyLength) { i => arrayContextClauses(i)(outerCounter(i)).head.length - 1 }
      val headBuffer = new Array[Literal](headBufferLength)
      // Head of a pred clause contains only predicates, so neither the Ineq rule nor contextual literal cutting can apply.
      var w = 0
      cforeach(predClause.head) { literal =>
        headBuffer(w) = literal
        w += 1
      }
      // Copy heads of clauses excluding matched predicates.
      crange(0, predClauseBodyLength) { i =>
        val j = outerCounter(i)
        val predClauseBodyPredicate = predClause.body(i)
        val head = arrayContextClauses(i)(j).head
        cforeach(head) { literal =>
          if (literal.compare(predClauseBodyPredicate) != 0) {
            headBuffer(w) = literal
            w += 1
          }
        }
      }
      val newHead = sortUnique(headBuffer, w, ArrayBuilders.literalArrayBuilder)

      val bodyBufferLength: Int = csum(0, predClauseBodyLength) { i => arrayContextClauses(i)(outerCounter(i)).body.length }
      val bodyBuffer = new Array[Predicate](bodyBufferLength)
      w = 0
      crange(0, predClauseBodyLength) { i =>
        val j = outerCounter(i)
        cforeach(arrayContextClauses(i)(j).body) { predicate =>
          bodyBuffer(w) = predicate
          w += 1
        }
      }
      val newBody = sortUnique(bodyBuffer, w, ArrayBuilders.predicateArrayBuilder)

      val conclusion = ContextClause(newBody, newHead)(ordering)

      if (resultsBuffer.removeRedundant(conclusion)) resultsBuffer.addFirst(conclusion)

    } while (incOuterCounter())
  }

  /** Given a nominal o, a set of context clauses in a root context contexClauseLookup, a clause of the form A(o) ^ B(o) ^  ... -> C(x) v D(x) ,
    * where A(x) is the core of this context,
    * and the auxiliary arguments, this rule searches for clauses of the form gamma -> delta v x = o, which essentially
    * corresponds to clauses with A(o) maximal, since we assume that a context clause T -> A(x) exists;
    * and produces * gamma -> delta v C(x) v D(x) v heads of other clauses */
  def Close(contextClauseEqualityLookup: Equality => IndexedSequence[ContextClause],
            contextClausePredicateLookup: Predicate => IndexedSequence[ContextClause],
            corePredicate: IRI,
            predClause: PredClause,
            nominal: Constant,
            ordering: ContextLiteralOrdering,
            resultsBuffer: UnprocessedDeque): Unit = {
    //val predClauseBodyLength = predClause.body.length
    // Because the substitution has been already applied in the pred clause body, no unification is required.
    // Also, notice that the pred clause body STILL contains B(o), with B(x) the context core
    /** First step: remove the B(o) atom from the body */
    val predClauseBodyLength: Int = if (predClause.body.isEmpty) predClause.body.length; else predClause.body.length - 1
    val transformedBody: Array[Predicate] = new Array[Predicate](predClauseBodyLength)
    var foundAtomToRemove: Boolean = false
    crange(0, transformedBody.length) { i =>
            if (foundAtomToRemove) transformedBody(i-1) = predClause.body(i)
            else if (predClause.body(i).iri == corePredicate) {
              foundAtomToRemove = true
            } else transformedBody(i) = predClause.body(i)
    }
    /** Then we proceed */
    val arrayContextClauses = new Array[IndexedSequence[ContextClause]](predClauseBodyLength + 1)
    crange(0, predClauseBodyLength) { i =>
      val candidates = contextClausePredicateLookup(transformedBody(i))
      arrayContextClauses(i) = candidates
      if (candidates.isEmpty)  return
    }
    val candidates = new ArrayIndexedSequence[ContextClause](8, ArrayBuilders.contextClauseArrayBuilder)
    for (clause <- contextClauseEqualityLookup(Equality(CentralVariable, nominal))) candidates += clause
    for (clause <- contextClauseEqualityLookup(Equality(nominal, CentralVariable))) candidates += clause
    arrayContextClauses(predClauseBodyLength) = candidates
    if (candidates.isEmpty) return

    val outerCounter = new Array[Int](predClauseBodyLength + 1)

    @inline
    @tailrec def incOuterCounter(k: Int = 0): Boolean =
      (k < predClauseBodyLength + 1) && {
        (outerCounter(k) + 1 < arrayContextClauses(k).length && {
          outerCounter(k) += 1; true
        }) || {
          outerCounter(k) = 0; incOuterCounter(k + 1)
        }
      }

    do {
      // Set the buffer to the maximum length of the head of the new clause.
      val headBufferLength: Int =
        predClause.head.length + csum(0, predClauseBodyLength + 1) { i => arrayContextClauses(i)(outerCounter(i)).head.length - 1 }
      val headBuffer = new Array[Literal](headBufferLength)
      // Head of a pred clause contains only predicates, so neither the Ineq rule nor contextual literal cutting can apply.
      var w = 0
      cforeach(predClause.head) { literal =>
        headBuffer(w) = literal
        w += 1
      }
      // Copy heads of clauses excluding matched predicates.
      crange(0, predClauseBodyLength) { i =>
        val j = outerCounter(i)
        val predClauseBodyPredicate = transformedBody(i)
        val head = arrayContextClauses(i)(j).head
        cforeach(head) { literal =>
          if (literal.compare(predClauseBodyPredicate) != 0) {
            headBuffer(w) = literal
            w += 1
          }
        }
      }
      val finalIndex = predClauseBodyLength
      val j = outerCounter(finalIndex)
        val equality1 = Equality(CentralVariable,nominal)
        val equality2 = Equality(nominal, CentralVariable)
        val head = arrayContextClauses(finalIndex)(j).head
        cforeach(head) { literal =>
          //Compare all head literals, select only those distinct from both equalities.
          if (literal.compare(equality1) != 0 && literal.compare(equality2) != 0) {
            headBuffer(w) = literal
            w += 1
          }
        }
      val newHead = sortUnique(headBuffer, w, ArrayBuilders.literalArrayBuilder)

      // Copy bodies of all clauses used as side premises.
      val bodyBufferLength: Int = csum(0, predClauseBodyLength + 1 ) { i => arrayContextClauses(i)(outerCounter(i)).body.length }
      val bodyBuffer = new Array[Predicate](bodyBufferLength)
      w = 0
      crange(0, predClauseBodyLength + 1) { i =>
        val j = outerCounter(i)
        cforeach(arrayContextClauses(i)(j).body) { predicate =>
          bodyBuffer(w) = predicate
          w += 1
        }
      }
      val newBody = sortUnique(bodyBuffer, w, ArrayBuilders.predicateArrayBuilder)


      val conclusion = ContextClause(newBody, newHead)(ordering)
      if (resultsBuffer.removeRedundant(conclusion)) resultsBuffer.addFirst(conclusion)

    } while (incOuterCounter())
  }


  // OLD: delete after a while if not needed
  //  def Close(nominal: Constant,
  //            contextClauseLookup: Equality => IndexedSequence[ContextClause],
  //            newClause: PredClause,
  //            ordering: ContextLiteralOrdering,
  //            resultsBuffer: UnprocessedDeque): Unit = {
  //      for (clause <- contextClauseLookup(Equality(CentralVariable,nominal))) {
  //        val conclusion = ContextClause(clause.body, (newClause.head ++ clause.head.filter(l => (l != Equality(CentralVariable, nominal)) && (l != Equality(nominal, CentralVariable)))).distinct)(ordering)
  //        if (resultsBuffer.removeRedundant(conclusion)) resultsBuffer.addFirst(conclusion)
  //      }
  //      for (clause <- contextClauseLookup(Equality(nominal,CentralVariable))) {
  //        val conclusion = ContextClause(clause.body, (newClause.head ++ clause.head.filter(l => (l != Equality(CentralVariable, nominal)) && (l != Equality(nominal, CentralVariable)))).distinct)(ordering)
  //        if (resultsBuffer.removeRedundant(conclusion)) resultsBuffer.addFirst(conclusion)
  //      }
//   }



  /** Implementation of the RootPred rule from the calculus.
    *
    * @param contextClauseLookup  function from a predicate `p` to the clauses containing `p` maximally in the head
    * @param predClause           clause pushed back from the successor context to this predecessor context (with substitution applied to body and head)
    * @param ordering             ordering on literals used in this predecessor context
    * @param resultsBuffer        buffer to accumulate results
    */
  def RootPred(contextClauseLookup: Predicate => IndexedSequence[ContextClause],
           predClause: PredClause,
           ordering: ContextLiteralOrdering,
           resultsBuffer: UnprocessedDeque): Unit = {

    val predClauseBodyLength = predClause.body.length
    // Because the substitution has been already applied in the pred clause body, no unification is required.
    val arrayContextClauses = new Array[IndexedSequence[ContextClause]](predClauseBodyLength)
    crange(0, predClauseBodyLength) { i =>
      val candidates = contextClauseLookup(predClause.body(i))
      arrayContextClauses(i) = candidates
      if (candidates.isEmpty) return
    }

    val outerCounter = new Array[Int](predClauseBodyLength)
    @inline @tailrec def incOuterCounter(k: Int = 0): Boolean =
      (k < predClauseBodyLength) && {
        (outerCounter(k) + 1 < arrayContextClauses(k).length && { outerCounter(k) += 1; true }) ||
          { outerCounter(k) = 0; incOuterCounter(k + 1) }
      }

    do {
      // Set the buffer to the maximum length of the head of the new clause.
      val headBufferLength: Int =
        predClause.head.length + csum (0, predClauseBodyLength) { i => arrayContextClauses(i)(outerCounter(i)).head.length - 1 }
      val headBuffer = new Array[Literal](headBufferLength)
      // Head of a pred clause contains only predicates, so neither the Ineq rule nor contextual literal cutting can apply.
      var w = 0
      cforeach (predClause.head) { literal =>
        headBuffer(w) = literal
        w += 1
      }
      // Copy heads of clauses excluding matched predicates.
      crange (0, predClauseBodyLength) { i =>
        val j = outerCounter(i)
        val predClauseBodyPredicate = predClause.body(i)
        val head = arrayContextClauses(i)(j).head
        cforeach (head) { literal =>
          if (literal.compare(predClauseBodyPredicate) != 0) {
            headBuffer(w) = literal
            w += 1
          }
        }
      }
      val newHead = sortUnique(headBuffer, w, ArrayBuilders.literalArrayBuilder)

      val bodyBufferLength: Int = csum (0, predClauseBodyLength) { i => arrayContextClauses(i)(outerCounter(i)).body.length }
      val bodyBuffer = new Array[Predicate](bodyBufferLength)
      w = 0
      crange (0, predClauseBodyLength) { i =>
        val j = outerCounter(i)
        cforeach (arrayContextClauses(i)(j).body) { predicate =>
          bodyBuffer(w) = predicate
          w += 1
        }
      }
      val newBody = sortUnique(bodyBuffer, w, ArrayBuilders.predicateArrayBuilder)

      val conclusion = ContextClause(newBody, newHead)(ordering)

      if (resultsBuffer.removeRedundant(conclusion)) resultsBuffer.addFirst(conclusion)

    } while (incOuterCounter())
  }

  /** Implementation of Eq rule, where max is the maximal literal where the equality is being applied, in the
    * context clause _contextClause_, the equality is from _equalityContextClause_; */

  def Eq(targetLiteral: Literal,
         targetTerm: Term,
         contextClause: ContextClause,
         equality: Equality,
         equalityContextClause: ContextClause,
         ordering: ContextLiteralOrdering,
         cutting: EqualityOptimization,
         resultsBuffer: UnprocessedDeque): Unit = {
   // println("Applying eq. to target literal " + targetLiteral + " with equality " + equality)



    require(targetLiteral.contains(targetTerm) && equality.contains(targetTerm))
    val newTerm: Term = if (equality.s == targetTerm) equality.t else equality.s
    val headBufferLength: Int = contextClause.head.length + equalityContextClause.head.length - 1
    val headBuffer = new Array[Literal](headBufferLength)
    var w = 0

    targetLiteral match {
      case Concept(_,_) =>
         headBuffer(w) = targetLiteral.rewrite(targetTerm, newTerm, firstPosition = true)
         w += 1
      case Role(_,r,_)  =>
        headBuffer(w) = targetLiteral.rewrite(targetTerm, newTerm , r == targetTerm)
        w += 1
      case Equality(_, t2) if targetTerm == t2 =>
        return // The new clause is redundant.
      case Equality(r, _) =>
        headBuffer(w) = targetLiteral.rewrite(targetTerm, newTerm, r == targetTerm)
        w += 1
      case Inequality(r, t) =>
        /** This `if` applies eagerly the Ineq rule */
        if (r == targetTerm && t != newTerm) {
        headBuffer(w) = targetLiteral.rewrite(targetTerm, newTerm, firstPosition =  true)
        w += 1
       } else if ( t == targetTerm && r != newTerm) {
        /** This second case should not happen since we only rewrite to smaller elements */
         headBuffer(w) = targetLiteral.rewrite(targetTerm, newTerm, firstPosition =  false)
         w += 1
       } else {}

      case _ => throw new IllegalArgumentException("Eq rule is not applicable.")
    }

    cforeach (contextClause.head) { literal =>
      if (literal.compare(targetLiteral) != 0) {
        headBuffer(w) = literal
        w += 1
      }
    }
    cforeach (equalityContextClause.head) { literal =>
      if (literal.compare(equality) != 0) {
        headBuffer(w) = literal
        w += 1
      }
    }
    val newHead = sortUnique(headBuffer, w, ArrayBuilders.literalArrayBuilder)

    val bodyBufferLength: Int = contextClause.body.length + equalityContextClause.body.length
    val bodyBuffer = new Array[Predicate](bodyBufferLength)
    System.arraycopy(contextClause.body, 0, bodyBuffer, 0, contextClause.body.length)
    System.arraycopy(equalityContextClause.body, 0, bodyBuffer, contextClause.body.length, equalityContextClause.body.length)
    val newBody = sortUnique(bodyBuffer, bodyBufferLength, ArrayBuilders.predicateArrayBuilder)

    val conclusion = ContextClause(newBody, newHead)(ordering)

    if (!conclusion.isHeadTautology) resultsBuffer.addFirst(conclusion)
  }

}
