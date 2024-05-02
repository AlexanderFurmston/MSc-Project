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

import com.sequoiareasoner.arrayops._
import com.sequoiareasoner.kernel.clauses._
import com.sequoiareasoner.kernel.context.inferenceRule._
import com.sequoiareasoner.kernel.index._
import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.structural.DLOntology
import io.cso._

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/** Class that combines all data structures used to maintain the state of the derivation within a context.
  * Special case for when you have a nominal context. */

/** The required arguments for creating a context state are:
  * --The set of query contexts for that concept
  * --The core of the context
  * --The index for clauses in this context
  * --The index for clauses that have been pushed back from a successor.
  * --A redundancy intex for clauses in this context.
  * */

class NominalContextState(override val queryConcepts: Set[Int],
                          override val core: ImmutableSet[Predicate],
                          override val isRootContext: Boolean,
                          override val workedOffClauses: ContextClauseIndex,
                          override val neighborIndex: NeighborPredClauseIndex,
                          override val cutting: EqualityOptimization,
                          redundancyIndex: ContextClauseRedundancyIndex,
                          override val hornPhaseActiveAtCreation: Boolean,
                          override val ordering: ContextLiteralOrdering,
                          override val ontology: DLOntology,
                          override val contextStructureManager: ContextStructureManager) extends ContextState(queryConcepts,
                              core, isRootContext,workedOffClauses,neighborIndex,cutting,redundancyIndex,hornPhaseActiveAtCreation, ordering,
                              ontology, contextStructureManager: ContextStructureManager) {

  /** This checks that the definition of core from the technical report is adhered to. */
  require { core forall { l => l.isLegalInContextClauseBody } }

  /** CORE INFO METHODS */ //-----------------------------------------------------------

  override val isNominalContext: Boolean = true
  def getCoreConstant: Constant = Term(IRI.nominalConceptUid2NominalIriStringName(this.getCoreConcept.iri.uid))

  /** STORED SETS OF CLAUSES */ //----------------------------------------------------------

//  /** Set of unprocessed ground facts (?? what are these ??) */
//  val certainGroundFacts = new mutable.HashSet[Int]
//  /** Set of unprocessed binary ground facts */
//  val certainBinaryGroundFacts = new mutable.HashSet[Role]
//  /** Set of unprocessed unary ground facts */
//  val certainUnaryGroundFacts = new mutable.HashSet[Concept]
//  /** Set of unprocessed equality ground facts */
//  val certainEqualityGroundFacts = new mutable.HashSet[Equality]
  /** Sets of certain ground clauses, only relevant in nominal contexts. */
  val certainGroundClausesOnLastRound = new UnprocessedClauses
  val workedOffCertainGroundClauses = new mutable.HashSet[ContextClause]()

  /** PREDECESSOR OPERATIONS */  //--------------------------------------------------------------------------

  val constantPredecessors = mutable.HashSet[UnboundedChannel[InterContextMessage]]()
  private[this] val rootPredecessors = new mutable.AnyRefMap[Predicate, UnboundedChannel[InterContextMessage]]
  def getRootPredecessor(p: Predicate): Option[UnboundedChannel[InterContextMessage]] = rootPredecessors.get(p)
  def getAllRootPredecessors(): Iterable[UnboundedChannel[InterContextMessage]] = rootPredecessors.values
  def addRootPredecessor(incomingEdge: UnboundedChannel[InterContextMessage], edgeLabel: Predicate): Unit = {
    rootPredecessors.getOrElseUpdate(edgeLabel, incomingEdge)
  }

 /** CERTAIN CLAUSE EXTRACTOR */ //-------------------------------------------------------------------------


//  def toSetAndClear[T <: Any](originalSet: mutable.HashSet[T]): Set[T] = {
//    val output = originalSet.toSet
//    originalSet.clear()
//    output
//  }
  // def newCertainGroundFacts: Set[Int] = toSetAndClear[Int](certainGroundFacts)
  //def newBinaryCertainGroundFacts: Set[Role] = toSetAndClear[Role](certainBinaryGroundFacts)
  //def newUnaryCertainGroundFacts: Set[Concept] = toSetAndClear[Concept](certainUnaryGroundFacts)
  //def newEqualityCertainGroundFacts: Set[Equality] = toSetAndClear[Equality](certainEqualityGroundFacts)


  /** PROCESSING DERIVED CLAUSES */ //-------------------------------------------------------------------------


// NOTE: it seems like this is a very small optimisation which did not use to work because of the private[this]
// modifier. Keeping it off for the moment, but could be added in the future.
//  private[this] def addClauseToContext(clause: ContextClause): Boolean = {
//    if (clause.isEmpty) workedOffCertainGroundClauses.clear()
//    super.addClauseToContext(clause)
//  }


  /** Given a newly (for sure) derived clause, we update the set of pred clauses derived in the last round, as well as
    * updating the set of triggers for Succ rules */
  private[context] override def preparePushesForEndOfRound(clause: ContextClause): Unit = {
    /** predClausesOnLastRound will be empty at the start of the round, so at the end of the round,
      * predClausesOnLastRound will only contain non-redundant clauses. */

    super.preparePushesForEndOfRound(clause)

    /** Next, update Query to do, if the clause head consists exclusively of query atoms or conceptFor for nominals */
    if (clause.isClauseHeadForQuery) {
      queryClausesOnLastRound.removeRedundant(clause)
      queryClausesOnLastRound.addLast(clause)
    }
    /** If this is a nominal context, we update the set of CGCs, and we prepare a propagation to all relevant contexts
      * of any new clause. */
    if (clause.isCertainFunctionFreeGroundClause) {
      certainGroundClausesOnLastRound.addUnprocessedClause(clause)
      workedOffCertainGroundClauses.add(clause)
    }

      //    if (isNominalContext && clause.isFact && clause.isHorn && !clause.head.isEmpty) clause.head(0) match {
      //     // /** First, the certain ground facts used only for redundancy checks */
      //     //case Concept(iri,CentralVariable) => certainGroundFacts += iri.uid
      //      /** Then, the CGFs exchanged between nominal contexts */
      //      case Role(iri,CentralVariable,_: Constant) => certainBinaryGroundFacts += clause.head(0).asInstanceOf[Role]
      //      case Role(iri,_: Constant,CentralVariable) => certainBinaryGroundFacts += clause.head(0).asInstanceOf[Role]
      //      /** No roles will have two constants, and those that have two x's don't need to go anywhere */
      //      case Concept(iri,_: Constant) => certainUnaryGroundFacts += clause.head(0).asInstanceOf[Concept]
      //        /** Same with equalities */
      //      case Equality(CentralVariable,_: Constant) | Equality(_: Constant,CentralVariable) | Equality( _: Constant, _: Constant) =>
      //        certainEqualityGroundFacts += clause.head(0).asInstanceOf[Equality]
      //      case _ =>
      //    }
      /** If the following happens, the ontology must be inconsistent. For original nominals, this is clear. For
        * artificial individuals, we will never derive a clause of the form top -> A(o), because those clauses
        * are only derived from ABox axioms (indeed, only ABox axioms can add clauses of the form Top -> ... to
        * the root context(s); in this implementation, the only exception is \top to conceptFor(o), but such concept
        * never appears on the LHS of an axiom, so no problem. */
    if (clause.isHornAndBodyIsEmpty && clause.head.isEmpty) {
        inconsistencyGuaranteed = true
    }

    }

  }

