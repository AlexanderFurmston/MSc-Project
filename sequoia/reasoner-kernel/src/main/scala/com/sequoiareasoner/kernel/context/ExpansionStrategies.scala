package com.sequoiareasoner.kernel.context

import com.sequoiareasoner.kernel.clauses.{Concept, Predicate}
import com.sequoiareasoner.kernel.index.ImmutableSet

object ExpansionStrategies {

  def trivialStrategy(predicates: ImmutableSet[Predicate]): ImmutableSet[Predicate] = ImmutableSet.empty
  /** Gets all concepts in a set of predicates */
  def centralStrategy(predicates: ImmutableSet[Predicate]): ImmutableSet[Predicate] = predicates filter {
    case Concept(iri, _)  => true
    case _ => false
  }
  /** A core is forbidden if it contains a nominal and another predicate  */
  def isForbidden(predicates: ImmutableSet[Predicate]): Boolean = {
    var oneNominalAlready = false
    for (predicate <- predicates) {
      if (oneNominalAlready) return true
      if (!oneNominalAlready && predicate.iri.isInternalIndividual) oneNominalAlready = true
    }
    false
  }

  def safeCentralStrategy(predicates: ImmutableSet[Predicate]): ImmutableSet[Predicate] = {
    val core = centralStrategy(predicates)
    if (core.isEmpty) predicates
    else if (isForbidden(core)) predicates.filter {
      case Concept(iri,_) if !iri.isInternalIndividual => true
      case _ => false
    }
    else core
  }
  def eagerStrategy(predicates: ImmutableSet[Predicate]): ImmutableSet[Predicate] = predicates

}
