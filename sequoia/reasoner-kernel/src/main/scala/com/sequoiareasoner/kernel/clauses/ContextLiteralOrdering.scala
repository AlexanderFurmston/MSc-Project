package com.sequoiareasoner.kernel.clauses


import scala.collection.immutable.Set


object ContextLiteralOrdering {

  def apply(query: Set[Int] = Set.empty[Int]): ContextLiteralOrdering =
    new ContextLiteralOrdering(query)

}


//TODO: A closer-to-theory system can be done by taking out restrictions from the contextordering general trait and putting them into some named sub-trait.
/** Class representing a particular type of Context Literal Ordering. */
final class ContextLiteralOrdering private[clauses] (query: Set[Int]) extends PartialOrdering[Literal] {

  override def tryCompare(x: Literal, y: Literal): Option[Int] = {
    throw new IllegalStateException("Method `tryCompare` should not have been called")
  }

  def verifyQuery(outsideQuery: Set[Int]): Boolean = this.query == outsideQuery

  /** The context order extends the a-term ordering to any kind of term. The following is a need of conditions
    * that need to be satisfied, in addition to the conditions of a partial order (reflexivity, antisym, transitivity):
    * (1) Predicate > x
    * (2) Predicate[t]_p > t
    * (3) A[t]_p > A[s]_p if t > s.
    * (4) PredTrigger Predicates should not be greater than terms other than x,y or o, or itself.
    * (5) Query Predicates should not be greater than other predicates that do not contain variable y, except themselves.
    * We can separate these constraints in two groups:
    * -Monotonic constraints: once satisfied, any extension of the order also satisfies them: reflexivity, (1), (2), (3)
    * -NonMonontonic constraints: once satisfied, further extensions of the order can violate them: antisym, trans, (4), (5)
    * To prove the result is a context order, it suffices to show that all monotonic constraints are added in some step,
    * and that each step keeps the non-monotonic constraints.
    *
    * The term order is clearly reflexive, antisymmetric, and transitive. We extend it to define the following CONTEXT ORDER:
    *
    * -Step 1:
    * --A(t) > x
    * --A(t) > y
    * (1) added. Antisymmetry is not violated. Transitivity is not violated. (4), (5) are not violated.
    *
    * -Step 2:
    * --A(t) > t
    * --A(t) > s, for each s < t.
    * (2) added. Antisymmetry is not violated. Transitivity is not violated. (4) not violated (PredTriggers do not contain terms other than x,y,o, or that dominate terms other than x,y,o). (5) not violated.
    *
    * -Step 3:
    * -- A(t) > A(t)
    * Reflexivty added. Antisymmetry not violated. Transitivity not violated. (4) and (5) not violated.
    *
    * -Step 4:
    * -- A[t]_p > A[s]_p
    * (3) added. Antisymmetry not violated. Transitivity not violated. (4) not violated (no inner term in a PredTrigger leads to another PredTrigger when replaced by a smaller term). (5) not violated.
    *
    * -Step 5:
    * -- N(t) > P(t) for every PredTrigger P(t) and non PredTrigger N(t).
    * Optimisation. Antisymmetry not violated. Transitivity not violated. (4) not violated. (5) not violated (all PredTriggers contain y).
    *
    * -Step 6: if a term dominates all inner terms of a predicate, then the predicate precedes it, unless
    * it violates the previous entries. This leads to the following additions:
    * --f(x) > B(y)
    * --f(x) > B(x)
    * --f(x) > B(o)
    * --g(x) > B(f(g))
    * --f(x) > S(y,x)
    * --f(x) > A(x,y)
    * --f(x) > S(y,o)
    * --f(x) > S(o,y)
    * --f(x) > S(x,x)
    * --f(x) > S(o,a)
    * --   u > S(o,a)
    * --g(x) > S(x,f(x))
    * --g(x) > S(f(x),x)
    * --g(x) > S(o,f(x))
    * --g(x) > S(f(x),o)    (for all g,f where g > f, and u,o,a where u > o and u > a)
    * Optimisation. Antisymmetry not violated. Transitivity not violated. (4) not violated. (5) not violated.
    *
    * -Step 7:
    * --NonInternalDisjunct(t) > InternalDisjunct(t), for all non-PredTriggers, non-Query pairs of predicates.
    * Optimisation. Antisymmetry not violated. Transitivity not violated. (4) not violated. (5) not violated.
    *
    * -Step 8:
    * --N(t) > Q(x) for every non-pred, non-query trigger predicate (all those not containing y are included) N(t) and query predicate Q(x)
    * Optimisation. Antisymmetry not violated. Transitivity not violated. (4) not violated. (5) not violated.
    *
    * -Step 9: For any other pair of predicates, compare terms first, then iris.
    * Optimisation. Antisymmetry not violated (it is ordered, so no cycles), transitivity not violated, (4) not violated, (5) not violated.
    */


  /** Comparison of TERMS AND TERMS */
  /**  ~ term ordering ~ */

  /** Comparison of TERMS AND PREDICATES */
  def termSmallerThanPredicate(s: Term, p: Predicate): Boolean = {
    /** Step 1 */
    s match {
      case CentralVariable => return true
      case PredVariable =>  return true
      case _ =>
    }
    /** Step 2 */
    p match {
      case Concept(_, t) => s == t || s < t
      case Role(_, t1, t2) => s == t1 || s == t2 || s < t1 || s < t2
    }
  }
  def predicateSmallerThanTerm(p: Predicate, s: Term): Boolean = {
    /** Step 6 */
    if (termSmallerThanPredicate(s, p)) return false
    p match {
      case Concept(_, t) => s > t
      case Role(_, t1, t2) => s > t1 && s > t2
    }
  }

  /** Comparison of PREDICATES AND PREDICATES */
  def predicateSmallerThanPredicate(p1: Predicate, p2: Predicate): Boolean = (p1, p2) match {
    /** Step 3 */
    case (_, _) if p1 == p2 =>  true

    /** From now on, p1 != p2 */

    /** Optimisation: due to condition (4), we can determine that this case is false without further tests */
    case (_: Predicate, _: Predicate) if p2.isPredTrigger => false

    /** From now on, p2 is not a predTrigger */

    /** Step 5 */
    case (_: Predicate, _: Predicate) if p1.isPredTrigger =>  true

    /** From now on, neither p1 nor p2 are predTriggers */
    /** From now on, p1 != p2 */

    /** Optimisation: due to condition (5), and the fact that p1 is not predTrigger so it does not contain y,
      * we can determine that this case is false without further tests */
    // case (Concept(_, _), Concept(iri, CentralVariable)) if query.contains(iri.uid) => false
    //TODO: This is a hack; ideally we use the variable `query' to know which are the query concepts.
    // See Reasoner.scala for details. The right code would be the line above this.
//    case (Concept(_, _), Concept(iri, CentralVariable)) if iri.isImported => false

    /** From now on, p2 is not a query trigger */

    /** Step 8 */
    //case (Concept(iri, CentralVariable), Concept(_, _)) if query.contains(iri.uid) =>  true
//     case (Concept(iri, CentralVariable), Concept(_, _)) if iri.isImported =>  true


    /** From now on, neither p1 nor p2 are query concepts */

    /** Step 7 */
    case (p1: Predicate, p2: Predicate) if p1.iri.isInternalDisjunct && !p2.iri.isInternalDisjunct =>  true

    /** Steps 4 and 9 */
    case (Role(iri1, s1, t1), Role(iri2, s2, t2)) =>
      /* Both of the following are valid orders:
     *   (1) iri < iri2 || (iri == iri2 && (s1 < s2 || (s1 == s2 && t1 < t2)))
     *   (2) s1 < s2 || (s1 == s2 && (t1 < t2 || (t1 == t2 && iri <= iri2)))
     * In practice, reasoning performance will be significantly slower with (1) instead of (2). For an explanation,
     * see the other comment about for concepts below.
     */
      s1 < s2 || (s1 == s2 && (t1 < t2 || (t1 == t2 && iri1 <= iri2)))
    case (Concept(iri1, s), Concept(iri2, t)) =>
      /* Both of the following are valid orders:
     *   (1) iri1 < iri2 || (iri1 == iri2 && s <= t)
     *   (2) s < t || (s == t && iri1 <= iri2)
     * However, while (2) has the property that B(x) < A(f(x)) regardless of the IRI ordering on A and B, (1) does
     * not. In practice, reasoning performance will be significantly slower with (1) instead of (2). We have thus
     * effectively put function symbols higher in the order than predicate symbol when constructing the
     * lexicographic path order, and this is the opposite of the advice given in Section 3.2, Paramodulation-Based
     * Theorem Proving, Handbook of Automated Reasoning, Volume 1 (2001). This ordering reduces the number of
     * applications of Hyper in a context, because only concepts of the form C(x) are matched against clause bodies.
     */
       s < t || (s == t && iri1 <= iri2)
    case (Role(iri1, s1, t1), Concept(iri2, t)) =>
      /* This ordering has also been designed to reduce the number of applications of Hyper. See above. */
      s1 < t || (s1 == t && (t1 < t || (t1 == t && iri1 <= iri2)))
    case (Concept(iri2, t), Role(iri1, s1, t1)) =>
      !(s1 < t || (s1 == t && (t1 < t || (t1 == t && iri1 <= iri2))))
    case _ => false
  }

  override def lteq(X: Literal, Y: Literal): Boolean = (X, Y) match {
    /** EQUATION VS EQUATION
      * The multiset order extension determines the comparison of equations based on the term order */
    case (e1: Equation, e2: Equation) =>
      val (x: List[Term], y: List[Term]) = multisetDifference(e1.toMultiset, e2.toMultiset)
      x.forall(ex => y.exists(ey => ey > ex))


    /** EQUATION VS PREDICATE
      * The multiset order extension determines the comparison of an equation and a predicate based on
      * the comparison between a term and a predicate */
    case (e: Equation, p: Predicate) => e.toMultiset.forall(t => termSmallerThanPredicate(t,p))
    case (p: Predicate, e: Equation) => e.toMultiset.exists( t => predicateSmallerThanTerm(p,t))
    /** PREDICADE VS PREDICATE
      * Multiset order extension implies that we must simply compare predicates */
    case (p1: Predicate, p2: Predicate) => {
      predicateSmallerThanPredicate(p1,p2)
    }
    case _ => throw new IllegalArgumentException(s"One of the arguments $X or $Y is neither an Equation or a Predicate")
  }

  /** This method returns (X\Y,Y\X), the two multiset differences.*/
def multisetDifference(X: List[Term], Y: List[Term]): (List[Term], List[Term]) = {
    X.foldLeft((List[Term](),Y)){ ( z: (List[Term],List[Term]), t: Term) =>
      (z._1 ::: Some(t).filterNot(x => z._2.contains(x)).toList, z._2.takeWhile(y => y != t) ::: z._2.dropWhile(y => y!= t).drop(1))
    }
  }

}


//* * * * If r1 < r2, then r2 could be bigger than l1; false.
//* If l1 ~ l2, then:
//* * If l1 > r2, then:
//* * * If l1 > r1, then l2 ~ r1 or l2 > r1 (r1 > l2 would imply l1 > l2).
/** If X and Y are equations, the only way to ensure X < Y is:
        * --- They have exactly the same elements, but Y is an inequality, while X is an equality.
        * --- Some element x of X is equal(syntactically) to some element y of Y, and the other element x' of X dominates the other y' of Y.
        * --- No element of X is equal to an element of Y, and all elements of Y are dominated by elements of X.
        *
        * PROOF:
        *  If some element x of X is equal to an element y of Y, then given any possible combination of restrictions between
        *  elements of X and Y, we have that if x' > y' is among them, then X is guaranteed to be bigger (easy to see) and if it is not,
        *  then we can always find a case where grounding of Y is above the grounding of X.
        *  Indeed, if x' > y' is not a restriction, consider grounding where y' is in the maximum position within its restrictions, and
        *  once that is fixed, x' is put in minimum position allowed by restrictions, and suppose X is greater than Y.
        *  Then, x' is greater than y', but this is only possible if the lower bound in the restriction for x' is strictly greater
        *  than the upper bound for y';
        *  With our restriction language, any upper bound for y' can only be x > y', and then any lower bound for x' can
        *  only be x' > y' (forbidden by hypothesis), x' = y' (not greater, then) or x' > x (but then  x' > y' must be a restriction,
        *  by transitivity of restriction language.
        *  Now, assuming no equalities,
        *  if one element b of Y is not dominated by any of X, then a maximal element c in Y is not dominated (either b is maximal, or b
        *  is smaller than b' in Y, and b' cannot be dominated since otherwise b would be dominated). If c is not bounded by c',
        *  and c is not bounded by any element of X, then a grounding of c can be above groundings of all other elements.
        *
        */
