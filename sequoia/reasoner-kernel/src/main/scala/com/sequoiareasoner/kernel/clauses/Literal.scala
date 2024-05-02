package com.sequoiareasoner.kernel.clauses

import com.sequoiareasoner.kernel.owl.iri.IRI
import com.sequoiareasoner.kernel.structural.DLOntology


// COME HERE: HOW ABOUT YOU make literal extend Ordered, even if the order here contradicts the order in the algorithm, because
// max predicates are chosen using the context literal ordering, not the order you use to order literals.
// Make uid and use that to compare. It is for time's sake; minimal modifications. Update inidices.

/** Represents any kind of literal, including context and clause literals */
sealed trait Literal extends Ordered[Literal] {
  self =>

  type T <: Literal


  //TODO: Prevent Equalities of the form Equality(o,x). Do them instead as Equality(x,o) ? No, because of Eq? Or maybe yes, actually,
  //because of how the EQ rule is now implemented.

  /** USEFUL TEST FUNCTIONS */

  /** Return `true` if and only if this literal is a predecessor trigger. */
  def isPredTrigger: Boolean
  /** Return `true` if and only if this literal is ground. */
  def isGround: Boolean
  /** Return `true` if and only if this literal does not contain a function term at any sub-position. */
  def isFunctionFree: Boolean
  /** Returns `true` if and only if this literal is an inequality of the form `Inequality(t, t)` for some term `t`. */
  def isInvalidEquation: Boolean
  /** Returns `true` if and only if this literal is an equality of the form `Equality(t, t)` for some term `t`. */
  def isValidEquation: Boolean
  /** Returns `true` if and only if the form of this predicate is allowed to occur in the body of a context clause. */
  def isLegalInContextClauseBody: Boolean
  /** Return `true` if and only if the form of this predicate is allowed to occur in the head of a context clause. */
  def isLegalInContextClauseHead: Boolean
  /** Return `true` if and only if the form of this predicate is allowed to occur in the body of an ontology clause. */
  def isLegalInOntologyClauseBody: Boolean
  /** Return `true` if and only if the form of this predicate is allowed to occur in the head of an ontology clause. */
  def isLegalInOntologyClauseHead: Boolean

  def constants: (Option[Constant],Option[Constant])

  /** Applies a given mapping to the literal */
  def applySubstitution(sigma: Substitution): T

  /** Test if term `l` is contained in a maximal position */
  def containsAtRewritePosition(l: Term): Boolean = (l == maximalTerms._1) || maximalTerms._2.contains(l)
//  def rewrite(l: Term, r: Term): T
  def contains(l: Term): Boolean

  /** Replace term l by term r, in first position if _firstPosition_ is true */
  def rewrite(l: Term, r: Term, firstPosition: Boolean): T
  def maximalTerms: (Term,Option[Term])
  def minimalTerms: (Term,Option[Term])

  final def compare(that:Literal): Int =  (this,that) match {
    case (Concept(iri1,t1),Concept(iri2,t2)) => if (iri1 == iri2 && t1 == t2) 0 else -1
    case (Role(iri1,s1,t1),Role(iri2,s2,t2)) => if (iri1 == iri2 && s1 == s2 && t1 == t2) 0 else -1
    case (Equality(s1,t1), Equality(s2,t2)) =>  if ((s1 == s2 && t1 == t2) || (s1 == t2 && t1 == s2)) 0 else -1
    case (Inequality(s1,t1), Inequality(s2,t2)) =>  if ((s1 == s2 && t1 == t2) || (s1 == t2 && t1 == s2)) 0 else -1
    case _ => -1
    }
  }


/** Predicate */

/** Represents a literal with a predicate. */
sealed trait Predicate extends Literal {
  override type T <: Predicate

  def iri: IRI
  def isSuccTrigger: Boolean
  def isRSuccTrigger: Boolean
  def hasCentralVariable: Boolean
  def containsFunctionalTerm: Boolean
  def containsConstant: Boolean
  final override def isInvalidEquation: Boolean = false
  final override def isValidEquation: Boolean = false


  /** Returns a bit string that can be used to quickly determine whether two predicates cannot centrally unify.
    * Given two predicates `p1` and `p2`, and a central substitution `sigma`, the bit string is such that if either
    * `sigma(p1) == p2` or `sigma(p2) == p1` then `p1.centralUnifierPattern == p2.centralUnifierPattern`.
    *
    * @return a bit string that determines whether this predicate can centrally unify with another.
    */
  def centralUnifierPattern: Long

}

/** CONCEPT */

/** Represents a concept  of the form `iri(t)`. */
final case class Concept(iri: IRI, t: Term)(implicit ontology: DLOntology) extends Predicate {
  override type T = Concept
  override def centralUnifierPattern: Long = {
    this match {
      case Concept(_,CentralVariable) => iri.uid.toLong
      case _ => iri.uid.toLong  | (1.toLong << 29)
    }
  }
  override val hashCode: Int = {
    t match {
      case CentralVariable => iri.uid
      case PredVariable => iri.uid ^ (-1)
      case NeighbourVariable(id) => iri.uid ^ id
      case FunctionalTerm(id) => iri.uid ^ (id | (1 << 29))
      case OriginalIndividual(id) => iri.uid ^ (id | 2 << 29)
      case ArtificialIndividual(id) => iri.uid ^ (id | 3 << 29)
    }
  }
  override def applySubstitution(sigma: Substitution) = Concept(iri, sigma(t))
  override def contains(l: Term): Boolean = l == t

  override def constants = if (containsConstant) (Some(t.asInstanceOf[Constant]),None) else (None,None)

  override def containsFunctionalTerm: Boolean = t match {
    case FunctionalTerm(_) => true
    case _ => false
  }
  override def containsConstant: Boolean = t match {
    case _: Constant => true
    case _ => false
  }
  override def rewrite(l: Term, r: Term, firstPosition: Boolean): Concept = {
    require(firstPosition)
    if (l == t) Concept(iri, r)
    else throw new IllegalArgumentException(s"Term $l does not appear in $toString")
  }
  def copy(t: Term): Concept = Concept(iri, t)(ontology)
  /** A concept is a successor trigger iff it is of the form B(f(x)), with B(x) occurring in the body of some ontology clause.
    * The DLOntology method isConceptSuccTrigger should be able to test if this is the case. */
  override def isSuccTrigger: Boolean = t match {
    case FunctionalTerm(_) => ontology.isConceptSuccTrigger(iri)
    case _ => false
  }
  /** A concept is a nominal successor trigger iff it is of the form B(o), with B(x) occurring in the body of some ontology clause.
    * As above, we can test this with isConceptSuccTrigger */
  override def isRSuccTrigger: Boolean = t match {
    case _: Constant => ontology.isConceptSuccTrigger(iri)
    case _ => false
  }
  /** A concept is a predecessor trigger iff it is of the form B(y) */
  override def isPredTrigger: Boolean =  t match {
    case PredVariable => true
    case _ => false
  }
  override def isFunctionFree: Boolean = t match {
    case FunctionalTerm(_) => false
    case _ => true
  }
  override def hasCentralVariable: Boolean = t match {
    case CentralVariable => true
    case _ => false
  }
  override def maximalTerms: (Term,Option[Term]) = (t,None)
  override def minimalTerms: (Term,Option[Term]) = (t,None)

  override def isLegalInContextClauseBody: Boolean = t match {
    case CentralVariable | PredVariable | _: Constant => true
    case _ => false
  }
  override def isLegalInContextClauseHead: Boolean = t match {
    case CentralVariable | PredVariable | FunctionalTerm(_) | _: Constant => true
    case _ => false
  }
  override def isLegalInOntologyClauseBody: Boolean = t match {
    case CentralVariable | NeighbourVariable(_) => true
    case _ => false
  }
  override def isLegalInOntologyClauseHead: Boolean = t match {
   case CentralVariable | NeighbourVariable(_) | FunctionalTerm(_)  => true
   case _ => false
  }
  def isAtomicConcept: Boolean = this match {
    case Concept(_,CentralVariable) if iri.isImported => true
  }
  override def toString: String = s"$iri($t)"
  def isGround: Boolean = t match {
    case _: Constant => true
    case _ => false
  }
}


/** ROLE */

/** Represents a role of the form `iri(s, t)`. */
final case class Role(iri: IRI, s: Term, t: Term)(implicit ontology: DLOntology) extends Predicate {

  override type T = Role

  override def centralUnifierPattern: Long = this match {
    case Role(_,CentralVariable,CentralVariable) => iri.uid.toLong  | (2.toLong << 29)
    case Role(_,CentralVariable,_) => iri.uid.toLong  | (3.toLong << 29)
    case Role(_,_,CentralVariable) => iri.uid.toLong  | (4.toLong << 29)
    case Role(_,_,_) => iri.uid.toLong  | (5.toLong << 29)
  }

  override val hashCode: Int = {
    val first = s match {
      case CentralVariable => 0
      case PredVariable =>  -1
      case NeighbourVariable(id) => id
      case FunctionalTerm(id) => id | (1 << 29)
      case OriginalIndividual(id) => id | 2 << 29
      case ArtificialIndividual(id) => id | 3 << 29
    }
    val second = t match {
      case CentralVariable => 0
      case PredVariable =>  -1
      case NeighbourVariable(id) => id
      case FunctionalTerm(id) => id | (1 << 29)
      case OriginalIndividual(id) => id | 2 << 29
      case ArtificialIndividual(id) => id | 3 << 29
    }
    (iri.uid ^ first) ^ second
  }

  override def applySubstitution(sigma: Substitution) = Role(iri, sigma(s), sigma(t))

  override def constants = (t match {
    case a: Constant => Some(a)
    case _ => None
  }, s match {
    case b: Constant => Some(b)
    case _ => None
  }
  )

  override def contains(l: Term): Boolean = l == s || l == t
  override def containsFunctionalTerm: Boolean =  (t match {
    case FunctionalTerm(_) => true
    case _ => false
  }) ||  (s match {
    case FunctionalTerm(_) => true
    case _ => false
  })
  override def containsConstant: Boolean =  (t match {
    case _: Constant => true
    case _ => false
  }) ||  (s match {
    case _: Constant => true
    case _ => false
  })
  override def rewrite(l: Term, r: Term, firstPosition: Boolean): Role = {
    if (firstPosition && l == s) Role(iri, r, t)
    else if (!firstPosition && l == t) Role(iri, s, r)
    else throw new IllegalArgumentException(s"Term $l does not appear in the ${if (firstPosition) "first" else "second"} position of $toString")
  }
  def copy(s: Term, t: Term): Role = Role(iri, s, t)(ontology)

  /** A role is a successor trigger if it is of the form R(x,f(x)) or R(f(x),x) where the ontology contains R(x,z_i) or R(z_i,x), respectively, in the body of a clause. */
  override def isSuccTrigger: Boolean = this match {
    case Role(_,CentralVariable, FunctionalTerm(_)) if ontology.isBackwardRoleSuccTrigger(iri) => true
    case Role(_,FunctionalTerm(_), CentralVariable) if ontology.isForwardRoleSuccTrigger(iri) => true
    case _ => false
  }
  /** A role is a successor trigger if it is of the form R(x,o) or R(o,x) where the ontology contains R(x,z_i) or R(z_i,x), respectively, in the body of a clause. */
  override def isRSuccTrigger: Boolean = this match {
    case Role(_,CentralVariable, _: Constant) if ontology.isBackwardRoleSuccTrigger(iri) => true
    case Role(_, _: Constant, CentralVariable) if ontology.isForwardRoleSuccTrigger(iri) => true
    case _ => false
  }
  /** A role is a predecessor trigger if it is of the form R(x,y) or R(y,x) and the ontology contains in the body a clause of the form R(z_i,x) or R(x,z_i), respectively. */
  override def isPredTrigger: Boolean = this match {
    case Role(_,CentralVariable, PredVariable) if ontology.isBackwardRoleSuccTrigger(iri) => true
    case Role(_,PredVariable, CentralVariable) if ontology.isForwardRoleSuccTrigger(iri) => true
    case _ => false
  }
  override def isFunctionFree: Boolean = this match {
    case Role(_,FunctionalTerm(_),_) | Role(_,_,FunctionalTerm(_)) => false
    case _ => true
  }
  override def hasCentralVariable: Boolean = this match {
    case Role(_, CentralVariable, _) | Role(_, _, CentralVariable) => true
    case _ => false
  }
  override def isLegalInContextClauseBody: Boolean = this match {
    case Role(_,CentralVariable,CentralVariable) | Role(_,CentralVariable,PredVariable) | Role (_,PredVariable,CentralVariable) |
      Role(_,PredVariable,_: Constant) | Role(_,_:Constant,PredVariable) | Role(_, _: Constant,_: Constant) |
     Role(_,CentralVariable,_: Constant) | Role(_,_:Constant,CentralVariable) => true
    case _ => false
  }
  override def isLegalInContextClauseHead: Boolean = this match {
    case _ if isLegalInContextClauseBody => true
    case Role(_,CentralVariable,_: Constant) | Role(_,_: Constant, CentralVariable) |
      Role(_,CentralVariable,FunctionalTerm(_))  | Role(_,FunctionalTerm(_),CentralVariable) => true
    case _ => false
  }
  override def isLegalInOntologyClauseBody: Boolean = this match {
    case Role(_,CentralVariable,CentralVariable) | Role(_,CentralVariable,NeighbourVariable(_)) |
         Role(_,NeighbourVariable(_),CentralVariable) => true
    case _ => false
  }
  override def isLegalInOntologyClauseHead: Boolean = this match {
    case _ if isLegalInOntologyClauseBody => true
    case Role(_,CentralVariable,FunctionalTerm(_)) | Role(_,FunctionalTerm(_),CentralVariable) |
      Role(_,CentralVariable,_: Constant) | Role(_,_: Constant, CentralVariable) => true
    case _ => false
  }
  def inverse = Role(iri, t, s)
  override def maximalTerms: (Term,Option[Term]) = (s.max(t).getOrElse(s),if (s.max(t).isDefined) None else Some(t))
  override def minimalTerms: (Term,Option[Term]) = (s.min(t).getOrElse(s),if (s.min(t).isDefined) None else Some(t))
 def isGround: Boolean = this match {
   case Role(_,_: Constant, _: Constant) => true
   case _ => false
 }
 override def toString: String = s"$iri($s, $t)"
}


/** EQUATION */

/** Represents an equality or inequality */
sealed trait Equation extends Literal {
    override type T <: Equation
    /** Return the maximum term of the equation, if there is one. */
    def maxTerm: Option[Term]
    /** Return the minimum term of the equation, if there is one. */
    def minTerm: Option[Term]

    assert( (maxTerm.isEmpty && minTerm.isEmpty) || (maxTerm.isDefined && minTerm.isDefined) )

  /** Return a tuple containing the two terms of the equation */
    def asTuple: (Term,Term)
  /** Return a tuple containing the two terms of the equation, so that if one of them is bigger, it is given first */
    def asOrderedTuple: (Term,Term)
  /** Return the equation reversing the term order */
    def reverse: Equation
  /** Transforms the literal into a multiorder in the standard way: equality s=t becomes {s,t}, and inequality s=/=t becomes {s,s,t,t} */
    def toMultiset: List[Term]

    def isStrict : Boolean = maxTerm.isDefined

    def isXEquality: Boolean = this match {
      case Equality(CentralVariable, _: Constant) => true
      case Equality(_: Constant, CentralVariable) => true
      case _ => false
    }





  /** No equations are allowed in the body of a context clause */
  final override def isLegalInContextClauseBody: Boolean = false
  /** All equations that do not include neighbour variables are allowed, if term orders are respected */
  final override def isLegalInContextClauseHead: Boolean = maxTerm match {
    case Some(FunctionalTerm(_)) => minTerm match {
      case Some(FunctionalTerm(_)) => true
      case Some(CentralVariable) => true
      case Some(PredVariable) => true
      case Some(_: Constant) => true
      case _ => false
    }
    case Some(CentralVariable) => minTerm match {
      case Some(PredVariable) => true
      case _ => false
    }
    case Some(_: Constant) => minTerm match {
      case Some(_: Constant) => true
      case _ => false
    }
    case Some(NeighbourVariable(_)) => false
    case Some(PredVariable) => false
    case None => asTuple match {
      case (_: Constant, CentralVariable) | (_: Constant, PredVariable) => true
      case (CentralVariable, _: Constant) | (PredVariable, _: Constant) => true
      case _ => false
    }
  }
  /** No equations are allowed in the body of an ontology clause */
  final override def isLegalInOntologyClauseBody: Boolean = false

  /** Equations in ontology clause heads must respect the order. Also:
    * -function symbols appear only in the form f(x) =/= g(x)
    * -central variable appears only in the form x = o
    * -individuals appear only in the form x = o
    * -neighbour variables appear in the form z_i = z_j
    * -predicate variable does not appear */
    final override def isLegalInOntologyClauseHead: Boolean = maxTerm match {
      case Some(FunctionalTerm(_)) => minTerm match {
        case Some(FunctionalTerm(_)) => true
        case _ => false
      }
      case Some(CentralVariable) => false
      case Some(_: Constant) => false
      case Some(NeighbourVariable(_)) => minTerm match {
        case Some(NeighbourVariable(_)) => true
        case _ => false
      }
      case Some(PredVariable) => false
      case None => asTuple match {
        case (_: Constant, CentralVariable)  => true
        case (CentralVariable, _: Constant)  => true
        case _ => false
      }
    }
  final override def isFunctionFree: Boolean = asTuple match {
    case (FunctionalTerm(_),_) | (_,FunctionalTerm(_))  => false
    case _ => true
  }
  final override def isGround: Boolean = asTuple match {
    case (_: Constant, _: Constant)  => true
    case _ => false
  }
  /**  An equation is a predecessor trigger iff it is of the form x = y, x = o, y = o  */
  def isPredTrigger: Boolean = asTuple match {
    case (CentralVariable,PredVariable) | (PredVariable,CentralVariable) |
         (CentralVariable, _: Constant) | (_: Constant, CentralVariable) |
         (PredVariable, _: Constant) | (_: Constant, PredVariable) => true
    case _ => false
  }

  override def maximalTerms: (Term,Option[Term]) = (maxTerm.getOrElse(asTuple._1),if (maxTerm.isDefined) None else Some(asTuple._2))
  override def minimalTerms: (Term,Option[Term]) = (minTerm.getOrElse(asTuple._1),if (maxTerm.isDefined) None else Some(asTuple._2))

}


/** Equality */

/** Represents an equality `s == t` such that either `s > t` or `s == t` using the syntactic order on terms. */
final case class Equality(s: Term, t: Term) extends Equation {
  require( !(s < t) )
  override type T = Equality
  override def applySubstitution(sigma: Substitution): Equality = {
    val l = sigma(s); val r = sigma(t)
    if (l > r) Equality(l, r) else Equality(r, l)
  }
  override def maxTerm = if (s > t) Some(s) else None
  override def minTerm = if (s > t) Some(t) else None
  override def reverse: Equality = Equality(t,s)
  override def asTuple: (Term,Term) = (s,t)
  override def asOrderedTuple: (Term, Term) = if (t > s) (t,s) else (s,t)
  override def contains(l: Term): Boolean =  l == s || l == t
  override def rewrite(l: Term, r: Term, firstPlace: Boolean): Equality = {
    if (firstPlace) {
      assert(s == l)
      if (r > t) Equality(r, t) else Equality(t, r)
    } else {
      assert(t == l)
      if (l > s) throw new IllegalArgumentException(s"Since $s and $t cannot be compared, as that is the reason why we " +
        s"are applying Eq to the second element, and $l should be equal to $t, it cannot be that $l is greater than $s")
      Equality(s, r)
    }
  }

  override def constants = (t match {
    case a: Constant => Some(a)
    case _ => None
  }, s match {
    case b: Constant => Some(b)
    case _ => None
  }
  )

  override def isInvalidEquation: Boolean = false
  override def isValidEquation: Boolean = s == t
  override def toMultiset = List(s,t)
}


/** Inequality */

/** Represents an inequality `s =/= t` such that either `s > t` or `s == t`. */
final case class Inequality(s: Term, t: Term) extends Equation {
  require( !(s < t) )
  override type T = Inequality
  override def applySubstitution(sigma: Substitution): Inequality = {
    val l = sigma(s); val r = sigma(t)
    if (l > r) Inequality(l, r) else Inequality(r, l)
  }
  override def maxTerm = if (s > t) Some(s) else None
  override def minTerm = if (s > t) Some(t) else None
  override def asTuple: (Term,Term) = (s,t)
  override def asOrderedTuple: (Term, Term) = if (t > s) (t,s) else (s,t)
  override def reverse: Inequality = Inequality(t,s)
  override def contains(l: Term): Boolean =  l == s || l == t
  override def rewrite(l: Term, r: Term, firstPlace: Boolean): Inequality = {
    if (firstPlace) {
      assert(s == l)
      if (r > t) Inequality(r, t) else Inequality(t, r)
    } else {
      assert(t == l)
      if (l > s) throw new IllegalArgumentException(s"Since $s and $t cannot be compared, and $l should not be greater than $t, it cannot be that $l is greater than $s")
      Inequality(s, r)
    }
  }

  override def constants = (t match {
    case a: Constant => Some(a)
    case _ => None
  }, s match {
    case b: Constant => Some(b)
    case _ => None
  }
  )

  override def isInvalidEquation: Boolean = s == t
  override def isValidEquation: Boolean = false
  override def toMultiset = List(s,s,t,t)
}


