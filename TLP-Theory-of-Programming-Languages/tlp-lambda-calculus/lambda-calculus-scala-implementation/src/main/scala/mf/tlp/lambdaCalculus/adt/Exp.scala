package mf.tlp.lambdaCalculus.adt

import mf.tlp.lambdaCalculus.adt.Exp.pretty

import scala.annotation.tailrec
import scala.language.implicitConversions

sealed trait Exp[T] {
  self =>
  override def toString: String = pretty[T](self)

  def <>(e: Exp[T]): Application[T] = Application[T](self, e)
}

case class Var[T](value: T) extends Exp[T] {
  def ~>(e: Exp[T]): Lambda[T] = Lambda(this, e)
}

case class Lambda[T](v: Var[T], scope: Exp[T]) extends Exp[T]

case class Application[T](e1: Exp[T], e2: Exp[T]) extends Exp[T]

object Exp {


  def v[T](value: T): Var[T] = Var[T](value)

  def \[T](v: Var[T], scope: Exp[T]): Lambda[T] = Lambda[T](v, scope)

  def <>[T](e1: Exp[T], e2: Exp[T]): Application[T] = Application[T](e1, e2)


  def pretty[T](term: Exp[T], m: Int = 0): String = term match {
    case Var(value) => value.toString
    case Lambda(v, scope) => {
      lazy val s: String = s"λ$v.${pretty(scope)}"
      if (m != 0) s"($s)" else s
    }
    case Application(e1, e2) => {
      lazy val s: String = s"${pretty(e1, 1)} ${pretty(e2, 2)}"
      if (m == 2) s"($s)" else s
    }
  }

  def show[T](term: Exp[T]): String = {
    def aux(t: Exp[T]): String = {
      t match {
        case Var(value) => value.toString
        case Lambda(v, scope) => s"(λ${aux(v)}.${aux(scope)})"
        case Application(e1, e2) => s"(${aux(e1)} ${aux(e2)})"
      }
    }

    aux(term).tail.init
  }

  def numeral(n: Int): Exp[String] = {
    def aux(m: Int): Exp[String] = {
      if (m == 0) Var("x")
      else <>(Var("f"), aux(m - 1))
    }

    Lambda(Var("f"), Lambda(Var("x"), aux(n)))
  }

  def freeVariable[T](term: Exp[T]): List[T] = {
    def aux(exp: Exp[T], bounded: List[T], free: List[T]): List[T] = exp match {
      case Var(value) => if (bounded.contains(value)) free else value :: free
      case Lambda(v, scope) => aux(scope, v.value :: bounded, free)
      case Application(e1, e2) => aux(e1, bounded, free) ++ aux(e2, bounded, free)
    }

    aux(term, Nil, Nil)
  }

  def fv[T](term: Exp[T]): Set[Var[T]] = used(term)

  def used[T](term: Exp[T]): Set[Var[T]] = term match {
    case v@Var(_) => Set(v)
    case Lambda(v, scope) => Set(v).union(used(scope))
    case Application(e1, e2) => used(e1).union(used(e2))
  }

  def ocurrence[T](term: Exp[T]): Set[T] = {
    def aux(exp: Exp[T], occ: List[T]): List[T] = exp match {
      case Var(value) => value :: occ
      case Lambda(v, scope) => aux(scope, v.value :: occ)
      case Application(e1, e2) => aux(e1, occ) ++ aux(e2, occ)
    }

    aux(term, Nil).toSet
  }

  def fresh(set: Set[String], v: String = "x"): Var[String] = {
    val nv: Int => String = (i: Int) => s"$v$i"

    @tailrec
    def generate(acc: Int): String = if (set.contains(nv(acc))) generate(acc + 1) else nv(acc)

    Var(generate(0))
  }

  def fresh(set: Set[Var[String]], v: Var[String]): Var[String] = {
    val setV: Set[String] = set.map(_.value)
    fresh(setV, v.value)
  }

  def fresh(v: Var[String], term: Exp[String]): Var[String] = {
    val occ: Set[String] = ocurrence(term)
    fresh(occ, v.value)
  }

  def cas(term: Exp[String], x: Var[String], N: Exp[String]): Exp[String] = {
    term match {
      case v@Var(_) if v.equals(x) => N
      case v@Var(_) => v
      case Application(e1, e2) => <>(cas(e1, x, N), cas(e2, x, N))
      case l@Lambda(v, _) if v.equals(x) => l
      case l@Lambda(y, scope) if !fv(scope).contains(x) => l
      case Lambda(y, scope) if !fv(N).contains(y) => Lambda(y, cas(scope, x, N))
      case l@Lambda(y, scope) =>
        val nv: Var[String] = fresh(fv(scope).union(fv(N)), y)
        Lambda(nv, cas(cas(scope, y, nv), x, N))
    }
  }

  def alpha(term: Exp[String], from: Var[String], to: Var[String]): Exp[String] = cas(term, from, to)

  def alphaconversion(term: Exp[String]): Exp[String] = term match {
    case Lambda(v, scope) =>
      val nv: Var[String] = fresh(fv(scope), v)
      Lambda(nv, alphaconversion(alpha(scope, v, nv)))
    case e: Exp[String] => e
  }

  def beta(term: Exp[String], from: Var[String], to: Exp[String]): Exp[String] = cas(term, from, to)

  def betaconversion(term: Exp[String]): Exp[String] = term match {
    case Lambda(v, scope) => Lambda(v, betaconversion(scope))
    case Application(e1: Application[String], e2) => betaconversion(Application(betaconversion(e1), e2))
    case Application(e1: Lambda[String], e2) => betaconversion(beta(e1.scope, e1.v, e2))
    case e: Exp[String] => e
  }

  def red(term: Exp[String]): Exp[String] = betaconversion(term)


}