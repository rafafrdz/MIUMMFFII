//package mf.tlp.lambdaCalculus.adt
//
//sealed trait OLExp[Repr[_]] {
//  def vx[T](value: T): Repr[T => T]
//
//  def lambda[T, S](scope: => Repr[T] => Repr[S]): Repr[T => S]
//
//  def application[T, S, A](e1: Repr[A => S], e2: => Repr[T => A]): Repr[T] => Repr[S]
//}
//
//sealed trait RLExp[T] {
//  def vr[A](value: T): A => T = (_: A) => value
//
//  def \[S,B](scope: => S): S = scope
//
//  def <>[S, A, B](e1:  A => S, e2: B => A): B => S =  e1.compose(e2)
//}
//
//object example extends App {
//
//  def rlexId[T]: RLExp[T] = new RLExp[T] {}
//
//  val exp = rlexId[Int]
//
//  import exp._
//
//  val x = vr(1)
//  val y = vr(2)
//  val z = vr(3)
//  val l1 = \(y)
//  val l2 = \(x)
//  val id = \((x: Int) => x)
//  val l3 = \(\(<>(id,y)))
//  val algo = <>(id,y)
//  //  val TRUE = \((x:String) => \( (y: String) => <>(x,y)))
//  println(algo())
//  //  val FALSE = \(\( <>(y,x)))
//  //  val NEG: String => String => String => String = <>(FALSE, TRUE) // todo
//  //  println(TRUE("a")("b"))
//  //  println(FALSE("a")("b"))
//}