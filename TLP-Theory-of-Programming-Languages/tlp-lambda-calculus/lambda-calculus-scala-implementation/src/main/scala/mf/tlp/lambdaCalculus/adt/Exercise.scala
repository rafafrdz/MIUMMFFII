package mf.tlp.lambdaCalculus.adt

import mf.tlp.lambdaCalculus.adt.Exp.v

trait Exercise extends App {
  val x: Var[String] = v("x")

  val y: Var[String] = v("y")

  val b: Var[String] = v("b")

  val a: Var[String] = v("a")

  val f: Var[String] = v("f")

  val p: Var[String] = v("p")

  val z: Var[String] = v("z")

  def evaluate(x: Any*): Unit = x foreach println

}
