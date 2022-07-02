package dev.tfm.redblack.domain


//trait Show[V, C <: Color] {
//  self: RBTreeBinary[V, C] =>
//  val refName: String
//
//  override def toString: String = s"$refName($value, $left, $right)"
//
//  def tab(n: Int): String = List.fill(3 * n)("\t").mkString
//
//  def show(ic: String): String =
//    s"""
//       |      ${tab(level * level)}${right}
//       |      ${tab(level)}/
//       |${tab(level)}$ic $value
//       |      ${tab(level)}\\
//       |      ${tab(level)}${left}
//       |""".stripMargin
//}


trait Show[+V] {
  self =>

  val refName: String

  override def toString: String = show()

  def tab(n: Int): String = List.fill(3 * n)("\t").mkString

  def show(): String = refName.toLowerCase()
}