package dev.tfm.redblack.arithmetic

import dev.tfm.redblack.domain.Show

sealed trait Peano extends Show[Peano]

object Peano {

  def from(n: Int): Peano =
    if (n == 0) Z else S(from(n - 1))

  def to(p: Peano): Int = p match {
    case S(n) => 1 + to(n)
    case Z => 0
  }

}

case class S(n: Peano) extends Peano {
  override val refName: String = s"s($n)"
}

case object Z extends Peano {
  override val refName: String = "z"
}
