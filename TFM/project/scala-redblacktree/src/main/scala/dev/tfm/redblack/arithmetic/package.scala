package dev.tfm.redblack

package object arithmetic {
  object implicits {
    implicit val int2peano: Int => Peano = Peano.from
    implicit val peano2int: Peano => Int = Peano.to
  }
}
