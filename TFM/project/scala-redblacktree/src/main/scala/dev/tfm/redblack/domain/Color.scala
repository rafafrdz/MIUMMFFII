package dev.tfm.redblack.domain

sealed trait Color
case object Red extends Color
case object Black extends Color
object Color {
  type Red = Red.type
  type Black = Black.type
}
