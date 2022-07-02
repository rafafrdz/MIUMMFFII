package dev.tfm

import dev.tfm.redblack.domain.{BlackTree, Nil}


package object redblack {
  object implicits {
    implicit class V2RBTree[V](value: V) {
      def rb: BlackTree[V] = BlackTree(value, Nil, Nil)
    }

    implicit def implicitV2RBTree[V](value: V): BlackTree[V] = value.rb

  }
}
