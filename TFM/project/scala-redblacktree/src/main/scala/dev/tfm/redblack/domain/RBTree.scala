package dev.tfm.redblack.domain

sealed trait RBTree[+V] extends Show[V] {
  self =>
  val level: Int = 0

  def map[W](f: V => W)(implicit F: Functor[RBTree]): RBTree[W] = F.fmap(f)(self)
  def eval[W](implicit convers: V => W, F: Functor[RBTree]): RBTree[W] = map(convers)
}

case class BlackTree[V](value: V, left: RBTree[V], right: RBTree[V]) extends RBTreeBinary[V] {
  override val refName: String = "b"
}

case class RedTree[V](value: V, left: RBTree[V], right: RBTree[V]) extends RBTreeBinary[V] {
  override val refName: String = "r"
}

case object Nil extends RBTree[Nothing] {
  override val refName: String = "nil"
}

object RBTreeBinary {

  def l[V](self: RBTreeBinary[V], _left: RBTree[V]): RBTreeBinary[V] =
    new RBTreeBinary[V] {
      override val level: Int = self.level + 1
      override val refName: String = self.refName

      val value: V = self.value
      val left: RBTree[V] = _left
      val right: RBTree[V] = self.right
    }

  def r[V](self: RBTreeBinary[V], _right: RBTree[V]): RBTreeBinary[V] =
    new RBTreeBinary[V] {
      override val level: Int = self.level + 1
      override val refName: String = self.refName

      val value: V = self.value
      val left: RBTree[V] = self.left
      val right: RBTree[V] = _right
    }

  def both[V](self: RBTreeBinary[V], _left: RBTree[V], _right: RBTree[V]): RBTreeBinary[V] =
    new RBTreeBinary[V] {
      override val level: Int = self.level + 1
      override val refName: String = self.refName

      val value: V = self.value
      val left: RBTree[V] = _left
      val right: RBTree[V] = _right
    }
}

trait RBTreeBinary[V] extends RBTree[V] {
  self =>

  val value: V
  val refName: String

  val left: RBTree[V]
  val right: RBTree[V]

  def l(_left: RBTree[V]): RBTreeBinary[V] = RBTreeBinary.l(self, _left)

  def r(_right: RBTree[V]): RBTreeBinary[V] = RBTreeBinary.r(self, _right)

  def both(_left: RBTree[V], _right: RBTree[V]): RBTreeBinary[V] = RBTreeBinary.both(self, _left, _right)

  def end(): RBTreeBinary[V] = both(Nil, Nil)

  def red(): RedTree[V] = RedTree(self.value, self.left, self.right)

  def black(): BlackTree[V] = BlackTree(self.value, self.left, self.right)

  override def show(): String = s"$refName($value, $left, $right)"

}

