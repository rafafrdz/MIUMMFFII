package dev.tfm.redblack.domain

trait Functor[F[_]] {
  def fmap[A, B](f: A => B)(fa: F[A]): F[B]
}

object Functor {

  implicit val rbtreeFunctor: Functor[RBTree] = new Functor[RBTree] {
    def fmap[A, B](f: A => B)(fa: RBTree[A]): RBTree[B] = fa match {
      case binary: RBTreeBinary[A] => new RBTreeBinary[B] {
        override val refName: String = binary.refName
        val value: B = f(binary.value)
        val left: RBTree[B] = fmap(f)(binary.left)
        val right: RBTree[B] = fmap(f)(binary.right)
      }
      case Nil => Nil
    }
  }

}
