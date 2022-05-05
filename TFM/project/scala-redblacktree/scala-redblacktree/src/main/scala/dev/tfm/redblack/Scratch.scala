package dev.tfm.redblack

object Scratch {
  sealed trait RBTree {
    val level: Int = 0
  }

  sealed trait Color

  trait Red extends Color

  trait Black extends Color

  trait Show[Color] {
    self: RBTreeBinary[Color] =>
    val prfx: String
    //    val pretty: String

    override def toString: String = s"$prfx($n, $left, $right)"

    //    override def toString: String = show(prfx)
    def tab(n: Int) = List.fill(3 * n)("\t").mkString

    def show(ic: String): String =
      s"""
         |      ${tab(level * level)}${right}
         |      ${tab(level)}/
         |${tab(level)}$ic $n
         |      ${tab(level)}\\
         |      ${tab(level)}${left}
         |""".stripMargin
  }

  trait RBTreeBinary[Color] extends RBTree with Show[Color] {
    self =>
    val n: Int
    val left: RBTree
    val right: RBTree
    val prfx: String

    def l(_left: RBTree): RBTreeBinary[Color] = new RBTreeBinary[Color] {
      override val n: Int = self.n
      override val left: RBTree = _left
      override val right: RBTree = self.right
      override val level: Int = self.level + 1
      override val prfx: String = self.prfx
    }

    def r(_right: RBTree): RBTreeBinary[Color] = new RBTreeBinary[Color] {
      override val n: Int = self.n
      override val left: RBTree = self.left
      override val right: RBTree = _right
      override val level: Int = self.level + 1
      override val prfx: String = self.prfx
    }

    def both(_left: RBTree, _right: RBTree): RBTreeBinary[Color] = new RBTreeBinary[Color] {
      override val n: Int = self.n
      override val left: RBTree = _left
      override val right: RBTree = _right
      override val level: Int = self.level + 1
      override val prfx: String = self.prfx
    }

    def end(): RBTreeBinary[Color] = both(nil, nil)

    def red(): rt = rt(self.n, self.left, self.right)

    def black(): bt = bt(self.n, self.left, self.right)

  }

  case class bt(n: Int, left: RBTree, right: RBTree) extends RBTreeBinary[Black] {
    override val prfx: String = "b"
  }

  case class rt(n: Int, left: RBTree, right: RBTree) extends RBTreeBinary[Red] {
    override val prfx: String = "r"
  }

  case object nil extends RBTree

  implicit class Int2RBTree(m: Int) {
    def rb: bt = bt(m, nil, nil)
  }

  implicit def implicitInt2RBTree(n: Int): bt = n.rb

}

object Test extends App {

  import Scratch._

  val X1 =
    12
      .r(15
        .r(17)
        .l(13
          .r(14.red())
        )
      )
      .l(5
        .r(10.red()
          .r(11)
          .l(7
            .r(8.red())
            .l(6.red())))
        .l(3
          .r(4.red()))
      ).black()

  val X2 =
    61
      .r(85
        .r(93.red()
          .r(101)
          .l(90))
        .l(76.red()
          .r(81)
          .l(71
            .l(65.red()))))
      .l(52
        .r(55)
        .l(20
          .l(16.red())))

  println(X1)
  println(X2)


}
