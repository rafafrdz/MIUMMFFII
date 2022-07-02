package dev.tfm.redblack

import dev.tfm.redblack.arithmetic.Peano
import dev.tfm.redblack.domain.RBTree

object Example {

  import arithmetic.implicits._
  import implicits._

  /**
   * Picture: pictures/01-rbtree.png
   * b(12, b(5, b(3, nil, r(4, nil, nil)), r(10, b(7, r(6, nil, nil), r(8, nil, nil)), b(11, nil, nil))), b(15, b(13, nil, r(14, nil, nil)), b(17, nil, nil)))
   */
  val example1: RBTree[Int] =
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

  /**
   * Picture: pictures/02-rbtree.png
   * b(61, b(52, b(20, r(16, nil, nil), nil), b(55, nil, nil)), b(85, r(76, b(71, r(65, nil, nil), nil), b(81, nil, nil)), r(93, b(90, nil, nil), b(101, nil, nil))))
   */
  val example2: RBTree[Int] =
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


  def main(args: Array[String]): Unit = {

    List(
      example1,
      example2,
      example1.eval[Peano],
      example2.eval[Peano]
    ) foreach println

  }

}
