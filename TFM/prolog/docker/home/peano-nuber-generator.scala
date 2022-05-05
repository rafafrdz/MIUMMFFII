object Test extends App {

  def getNum(n: Int): String = Numerals.numeral(n).toString
      .replace("f", "s")
      .replace("x", "z")
      .replace("λs.λz.", "")
      .replace(" ","")
      .replace("sz", "s(z)")

  @tailrec
  def algo(txt: String, values: List[Int]): String = values match {
    case ::(head, next) => algo(txt.replace(head.toString, getNum(head)), next)
    case Nil => txt
  }

  val txt1: String = "b(13, r(8, b(1, nil, r(6, nil, nil)), b(11, nil,nil)), r(17, b(15, nil, nil), b(25, r(22, nil,nil), r(27, nil,nil))))"
  val txt2: String = "b(13, r(8, nil, nil), r(6, nil, nil))"
  
  println(algo(txt1, List(13,8,1,6,11,17,15,25,22,27).sorted.reverse))
  println(algo(txt2, List(13,8,6).sorted.reverse))


  
//  println(getNum(13))
//  println(getNum(8))
//  println(getNum(1))
//  println(getNum(6))
//  println(getNum(11))
//  println(getNum(17))
//  println(getNum(15))
//  println(getNum(25))
//  println(getNum(22))
//  println(getNum(27))

}