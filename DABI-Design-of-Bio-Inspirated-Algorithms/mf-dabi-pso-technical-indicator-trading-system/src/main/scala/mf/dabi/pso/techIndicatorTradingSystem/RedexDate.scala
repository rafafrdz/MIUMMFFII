package mf.dabi.pso.techIndicatorTradingSystem

import org.apache.spark.sql.functions.col
import org.apache.spark.sql.{DataFrame, SparkSession}

import scala.util.matching.Regex

object RegexDate {

  val spark: SparkSession =
    SparkSession
      .builder()
      .master("local[*]")
      .getOrCreate()

  /** Format Date: YYYY-mm-dd */
  val data: DataFrame =
    spark.read.option("header", true)
      .csv("src/main/resources/historical-data/csv/stocks/AAPL.csv")

  /** Format Date Errors */
  sealed trait FormatDateError {
    self =>
    protected val mssg: String
    protected lazy val name: String = self.getClass.getSimpleName.replace("$", "")
    protected val header: String = s"[${name}]"

    def exception: Exception = new Exception(toString)

    override def toString: String = s"${header} ${mssg}"
  }

  case object InvalidFormat extends FormatDateError {
    val mssg: String = s"Invalid date format. Advice: Try with the standard format yyyy-mm-dd"

  }


  sealed trait DateRegex {
    val pattern: String
    lazy val regex: Regex = pattern.r

    protected def map(date: String): StandardDate

    def transform(date: String): Option[StandardDate] = {
      if (date.matches(regex.regex)) Option(map(date)) else None
    }
  }

  /** yyyy[sep]mm[sep]dd format */
  case class FullDateFirstYear(sep: String) extends DateRegex {
    val pattern: String = s"([0-9]{4,})([$sep])([0-9]{2,})([$sep])([0-9]{2,})"

    override protected def map(date: String): StandardDate = date match {
      case regex(year, _, month, _, day) => StandardDate(day, month, year)
    }
  }

  /** dd[sep]mm[sep]yyyy format */
  case class FullDateLastYear(sep: String) extends DateRegex {
    val pattern: String = s"([0-9]{2,})([$sep])([0-9]{2,})([$sep])([0-9]{4,})"

    override protected def map(date: String): StandardDate = date match {
      case regex(day, _, month, _, year) => StandardDate(day, month, year)
    }
  }

  /** mm[sep]yyyy format */
  case class MonthAndYear(sep: String) extends DateRegex {
    val pattern: String = s"([0-9]{2,})([$sep])([0-9]{4,})"

    override protected def map(date: String): StandardDate = date match {
      case regex(month, _, year) => StandardDate.monthyear(month, year)
    }
  }

  /** yyyy[sep]mm format */
  case class YearAndMonth(sep: String) extends DateRegex {
    val pattern: String = s"([0-9]{4,})([$sep])([0-9]{2,})"

    override protected def map(date: String): StandardDate = date match {
      case regex(year, _, month) => StandardDate.monthyear(month, year)
    }
  }

  /** yyyy format */
  case object OnlyYear extends DateRegex {
    val pattern: String = s"([0-9]{4,})"

    override protected def map(date: String): StandardDate = date match {
      case regex(year) => StandardDate.year(year)
    }
  }

  /** Smart Constructor for correct standard date */
  case class StandardDate(day: String, month: String, year: String, sepdate: String = "-") {

    def normalize(): String = Array(year, month, day).mkString(sepdate)

    def setSeparator(newSep: String): StandardDate = StandardDate(day, month, year, newSep)

    override def toString: String = normalize()
  }

  /** Singleton */
  object StandardDate {

    private val first: String = "01"

    def build(date: String)(implicit dateRegexs: List[DateRegex]): StandardDate =
      apply(date)(dateRegexs) match {
        case Left(stddate) => stddate
        case Right(error) => throw error.exception
      }

    def year(year: String): StandardDate = {
      require(year.length == 4, "Year must have 4 digits")
      StandardDate(first, first, year)
    }

    def monthyear(month: String, year: String): StandardDate = {
      require(year.length == 4, "Year must have 4 digits")
      require(month.length == 2, "Month must have 4 digits")
      StandardDate(first, month, year)
    }

    private def apply(date: String)(dateRegexs: List[DateRegex]): Either[StandardDate, FormatDateError] =
      normalizeDate(date)(dateRegexs)

    private def normalizeDate(date: String)(dateRegexs: List[DateRegex]): Either[StandardDate, FormatDateError] =
      dateRegexs.flatMap(dtrdx => dtrdx.transform(date)).headOption match {
        case Some(standardDate) => Left(standardDate)
        case None => Right(InvalidFormat)
      }
  }

  /** Implicit Date Regex */

  implicit val dateRegexs: List[DateRegex] =
    List(
      FullDateFirstYear("/"),
      FullDateFirstYear("-"),
      FullDateLastYear("/"),
      FullDateLastYear("-"),
      MonthAndYear("/"),
      MonthAndYear("-"),
      YearAndMonth("/"),
      YearAndMonth("-"),
      OnlyYear
    )


  /** Main feature */
  def showFrom(date: String): Unit = {
    val stdDate: StandardDate = StandardDate.build(date)
    data.where(col("Date") >= stdDate).show(false)
  }

  def main(args: Array[String]): Unit = {

    val dates: List[String] =
      List(
        "2021/07/10",
        "2021-07-10",
        "10/07/2021",
        "10-07-2021",
        "2021/07",
        "2021-07",
        "07/2021",
        "07-2021",
        "2021")

    dates.map(date => StandardDate.build(date).normalize()) foreach println

    /**
     * 2021-07-10
     * 2021-07-10
     * 2021-07-10
     * 2021-07-10
     * 2021-07-01
     * 2021-07-01
     * 2021-07-01
     * 2021-07-01
     * 2021-01-01
     */

  }

}
