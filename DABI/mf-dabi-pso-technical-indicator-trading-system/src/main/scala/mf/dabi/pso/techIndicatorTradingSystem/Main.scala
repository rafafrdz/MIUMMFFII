package mf.dabi.pso.techIndicatorTradingSystem

import org.apache.spark.sql.functions.col
import org.apache.spark.sql.{DataFrame, SparkSession}

object Main {

  lazy val spark: SparkSession =
    SparkSession
      .builder()
      .master("local[*]")
      .getOrCreate()

  /** Format Date: YYYY-mm-dd */
  val data: DataFrame = spark.read.option("header", true).csv("src/main/resources/historical-data/csv/stocks/AAPL.csv")

  def showFrom(date: String): Unit =
    data.where(col("Date")>=date).show(false)


  def main(args: Array[String]): Unit = {
    val date: String = "2021-07-10"
    showFrom(date)
  }

}
