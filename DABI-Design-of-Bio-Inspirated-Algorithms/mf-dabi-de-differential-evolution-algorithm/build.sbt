name := "mf-dabi-de-differential-evolution-algorithm"

version := "0.1"

scalaVersion := "2.13.5"
libraryDependencies ++= Seq(
  "org.scalanlp" %% "breeze" % "1.2" withSources(),
  "org.scalanlp" %% "breeze-viz" % "1.2" withSources(),
  "org.scala-lang.modules" %% "scala-parallel-collections" % "1.0.0"

)