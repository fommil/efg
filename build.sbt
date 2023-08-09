organization := "com.fommil"
name := "electronics"

licenses := List(License.GPL3_or_later)
ThisBuild / scalaVersion := "2.13.11"

libraryDependencies += "com.fommil" %% "jzon" % "1.1.0"

scalacOptions += "-Ywarn-unused"

assembly / assemblyOutputPath := file(s"${name.value}.jar")
assemblyMergeStrategy := {
  case "rootdoc.txt" => MergeStrategy.discard
  case x => assemblyMergeStrategy.value(x)
}

// TODO reverse engineer all the examples from McCluskey
// TODO Ben Eater's digital LED
// TODO full adder
// TODO 4 bit adder
