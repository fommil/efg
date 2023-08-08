organization := "com.fommil"
name := "electronics"

licenses := List(License.GPL3_or_later)
ThisBuild / scalaVersion := "2.13.11"

scalacOptions += "-Ywarn-unused"

assembly / assemblyOutputPath := file(s"${name.value}.jar")
assemblyMergeStrategy := {
  case "rootdoc.txt" => MergeStrategy.discard
  case x => assemblyMergeStrategy.value(x)
}
