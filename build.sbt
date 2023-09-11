organization := "com.fommil"
name := "electronics"

licenses := List(License.GPL3_or_later)
ThisBuild / scalaVersion := "2.13.12"

libraryDependencies += "com.fommil" %% "jzon" % "1.1.0"

scalacOptions ++= Seq(
  "-Ywarn-unused",
  "-deprecation"
)

assembly / assemblyOutputPath := file(s"${name.value}.jar")
assemblyMergeStrategy := {
  case "rootdoc.txt" => MergeStrategy.discard
  case x => assemblyMergeStrategy.value(x)
}

libraryDependencies ++= Seq(
  "com.novocode" % "junit-interface" % "0.11" % Test,
  "junit"        % "junit"           % "4.13.2" % Test
)
Test / crossPaths := false // https://github.com/sbt/junit-interface/issues/35
testOptions += Tests.Argument(TestFrameworks.JUnit, "-v")
fork := true
