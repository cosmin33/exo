import sbtcrossproject.CrossPlugin.autoImport.crossProject
import sbtcrossproject.CrossType

inThisBuild(Seq(
  organization := "io.cosmo",
  scalaVersion := "3.3.0",
  version := "0.0.1-SNAPSHOT",
  crossScalaVersions := Seq("3.3.0"),
  scalacOptions ++= Seq("-unchecked", "-deprecation"),
))

lazy val versionOf = new {
  val zioTest = "2.0.13"
}

lazy val commonSettings = Seq(
  organization := "io.cosmo",
  version := "0.0.1-SNAPSHOT",
  licenses += ("MIT", url("http://opensource.org/licenses/MIT")),
  homepage := Some(url("https://github.com/cosmin33/exo")),
  scalacOptions ++= Seq(
    "-encoding", "UTF-8",
    "-Ykind-projector:underscores",
  ),
  libraryDependencies ++= Seq(
    "dev.zio" %% "zio-test" % "2.0.13" % Test,
    "dev.zio" %% "zio-test-magnolia" % "2.0.13" % Test,
    "dev.zio" %% "zio-test-sbt" % "2.0.13" % Test,
  ),
  testFrameworks += new TestFramework("zio.test.sbt.ZTestFramework"),
)

lazy val root = project.in(file("."))
  .aggregate(
    core.jvm,
    core.js,
  )
  .settings(commonSettings)
  .settings(
    name := "exo",
    publish / skip := true,
    publish := {},
    publishLocal := {},
    publishArtifact := false,
    publishTo := None,
  )

lazy val core = crossProject(JSPlatform, JVMPlatform)
  .crossType(CrossType.Pure)
  .settings(name := "exo-core")
  .settings(commonSettings)
