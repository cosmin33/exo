import sbtcrossproject.CrossPlugin.autoImport.crossProject
import sbtcrossproject.CrossType

inThisBuild(Seq(
  organization := "io.github.cosmin33",
  scalaVersion := "3.3.7",
  version := "0.0.1",
  crossScalaVersions := Seq("3.3.7"),
  scalacOptions ++= Seq("-unchecked", "-deprecation"),
))

lazy val versionOf = new {
  val zioTest = "2.0.13"
}

lazy val publishSettings = Seq(
  licenses += ("MIT", url("http://opensource.org/licenses/MIT")),
  homepage := Some(url("https://github.com/cosmin33/exo")),
  scmInfo := Some(ScmInfo(
    url("https://github.com/cosmin33/exo"),
    "scm:git@github.com:cosmin33/exo.git",
  )),
  developers := List(Developer(
    id    = "cosmin33",
    name  = "Cosmo",
    email = "3cosmo@gmail.com",
    url   = url("https://github.com/cosmin33"),
  )),
  publishMavenStyle := true,
  sonatypeCredentialHost := "central.sonatype.com",
  publishTo := sonatypePublishToBundle.value,
)

lazy val commonSettings = Seq(
  organization := "io.github.cosmin33",
  version := "0.0.1",
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
  .settings(publishSettings)
