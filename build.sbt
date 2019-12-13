import sbtcrossproject.CrossPlugin.autoImport.crossProject
import sbtcrossproject.CrossType

inThisBuild(Seq(
  organization := "io.cosmo",
  scalaVersion := "2.13.0",
  version := "0.0.1-SNAPSHOT",
  crossScalaVersions := Seq("2.13.0"),
))

lazy val versionOf = new {
  val simulacrum = "0.19.0"
  val mouse = "0.23"
  val monix = "3.1.0"
  val cats = "2.0.0"
  val scalaz = "7.2.29"
  val shapeless = "2.3.3"
  val scalaCheck = "1.14.2"
  val scalaCheckCats = "0.2.0"
  val scalatest = "3.2.0-M1"
  val estaticoNewtype = "0.4.3"
}

lazy val commonSettings = Seq(
  organization := "io.cosmo",
  version := "0.0.1-SNAPSHOT",
  licenses += ("MIT", url("http://opensource.org/licenses/MIT")),
  homepage := Some(url("https://github.com/cosmin33/exo")),
  resolvers ++= Seq(
    Resolver.sonatypeRepo("releases"),
    Resolver.sonatypeRepo("public"),
    Resolver.typesafeRepo("releases"),
    Resolver.typesafeIvyRepo("releasesIvy"),
    Resolver.sonatypeRepo("snapshots")
  ),
  addCompilerPlugin("org.typelevel" % "kind-projector" % "0.10.3" cross CrossVersion.binary),
  addCompilerPlugin("com.olegpy" %% "better-monadic-for" % "0.3.1"),
  addCompilerPlugin("com.github.tomasmikula" %% "pascal" % "0.3.5"),
  scalacOptions ++= Seq(
    "-encoding", "UTF-8",
    "-Ymacro-annotations", // macros (instead of Paradise from 2.13 on)
    "-deprecation", // Emit warning and location for usages of deprecated APIs.
    "-explaintypes", // Explain type errors in more detail.
    "-feature", // Emit warning and location for usages of features that should be imported explicitly.
    "-language:existentials", // Existential types (besides wildcard types) can be written and inferred
    "-language:experimental.macros", // Allow macro definition (besides implementation and application)
    "-language:higherKinds", // Allow higher-kinded types
    "-language:implicitConversions", // Allow definition of implicit functions called views
    "-unchecked", // Enable additional warnings where generated code depends on assumptions.
    "-Xcheckinit", // Wrap field accessors to throw an exception on uninitialized access.
    "-Xfatal-warnings", // Fail the compilation if there are any warnings.
    "-Xlint:adapted-args", // Warn if an argument list is modified to match the receiver.
    "-Xlint:constant", // Evaluation of a constant arithmetic expression results in an error.
    "-Xlint:delayedinit-select", // Selecting member of DelayedInit.
    "-Xlint:doc-detached", // A Scaladoc comment appears to be detached from its element.
    "-Xlint:inaccessible", // Warn about inaccessible types in method signatures.
    "-Xlint:infer-any", // Warn when a type argument is inferred to be `Any`.
    "-Xlint:missing-interpolator", // A string literal appears to be missing an interpolator id.
    "-Xlint:nullary-override", // Warn when non-nullary `def f()' overrides nullary `def f'.
    "-Xlint:nullary-unit", // Warn when nullary methods return Unit.
    "-Xlint:option-implicit", // Option.apply used implicit view.
    "-Xlint:package-object-classes", // Class or object defined in package object.
    "-Xlint:poly-implicit-overload", // Parameterized overloaded implicit methods are not visible as view bounds.
    "-Xlint:private-shadow", // A private field (or class parameter) shadows a superclass field.
    "-Xlint:stars-align", // Pattern sequence wildcard must align with sequence component.
    "-Ywarn-extra-implicit", // Warn when more than one implicit parameter section is defined.
    "-Ywarn-numeric-widen", // Warn when numerics are widened.
    "-Ybackend-parallelism", "4", // Enable paralellisation — change to desired number!
    "-Ycache-plugin-class-loader:last-modified", // Enables caching of classloaders for compiler plugins
    "-Ycache-macro-class-loader:last-modified", // and macro definitions. This can lead to performance improvements.
  ),
  libraryDependencies ++= Seq(
    "org.typelevel"        %%% "mouse"               % versionOf.mouse,
    "com.github.mpilquist" %%% "simulacrum"          % versionOf.simulacrum,
    "org.typelevel"        %%% "cats-core"           % versionOf.cats,
//    "org.typelevel"        %%% "cats-effect"         % versionOf.catsEffect,
    "org.typelevel"        %%% "cats-free"           % versionOf.cats,
    "org.typelevel"        %%% "alleycats-core"      % versionOf.cats,
//    "org.typelevel"        %%% "cats-effect"         % versionOf.catsEffect,
    "io.monix"             %%% "monix"               % versionOf.monix,
    "org.scalaz"           %%% "scalaz-core"         % versionOf.scalaz,
    "com.github.alexarchambault" %%% "scalacheck-shapeless_1.14" % "1.2.3",
    "io.estatico"          %%% "newtype"             % versionOf.estaticoNewtype,
    "io.chrisdavenport"    %%% "cats-scalacheck"     % versionOf.scalaCheckCats, // % Test,
    "org.scalatest"        %%% "scalatest"           % versionOf.scalatest % Test,
    "org.scalacheck"       %%% "scalacheck"          % versionOf.scalaCheck % Test,
    "com.chuusai"          %%% "shapeless"           % versionOf.shapeless,
  )
)

lazy val root = project.in(file("."))
  .aggregate(
    core.jvm,
    core.js,
  )
  .settings(commonSettings)
  .settings(
    name := "exo",
    skip in publish := true,
    publish := {},
    publishLocal := {},
    publishArtifact := false,
    publishTo := None,
  )

lazy val core = crossProject(JSPlatform, JVMPlatform)
  .crossType(CrossType.Pure)
  .settings(name := "meow-mtl-core")
  .settings(commonSettings)
