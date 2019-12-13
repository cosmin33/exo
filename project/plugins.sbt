// Allows To Continuously Reload Applications
addSbtPlugin("io.spray" % "sbt-revolver" % "0.9.1")

// Allows Scala.js Compilation
addSbtPlugin("org.scala-js" % "sbt-scalajs" % "0.6.29")
addSbtPlugin("org.portable-scala" % "sbt-scalajs-crossproject" % "0.6.1")

// Extract metadata from sbt and make it available to the code
addSbtPlugin("com.eed3si9n" % "sbt-buildinfo" % "0.9.0")

addSbtPlugin("com.timushev.sbt" % "sbt-updates" % "0.4.2")

addSbtPlugin("ch.epfl.scala" % "sbt-bloop" % "1.3.2")
addSbtPlugin("ch.epfl.scala" % "sbt-scalajs-bundler" % "0.15.0-0.6")
addSbtPlugin("org.wartremover" % "sbt-wartremover" % "2.4.2")
