// Allows To Continuously Reload Applications
addSbtPlugin("io.spray" % "sbt-revolver" % "0.9.1")

// Allows Scala.js Compilation
addSbtPlugin("org.scala-js" % "sbt-scalajs" % "1.0.1")
addSbtPlugin("org.scala-js" % "sbt-jsdependencies" % "1.0.0")
addSbtPlugin("org.portable-scala" % "sbt-scalajs-crossproject" % "1.0.0")

// Extract metadata from sbt and make it available to the code
addSbtPlugin("com.eed3si9n" % "sbt-buildinfo" % "0.9.0")

addSbtPlugin("com.timushev.sbt" % "sbt-updates" % "0.4.2")

//addSbtPlugin("ch.epfl.scala" % "sbt-bloop" % "1.3.2")
addSbtPlugin("ch.epfl.scala" % "sbt-scalajs-bundler" % "0.17.0")
addSbtPlugin("org.wartremover" % "sbt-wartremover" % "2.4.7")
