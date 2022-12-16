package io.cosmo.exo

import cats.implicits._

object Test {


  sealed trait Opt[+A] {
    def fold[B](ifEmpty: Unit => B)(ifDefined: A => B): B
  }

  case class Som[A](value: A) extends Opt[A] {
    override def fold[B](ifEmpty: Unit => B)(ifDefined: A => B): B = ifDefined(value)
  }

  object Non extends Opt[Nothing] {
    override def fold[B](ifEmpty: Unit => B)(ifDefined: Nothing => B): B = ifEmpty(())
  }

//  trait Opt1[+A] {
//    def ifEmpty[B]: Unit => B
//    def ifDefined[B]: A => B
//  }

  def main(args: Array[String]): Unit = {
    println("Hello, world!")
  }

}
