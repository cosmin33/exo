package io.cosmo.exo.categories.play

import cats.data.Ior
import io.cosmo.exo._

object CardinalityExperiment {

  trait Cardinality[A] {
    def cardinality: BigInt
  }

  object Cardinality {
    def of[A: Cardinality]: BigInt = apply[A].cardinality
    def unsafe[A](fn: => BigInt): Cardinality[A] = new Cardinality[A] {def cardinality = fn}
    def apply[A: Cardinality]: Cardinality[A] = implicitly
  }

  implicit def booleanCardinality: Cardinality[Boolean] = Cardinality.unsafe(BigInt(2))
  implicit def longCardinality: Cardinality[Long] = Cardinality.unsafe(BigInt(2).pow(64))
  implicit def intCardinality: Cardinality[Int] = Cardinality.unsafe(BigInt(2).pow(32))
  implicit def shortCardinality: Cardinality[Short] = Cardinality.unsafe(BigInt(2).pow(16))
  implicit def byteCardinality: Cardinality[Byte] = Cardinality.unsafe(BigInt(2).pow(8))
  implicit def unitCardinality: Cardinality[Unit] = Cardinality.unsafe(1)
  implicit def nothingCardinality: Cardinality[Void] = Cardinality.unsafe(0)
  implicit def tupleCardinality[A: Cardinality, B: Cardinality]: Cardinality[(A, B)] =
    Cardinality.unsafe(Cardinality[A].cardinality * Cardinality[B].cardinality)
  implicit def eitherCardinality[A: Cardinality, B: Cardinality]: Cardinality[Either[A, B]] =
    Cardinality.unsafe(Cardinality[A].cardinality + Cardinality[B].cardinality)
  implicit def fnCardinality[A: Cardinality, B: Cardinality]: Cardinality[A => B] =
    Cardinality.unsafe(Cardinality.of[B].pow(Cardinality.of[A].toInt))
  implicit def optionCardinality[A: Cardinality]: Cardinality[Option[A]] =
    Cardinality.unsafe(Cardinality.of[A] + 1)
  implicit def iorCardinality[A: Cardinality, B: Cardinality]: Cardinality[Ior[A, B]] =
    Cardinality.unsafe(Cardinality.of[A] + Cardinality.of[B] + Cardinality.of[A] * Cardinality.of[B])


  def main(args: Array[String]): Unit = {
    println("Cosmo here")
    println(Cardinality.of[Int])
    println(Cardinality.of[Unit])
    println(Cardinality.of[Long])
    println("=========================")
    println(Cardinality.of[(Unit, (Unit, Boolean))])
    println(Cardinality.of[Either[Int, (Boolean, Unit)]])

    Cardinality.of[Int]
    Cardinality.of[(Int, Boolean)]
    Cardinality.of[(Void, Boolean)]

    Cardinality.of[(Void, Boolean)] == 0
    Cardinality.of[Either[Void, Boolean]] == 2

    Cardinality.of[Either[Void, Boolean]]

  }

}
