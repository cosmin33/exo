package io.cosmo.exo.categories.play

import scala.annotation.tailrec

object CampbellPlay {

  sealed abstract class Eq[+H, A <: H, B <: H] private[Eq] () { ab =>
    def subst[F[_ <: H]](fa: F[A]): F[B]

    final def coerce(a: A): B =
      subst[λ[α => α]](a)

    final def andThen[H2 >: H, C <: H2](bc: Eq[H2, B, C]): Eq[H2, A, C] =
      Eq.trans[H2, A, B, C](bc, ab)

    final def compose[H2 >: H, ZZ <: H2](za: Eq[H2, ZZ, A]): Eq[H2, ZZ, B] =
      Eq.trans[H2, ZZ, A, B](ab, za)

    final def flip: Eq[H, B, A] =
      Eq.sym(ab)

    final def lift[HF, F[_ <: H] <: HF]: Eq[HF, F[A], F[B]] =
      Eq.lift[H, A, B, HF, F](ab)
  }
  object Eq {
    private[this] final case class Refl[A]() extends Eq[A, A, A] {
      def subst[F[_ <: A]](fa: F[A]): F[A] = fa
    }
    private[this] val anyRefl: Eq[Any, Any, Any] = Refl[Any]()

    def assert[H, A <: H, B <: H]: Eq[H, A, B] =
      anyRefl.asInstanceOf[Eq[H, A, B]]

    def refl[A]: Eq[A, A, A] = assert[A, A, A]
    def refl_[H, A <: H]: Eq[H, A, A] = assert[H, A, A]

    def trans[H, A <: H, B <: H, C <: H](bc: Eq[H, B, C], ab: Eq[H, A, B]): Eq[H, A, C] =
      bc.subst[λ[`α <: H` => Eq[H, A, α]]](ab)

    def sym[H, A <: H, B <: H](ab: Eq[H, A, B]): Eq[H, B, A] =
      ab.subst[λ[`α <: H` => Eq[H, α, A]]](refl)

    def lift[H, A <: H, B <: H, HF, F[_ <: H] <: HF] (eq: Eq[H, A, B]): Eq[HF, F[A], F[B]] =
      eq.subst[λ[`α <: H` => Eq[HF, F[A], F[α]]]](refl_[HF, F[A]])
  }

  // Type and Value holes.
  type ??? = Nothing with ({ type Type = Nothing })
  def ??? : ??? = throw new scala.NotImplementedError("???")

  trait Lifted { self =>
    type Type >: self.type
    type Value
  }

  trait Value[A <: Lifted] {
    def value: A#Value
  }

  object Value {
    def apply[T <: Lifted](implicit T: Value[T]): T#Value =
      T.value

    def cmp[H <: Lifted, A <: H, B <: H](a: Value[A], b : Value[B]): Option[Eq[H, A, B]] =
      if (a.value == b.value) Some(Eq.assert[H, A, B]) else None
  }

  trait Reduce[T <: Lifted] {
    type Result <: T#Type
    def proof: Eq[T#Type, T, Result]
  }

  object Reduce {
    trait Aux[T <: Lifted, R <: T#Type] extends Reduce[T] {
      type Result = R
    }

    def assert[T <: Lifted, R <: T#Type]: Aux[T, R] = new Aux[T, R] { def proof = Eq.assert[T#Type, T, R] }

    def apply[T <: Lifted](implicit r: Reduce[T]): Eq[T#Type, T, r.Result] = r.proof
  }


  def test[N <: Nat, M <: Nat]: Unit = {
    println(Reduce[S[N] + S[M]])
  }
  test[S[Z], Z]
  println(Reduce[S[Z] + Z])

  trait Exists[H, F[_ <: H]] {
    type Type <: H
    def value: F[Type]
  }

  // data Nat : Type where
  //   Z : Nat
  //   S : Nat -> Nat
  sealed trait NatV
  object NatV {
    final case object Z extends NatV
    final case class S(v: NatV) extends NatV
  }

  sealed trait Nat extends Lifted { type Type = Nat; type Value = NatV }
  final class Z private () extends Nat { override type Type = Nat }
  final class S[N <: Nat] private () extends Nat { override type Type = Nat }

  object Nat {
    implicit def z: Value[Z] =
      new Value[Z] { def value = NatV.Z }
    implicit def s[N <: Nat](implicit N: Value[N]): Value[S[N]] =
      new Value[S[N]] { def value = NatV.S(N.value) }
  }

  type ===[A <: Nat, B <: Nat] = Eq[Nat, A, B]

  final class Plus[n <: Nat, m <: Nat] private () extends Nat
  type +[n <: Nat, m <: Nat] = Plus[n, m]
  trait LowerPriority {
    implicit def concrete[T <: Lifted]: Reduce.Aux[T, T] = new Reduce.Aux[T, T] { def proof = Eq.refl }
  }
  object Plus extends LowerPriority {
    def plus(n : NatV, m : NatV): NatV = n match {
      case NatV.Z    => m
      case NatV.S(n) => NatV.S(plus(n, m))
    }

    // These are used for proofs and/or for type-level computations.
    // def case1[m <: Nat]:           (Z    + m) ===       m  = Eq.assert
    // def case2[n <: Nat, m <: Nat]: (S[n] + m) === S[n + m] = Eq.assert

    implicit def case1r[M <: Nat]: Reduce.Aux[Z + M, M] =
      Reduce.assert
    implicit def case2r[N <: Nat, M <: Nat]
    (implicit rec: Reduce[N + M]): Reduce.Aux[S[N] + M, S[rec.Result]] =
      Reduce.assert

    // All three functions (value-level, type-level, and "witness-level")
    // must be the same.
    implicit def run[N <: Nat, M <: Nat](implicit N: Value[N], M: Value[M]): Value[N + M] =
      new Value[N + M] { def value: NatV = plus(N.value, M.value) }
  }

  //plus_commutes_Z : m = plus m 0
  final case class PlusCommutes[m <: Nat](proof: m === (m + Z))
  object PlusCommutes {
    implicit def plus_commutes_Z_1: PlusCommutes[Z] =
      PlusCommutes(Reduce[Z + Z].flip)
    implicit def plus_commutes_Z_2[n <: Nat](rec: PlusCommutes[n]): PlusCommutes[S[n]] = PlusCommutes {
      val p1: (S[n] + Z) === S[n + Z] = Reduce[S[n] + Z]
      val p2: n          === (n + Z)  = rec.proof
      val p3: S[n]       === S[n + Z] = p2.lift[Nat, S]
      (p1 andThen p3.flip).flip
    }

    // If we know it's total, we can just assert it.
    // totality of proofs leads to erasure of witnesses.
  }

  sealed trait Vec[N <: Nat, +A] extends Product with Serializable {
    import Vec._

    def ::[B >: A](el: B): Vec[S[N], B] = new ::[N, B](el, this)

    def ++[M <: Nat, B >: A](u : Vec[M, B]): Vec[N + M, B]

    def map[B](f: A => B): Vec[N, B]

    final def simplify(implicit r: Reduce[N]): Vec[r.Result, A] = {
      type f[a <: Nat] = Vec[a, A]
      r.proof.subst[f](this)
    }
  }
  object Vec {
    final case object Nil extends Vec[Z, Nothing] {
      def ++[M <: Nat, A](u : Vec[M, A]): Vec[Z + M, A] = {
        type f[a <: Nat] = Vec[a, A]
        Reduce[Z + M].flip.subst[f](u)
      }

      def map[B](f: Nothing => B): Vec[Z, B] = Nil
    }
    final case class ::[N <: Nat, A](head: A, tail: Vec[N, A]) extends Vec[S[N], A] {
      def ++[M <: Nat, B >: A](u : Vec[M, B]): Vec[S[N] + M, B] = {
        val u1: Vec[N + M, B] = tail ++ u
        type f[a <: Nat] = Vec[a, B]
        Reduce[S[N] + M].flip.subst[f](new ::[N + M, B](head, u1))
      }

      def map[B](f: A => B): Vec[S[N], B] =
        f(head) :: tail.map(f)
    }
  }

  def listToVec[A](s: List[A]): Exists[Nat, λ[`N <: Nat` => (Value[N], Vec[N, A])]] = {
    type L[N <: Nat] = (Value[N], Vec[N, A])

    s match {
      case Nil =>
        new Exists[Nat, L] {
          type Type = Z
          def value: (Value[Z], Vec[Z, A]) = (implicitly, Vec.Nil)
        }
      case x :: xs =>
        val rec: Exists[Nat, L] = listToVec(xs)
        new Exists[Nat, L] {
          type Type = S[rec.Type]
          def value: (Value[Type], Vec[Type, A]) =
            (Nat.s(rec.value._1), x :: rec.value._2)
        }
    }
  }

  def main(args: Array[String]): Unit = {
    def test[N <: Nat, M <: Nat]: Unit = {
      println(Reduce[S[N] + S[M]])
    }
    test[S[Z], Z]

    println(s"reduce = ${Reduce[S[Z] + Z]}")

    import Vec._

    val l = (1 :: 2 :: 3 :: Nil).map(_ + 2) ++ (1 :: 2 :: Nil)

    println("===============================")
    println(Value[S[S[Z]] + S[Z]])
    println(Reduce[S[S[Z]] + S[Z]])


  }


}
