package io.cosmo.exo.categories.play

object AlexKnvlDeptypesPlay {

  // Type-level pairs.
  final class Pair[a, b] { type Cata[g[_, _]] = g[a, b] }
  type FF[A, B] = A
  type SS[A, B] = B
  type Fst[t[_[_, _]]] = t[FF]
  type Snd[t[_[_, _]]] = t[SS]
//  type Fst[t[_[_, _]]] = t[λ[(a, b) => a]]
//  type Snd[t[_[_, _]]] = t[λ[(a, b) => b]]

  // Bounded equality.
  sealed abstract class EqT[+H, A <: H, B <: H] {
    def subst[F[_ <: H]](fa: F[A]): F[B]
  }
  object EqT {
    def refl[A]: EqT[A, A, A] = new EqT[A, A, A] {
      def subst[F[_ <: A]](fa: F[A]): F[A] = fa
    }

    def force[H, A <: H, B <: H] = new EqT[H, A, B] {
      def subst[F[_ <: H]](fa: F[A]): F[B] = fa.asInstanceOf[F[B]]
    }
  }

  // A "type" t consists of a pair of type-level `Fst[...]` and a value-level `Snd[...]`.
  type Type[t[_[_, _]]] = Fst[t]
  type Value[t[_[_, _]]] = Snd[t]

  // Witnesses witness that a type-level value has a certain value-level value.
  final case class Witness[t[_[_, _]], A <: Type[t]](value: Value[t]) extends AnyVal

  // Existentially bound value. Similar to `Witness[t, A] forSome { A <: Type[t] }`
  trait Exists[t[_[_, _]]] {
    type A <: Type[t]
    def value: Witness[t, A]
  }

  // Sigma-type.
  trait Sigma[t[_[_, _]], P[_ <: Type[t]]] {
    type First <: Type[t]
    def first: Witness[t, First]
    def second: P[First]
  }

  // Pi-type.
  trait Pi[t[_[_, _]], P[_ <: Type[t]]] {
    def run[A <: Type[t]](implicit value: Witness[t, A]): P[A]
  }

  // Naturals are represented as Ints at runtime.
  type Nat[f[_, _]] = f[Nat.Type, Int]
  object Nat {
    sealed abstract class Type
    final class Z private() extends Type
    final class S[N <: Type] extends Type

    implicit val zValue: Witness[Nat, Z] = Witness[Nat, Z](0)
    implicit def sValue[N <: Type](implicit N: Witness[Nat, N]): Witness[Nat, S[N]] =
      Witness[Nat, S[N]](N.value + 1)
  }

  // Lift a runtime value to type-level.
  def lift[t[_[_, _]]](x: Snd[t]): Exists[t] = new Exists[t] {
    type A = Type[t]
    def value: Witness[t, A] = Witness[t, A](x)
  }

  // Evaluate a type-level value.
  def eval[t[_[_, _]], N <: Type[t]](implicit N: Witness[t, N]): Value[t] = N.value

  // Compare two type-level values.
  def cmp[t[_[_, _]], N <: Type[t], M <: Type[t]](n: Witness[t, N], m: Witness[t, M])(implicit eq: Equiv[Value[t]]): Option[EqT[Type[t], N, M]] =
    if (eq.equiv(n.value, m.value))
      Some(EqT.force[Type[t], N, M])
    else None

  import Nat._
  println(eval[Nat, S[S[Z]]])

  println({
    val a = lift[Nat](10)
    val b = lift[Nat](10)

    cmp[Nat, a.A, b.A](a.value, b.value) match {
      case Some(proof) =>
        type f[a <: Type[Nat]] = Witness[Nat, a]
        proof.subst[f](a.value) : Witness[Nat, b.A]
      case None =>
        ???
    }
  })

}
