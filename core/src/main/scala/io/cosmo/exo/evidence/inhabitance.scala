package io.cosmo.exo.evidence

import cats.{Contravariant, ContravariantSemigroupal, FlatMap, Monad, Semigroupal, StackSafeMonad}
import cats.implicits._
import io.cosmo.exo.Iso.HasIso
import io.cosmo.exo._
import io.estatico.newtype.Coercible
import io.estatico.newtype.macros.newsubtype
import io.estatico.newtype.ops._

import scala.language.experimental.macros

/**
 * Inspired from Alexander Konovalov's library: https://github.com/alexknvl/leibniz
 */
object inhabitance {

  trait Proposition[A] extends WeakProposition[A] { A =>
    def proved(implicit A: ¬¬[A]): A

    def isomap[B](f: A <=> B): Proposition[B] =
      (p: ¬¬[B]) => f.to(A.proved(p.map(f.from)))

    def zip[B](implicit B: Proposition[B]): Proposition[(A, B)] =
      (proof: ¬¬[(A, B)]) => (A.proved(proof.map(_._1)), B.proved(proof.map(_._2)))
  }

  object Proposition {
    def apply[A](implicit A: Proposition[A]): Proposition[A] = A

    def witness[A](fn: ¬¬[A] => A): Proposition[A] = (A: ¬¬[A]) => fn(A)

    // This covers the initial object.
    implicit val voidIsProposition: Proposition[Void] =
      (p: ¬¬[Void]) => p.run(a => a)

    // This covers Unit & other terminal objects.
    implicit def unitProp: Proposition[Unit] = (_: ¬¬[Unit]) => ()
    implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): Proposition[A] =
      (_: Inhabited[A]) => A.value

    implicit def negation[A]: Proposition[¬[A]] = negationV[A].isomap(Uninhabited.isoCanonic[A])

    def negationV[A]: Proposition[A => Void] = new Proposition[A => Void] {
      override def proved(implicit A: ¬¬[A => Void]): A => Void = (a: A) =>
        A.run((k : A => Void) => k(a))
    }

    // Proposition is proposition
    implicit def propOfProp[A](implicit prop: Proposition[A]): Proposition[Proposition[A]] =
      (_: Inhabited[Proposition[A]]) => prop

    implicit def semigroupal: Semigroupal[Proposition] = new Semigroupal[Proposition] {
      def product[A, B](fa: Proposition[A], fb: Proposition[B]) = fa.zip(fb)
    }
  }

  @newsubtype class Uninhabited[A](val run: A => Void) {

    def contradicts(a: A): Void = run(a)

    def notInhabited(a: ¬¬[A]): Void = a.contradicts(run)

    def contramap[B](f: B => A): ¬[B] = ¬.witness[B](f >>> run)

    def zip[B](notB: ¬[B]): ¬[Either[A, B]] = ¬.witness[Either[A, B]](_.fold(run, notB.run))
  }

  object Uninhabited {
    def apply[A](implicit ev: ¬[A]): ¬[A] = ev

    def witness[A](f: A => Void): ¬[A] = f.coerce[¬[A]]

    def eqCanonic [A]: (A => Void) === ¬[A] = implicitly[(A => Void) === ¬[A]]

    def isoCanonic[A]: (A => Void) <=> ¬[A] = <=>[A => Void, ¬[A]]

    def contramap2[A, B, C](p: ¬¬[Either[¬[A], ¬[B]]])(f: C => (A, B)): ¬[C] =
      witness { c =>
        val (a, b) = f(c)
        p.contradicts {
          case Left(notA) => notA.contradicts(a)
          case Right(notB) => notB.contradicts(b)
        }
      }

    def codivide[A, B, C](p: ¬¬[(¬[A], ¬[B])])(f: C => Either[A, B]): ¬[C] =
      witness { c =>
        p.contradicts { case (notA, notB) =>
          f(c) match {
            case Left(a) => notA.contradicts(a)
            case Right(b) => notB.contradicts(b)
          }
        }
      }

    implicit def inhabited[A](implicit A: ¬[A]): ¬¬[¬[A]] = ¬¬.witness(f => f(A))

    implicit def uninhabited[A](implicit A: ¬¬[A]): ¬[¬[A]] = ¬.witness(nA => A.notUninhabited(nA))

    implicit def func[A, B](implicit A: ¬¬[A], B: ¬[B]): ¬[A => B] = ¬.witness(f => A.notUninhabited(B.contramap(f)))

    def proposition[A]: Proposition[¬[A]] =
      Proposition.witness((nnA: ¬¬[¬[A]]) => ¬.witness((a : A) => nnA.contradicts(A => A.contradicts(a))))

    implicit def contraSem: Contravariant[¬] = Contravariant[* => Void].coerce
  }

  @newsubtype class Inhabited[A](val run: (A => Void) => Void) {
    def contradicts(f: A => Void): Void = run(f)
    def notUninhabited(f: ¬[A]): Void = contradicts(f.contradicts)
    def proved(implicit ev: Proposition[A]): A = ev.proved(this)
  }
  trait InhabitedLowerPriority {
    implicit def mkInhabited[A]: ¬¬[A] = macro evidence.internal.MacroUtil.mkInhabited[A]
  }
  object Inhabited extends InhabitedLowerPriority {
    def apply[A](implicit A: ¬¬[A]): ¬¬[A] = A
    def witness[A](f: (A => Void) => Void): ¬¬[A] = f.coerce
    def value[A](a: A): ¬¬[A] = witness[A](f => f(a))

    implicit def isoCanonic[A]: ((A => Void) => Void) <=> ¬¬[A] = Iso.unsafe(witness, _.run)

    def lemEither[A]: ¬¬[Either[A => Void, A]] = witness(k => k(Left(a => k(Right(a)))))

    def lemDisj[A]: ¬¬[(A => Void) \/ A] = witness(k => k(-\/(a => k(\/-(a)))))

    implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): ¬¬[A] =
      witness(f => f(A.value))

    implicit def inhabited[A](implicit A: ¬¬[A]): ¬¬[¬¬[A]] =
      witness(f => f(A))

    implicit def uninhabited[A](implicit na: ¬[A]): ¬[¬¬[A]] =
      ¬.witness(A => A.notUninhabited(na))

    implicit def proposition[A]: Proposition[¬¬[A]] =
      Proposition.witness((p: ¬¬[¬¬[A]]) => p.flatMap(identity))

    implicit def contractible[A](implicit A: ¬¬[A]): Contractible[¬¬[A]] =
      Contractible.witness[¬¬[A]](inhabited, proposition[A])

    /**
     * Law of excluded middle.
     */
    def lem[A]: ¬¬[¬[A] \/ A] = lemEither[A].map(e => \/(e.left.map(¬.witness[A])))

    def and[A, B](f: (A, B) => Void): ¬¬[(A => Void) \/ (B => Void)] =
      witness(p => p(\/-(b => p(-\/(a => f(a, b))))))

    def imp[A, B](f: A => B): ¬¬[(A => Void) \/ B] = witness(k => k(-\/(a => k(\/-(f(a))))))

    def andE[A, B](f: (A, B) => Void): ¬¬[Either[A => Void, B => Void]] =
      witness(p => p(Right(b => p(Left(a => f(a, b))))))

    def impE[A, B](f: A => B): ¬¬[Either[A => Void, B]] =
      witness(k => k(Left(a => k(Right(f(a))))))

    def pierce[A]: ¬¬[((A => Void) => A) => A] =
      witness(k => k((p: (A => Void) => A) => p((a: A) => k(_ => a))))

    implicit def monad: Monad[Inhabited] = new StackSafeMonad[¬¬] {
      def pure[A](a: A): ¬¬[A] = value(a)
      def flatMap[A, B](fa: ¬¬[A])(f: A => ¬¬[B]): ¬¬[B] = ¬¬.witness[B](k => fa.run(a => f(a).run(k)))
    }

  }

  final case class Contractible[A](inhabited: Inhabited[A], proposition: WeakProposition[A]) {
    /** All inhabited subtypes of a contractible type are equal. */
    def contract[B](implicit p: B <~< A, B: Inhabited[B]): B === A =
      proposition.equal[B, A](InhabitedSubset(p, B), InhabitedSubset(As.refl[A], inhabited))
  }
  object Contractible {
    def apply[A](implicit A: Contractible[A]): Contractible[A] = A

    implicit def isoCanonic[A]: (¬¬[A], WeakProposition[A])  <=> Contractible[A] =
      Iso.unsafe({case (i, w) => witness(i, w)}, c => (c.inhabited, c.proposition))

    implicit def witness[A](implicit inhabited: ¬¬[A], proposition: WeakProposition[A]): Contractible[A] =
      Contractible[A](inhabited, proposition)

    implicit def singleton[A <: Singleton](implicit A: ValueOf[A]): Contractible[A] =
      new Contractible[A](¬¬.value(A.value), Proposition.singleton[A])
  }

  /** Witnesses that all `(a: A)` are equal, that [[A <~< B]] and that [[A]] is inhabited. */
  sealed abstract class SingletonOf[A, +B] { ab =>
    import SingletonOf._

    def conforms: A <~< B
    def isInhabited: Inhabited[A]
    def isProposition: Proposition[A]
    def isContractible: Contractible[A]

    def andThen[BB >: B, C](bc: SingletonOf[BB, C]): SingletonOf[A, C] =
      witness[A, C](isInhabited.contradicts, conforms andThen bc.conforms, isProposition)

    def compose[Z](za: SingletonOf[Z, A]): SingletonOf[Z, B] =
      za andThen ab

    def contract[C](implicit C: Inhabited[C], ca: C <~< A): C === A =
      isContractible.contract[C](ca, C)

    def contract_(c: A): c.type === A =
      contract[c.type](Inhabited.value(c), As.refl[c.type])

    def equal[X <: A, Y <: A](x: X, y: Y): X === Y =
      isProposition.equal[X, Y](
        InhabitedSubset[X, A](As.refl[X], Inhabited.value(x)),
        InhabitedSubset[Y, A](As.refl[Y], Inhabited.value(y)))

    def equal_(x: A, y: A): x.type === y.type =
      equal[x.type, y.type](x, y)

    def piSigma[F[_]](a: A)(f: Pi[B, F]): Sigma[A, F] = {
      //val ir: A === a.type = Is.refl[a.type]
      val s: Sigma[A, * === a.type] = Sigma[A, λ[x => x === a.type]](a)(Is.refl[a.type])
      type f[+x] = Sigma[x, λ[x => x === a.type]]
      val b: Sigma[B, λ[x => x === a.type]] = conforms.substCv[f](s)

      val p : b.first.type === a.type = b.second
      Sigma.apply[A, F](a)(b.second.subst[F](f(b.first)))
    }

    def pi[F[_]](a: A)(f: Pi[B, F]): F[A] = {
      val s = Sigma[A, λ[x => x === A]](a)(contract_(a))
      type f[+x] = Sigma[x, λ[x => x === A]]
      val b: Sigma[B, λ[x => x === A]] = conforms.substCv[f](s)

      b.second.subst[F](f(b.first))
    }

    def pi_[F[_]](a: A)(f: Pi[B, F]): F[a.type] = {
      val s = Sigma[A, λ[x => x === a.type]](a)(Is.refl[a.type])
      type f[+x] = Sigma[x, λ[x => x === a.type]]
      val b: Sigma[B, λ[x => x === a.type]] = conforms.substCv[f](s)

      b.second.subst[F](f(b.first))
    }
  }
  object SingletonOf {
    private[this] final class Witness[A, B](
      proof: (A => Void) => Void,
      val conforms: A <~< B,
      val isProposition: Proposition[A]
    ) extends SingletonOf[A, B] {
      val isInhabited: Inhabited[A] = Inhabited.witness[A](proof)

      val isContractible: Contractible[A] = Contractible.witness[A](isInhabited, isProposition)
    }

    def apply[A, B](implicit ev: SingletonOf[A, B]): SingletonOf[A, B] = ev

    def witness[A, B](proof: (A => Void) => Void, conformity: A <~< B,
      proposition: Proposition[A]): SingletonOf[A, B] =
      new Witness[A, B](proof, conformity, proposition)

    implicit def refl[A <: Singleton](implicit A: ValueOf[A]): SingletonOf[A, A] =
      witness[A, A](f => f(A.value), As.refl[A], Proposition.singleton[A])
  }
}
