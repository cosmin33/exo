package io.cosmo.exo.categories.play

import cats.{Foldable, Monad}
import cats.data.{Kleisli, ValidatedNel}
import cats.kernel.Monoid
import cats.syntax._
import cats.implicits._
import io.cosmo.exo.evidence.{<~<, ===, As, Is}

import scala.util.{Failure, Success}

class NewtypesPlay {

  object Labels {
    sealed abstract class LabelImpl {
      type T
      def apply(s: String): T
      def unwrap(lbl: T): String
      def subst[F[_]](fs: F[String]): F[T]
      def widen[F[+_]](ft: F[T]): F[String]
//      def narrow[F[_]: Foldable](fs: F[String]): ValidatedNel[String, F[T]]

      //def widen[F[_]: Functor](ft: F[T]): F[String]
      //def cwiden[F[_]: Contravariant](fs: F[String]): F[T]
    }

    // do not forget `: LabelImpl`; it is key
    val Label: LabelImpl = new LabelImpl {
      type T = String
      override def apply(s: String) = s
      override def unwrap(lbl: T) = lbl
      override def subst[F[_]](fs: F[String]) = fs
      override def widen[F[+_]](ft: F[T]): F[String] = ft
      def cwiden[F[-_]](fs: F[String]): F[Label] = Label.widen[λ[`+x` => F[x] => F[Label]]](identity)(fs)
//      override def narrow[F[_]: Foldable](fs: F[String]) =
//        fs.foldMap {string =>
//          // return errors if not OK, INil() if OK
//        }.toNel cata (Failure(_), Success(fs))

    }

    type Label = Label.T
  }

  import Labels._

  //Err: val xx = "hi there": Label
  //Err: val ff2: Label = "cosmo"
  val fst: Label = Label("first")
  val snd: Label = Label("second")

  val s: String = Label.unwrap(fst)
  val taggedList: List[Label] = Label.subst(List("hello", "world"))
  val taggedList1: List[String] = Label.widen(taggedList)

  //You can use this to untag a whole list in constant time.
  val l: List[String] = Label.subst[λ[x => List[x] => List[String]]](identity)(taggedList)
  val l1: List[String] = Label.widen(taggedList)

  def cwiden[F[-_]](fs: F[String]): F[Label] = Label.widen[λ[`+x` => F[x] => F[Label]]](identity)(fs)

  def report(xs: List[String]): Unit = ()
  val reportTagged: List[Label] => Unit = cwiden[λ[`-x` => List[x] => Unit]](report)

  //Functions and typeclass instance can be tagged or untagged, too.
  val rrr: (Label, Int) => Label =
    Label.subst[λ[x => (x, Int) => x]](_ substring _)


  val m: Monoid[String] = Monoid.instance("", _ + _)
  val ls: Monoid[Label] = Label.subst(m)
  //All of this works because subst is really evidence that, deep down, String and Label are the same.

  val refl: String === Label = Label.subst[String === *](Is.refl)
  val subt: Label <~< String = Label.widen[λ[`+x` => (Label <~< x)]](As.refl[Label])


  type KWConcrete[W, A, B] = Kleisli[(W, *), A, B]
  sealed abstract class KWImpl {
    type T[W, A, B]
    def subst[F[_[_, _, _]]](fk: F[KWConcrete]): F[T]
  }

  type KW[W, A, B] = KW.T[W, A, B]
  val KW: KWImpl = new KWImpl {
    type T[W, A, B] = KWConcrete[W, A, B]
    override def subst[F[_[_, _, _]]](fk: F[KWConcrete]) = fk
  }

  implicit def monadKW[W: Monoid, A]: Monad[KW[W, A, *]] = {
    type MF[KWC[_, _, _]] = Monad[KWC[W, A, *]]
    val rr: MF[KW.T] = KW.subst[MF](implicitly)
    rr
  }

}
