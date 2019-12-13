package io.cosmo.exo.categories.play


//trait BoxFactory {
//  type Value[+TC]
//  trait Box[+TC] extends Any {
//    def value: Value[TC]
//  }
//  type Facade[+TC] <: Box[TC]
//  implicit def Facade[TC](value: Value[TC]): Facade[TC]
//}
//
//trait BoxCompanion extends BoxFactory {
//  def apply[TC](value: Value[TC]): Facade[TC] = Facade(value)
//  def unapply[TC](facade: Facade[TC]): Some[Value[TC]] = Some(facade.value)
//}
trait BoxFactory {
  type Value[F[_], A, B]
  trait Box[F[_], A, B] extends Any {
    def value: Value[F, A, B]
  }
  type Facade[F[_], A, B] <: Box[F, A, B]
  implicit def Facade[F[_], A, B](value: Value[F, A, B]): Facade[F, A, B]
}

trait BoxCompanion extends BoxFactory {
  def apply  [F[_], A, B](value: Value[F, A, B]): Facade[F, A, B] = Facade(value)
  def unapply[F[_], A, B](facade: Facade[F, A, B]): Some[Value[F, A, B]] = Some(facade.value)
}

object BoxTest {

//  trait EitherI extends BoxFactory {
//    type Value[f[_], TC, B] = Any
//    type Facade[f[_], TC, B] <: Kleisli[f, TC, B]
//
//    override implicit def Facade[f[_], TC, B](value: Any): Facade[f, TC, B] = ???
//  }

  trait FunctorFactory {
    type Facade[+A] <: Functor[A]

    trait Functor[+A] {
      def map[B](mapper: A => B): Facade[B]
    }
  }

  object listFunctor extends FunctorFactory {
    case class Facade[+A](list: List[A]) extends Functor[A] {
      override def map[B](mapper: A => B): Facade[B] = Facade[B](list.map(mapper))
    }
  }

  type ListFunctor[A] = listFunctor.Facade[A]

  listFunctor.Facade(List(1, 2, 3)).map(_ + 1)
}

object MirrorPlay {

  sealed trait Mirror {
    type MirroredMonoType
    type MirroredLabel <: String
    type MirroredElemLabels <: (_, _)
  }

  trait Sum extends Mirror {
    def ordinal(x: MirroredMonoType): Int
  }

  trait Product extends Mirror {
    def fromProduct(p: scala.Product): MirroredMonoType
  }

//  case class ISB(i: Int, s: String, b: Boolean)
//
//  //implicitly[Mirror { type MirroredType = ISB }]
//  trait Xxx extends MirrorPlay.Product {
//    override type MirroredMonoType = ISB
//    override type MirroredLabel = ISB
//    override type MirroredElemLabels = this.type
//
//    override def fromProduct(p: scala.Product) = ???
//  }

}
