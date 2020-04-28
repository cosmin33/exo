package io.cosmo.exo

import cats.{Id, ⊥}
import cats.implicits._
import io.cosmo.exo.categories.{Endofunctor, Subcat, Trivial}
import io.cosmo.exo.categories.functors.{Endofunctor, Exofunctor}
import io.cosmo.exo.evidence._
import io.cosmo.exo.evidence.variance._
import shapeless.{LowPriority, Refute, the}

abstract class InstanceOfModule {
  type InstanceOf[T] <: T
  def is[T]: T === InstanceOf[T]
  def isId: InstanceOf =~= Id
}
private[exo] object InstanceOfImpl extends InstanceOfModule {
  type InstanceOf[T] = T
  def is[T] = Is.refl
  def isId = IsK.refl[Id]
}
object InstanceOfModule {
  implicit def isCovariant: IsCovariant[InstanceOf] = IsCovariant.witness(fnEq(the[Void <~< Any]))
  implicit def isInjective: IsInjective[InstanceOf] = IsInjective.witness(fnEq(the[Void =!= Any]))
  implicit def isoInstance[T]: T <=> InstanceOf[T] = InstanceOf.is[T].toIso
  private def fnEq[->[_,_], A, B]: (A -> B) === (InstanceOf[A] -> InstanceOf[B]) =
    Is.lift2[->](InstanceOf.is[A], InstanceOf.is[B])
}

/////////////////////////////////////////////////////////////////////////
// Experimental hierarchical InstanceOf
/////////////////////////////////////////////////////////////////////////
object IofModule {
  type Iof[H, A <: H] = IofModule[Any with H]#Type[A]
  @inline final def instOf[H] = new IosHelper[H]; class IosHelper[H](val d: Boolean = true) extends AnyVal {
    def apply[A <: H](a: A) = companion[H].leibniz(a)
  }
  def companion[H]: IofCompanion[Any with H] = IofCompanion[Any with H](IofImpl[Any with H]())
  def leibniz[H, A <: Any with H]: Leibniz[⊥, Any with H, A, Iof[Any with H, A]] = companion[H].leibniz[A]
  def is[H, A <: Any with H]: A === Iof[H, A] = companion[H].leibniz[A].toIs

  def functorEq [->[_,_], H, A <: H, B <: H]:         (A -> B) === (Iof[H, A] -> Iof[H, B]) = Is.lift2[->](is[H, A], is[H, B])
  def functorEq1[->[_,_], H, A <: H, S >: H, B <: S]: (A -> B) === (Iof[H, A] -> Iof[S, B]) = Is.lift2[->](is[H, A], is[S, B])

  def map[H] = new MapHelper[H]; final class MapHelper[H](val d: Boolean = true) extends AnyVal {
    def apply[->[_,_], A <: H, B <: H](ab: A -> B): Iof[H, A] -> Iof[H, B] = functorEq[->, H, A, B](ab)
  }
  def map[H, S >: H] = new Map1Helper[H, S]; final class Map1Helper[H, S >: H](val i: Int = 0) extends AnyVal {
    def apply[->[_,_], A <: H, B <: S](ab: A -> B): Iof[H, A] -> Iof[S, B] = functorEq1[->, H, A, S, B](ab)
  }

  def covary[HL, A <: HL : * <~< B, HH >: HL, B <: HH]: Iof[HL, A] <~< Iof[HH, B] = map[HL, HH](<~<[A, B])

  implicit def isCovariant: IsCovariant[Iof[Any, *]] = IsCovariant.witness[Iof[Any, *]](functorEq[<~<, Any, Void, Any](<~<[Void, Any]))
  implicit def isInjective: IsInjective[Iof[Any, *]] = IsInjective.witness[Iof[Any, *]](functorEq[=!=, Any, Void, Any](=!=[Void, Any]))
}
sealed abstract class IofModule[H] {
  type Type[A <: H] <: A
  def leibniz[A <: H]: Leibniz[⊥, H, A, Type[A]]
}
private[exo] case class IofImpl[H]() extends IofModule[Any with H] {
  type Type[A <: Any with H] = A
  def leibniz[A <: Any with H] = Leibniz[⊥, Any with H, A, A]
}
private[exo] case class IofCompanion[H](base: IofModule[H]) {
  import IofModule.Iof
  def leibniz[A <: H]: Leibniz[⊥, H, A, Iof[H, A]] = {
    val l: A <~< Iof[H, A] = base.leibniz[A].toAs.andThen(<~<[base.Type[A], Iof[H, A]])
    Leibniz.fromIs[⊥, H, A, Iof[H, A]](As.bracket(l, <~<[Iof[H, A], A]))
  }
}
