package io.cosmo.exo.typeclasses

import io.cosmo.exo._
import io.cosmo.exo.categories.functors.Exofunctor
import io.cosmo.exo.categories.{Subcat, Ccc, Trivial}
import io.cosmo.exo.evidence.{===, Is}
import shapeless.the

trait HasTc[TC[_[_]], TF] {
  type F[_]
  def leibniz: TypeF[F] === TF
  def instance: TC[F]
}
object HasTc {
  type Aux[TC[_[_]], TF, F0[_]] = HasTc[TC, TF] {type F[x] = F0[x]}
  type Aux1[TC[_[_]], F0[_]] = HasTc[TC, _] {type F[x] = F0[x]}

  def apply[TC[_[_]], F[_]](implicit h: HasTc[TC, TypeF[F]]): HasTc.Aux[TC, TypeF[F], h.F] = h
//  def apply[TC[_[_]], TF](implicit h: HasTc[TC, TF]): HasTc.Aux[TC, TF, h.F] = h

  implicit def steal[TC[_[_]], F0[_]](implicit source: TC[F0]): HasTc.Aux[TC, TypeF[F0], F0] =
    new HasTc[TC, TypeF[F0]] {type F[x] = F0[x]; val leibniz = Is.refl; val instance = source}

  def isoCanonic[TC[_[_]], FF[_]]: TC[FF] <=> HasTc[TC, TypeF[FF]] =
    Iso.unsafe(HasTc.steal(_), h => TypeF.injectivity(h.leibniz).subst(h.instance))

  private def exofunc[->[_,_], TC[_[_]]](implicit
    c: Subcat.Aux[->, IsTypeF],
    ccc: Ccc.Aux[->, IsTypeF, (*, *), Unit, ->]
  ): Exofunctor[->, * => *, HasTc[TC, *]] =
    new Exofunctor[->, * => *, HasTc[TC, *]] {
//      type TC1[a] = IsTypeF[a]
//      type TC2[a] = Trivial.T1[a]
//      def C: Subcat.Aux[->, IsTypeF] = c
//      def D = the[Subcat.Aux[* => *, Trivial.T1]]
      def map[A, B](f: A -> B): HasTc[TC, A] => HasTc[TC, B] = ???
    }

}
