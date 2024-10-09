package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.functors.*
import io.cosmo.exo.internal.*

trait Semicategory[->[_,_]]:
  final def compose[A, B, C](f: B -> C, g: A -> B): A -> C = andThen(g, f)
  def andThen[A, B, C](ab: A -> B, bc: B -> C): A -> C

object Semicategory
  extends Function1SemicategoryInstances
  with DualSemicategoryInstances
  with EvidenceCatSubcatInstances
  with ProdcatSemicategoryInstances:
  
  def apply[->[_,_]](using ev: Semicategory[->]): Semicategory[->] = ev

  given arrowFunctor[->[_,_], T[_]]: IsoFunctorK2[[f[_,_]] =>> Subcat.Aux[f, T]] =
    new IsoFunctorK2.Proto[[f[_,_]] =>> Subcat.Aux[f, T]]:
      protected def mapK[F[_, _], G[_, _]](iso: F <~~> G): Subcat.Aux[F, T] => Subcat.Aux[G, T] = sf =>
        new Subcat[G]:
          type TC[a] = T[a]
          def id[A](using A: T[A]): G[A, A] = iso[A, A](sf.id[A])
          def andThen[A, B, C](ab: G[A, B], bc: G[B, C]): G[A, C] =
            iso[A, C].to(sf.andThen(iso[A, B].from(ab), iso[B, C].from(bc)))


end Semicategory
