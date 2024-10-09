package io.cosmo.exo

object IsKindTest {
  summon[IsKind.Aux[TypeK[List], List]]
  summon[IsKind.Aux[TypeK[Option], Option]]
  summon[IsKind[(TypeK[Option], TypeK[List])]]
  summon[IsKind[(TypeK[Vector], TypeK[Option] Either TypeK[List])]]
  
  trait IK[A]:
    type Type[_]

  object IK:
    type Aux[A, T[_]] = IK[A] { type Type[a] = T[a] }
    given impl[F[_]]: IK.Aux[TypeK[F], F] = new IK[TypeK[F]] { type Type[a] = F[a] }

    given givenTuple[A, B, F[_], G[_]](using l: IK.Aux[A, F], r: IK.Aux[B, G]): IK.Aux[(A, B), [a] =>> (F[a], G[a])] =
      new IK[(A, B)] { type Type[α] = (F[α], G[α]) }
//    given givenTuple[A, B](using l: IK[A], r: IK[B]): IK.Aux[(A, B), [a] =>> (l.Type[a], r.Type[a])] =
//      new IK[(A, B)] { type Type[α] = (l.Type[α], r.Type[α]) }
  
  summon[IK[(TypeK[Option], TypeK[List])]]
  summon[IK.Aux[(TypeK[Option], TypeK[List]), [α] =>> (Option[α], List[α])]]
  summon[IK[(TypeK[Vector], (TypeK[Option], TypeK[List]))]]
//  summon[IK.Aux[(TypeK[Vector], (TypeK[Option], TypeK[List])), [α] =>> (Vector[α], (Option[α], List[α]))]]

  

}
