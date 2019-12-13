package io.cosmo.exo.evidence

trait TypeHolderModule {
  type Type
}

object TypeHolderModule {
  trait Tag extends Any
  type Aux[T] = TypeHolderModule with Tag { type Type = T }

  def apply[T]: Aux[T] = new TypeHolderModule with Tag { type Type = T }
}

trait TypeHolder2Module {
  type TypeA
  type TypeB
}

object TypeHolder2Module {
  trait Tag extends Any
  type Aux[A, B] = TypeHolder2Module with Tag { type TypeA = A; type TypeB = B }

  def apply[A, B]: Aux[A, B] = new TypeHolder2Module with Tag { type TypeA = A; type TypeB = B }
}

trait TypeHolder3Module {
  type TypeA
  type TypeB
  type TypeC
}

object TypeHolder3Module {
  trait Tag extends Any
  type Aux[A, B, C] = TypeHolder3Module with Tag { type TypeA = A; type TypeB = B; type TypeC = C }

  def apply[A, B, C]: Aux[A, B, C] = new TypeHolder3Module with Tag { type TypeA = A; type TypeB = B; type TypeC = C }
}

trait TypeHolderKModule {
  type TypeF[_]
}

object TypeHolderKModule {
  trait Tag extends Any
  type Aux[F[_]] = TypeHolderKModule with Tag {type TypeF[x] = F[x]}

  def apply[F[_]]: Aux[F] = new TypeHolderKModule with Tag {type TypeF[x] = F[x]}
}

trait TypeholderHKModule {
  type TypeH[_[_]]
}

object TypeholderHKModule {
  trait Tag extends Any
  type Aux[H[_[_]]] = TypeholderHKModule with Tag {type TypeH[x[_]] = H[x]}

  def apply[H[_[_]]]: Aux[H] = new TypeholderHKModule with Tag {type TypeH[x[_]] = H[x]}
}

