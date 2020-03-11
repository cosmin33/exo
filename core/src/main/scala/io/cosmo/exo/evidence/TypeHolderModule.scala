package io.cosmo.exo.evidence

trait TypeHolderModule {
  type T
}

object TypeHolderModule {
  trait Tag extends Any
  type Aux[X] = TypeHolderModule with Tag { type T = X }

  def apply[X]: Aux[X] = new TypeHolderModule with Tag { type T = X }
}

trait TypeHolder2Module {
  type A
  type B
}

object TypeHolder2Module {
  trait Tag extends Any
  type Aux[X, Y] = TypeHolder2Module with Tag { type A = X; type B = Y }

  def apply[X, Y]: Aux[X, Y] = new TypeHolder2Module with Tag { type A = X; type B = Y }
}

trait TypeHolder3Module {
  type T1
  type T2
  type T3
}

object TypeHolder3Module {
  trait Tag extends Any
  type Aux[X, Y, Z] = TypeHolder3Module with Tag { type T1 = X; type T2 = Y; type T3 = Z }

  def apply[X, Y, Z]: Aux[X, Y, Z] = new TypeHolder3Module with Tag { type T1 = X; type T2 = Y; type T3 = Z }
}

trait TypeHolderKModule {
  type T[_]
}

object TypeHolderKModule {
  trait Tag extends Any
  type Aux[F[_]] = TypeHolderKModule with Tag {type T[x] = F[x]}

  def apply[F[_]]: Aux[F] = new TypeHolderKModule with Tag {type T[x] = F[x]}
}

trait TypeholderHKModule {
  type T[_[_]]
}

object TypeholderHKModule {
  trait Tag extends Any
  type Aux[H[_[_]]] = TypeholderHKModule with Tag {type T[x[_]] = H[x]}

  def apply[H[_[_]]]: Aux[H] = new TypeholderHKModule with Tag {type T[x[_]] = H[x]}
}

