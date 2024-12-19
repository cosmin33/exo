package io.cosmo.exo.categories

import io.cosmo.exo.*
import io.cosmo.exo.categories.Distributive.Aux
import io.cosmo.exo.functors.*

class CategoriesTest {
  // functorization for arrow
  summon[IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Distributive.Aux[f, Trivial, Tuple2, Unit, Either, Void]]]
  summon[IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Concrete.Aux[f, Trivial]]]
  summon[IsoFunctorK2[* => *, * => *, [f[_,_]] =>> Subcat.Aux[f, Trivial]]]
  summon[IsoFunctorK2[* => *, * => *, Semicategory]]
  // functorization for typeclass
  summon[CofunctorK[* => *, * => *, [f[_]] =>> Distributive.Aux[* => *, f, Tuple2, Unit, Either, Void]]]
  summon[IsoFunctorK[* => *, * => *, [f[_]] =>> Concrete.Aux[* => *, f]]]
  summon[CofunctorK[* => *, * => *, [f[_]] =>> Subcat.Aux[* => *, f]]]
}
