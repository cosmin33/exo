package io.cosmo.exo.evidence

type ===[A, B] = Is[A, B]
val === = Is

type =~=[A[_], B[_]] = IsK[A, B]
val =~= = IsK

type =~~=[A[_,_], B[_,_]] = IsK2[A, B]
val =~~= = IsK2

type <~<[-A, +B] = As[A, B]
val <~< = As

type >~<[A, B] = Incomparable[A, B]

type =!=[A, B] = WeakApart[A, B]
val =!= = WeakApart

type </<[-A, +B] = StrictAs[A, B]
