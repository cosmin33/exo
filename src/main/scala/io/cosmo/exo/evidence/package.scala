package io.cosmo.exo.evidence

infix type ===[A, B] = Is[A, B]
val === = Is

infix type =~=[A[_], B[_]] = IsK[A, B]
val =~= = IsK

infix type =~~=[A[_,_], B[_,_]] = IsK2[A, B]
val =~~= = IsK2

infix type =≈=[A[_[_]], B[_[_]]] = IsHK[A, B]
val =≈= = IsHK

infix type <~<[-A, +B] = As[A, B]
val <~< = As
infix type >~>[+B, -A] = As[A, B]

infix type >~<[A, B] = Incomparable[A, B]

infix type =!=[A, B] = WeakApart[A, B]
val =!= = WeakApart

infix type </<[-A, +B] = StrictAs[A, B]
