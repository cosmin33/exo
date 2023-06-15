package io.cosmo.exo.inhabitance

type ¬[A] = Uninhabited[A]
val ¬ = Uninhabited

type ¬¬[A] = Inhabited[A]
val ¬¬ = Inhabited
