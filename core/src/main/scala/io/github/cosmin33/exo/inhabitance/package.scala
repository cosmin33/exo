package io.github.cosmin33.exo.inhabitance

type ¬[A] = Uninhabited[A]
val ¬ = Uninhabited

type ¬¬[A] = Inhabited[A]
val ¬¬ = Inhabited
