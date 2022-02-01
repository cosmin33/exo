package io.cosmo.exo.categories

import io.cosmo.exo./\
import io.cosmo.exo.evidence.{<~<, ===}

package object data {

  type EvidenceStart[F[_], A, B] = F[A]
  type EvidenceEnd  [F[_], A, B] = F[B]
  type EvidenceSame [F[_], A, B] = (F[A], F[B])      // ProdCat[EvidenceStart[F,*,*], EvidenceEnd[F,*,*], A, B]
  type EvidenceBoth[F[_], G[_], A, B] = (F[A], G[B]) // ProdCat[EvidenceStart[F,*,*], EvidenceEnd[G,*,*], A, B]

  def xx[F[_], A, B] = implicitly[EvidenceSame[F, A, B] === Prodcat[EvidenceStart[F,*,*], EvidenceEnd[F,*,*], A, B]]

}
