package io.cosmo.exo.categories

import io.cosmo.exo./\

package object data {

  type EvidenceStart[T[_], A, B] = T[A]
  type EvidenceEnd  [T[_], A, B] = T[B]
  type EvidenceSame [T[_], A, B] = (T[A], T[B])          // ProdCat[EvidenceStart[T,*,*], EvidenceEnd[T,*,*], A, B]
  type EvidenceBoth[T1[_], T2[_], A, B] = (T1[A], T2[B]) // ProdCat[EvidenceStart[T1,*,*], EvidenceEnd[T2,*,*], A, B]


}
