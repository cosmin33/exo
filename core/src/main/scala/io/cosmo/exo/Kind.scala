package io.cosmo.exo

/*

 Numeric notation for kinds:

 K                          -> 0 (or no char)
 F[_]                       -> 1
 F[_,_]                     -> 2
 F[_,_,_]                   -> 3 ... 9

 A[_[_]]                    -> 10
 A[_[_],_]                  -> 11
 A[_[_],_,_]                -> 12
 A[_[_],_,_,_]              -> 13 ... 19
 B[_[_],_[_]]               -> 20
 B[_[_],_[_],_]             -> 21
 B[_[_],_[_],_,_]           -> 22 ... 29

 H[_[_[_]]]                 -> 50
 H[_[_[_]],_]               -> 51
 H[_[_[_]],_,_]             -> 52 ... 59
 H[_[_[_]],_[_]]            -> 62
 H[_[_[_]],_[_],_]          -> 63 ... 69
 H[_[_[_]],_[_],_[_]]       -> 70 ... ...

 B[_[_[_]],_[_[_]]]         -> 100
 B[_[_[_]],_[_[_]],_]       -> 101 ... 109
 B[_[_[_]],_[_[_]],_[_]]    -> 110 ... ...
 C[_[_[_]],_[_[_]],_[_[_]]] -> 150 ... ... ...

 U[_[_[_[_]]]]              -> 500 ... ... ... ...

 */

sealed trait Kind

object Kind {
  object Kind0 extends Kind
  type Kind0 = Kind0.type
  class Kind1 [A]                                  extends Kind
  class Kind2 [A, B]                                extends Kind
  class Kind3 [A, B, C]                            extends Kind
  class Kind10[F[_]]                               extends Kind
  class Kind11[F[_], A]                             extends Kind
  class Kind12[F[_], A, B]                           extends Kind
  class Kind13[F[_], A, B, C]                      extends Kind
  class Kind20[F[_], G[_]]                         extends Kind
  class Kind21[F[_], G[_], A]                      extends Kind
  class Kind22[F[_], G[_], A, B]                   extends Kind
  class Kind23[F[_], G[_], A, B, C]                extends Kind
  class Kind30[F[_], G[_], H[_]]                   extends Kind
  class Kind31[F[_], G[_], H[_], A]                extends Kind
  class Kind32[F[_], G[_], H[_], A, B]             extends Kind
  class Kind33[F[_], G[_], H[_], A, B, C]          extends Kind
  class Kind50[M[_[_]]]                            extends Kind
  class Kind51[M[_[_]], A]                          extends Kind
  class Kind52[M[_[_]], A, B]                        extends Kind
  class Kind53[M[_[_]], A, B, C]                      extends Kind
  class Kind60[M[_[_]], F[_]]                      extends Kind
  class Kind61[M[_[_]], F[_], A]                   extends Kind
  class Kind62[M[_[_]], F[_], A, B]                extends Kind
  class Kind63[M[_[_]], F[_], A, B, C]             extends Kind
  class Kind70[M[_[_]], F[_], G[_]]                extends Kind
  class Kind71[M[_[_]], F[_], G[_], A]             extends Kind
  class Kind72[M[_[_]], F[_], G[_], A, B]          extends Kind
  class Kind73[M[_[_]], F[_], G[_], A, B, C]       extends Kind
  class Kind80[M[_[_]], F[_], G[_], H[_]]          extends Kind
  class Kind81[M[_[_]], F[_], G[_], H[_], A]       extends Kind
  class Kind82[M[_[_]], F[_], G[_], H[_], A, B]    extends Kind
  class Kind83[M[_[_]], F[_], G[_], H[_], A, B, C] extends Kind
  class Kind100[M[_[_]], N[_[_]]]                  extends Kind
  class Kind101[M[_[_]], A]                          extends Kind
  class Kind102[M[_[_]], A, B]                        extends Kind
  class Kind103[M[_[_]], A, B, C]                      extends Kind
  class Kind110[M[_[_]], N[_[_]], F[_]]                 extends Kind
  class Kind111[M[_[_]], N[_[_]], F[_], A]               extends Kind
  class Kind112[M[_[_]], N[_[_]], F[_], A, B]             extends Kind
  class Kind113[M[_[_]], N[_[_]], F[_], A, B, C]           extends Kind
  class Kind120[M[_[_]], N[_[_]], F[_], G[_]]               extends Kind
  class Kind121[M[_[_]], N[_[_]], F[_], G[_], A]             extends Kind
  class Kind122[M[_[_]], N[_[_]], F[_], G[_], A, B]          extends Kind
  class Kind123[M[_[_]], N[_[_]], F[_], G[_], A, B, C]       extends Kind
  class Kind130[M[_[_]], N[_[_]], F[_], G[_], H[_]]          extends Kind
  class Kind131[M[_[_]], N[_[_]], F[_], G[_], H[_], A]       extends Kind
  class Kind132[M[_[_]], N[_[_]], F[_], G[_], H[_], A, B]    extends Kind
  class Kind133[M[_[_]], N[_[_]], F[_], G[_], H[_], A, B, C] extends Kind
  class Kind150[M[_[_]], N[_[_]], O[_[_]]]                   extends Kind
  class Kind500[U[_[_[_]]]]                                  extends Kind
  // ...
}

