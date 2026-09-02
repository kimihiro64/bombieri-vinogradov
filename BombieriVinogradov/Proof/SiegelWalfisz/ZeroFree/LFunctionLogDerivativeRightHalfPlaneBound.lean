import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeNormBound
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order

/-!
# Complex-height right-half-plane L-function logarithmic derivative bound

This module extends the real-axis zeta majorant to every complex point with
real part greater than one. The L-series term norm depends only on real part.
-/

set_option autoImplicit false

open ArithmeticFunction hiding log
open Complex
open scoped ComplexOrder LSeries.notation

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_neg_logDeriv_LFunction_le_zeta_re
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {s : Complex} (hs : 1 < s.re) :
    norm (-deriv chi.LFunction s / chi.LFunction s) <=
      norm (-deriv riemannZeta (s.re : Complex) /
        riemannZeta (s.re : Complex)) := by
  let twisted : Nat -> Complex :=
    fun n => chi n * (vonMangoldt n : Complex)
  let untwisted : Nat -> Complex :=
    fun n => (vonMangoldt n : Complex)
  have hsReal : 1 < ((s.re : Real) : Complex).re := by simpa
  have hZetaIdentity :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsReal
  rw [neg_logDeriv_LFunction_eq_twist_vonMangoldt chi hs,
    hZetaIdentity.symm]
  change norm (LSeries twisted s) <=
    norm (LSeries untwisted (s.re : Complex))
  have hCharacterSeries :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hs
  change LSeriesSummable twisted s at hCharacterSeries
  have hZeta := ArithmeticFunction.LSeriesSummable_vonMangoldt hsReal
  change LSeriesSummable untwisted (s.re : Complex) at hZeta
  have hZetaNonneg : forall n : Nat,
      0 <= LSeries.term untwisted (s.re : Complex) n := by
    intro n
    apply LSeries.term_nonneg
    simp only [untwisted]
    norm_cast
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hCoefficient : forall n : Nat,
      norm (twisted n) <= norm (untwisted n) := by
    intro n
    simp only [twisted, untwisted, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (chi.norm_le_one (n : ZMod N))
  have hTerm : forall n : Nat,
      norm (LSeries.term twisted s n) <=
        norm (LSeries.term untwisted (s.re : Complex) n) := by
    intro n
    calc
      norm (LSeries.term twisted s n) <=
          norm (LSeries.term untwisted s n) :=
        LSeries.norm_term_le s (hCoefficient n)
      _ = norm (LSeries.term untwisted (s.re : Complex) n) := by
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
        simp
  have hZetaNorm :
      tsum (fun n : Nat =>
        norm (LSeries.term untwisted (s.re : Complex) n)) =
        norm (tsum (fun n : Nat =>
          LSeries.term untwisted (s.re : Complex) n)) := by
    have hPointwise : forall n : Nat,
        norm (LSeries.term untwisted (s.re : Complex) n) =
          (LSeries.term untwisted (s.re : Complex) n).re := by
      intro n
      exact (Complex.re_eq_norm.mpr (hZetaNonneg n)).symm
    calc
      tsum (fun n : Nat =>
          norm (LSeries.term untwisted (s.re : Complex) n)) =
          tsum (fun n : Nat =>
            (LSeries.term untwisted (s.re : Complex) n).re) :=
        tsum_congr hPointwise
      _ = (tsum (fun n : Nat =>
          LSeries.term untwisted (s.re : Complex) n)).re :=
        (Complex.re_tsum hZeta).symm
      _ = norm (tsum (fun n : Nat =>
          LSeries.term untwisted (s.re : Complex) n)) := by
        apply Complex.re_eq_norm.mpr
        apply tsum_nonneg
        exact hZetaNonneg
  unfold LSeries
  calc
    norm (tsum (fun n : Nat => LSeries.term twisted s n)) <=
        tsum (fun n : Nat => norm (LSeries.term twisted s n)) :=
      norm_tsum_le_tsum_norm hCharacterSeries.norm
    _ <= tsum (fun n : Nat =>
        norm (LSeries.term untwisted (s.re : Complex) n)) :=
      hCharacterSeries.norm.tsum_le_tsum hTerm hZeta.norm
    _ = norm (tsum (fun n : Nat =>
        LSeries.term untwisted (s.re : Complex) n)) := hZetaNorm

end BombieriVinogradov.SiegelWalfisz
