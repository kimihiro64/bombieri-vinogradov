import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LogDerivativeSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Principal-character logarithmic-derivative comparison

This module dominates the principal-character von Mangoldt series by the full zeta
von Mangoldt series on the real half-line to the right of one.
-/

set_option autoImplicit false

open ArithmeticFunction hiding log
open Complex
open scoped ComplexOrder LSeries.notation

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_neg_logDeriv_principal_le_zeta
    {N : Nat} [NeZero N] {sigma : Real} (hsigma : 1 < sigma) :
    ‖-deriv (1 : DirichletCharacter Complex N).LFunction sigma /
        (1 : DirichletCharacter Complex N).LFunction sigma‖ ≤
      ‖-deriv riemannZeta sigma / riemannZeta sigma‖ := by
  have hsigmaComplex : 1 < (sigma : Complex).re := by simpa
  rw [neg_logDeriv_LFunction_eq_twist_vonMangoldt
      (1 : DirichletCharacter Complex N) hsigmaComplex,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      hsigmaComplex]
  have hPrincipal :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt
      (1 : DirichletCharacter Complex N) hsigmaComplex
  have hZeta := ArithmeticFunction.LSeriesSummable_vonMangoldt hsigmaComplex
  have hZetaNonneg : forall n : Nat,
      0 ≤ LSeries.term (fun m => (vonMangoldt m : Complex)) sigma n := by
    intro n
    apply LSeries.term_nonneg
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
  have hCoefficient : forall n : Nat,
      ‖((↗(1 : DirichletCharacter Complex N) * ↗vonMangoldt) n)‖ ≤
        ‖(vonMangoldt n : Complex)‖ := by
    intro n
    rw [Pi.mul_apply, norm_mul]
    have hCharacter :=
      (1 : DirichletCharacter Complex N).norm_le_one (n : ZMod N)
    exact mul_le_of_le_one_left (norm_nonneg _) hCharacter
  have hTerm : forall n : Nat,
      ‖LSeries.term (↗(1 : DirichletCharacter Complex N) * ↗vonMangoldt)
          sigma n‖ ≤
        ‖LSeries.term (fun m => (vonMangoldt m : Complex)) sigma n‖ := by
    intro n
    exact LSeries.norm_term_le sigma (hCoefficient n)
  have hZetaNorm :
      (∑' n : Nat,
          ‖LSeries.term (fun m => (vonMangoldt m : Complex)) sigma n‖) =
        ‖∑' n : Nat,
          LSeries.term (fun m => (vonMangoldt m : Complex)) sigma n‖ := by
    rw [← re_eq_norm.mpr]
    · rw [re_tsum hZeta]
      apply tsum_congr
      intro n
      exact (re_eq_norm.mpr (hZetaNonneg n)).symm
    · apply tsum_nonneg
      exact hZetaNonneg
  unfold LSeries
  calc
    ‖∑' n : Nat,
        LSeries.term (↗(1 : DirichletCharacter Complex N) * ↗vonMangoldt)
          sigma n‖ ≤
        ∑' n : Nat,
          ‖LSeries.term (↗(1 : DirichletCharacter Complex N) * ↗vonMangoldt)
            sigma n‖ :=
      norm_tsum_le_tsum_norm hPrincipal.norm
    _ ≤ ∑' n : Nat,
        ‖LSeries.term (fun m => (vonMangoldt m : Complex)) sigma n‖ :=
      hPrincipal.norm.tsum_le_tsum hTerm hZeta.norm
    _ = ‖∑' n : Nat,
        LSeries.term (fun m => (vonMangoldt m : Complex)) sigma n‖ :=
      hZetaNorm

end BombieriVinogradov.SiegelWalfisz
