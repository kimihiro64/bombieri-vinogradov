import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeNormBound
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.Linarith
import PrimeNumberTheoremAnd.ZetaBounds

/-!
# A lower bound for a real Dirichlet logarithmic derivative

This module formalizes the crude lower estimate used on page 175 of
Strombergsson's proof of Theorem 11.5.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_neg_inv_sub_le_neg_re_logDeriv_LFunction :
    exists C : Real, 0 ≤ C ∧
      forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
        {sigma : Real}, 1 < sigma -> sigma ≤ 2 ->
          -(sigma - 1)⁻¹ - C ≤ -(logDeriv chi.LFunction sigma).re := by
  obtain ⟨C, hCNonneg, hZeta⟩ := triv_bound_zeta
  refine Exists.intro C (And.intro hCNonneg ?_)
  intro N _hN chi sigma hsigma _hsigmaUpper
  let z : Complex := -deriv chi.LFunction sigma / chi.LFunction sigma
  have hNorm := norm_neg_logDeriv_LFunction_le_zeta chi hsigma
  have hZetaAtSigma :
      ‖-deriv riemannZeta sigma / riemannZeta sigma‖ ≤
        (sigma - 1)⁻¹ + C := by
    simpa using hZeta sigma 0 hsigma
  have hRealLower : -‖z‖ ≤ z.re := by
    exact (neg_le_neg (Complex.abs_re_le_norm z)).trans (neg_abs_le z.re)
  have hCombined : -((sigma - 1)⁻¹ + C) ≤ z.re := by
    calc
      -((sigma - 1)⁻¹ + C) ≤
          -‖-deriv riemannZeta sigma / riemannZeta sigma‖ :=
        neg_le_neg hZetaAtSigma
      _ ≤ -‖z‖ := neg_le_neg hNorm
      _ ≤ z.re := hRealLower
  have hzReal : z.re =
      -(deriv chi.LFunction sigma / chi.LFunction sigma).re := by
    dsimp [z]
    rw [neg_div, Complex.neg_re]
  rw [hzReal] at hCombined
  rw [logDeriv_apply]
  linarith

end BombieriVinogradov.SiegelWalfisz
