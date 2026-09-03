import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.EvenGammaResidue
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedOriginNonvanishing
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Nonvanishing of the even L-function derivative at the origin
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

open Filter

theorem deriv_LFunction_zero_ne_zero_of_even
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hEven : DirichletCharacter.Even chi) :
    Ne (deriv chi.LFunction 0) 0 := by
  have hNNeOne : Ne N 1 := by
    intro hN
    exact hchi (chi.level_one' hN)
  have hLZero : chi.LFunction 0 = 0 := by
    rw [DirichletCharacter.LFunction]
    rw [ZMod.LFunction_apply_zero_of_even hEven.to_fun]
    rw [chi.map_zero' hNNeOne]
    simp
  have hCompletedNe : Ne (chi.completedLFunction 0) 0 := by
    have hSymmetric :=
      symmetricCompletedLFunction_zero_ne_zero hchi hPrimitive
    simpa [symmetricCompletedLFunction] using hSymmetric
  have hCompletedTendsto :
      Filter.Tendsto chi.completedLFunction
        (nhdsWithin 0 (Compl.compl ({0} : Set Complex)))
        (nhds (chi.completedLFunction 0)) := by
    exact
      (DirichletCharacter.differentiableAt_completedLFunction chi 0
        (Or.inr hNNeOne) (Or.inr hchi)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
  have hGammaTendsto :=
    tendsto_self_mul_gammaFactor_zero_of_even hEven
  have hQuotientTendsto :
      Filter.Tendsto
        (fun s : Complex =>
          chi.completedLFunction s / (s * chi.gammaFactor s))
        (nhdsWithin 0 (Compl.compl ({0} : Set Complex)))
        (nhds (chi.completedLFunction 0 / 2)) :=
    hCompletedTendsto.div hGammaTendsto (by norm_num)
  have hDifferentiable :=
    DirichletCharacter.differentiable_LFunction hchi
  have hDerivativeTendsto :
      Filter.Tendsto (fun s : Complex => chi.LFunction s / s)
        (nhdsWithin 0 (Compl.compl ({0} : Set Complex)))
        (nhds (deriv chi.LFunction 0)) := by
    simpa only [zero_add, hLZero, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using
        (hDifferentiable.differentiableAt
          (x := (0 : Complex))).hasDerivAt.tendsto_slope_zero
  have hSlopeEq :
      Filter.EventuallyEq
        (nhdsWithin 0 (Compl.compl ({0} : Set Complex)))
        (fun s : Complex => chi.LFunction s / s)
        (fun s : Complex =>
          chi.completedLFunction s / (s * chi.gammaFactor s)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor
      chi s (Or.inl hs)]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hDerivativeAsQuotient :
      Filter.Tendsto
        (fun s : Complex =>
          chi.completedLFunction s / (s * chi.gammaFactor s))
        (nhdsWithin 0 (Compl.compl ({0} : Set Complex)))
        (nhds (deriv chi.LFunction 0)) :=
    hDerivativeTendsto.congr' hSlopeEq
  have hDerivativeEq :
      deriv chi.LFunction 0 = chi.completedLFunction 0 / 2 :=
    tendsto_nhds_unique hDerivativeAsQuotient hQuotientTendsto
  rw [hDerivativeEq]
  exact div_ne_zero hCompletedNe (by norm_num)

end BombieriVinogradov.SiegelWalfisz
