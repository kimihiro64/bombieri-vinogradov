import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductFormula
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorConjugation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionConjugation
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Complex conjugation of symmetric completed Dirichlet L-functions

This module lifts the separate L-function and gamma-factor conjugation identities
through analytic continuation to the symmetric completed L-function, then differentiates
the resulting identity.
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_inv_eq_conj_conj
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (s : Complex) :
    symmetricCompletedLFunction chi⁻¹ s =
      conj (symmetricCompletedLFunction chi (conj s)) := by
  have hInverseNe : chi⁻¹ ≠ 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  let g : Complex -> Complex :=
    conj ∘ symmetricCompletedLFunction chi ∘ conj
  have hDifferentiableG : Differentiable Complex g := by
    intro z
    have hAtConj :
        DifferentiableAt Complex (symmetricCompletedLFunction chi) (conj z) :=
      (differentiable_symmetricCompletedLFunction hchi).differentiableAt
    simpa [g] using hAtConj.conj_conj
  have hAnalyticInv :
      AnalyticOnNhd Complex (symmetricCompletedLFunction chi⁻¹)
        (Set.univ : Set Complex) :=
    (differentiable_symmetricCompletedLFunction hInverseNe).differentiableOn.analyticOnNhd
      isOpen_univ
  have hAnalyticG : AnalyticOnNhd Complex g (Set.univ : Set Complex) :=
    hDifferentiableG.differentiableOn.analyticOnNhd isOpen_univ
  have hRightHalfPlane : {z : Complex | 1 < z.re} ∈ nhds (2 : Complex) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have hEventually :
      symmetricCompletedLFunction chi⁻¹ =ᶠ[nhds (2 : Complex)] g := by
    filter_upwards [hRightHalfPlane] with z hz
    have hzConj : 1 < (conj z).re := by simpa using hz
    have hPower :
        conj ((N : Complex) ^ (conj z / 2)) = (N : Complex) ^ (z / 2) := by
      simpa only [map_div₀, map_ofNat] using
        (Complex.conj_natCast_cpow_conj N (z / 2))
    have hLFunction :=
      DirichletCharacter.LFunction_inv_eq_conj_conj hchi z
    have hGammaFactor :=
      DirichletCharacter.gammaFactor_inv_eq_conj_conj chi z
    change symmetricCompletedLFunction chi⁻¹ z =
      conj (symmetricCompletedLFunction chi (conj z))
    rw [symmetricCompletedLFunction, symmetricCompletedLFunction,
      DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_one_lt_re
        chi⁻¹ hz,
      DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_one_lt_re
        chi hzConj]
    change (N : Complex) ^ (z / 2) *
        (chi⁻¹.LFunction z * chi⁻¹.gammaFactor z) =
      conj ((N : Complex) ^ (conj z / 2) *
        (chi.LFunction (conj z) * chi.gammaFactor (conj z)))
    rw [map_mul, map_mul, hPower, ← hLFunction, ← hGammaFactor]
  have hFunctions : symmetricCompletedLFunction chi⁻¹ = g :=
    AnalyticOnNhd.eq_of_eventuallyEq hAnalyticInv hAnalyticG hEventually
  simpa [g] using congrFun hFunctions s

theorem logDeriv_symmetricCompletedLFunction_inv_eq_conj_conj
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (s : Complex) :
    logDeriv (symmetricCompletedLFunction chi⁻¹) s =
      conj (logDeriv (symmetricCompletedLFunction chi) (conj s)) := by
  have hFunctions : symmetricCompletedLFunction chi⁻¹ =
      conj ∘ symmetricCompletedLFunction chi ∘ conj := by
    funext z
    exact symmetricCompletedLFunction_inv_eq_conj_conj hchi z
  rw [hFunctions, logDeriv_apply, logDeriv_apply, deriv_conj_conj,
    map_div₀ (starRingEnd Complex)]
  rfl

end BombieriVinogradov.SiegelWalfisz
