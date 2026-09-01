import BombieriVinogradov.Helpers.DirichletCharacter.ComplexConjugation
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedNormalization
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionConjugation
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Complex conjugation of symmetric completed Dirichlet L-functions

This module proves conjugation for the real gamma factor, lifts it through analytic
continuation to the symmetric completed L-function, and differentiates the resulting
identity.
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace BombieriVinogradov.SiegelWalfisz

theorem Complex.Gammaℝ_conj (s : Complex) :
    Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  have hArg : Complex.arg (Real.pi : Complex) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have hPow := Complex.cpow_conj (Real.pi : Complex) (-s / 2) hArg
  have hGamma := Complex.Gamma_conj (s / 2)
  simp only [map_neg, map_div₀, map_ofNat] at hPow hGamma
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, map_mul]
  congr 1
  · simpa using hPow

theorem DirichletCharacter.gammaFactor_inv_eq_conj_conj
    {N : Nat} (chi : DirichletCharacter Complex N) (s : Complex) :
    chi⁻¹.gammaFactor s = conj (chi.gammaFactor (conj s)) := by
  rcases chi.even_or_odd with hEven | hOdd
  · have hEvenInv : DirichletCharacter.Even chi⁻¹ :=
      BombieriVinogradov.DirichletCharacter.Even.inv hEven
    rw [hEvenInv.gammaFactor_def, hEven.gammaFactor_def]
    simpa using Complex.Gammaℝ_conj (conj s)
  · have hOddInv : DirichletCharacter.Odd chi⁻¹ :=
      BombieriVinogradov.DirichletCharacter.Odd.inv hOdd
    rw [hOddInv.gammaFactor_def, hOdd.gammaFactor_def]
    simpa using Complex.Gammaℝ_conj (conj s + 1)

theorem DirichletCharacter.gammaFactor_ne_zero_of_re_pos
    {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : 0 < s.re) : chi.gammaFactor s ≠ 0 := by
  rcases chi.even_or_odd with hEven | hOdd
  · rw [hEven.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hOdd.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp
    linarith

theorem DirichletCharacter.gammaFactor_ne_zero_of_one_lt_re
    {N : Nat} (chi : DirichletCharacter Complex N) {s : Complex}
    (hs : 1 < s.re) : chi.gammaFactor s ≠ 0 :=
  DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi (lt_trans zero_lt_one hs)

theorem DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {s : Complex} (hs : 0 < s.re) :
    chi.completedLFunction s = chi.LFunction s * chi.gammaFactor s := by
  have hsNeZero : s ≠ 0 := by
    intro hsZero
    subst s
    norm_num at hs
  have hGammaNe :=
    DirichletCharacter.gammaFactor_ne_zero_of_re_pos chi hs
  exact ((eq_div_iff hGammaNe).mp
    (chi.LFunction_eq_completed_div_gammaFactor s (.inl hsNeZero))).symm

theorem DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_one_lt_re
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N)
    {s : Complex} (hs : 1 < s.re) :
    chi.completedLFunction s = chi.LFunction s * chi.gammaFactor s :=
  DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos
    chi (lt_trans zero_lt_one hs)

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
