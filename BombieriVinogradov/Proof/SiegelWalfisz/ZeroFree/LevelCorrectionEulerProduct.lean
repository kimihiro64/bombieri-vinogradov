import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionEulerFactor
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The finite Euler product for changing character level

This module identifies the imprimitive L-function with its primitive L-function
times the finite correction product, then differentiates that product.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_eq_primitive_mul_levelCorrection {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : chi ≠ 1)
    (s : Complex) :
    chi.LFunction s = chi.primitiveCharacter.LFunction s * levelCorrection chi s := by
  have hprimitive :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hchange := _root_.DirichletCharacter.LFunction_changeLevel
    chi.conductor_dvd_level chi.primitiveCharacter (s := s) (.inl hprimitive)
  rw [chi.changeLevel_primitiveCharacter] at hchange
  simpa [levelCorrection, levelCorrectionFactor] using hchange

theorem levelCorrection_ne_zero {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : Complex} (hs : 1 ≤ s.re) :
    levelCorrection chi s ≠ 0 := by
  have hChiNe := _root_.DirichletCharacter.LFunction_ne_zero_of_one_le_re
    chi (.inl hchi) hs
  intro hzero
  have hproduct := LFunction_eq_primitive_mul_levelCorrection chi hchi s
  rw [hzero, mul_zero] at hproduct
  exact hChiNe hproduct

theorem logDeriv_LFunction_eq_primitive_add_levelCorrection
    {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : Complex} (hs : 1 ≤ s.re) :
    logDeriv chi.LFunction s =
      logDeriv chi.primitiveCharacter.LFunction s + logDeriv (levelCorrection chi) s := by
  have hprimitive :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hChiNe := _root_.DirichletCharacter.LFunction_ne_zero_of_one_le_re
    chi (.inl hchi) hs
  have hPrimitiveNe := _root_.DirichletCharacter.LFunction_ne_zero_of_one_le_re
    chi.primitiveCharacter (.inl hprimitive) hs
  have hCorrectionNe : levelCorrection chi s ≠ 0 := by
    intro hzero
    have hproduct := LFunction_eq_primitive_mul_levelCorrection chi hchi s
    rw [hzero, mul_zero] at hproduct
    exact hChiNe hproduct
  have hFunctions : chi.LFunction =
      fun z => chi.primitiveCharacter.LFunction z * levelCorrection chi z := by
    funext z
    exact LFunction_eq_primitive_mul_levelCorrection chi hchi z
  calc
    logDeriv chi.LFunction s =
        logDeriv (fun z =>
          chi.primitiveCharacter.LFunction z * levelCorrection chi z) s := by
      rw [hFunctions]
    _ = logDeriv chi.primitiveCharacter.LFunction s +
        logDeriv (levelCorrection chi) s :=
      logDeriv_mul s hPrimitiveNe hCorrectionNe
        (_root_.DirichletCharacter.differentiable_LFunction hprimitive).differentiableAt
        (by
          change DifferentiableAt Complex
            (fun z : Complex =>
              ∏ p ∈ N.primeFactors, levelCorrectionFactor chi p z) s
          exact DifferentiableAt.fun_finsetProd (fun p hp =>
            differentiableAt_levelCorrectionFactor chi
              (Nat.prime_of_mem_primeFactors hp) s))

theorem logDeriv_levelCorrection_eq_sum {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : Complex} (hs : 1 ≤ s.re) :
    logDeriv (levelCorrection chi) s =
      ∑ p ∈ N.primeFactors, logDeriv (levelCorrectionFactor chi p) s := by
  have hCorrection := levelCorrection_ne_zero chi hchi hs
  have hProduct :
      (∏ p ∈ N.primeFactors, levelCorrectionFactor chi p s) ≠ 0 := by
    simpa only [levelCorrection] using hCorrection
  have hFactor : ∀ p ∈ N.primeFactors, levelCorrectionFactor chi p s ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hProduct
  change logDeriv
      (fun z : Complex =>
        ∏ p ∈ N.primeFactors, levelCorrectionFactor chi p z) s = _
  exact logDeriv_prod hFactor (fun p hp =>
    differentiableAt_levelCorrectionFactor chi
      (Nat.prime_of_mem_primeFactors hp) s)

end BombieriVinogradov.SiegelWalfisz
