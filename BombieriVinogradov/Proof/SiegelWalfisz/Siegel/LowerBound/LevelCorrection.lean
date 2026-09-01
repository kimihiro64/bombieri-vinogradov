import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.LowerBound.CharacterFacts
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Values
import Mathlib.Analysis.Complex.Order
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Positive correction from a primitive character to a higher level

This module proves that the finite Euler-factor correction introduced by
changing the level of a quadratic character is positive on the positive real
axis.
-/

set_option autoImplicit false

open scoped ComplexOrder

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def characterLevelCorrection {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (s : ℝ) : ℂ :=
  ∏ p ∈ N.primeFactors,
    (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-(s : ℂ)))

theorem characterLevelCorrection_pos {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchiSquare : chi ^ 2 = 1)
    {s : ℝ} (hs : 0 < s) : 0 < characterLevelCorrection chi s := by
  rw [characterLevelCorrection]
  apply Finset.prod_pos
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpgt : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  have hpnonneg : (0 : ℝ) ≤ p := by positivity
  have hrpowPos : 0 < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by positivity) _
  have hrpowLt : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpgt (neg_neg_of_pos hs)
  rcases quadraticValue_cases chi.primitiveCharacter
      (primitiveCharacter_sq_eq_one chi hchiSquare) p with hzero | hone | hneg
  · simp [hzero]
  · rw [hone, one_mul, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s),
      ← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.zero_lt_real.mpr (sub_pos.mpr hrpowLt)
  · rw [hneg, show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hpnonneg (-s)]
    convert Complex.zero_lt_real.mpr (show 0 < 1 + (p : ℝ) ^ (-s) by positivity) using 1
    norm_num [Complex.ofReal_add]

theorem LFunction_eq_primitive_mul_correction {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : ℝ} :
    chi.LFunction s =
      chi.primitiveCharacter.LFunction s * characterLevelCorrection chi s := by
  have hprimitive := primitiveCharacter_ne_one chi hchi
  have hchange := DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
    chi.primitiveCharacter (s := (s : ℂ)) (.inl hprimitive)
  rw [chi.changeLevel_primitiveCharacter] at hchange
  exact hchange

end BombieriVinogradov.SiegelWalfisz
