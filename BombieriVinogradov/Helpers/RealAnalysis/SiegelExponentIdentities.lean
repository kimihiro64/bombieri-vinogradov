import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Exact exponents in the Siegel modulus substitution

The choice one over three times the modulus exponent cancels to
negative one-third, and multiplication by the base gives two-thirds.
-/
set_option autoImplicit false

namespace BombieriVinogradov.RealAnalysis

theorem rpow_neg_siegelExponent_of_rpow
    {L A : Real} (hL : 0 < L) (hA : 0 < A) :
    (L ^ A) ^ (-(1 / (3 * A))) = L ^ (-(1 / 3 : Real)) := by
  have hExponent : A * (-(1 / (3 * A))) = -(1 / 3 : Real) := by field_simp
  calc
    (L ^ A) ^ (-(1 / (3 * A))) = L ^ (A * (-(1 / (3 * A)))) :=
      (Real.rpow_mul hL.le A (-(1 / (3 * A)))).symm
    _ = L ^ (-(1 / 3 : Real)) := congrArg (fun r : Real => L ^ r) hExponent

theorem rpow_neg_third_mul_self {L : Real} (hL : 0 < L) :
    L ^ (-(1 / 3 : Real)) * L = L ^ (2 / 3 : Real) := by
  calc
    L ^ (-(1 / 3 : Real)) * L = L ^ (-(1 / 3 : Real)) * L ^ (1 : Real) :=
      congrArg (fun r : Real => L ^ (-(1 / 3 : Real)) * r) (Real.rpow_one L).symm
    _ = L ^ (-(1 / 3 : Real) + 1) := (Real.rpow_add hL (-(1 / 3)) 1).symm
    _ = L ^ (2 / 3 : Real) := by norm_num

end BombieriVinogradov.RealAnalysis
