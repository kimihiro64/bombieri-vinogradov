import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Coefficient
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Pole coefficients in the source expansion

This module computes the coefficient of `(2 - s)^m` in `residue / (s - 1)`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/-- Every source-oriented coefficient of `residue / (s - 1)` at two equals `residue`. -/
theorem pole_source_coefficient (residue : ℂ) (m : ℕ) :
    (-1 : ℂ) ^ m * BombieriVinogradov.ComplexAnalysis.taylorCoefficient
      (fun s : ℂ => residue / (s - 1)) 2 m = residue := by
  rw [BombieriVinogradov.ComplexAnalysis.taylorCoefficient,
    show (fun s : ℂ => residue / (s - 1)) = fun s : ℂ => residue * (s - 1)⁻¹ by
      funext s
      rw [div_eq_mul_inv],
    iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate]
  have hinv : deriv^[m] (fun s : ℂ => (s - 1)⁻¹) 2 =
      (-1 : ℂ) ^ m * m.factorial := by
    have h := congrFun (iter_deriv_inv_linear_sub m (1 : ℂ) 1) 2
    norm_num at h
    simpa using h
  rw [hinv]
  field_simp [Nat.factorial_ne_zero]
  have hsign : (((-1 : ℂ) ^ m) ^ 2) = 1 := by
    rw [← pow_mul]
    simp
  rw [hsign, one_mul]

end BombieriVinogradov.SiegelWalfisz
