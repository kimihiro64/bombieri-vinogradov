import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegral
import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegralLFunction
import BombieriVinogradov.Helpers.DirichletCharacter.AbelKernelIntegralNorm
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.ZMod

/-!
# Character L-function bound on the right half-plane

This module owns composition of the Abel-kernel integral norm estimate with
the outer complex parameter.
-/

set_option autoImplicit false

namespace BombieriVinogradov

/-- A nonprincipal character satisfies `norm(L(s,chi)) <= 2*N*norm(s)` on `re(s)>=1/2`. -/
theorem norm_LFunction_le_two_mul_modulus_mul_norm {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : chi ≠ 1)
    {s : Complex} (hs : (1 : Real) / 2 ≤ s.re) :
    ‖ZMod.LFunction chi s‖ ≤ 2 * (N : Real) * ‖s‖ := by
  have hsPos : 0 < s.re := by linarith
  have hTwoRe : 1 ≤ 2 * s.re := by linarith
  have hRatio : (N : Real) / s.re ≤ 2 * (N : Real) := by
    apply (div_le_iff₀ hsPos).2
    calc
      (N : Real) = (N : Real) * 1 := by ring
      _ ≤ (N : Real) * (2 * s.re) :=
        mul_le_mul_of_nonneg_left hTwoRe (Nat.cast_nonneg N)
      _ = (2 * (N : Real)) * s.re := by ring
  rw [← characterAbelIntegral_eq_LFunction chi hchi hsPos, characterAbelIntegral, norm_mul]
  calc
    ‖s‖ * ‖∫ t in Set.Ioi (1 : Real),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1))‖ ≤
        ‖s‖ * ((N : Real) / s.re) :=
      mul_le_mul_of_nonneg_left (norm_characterAbelKernelIntegral_le chi hchi hsPos)
        (norm_nonneg s)
    _ ≤ ‖s‖ * (2 * (N : Real)) := mul_le_mul_of_nonneg_left hRatio (norm_nonneg s)
    _ = 2 * (N : Real) * ‖s‖ := by ring

end BombieriVinogradov
