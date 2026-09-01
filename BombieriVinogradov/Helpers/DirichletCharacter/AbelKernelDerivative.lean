import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Pointwise parameter derivative of the character Abel kernel

This module owns differentiation in the complex parameter while the real
integration variable is fixed above one.
-/

set_option autoImplicit false

open Filter Finset Set

namespace BombieriVinogradov

/-- The Abel kernel has its expected complex derivative in the parameter. -/
theorem characterAbelKernel_hasDerivAt {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) {t : Real} (ht : 1 < t) (s : Complex) :
    HasDerivAt
      (fun z : Complex => (∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(z + 1)))
      (-((Real.log t : Real) : Complex) *
        ((∑ k ∈ Icc 1 ⌊t⌋₊, chi k) * (t : Complex) ^ (-(s + 1)))) s := by
  have htPos : 0 < t := zero_lt_one.trans ht
  have htZero : Not ((t : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr htPos.ne'
  have hExponent : HasDerivAt (fun z : Complex => -(z + 1)) (-1) s := by
    have hRaw := ((hasDerivAt_id' s).add_const 1).neg
    exact hRaw.congr_of_eventuallyEq (Eventually.of_forall fun _ => rfl)
  have hPower := hExponent.const_cpow (Or.inl htZero)
  have hProduct := hPower.const_smul (∑ k ∈ Icc 1 ⌊t⌋₊, chi k)
  convert hProduct using 1 <;> try rfl
  rw [Complex.ofReal_log htPos.le]
  ring

end BombieriVinogradov
