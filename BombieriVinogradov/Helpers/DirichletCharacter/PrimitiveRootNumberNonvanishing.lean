import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveGaussSumNonvanishing
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Nonvanishing of primitive Dirichlet root numbers

This module transfers primitive Gauss-sum nonvanishing through Mathlib's exact global
root-number normalization.
-/

set_option autoImplicit false

namespace BombieriVinogradov

theorem primitive_rootNumber_ne_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    chi.rootNumber ≠ 0 := by
  have hNCast : (N : Complex) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNCpow : (N : Complex) ^ (1 / 2 : Complex) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl hNCast)
  rw [DirichletCharacter.rootNumber]
  exact div_ne_zero
    (div_ne_zero (primitive_gaussSum_stdAddChar_ne_zero hPrimitive)
      (pow_ne_zero _ Complex.I_ne_zero))
    hNCpow

end BombieriVinogradov
