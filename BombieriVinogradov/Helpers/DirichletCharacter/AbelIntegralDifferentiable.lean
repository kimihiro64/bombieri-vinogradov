import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegral
import BombieriVinogradov.Helpers.DirichletCharacter.AbelIntegralHasDerivAt
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiability of the normalized character Abel integral

This module owns the outer product rule after differentiability of the kernel
integral has been established.
-/

set_option autoImplicit false

namespace BombieriVinogradov

/-- The normalized nonprincipal character Abel integral is differentiable for `re(s)>0`. -/
theorem characterAbelIntegral_differentiableAt {N : Nat} [NeZero N]
    (chi : DirichletCharacter Complex N) (hchi : chi ≠ 1)
    {s : Complex} (hs : 0 < s.re) :
    DifferentiableAt Complex (characterAbelIntegral chi) s := by
  unfold characterAbelIntegral
  exact (hasDerivAt_id' s).differentiableAt.mul
    (characterAbelKernelIntegral_hasDerivAt chi hchi hs).differentiableAt

end BombieriVinogradov
