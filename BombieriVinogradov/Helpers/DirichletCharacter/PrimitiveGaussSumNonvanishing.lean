import Mathlib.Analysis.Fourier.ZMod

/-!
# Nonvanishing of primitive Dirichlet Gauss sums

This module uses Fourier inversion to prove that the standard Gauss sum of a primitive
Dirichlet character cannot vanish.
-/

set_option autoImplicit false

namespace BombieriVinogradov

theorem primitive_gaussSum_stdAddChar_ne_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    gaussSum chi ZMod.stdAddChar ≠ 0 := by
  intro hGauss
  have hFourierZero : ZMod.dft (fun x : ZMod N => chi x) = 0 := by
    funext k
    rw [hPrimitive.fourierTransform_eq_inv_mul_gaussSum, hGauss, mul_zero]
    rfl
  have hDouble := ZMod.dft_dft (fun x : ZMod N => chi x)
  rw [hFourierZero] at hDouble
  have hAt := congrFun hDouble (-1 : ZMod N)
  have hNCast : (N : Complex) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hZero : (N : Complex) = 0 := by
    simpa using hAt.symm
  exact hNCast hZero

end BombieriVinogradov
