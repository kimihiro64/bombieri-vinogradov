import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ZeroKernel

/-!
# The reciprocal kernel at an indexed zero height

This module turns the contribution of one multiplicity-indexed completed
L-function zero into the reciprocal horizontal distance used in the zero-free
region argument.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem indexedZeroKernel_re
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (p : SymmetricCompletedZeroIndex chi) {sigma t : Real}
    (hsigma : 1 < sigma)
    (him : (Complex.Hadamard.divisorZeroIndex₀_val p).im = t) :
    (1 / ((sigma : Complex) + Complex.I * t -
      Complex.Hadamard.divisorZeroIndex₀_val p)).re =
        (sigma - (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ := by
  have hStrip :=
    symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo hchi hPrimitive p
  have hPointRe :
      ((sigma : Complex) + Complex.I * t).re = sigma := by
    simp [Complex.mul_re]
  have hPointIm :
      ((sigma : Complex) + Complex.I * t).im = t := by
    simp [Complex.mul_im]
  have hReNe :
      ((sigma : Complex) + Complex.I * t).re ≠
        (Complex.Hadamard.divisorZeroIndex₀_val p).re := by
    rw [hPointRe]
    exact ne_of_gt (hStrip.2.trans hsigma)
  have hIm :
      ((sigma : Complex) + Complex.I * t).im =
        (Complex.Hadamard.divisorZeroIndex₀_val p).im := by
    rw [hPointIm]
    exact him.symm
  have hKernel := zeroKernel_re_of_same_im hReNe hIm
  rw [hPointRe] at hKernel
  simpa only [one_div] using hKernel

end BombieriVinogradov.SiegelWalfisz
