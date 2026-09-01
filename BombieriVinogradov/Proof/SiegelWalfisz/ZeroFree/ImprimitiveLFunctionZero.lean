import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionEulerProduct
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LevelCorrectionNonvanishing

/-!
# Transfer of an imprimitive L-function zero

The finite level-correction product does not vanish in the open right
half-plane, so every ambient L-function zero there is already a zero of the
inducing primitive character's L-function.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem primitive_LFunction_eq_zero_of_LFunction_eq_zero
    {N : Nat} [NeZero N] (chi : _root_.DirichletCharacter Complex N)
    [NeZero chi.conductor]
    (hchi : chi ≠ 1) {s : Complex} (hs : 0 < s.re)
    (hzero : chi.LFunction s = 0) :
    chi.primitiveCharacter.LFunction s = 0 := by
  have hCorrection := levelCorrection_ne_zero_of_re_pos chi hs
  have hProduct := LFunction_eq_primitive_mul_levelCorrection chi hchi s
  rw [hzero] at hProduct
  exact (mul_eq_zero.mp hProduct.symm).resolve_right hCorrection

end BombieriVinogradov.SiegelWalfisz
