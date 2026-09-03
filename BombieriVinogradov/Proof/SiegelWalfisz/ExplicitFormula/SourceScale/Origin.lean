import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.MultiplicityBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Origin logarithm versus the source scale
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_originMultiplicity_mul_log_le_sourceScale
    {N x : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hN : 3 <= N) (hx : 2 < x)
    {T : Real} (hT : 2 <= T) (hTx : T <= x) :
    norm
        ((lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex)) <=
      (x : Real) / T *
        (Real.log ((N * x : Nat) : Real)) ^ 2 := by
  let L := Real.log ((N * x : Nat) : Real)
  have hMultiplicity :=
    lFunctionOriginMultiplicity_le_one hchi hPrimitive
  have hMultiplicityReal :
      (lFunctionOriginMultiplicity chi : Real) <= 1 :=
    by
      have hRaw :
          (lFunctionOriginMultiplicity chi : Real) <= ((1 : Nat) : Real) :=
        (Nat.cast_le).2 hMultiplicity
      simpa only [Nat.cast_one] using hRaw
  have hMultiplicityNorm :
      norm (lFunctionOriginMultiplicity chi : Complex) <= 1 := by
    simpa using hMultiplicityReal
  have hxOneNat : 1 <= x :=
    le_trans (by norm_num) (Nat.le_of_lt hx)
  have hxOneReal : (1 : Real) <= (x : Real) :=
    by
      have hRaw : ((1 : Nat) : Real) <= (x : Real) :=
        (Nat.cast_le).2 hxOneNat
      simpa only [Nat.cast_one] using hRaw
  have hxNonneg : 0 <= (x : Real) := zero_le_one.trans hxOneReal
  have hLogXNonneg : 0 <= Real.log x :=
    Real.log_nonneg hxOneReal
  have hLogNorm :
      norm (Complex.log (x : Complex)) = Real.log x := by
    rw [show (x : Complex) = ((x : Real) : Complex) by norm_num]
    rw [Eq.symm (Complex.ofReal_log hxNonneg)]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hLogXNonneg]
  have hOrigin :
      norm
          ((lFunctionOriginMultiplicity chi : Complex) *
            Complex.log (x : Complex)) <=
        Real.log x := by
    rw [norm_mul, hLogNorm]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hMultiplicityNorm hLogXNonneg
  have hLOne : 1 <= L := by
    simpa [L] using one_le_log_level_mul_argument hN hx
  have hLNonneg : 0 <= L := zero_le_one.trans hLOne
  have hLSqProduct : 0 <= (L - 1) * L :=
    mul_nonneg (sub_nonneg.mpr hLOne) hLNonneg
  have hLSq : L <= L ^ 2 := by
    nlinarith
  have hLogX : Real.log x <= L := by
    simpa [L] using log_argument_le_log_level_mul_argument hN hx
  have hTPos : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hRatioRaw : T / T <= (x : Real) / T :=
    (div_le_div_iff_of_pos_right hTPos).2 hTx
  have hRatioOne : 1 <= (x : Real) / T := by
    simpa [ne_of_gt hTPos] using hRatioRaw
  calc
    norm
        ((lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex)) <=
      Real.log x :=
      hOrigin
    _ <= L ^ 2 :=
      hLogX.trans hLSq
    _ <= (x : Real) / T * L ^ 2 := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hRatioOne (sq_nonneg L)
    _ = (x : Real) / T *
        (Real.log ((N * x : Nat) : Real)) ^ 2 := by
      rfl

end BombieriVinogradov.SiegelWalfisz
