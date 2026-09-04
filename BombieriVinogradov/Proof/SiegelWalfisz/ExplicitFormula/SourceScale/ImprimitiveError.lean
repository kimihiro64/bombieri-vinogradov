import BombieriVinogradov.Helpers.RealAnalysis.BilinearLinearCorrection
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.ImprimitivePrimary
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorbing all imprimitive corrections into the published remainder

The Euler correction and the primitive-only reflected-zero correction fit
one constant times the existing primary plus quarter-power error scale.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem imprimitive_correction_le_remainder
    {c : Real} (hc : 0 < c) {N x : Nat} (hN : 3 <= N) (hx : 2 <= x)
    {T : Real} (hT : 2 <= T) (hTx : T <= x) :
    Real.log N * Real.log x / Real.log (2 : Real) + Real.log N / c +
      (x : Real) ^ (1 / 4 : Real) * Real.log x <=
        (1 / Real.log (2 : Real) + 1 / c + 1) *
          explicitFormulaRemainderMajorant N x T := by
  have hBounds := imprimitive_log_terms_le_primaryScale hN hx hT hTx
  have hTPos : 0 < T := by linarith
  have hP : 0 <= (x : Real) / T * (Real.log ((N * x : Nat) : Real)) ^ 2 :=
    by positivity
  have hQ : 0 <= (x : Real) ^ (1 / 4 : Real) * Real.log x := by positivity
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hk : 0 <= 1 / Real.log (2 : Real) := by positivity
  have hj : 0 <= 1 / c := by positivity
  have hAbstract := RealAnalysis.bilinear_linear_correction_le_scale
    hBounds.1 hBounds.2 hP hQ hk hj
  have hIdentity :
      Real.log N * Real.log x / Real.log (2 : Real) + Real.log N / c +
        (x : Real) ^ (1 / 4 : Real) * Real.log x =
      (1 / Real.log (2 : Real)) * (Real.log N * Real.log x) +
        (1 / c) * Real.log N + (x : Real) ^ (1 / 4 : Real) * Real.log x := by ring
  rw [hIdentity]
  exact hAbstract

end BombieriVinogradov.SiegelWalfisz
