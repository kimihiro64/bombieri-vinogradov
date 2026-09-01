import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeBoundCore
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorLogDerivativeScale
import Mathlib.Analysis.Real.Pi.Bounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

/-!
# Even-character gamma logarithmic-derivative bound

This module proves the vertical-strip logarithmic bound for even Dirichlet-character
gamma factors.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_gammaFactor_le_log_of_even :
    exists C : Real, 0 < C ∧
      forall {N : Nat} {chi : DirichletCharacter Complex N},
        DirichletCharacter.Even chi ->
          forall {s : Complex}, 1 < s.re -> s.re ≤ 2 ->
            ‖logDeriv chi.gammaFactor s‖ ≤
              C * Real.log (|s.im| + 2) := by
  obtain ⟨D, hDPos, hD⟩ :=
    Complex.exists_norm_digamma_le_log
      (a := (1 : Real) / 2) (b := 1) (by norm_num)
  let C : Real := Real.log Real.pi / Real.log 2 + D
  have hLogPi : 0 < Real.log Real.pi :=
    Real.log_pos ((by norm_num : (1 : Real) < 3).trans Real.pi_gt_three)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N chi hEven s hsLower hsUpper
  have hPositive : 0 < s.re := lt_trans zero_lt_one hsLower
  have hArgumentLower : (1 : Real) / 2 ≤ (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  have hArgumentUpper : (s / 2).re ≤ 1 := by
    rw [Complex.div_ofNat_re]
    linarith
  have hDigamma := hD (s / 2) hArgumentLower hArgumentUpper
  have hDigammaLog :
      ‖Complex.digamma (s / 2)‖ ≤
        D * Real.log (|s.im| + 2) :=
    hDigamma.trans
      (mul_le_mul_of_nonneg_left
        (log_abs_im_div_two_add_two_le s) hDPos.le)
  have hCore :=
    norm_logDeriv_gammaFactor_le_log_of_formula hDPos
      (logDeriv_gammaFactor_of_even hEven hPositive) hDigammaLog
  exact hCore.2

end BombieriVinogradov.SiegelWalfisz
