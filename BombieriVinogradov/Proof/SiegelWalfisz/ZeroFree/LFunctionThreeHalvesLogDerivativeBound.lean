import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeRightHalfPlaneBound

/-!
# L-function logarithmic derivative bound on the three-halves line

This module specializes the complex-height zeta majorant and absorbs its fixed
value into the logarithmic vertical scale.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_LFunction_le_log_of_re_eq_three_halves :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N]
        (chi : DirichletCharacter Complex N) {s : Complex},
          s.re = (3 : Real) / 2 ->
            norm (logDeriv chi.LFunction s) <=
              C * Real.log (abs s.im + 2)) := by
  let Z : Real :=
    norm (-deriv riemannZeta ((3 : Complex) / 2) /
      riemannZeta ((3 : Complex) / 2))
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : Real := Z / Real.log 2 + 1
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst chi s hsRe
  have hsRight : 1 < s.re := by
    rw [hsRe]
    norm_num
  have hMajorant := norm_neg_logDeriv_LFunction_le_zeta_re chi hsRight
  have hRaw : norm (logDeriv chi.LFunction s) <= Z := by
    rw [logDeriv_apply]
    rw [hsRe] at hMajorant
    simpa [Z] using hMajorant
  have hLogLower : Real.log 2 <= Real.log (abs s.im + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hZAbsorb :
      Z <= (Z / Real.log 2) * Real.log (abs s.im + 2) := by
    calc
      Z = (Z / Real.log 2) * Real.log 2 := by
        field_simp
      _ <= (Z / Real.log 2) * Real.log (abs s.im + 2) :=
        mul_le_mul_of_nonneg_left hLogLower
          (div_nonneg (norm_nonneg _) hLogTwo.le)
  have hLogNonneg : 0 <= Real.log (abs s.im + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg s.im])
  calc
    norm (logDeriv chi.LFunction s) <= Z := hRaw
    _ <= (Z / Real.log 2) * Real.log (abs s.im + 2) := hZAbsorb
    _ <= C * Real.log (abs s.im + 2) := by
      apply mul_le_mul_of_nonneg_right
      exact le_add_of_nonneg_right (by norm_num)
      exact hLogNonneg

end BombieriVinogradov.SiegelWalfisz
