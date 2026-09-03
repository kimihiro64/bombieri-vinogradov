import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.LeftIntegrandBound
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.LeftIntegrandTermContinuity
import BombieriVinogradov.Helpers.RealAnalysis.LogOverOnePlusAbsContinuity
import BombieriVinogradov.Helpers.RealAnalysis.LogOverOnePlusAbsIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.LeftBoundaryIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered left-boundary integral bound

This module combines the left-line pointwise estimate, continuity, and the
weighted reciprocal integral to bound the normalized centered vertical segment.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/--
The centered left vertical segment at real part `-1/2` is bounded by the
logarithmic majorant obtained from the reflected logarithmic derivative and
the centered power kernel.
-/
theorem exists_norm_centered_left_boundary_integral_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N]
        {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 1 <= x ->
              forall {T : Real}, 0 <= T ->
                norm
                    (centeredExplicitFormulaLeftBoundaryIntegral
                      chi x ((1 : Real) / 2) T) <=
                  (6 / Real.pi) *
                    (abs (Real.log N) +
                      C * Real.log (T + 2)) *
                    Real.log (T + 1)) := by
  choose C hCPos hPointwise using
    exists_norm_centered_explicitFormulaIntegrand_left_line_le
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst chi hchi hPrimitive x hx T hT
  let path : Real -> Complex := fun t =>
    (((-(1 : Real) / 2 : Real) : Complex) +
      (t : Complex) * Complex.I)
  let centered : Real -> Complex := fun t =>
    explicitFormulaIntegrand chi x (path t) -
      explicitFormulaIntegrand chi 1 (path t)
  let majorant : Real -> Real := fun t =>
    (abs (Real.log N) + C * Real.log (abs t + 2)) *
      (6 / (abs t + 1))
  have hxPos : 0 < x := Nat.zero_lt_of_lt hx
  have hIntX :
      IntervalIntegrable
        (fun t : Real => explicitFormulaIntegrand chi x (path t))
        MeasureTheory.volume (-T) T := by
    simpa [path] using
      intervalIntegrable_explicitFormulaIntegrand_left_line
        hchi hPrimitive x hxPos T
  have hIntOne :
      IntervalIntegrable
        (fun t : Real => explicitFormulaIntegrand chi 1 (path t))
        MeasureTheory.volume (-T) T := by
    simpa [path] using
      intervalIntegrable_explicitFormulaIntegrand_left_line
        hchi hPrimitive 1 (by norm_num) T
  have hMajorantIntegrable :
      IntervalIntegrable majorant MeasureTheory.volume (-T) T := by
    simpa [majorant] using
      BombieriVinogradov.RealAnalysis.intervalIntegrable_log_weight_div_abs_add_one
        (abs (Real.log N)) C T
  have hPointwiseAt :
      forall t : Real, norm (centered t) <= majorant t := by
    intro t
    have hsRe : (path t).re = -(1 : Real) / 2 := by
      dsimp [path]
      simp
    simpa [centered, majorant, path] using
      hPointwise hchi hPrimitive hx hsRe
  have hIntervalNorm :
      norm
          (intervalIntegral centered (-T) T MeasureTheory.volume) <=
        intervalIntegral majorant (-T) T MeasureTheory.volume := by
    exact intervalIntegral.norm_integral_le_of_norm_le
      (by linarith)
      (Filter.Eventually.of_forall (fun t _ => hPointwiseAt t))
      hMajorantIntegrable
  have hMajorantBound :
      intervalIntegral majorant (-T) T MeasureTheory.volume <=
        12 *
          (abs (Real.log N) + C * Real.log (T + 2)) *
          Real.log (T + 1) := by
    simpa [majorant] using
      BombieriVinogradov.RealAnalysis.intervalIntegral_log_weight_div_abs_add_one_le
        (abs (Real.log N)) C T hCPos.le hT
  have hBoundaryIdentity :
      centeredExplicitFormulaLeftBoundaryIntegral
          chi x ((1 : Real) / 2) T =
        (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          Complex.I *
          intervalIntegral centered (-T) T MeasureTheory.volume := by
    unfold centeredExplicitFormulaLeftBoundaryIntegral
    simp only [VIntegral', VIntegral, smul_eq_mul]
    rw [intervalIntegral.integral_sub hIntX hIntOne]
    dsimp [centered, path]
    ring_nf
  have hNormFactor :
      norm (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          norm Complex.I =
        1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  calc
    norm
        (centeredExplicitFormulaLeftBoundaryIntegral
          chi x ((1 : Real) / 2) T) =
      (1 / (2 * Real.pi)) *
        norm (intervalIntegral centered (-T) T MeasureTheory.volume) := by
      rw [hBoundaryIdentity, norm_mul, norm_mul, hNormFactor]
    _ <= (1 / (2 * Real.pi)) *
        intervalIntegral majorant (-T) T MeasureTheory.volume :=
      mul_le_mul_of_nonneg_left hIntervalNorm (by positivity)
    _ <= (1 / (2 * Real.pi)) *
        (12 *
          (abs (Real.log N) + C * Real.log (T + 2)) *
          Real.log (T + 1)) :=
      mul_le_mul_of_nonneg_left hMajorantBound (by positivity)
    _ = (6 / Real.pi) *
        (abs (Real.log N) + C * Real.log (T + 2)) *
        Real.log (T + 1) := by
      field_simp [ne_of_gt Real.pi_pos]
      ring

end BombieriVinogradov.SiegelWalfisz
