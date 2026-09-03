import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.HorizontalIntegrandTermContinuity
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.HorizontalIntegrandBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.TopBoundaryIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Centered top horizontal-boundary integral bound

This module integrates the pointwise centered horizontal majorant along the
top segment while retaining the exact normalization and interval length.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz
theorem norm_centeredExplicitFormulaTopBoundaryIntegral_le
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (x : Nat) (hx : 2 < x)
    {T B : Real} (hT : 0 < T)
    (hNonzero : forall u : Real,
      Set.uIcc (-(1 : Real) / 2) (optimizedPerronLine x) u ->
        Ne (chi.LFunction
          ((u : Complex) + (T : Complex) * Complex.I)) 0)
    (hLog : forall u : Real,
      Set.uIcc (-(1 : Real) / 2) (optimizedPerronLine x) u ->
        norm (logDeriv chi.LFunction
          ((u : Complex) + (T : Complex) * Complex.I)) <= B) :
    norm (centeredExplicitFormulaTopBoundaryIntegral chi x
      ((1 : Real) / 2) (optimizedPerronLine x) T) <=
      (1 / (2 * Real.pi)) *
        (B * (4 * (x : Real) / abs T) *
          abs (optimizedPerronLine x - (-(1 : Real) / 2))) := by
  let path : Real -> Complex := fun u =>
    (u : Complex) + (T : Complex) * Complex.I
  let centered : Real -> Complex := fun u =>
    explicitFormulaIntegrand chi x (path u) -
      explicitFormulaIntegrand chi 1 (path u)
  let majorant : Real :=
    B * (4 * (x : Real) / abs T)
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  have hTNe : Ne T 0 := ne_of_gt hT
  have hLineLower :
      -(1 : Real) / 2 <= optimizedPerronLine x := by
    linarith [optimizedPerronLine_gt_one hx]
  have hIntX :
      IntervalIntegrable
        (fun u : Real => explicitFormulaIntegrand chi x (path u))
        MeasureTheory.volume (-(1 : Real) / 2)
          (optimizedPerronLine x) := by
    simpa [path] using
      intervalIntegrable_explicitFormulaIntegrand_horizontal
        hchi x hxPos hTNe hNonzero
  have hIntOne :
      IntervalIntegrable
        (fun u : Real => explicitFormulaIntegrand chi 1 (path u))
        MeasureTheory.volume (-(1 : Real) / 2)
          (optimizedPerronLine x) := by
    simpa [path] using
      intervalIntegrable_explicitFormulaIntegrand_horizontal
        hchi 1 (by norm_num) hTNe hNonzero
  have hPointwise :
      forall u : Real,
        Set.uIcc (-(1 : Real) / 2) (optimizedPerronLine x) u ->
          norm (centered u) <= majorant := by
    intro u hu
    have huBounds :
        Set.Icc (-(1 : Real) / 2) (optimizedPerronLine x) u := by
      simpa [Set.uIcc_of_le hLineLower] using hu
    have hsRe : (path u).re <= optimizedPerronLine x := by
      simpa [path] using huBounds.2
    have hsIm : 0 < abs (path u).im := by
      simpa [path] using (abs_pos.mpr hTNe)
    simpa [centered, majorant, path] using
      norm_explicitFormulaIntegrand_sub_one_le
        chi x hx hsRe hsIm (hLog u hu)
  have hIntegralNorm :
      norm
          (intervalIntegral centered (-(1 : Real) / 2)
            (optimizedPerronLine x) MeasureTheory.volume) <=
        majorant *
          abs (optimizedPerronLine x - (-(1 : Real) / 2)) :=
    by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u hu
      simpa [centered] using
        hPointwise u (Set.uIoc_subset_uIcc hu)
  have hBoundaryIdentity :
      centeredExplicitFormulaTopBoundaryIntegral chi x
          ((1 : Real) / 2) (optimizedPerronLine x) T =
        (1 / (2 * (Real.pi : Complex) * Complex.I)) *
          intervalIntegral centered (-(1 : Real) / 2)
            (optimizedPerronLine x) MeasureTheory.volume := by
    unfold centeredExplicitFormulaTopBoundaryIntegral
    simp only [HIntegral', HIntegral, smul_eq_mul]
    rw [intervalIntegral.integral_sub hIntX hIntOne]
    dsimp [centered, path]
    ring_nf
  have hNormFactor :
      norm (1 / (2 * (Real.pi : Complex) * Complex.I)) =
        1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  calc
    norm (centeredExplicitFormulaTopBoundaryIntegral chi x
        ((1 : Real) / 2) (optimizedPerronLine x) T) =
      (1 / (2 * Real.pi)) *
        norm
          (intervalIntegral centered (-(1 : Real) / 2)
            (optimizedPerronLine x) MeasureTheory.volume) := by
      rw [hBoundaryIdentity, norm_mul, hNormFactor]
    _ <= (1 / (2 * Real.pi)) *
        (majorant *
          abs (optimizedPerronLine x - (-(1 : Real) / 2))) :=
      mul_le_mul_of_nonneg_left hIntegralNorm (by positivity)
    _ = (1 / (2 * Real.pi)) *
        (B * (4 * (x : Real) / abs T) *
          abs (optimizedPerronLine x - (-(1 : Real) / 2))) := by
      rfl

end BombieriVinogradov.SiegelWalfisz
