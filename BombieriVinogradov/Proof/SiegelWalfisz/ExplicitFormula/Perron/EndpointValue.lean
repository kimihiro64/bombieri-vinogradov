import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Definitions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact value of the endpoint Perron integral

This module evaluates the finite unsmoothed Perron kernel at `y = 1`.  The
calculation is kept separate from the later error bound so that contour-value
algebra and real inequalities have distinct dependency owners.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

private lemma inv_ofReal_add_ofReal_mul_I (c t : Real) :
    Inv.inv ((c : Complex) + (t : Complex) * Complex.I) =
      ((c / (c ^ 2 + t ^ 2) : Real) : Complex) -
        ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I := by
  rw [Complex.inv_def]
  simp [Complex.normSq_apply, div_eq_mul_inv]
  ring

private lemma odd_fraction_integral_eq_zero (c T : Real) :
    intervalIntegral (fun t : Real => t / (c ^ 2 + t ^ 2)) (-T) T
        MeasureTheory.volume = 0 := by
  let f : Real -> Real := fun t => t / (c ^ 2 + t ^ 2)
  have hOdd (t : Real) : f (-t) = -f t := by
    dsimp [f]
    ring
  have hComp := intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
  have hSame :
      intervalIntegral (fun t : Real => f (-t)) (-T) T MeasureTheory.volume =
        intervalIntegral f (-T) T MeasureTheory.volume := by
    simpa only [neg_neg] using hComp
  have hNeg :
      intervalIntegral (fun t : Real => f (-t)) (-T) T MeasureTheory.volume =
        -intervalIntegral f (-T) T MeasureTheory.volume := by
    calc
      intervalIntegral (fun t : Real => f (-t)) (-T) T MeasureTheory.volume =
          intervalIntegral (fun t : Real => -f t) (-T) T MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t _
        exact hOdd t
      _ = -intervalIntegral f (-T) T MeasureTheory.volume :=
        intervalIntegral.integral_neg
  have hZero : intervalIntegral f (-T) T MeasureTheory.volume = 0 := by
    linarith
  simpa [f] using hZero

private lemma reciprocal_vertical_integral_eq_arctan
    {c T : Real} (hc : 0 < c) :
    intervalIntegral
        (fun t : Real => Inv.inv ((c : Complex) + (t : Complex) * Complex.I))
        (-T) T MeasureTheory.volume =
      ((2 * Real.arctan (T / c) : Real) : Complex) := by
  have hden (t : Real) : Ne (c ^ 2 + t ^ 2) 0 := by
    nlinarith [sq_nonneg t]
  have hRealContinuous : Continuous (fun t : Real => c / (c ^ 2 + t ^ 2)) := by
    fun_prop (disch := exact hden _)
  have hImagContinuous : Continuous (fun t : Real => t / (c ^ 2 + t ^ 2)) := by
    fun_prop (disch := exact hden _)
  have hRealComplexContinuous :
      Continuous (fun t : Real => ((c / (c ^ 2 + t ^ 2) : Real) : Complex)) := by
    fun_prop
  have hImagComplexContinuous :
      Continuous
        (fun t : Real =>
          ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I) := by
    fun_prop
  have hRealIntegral :
      intervalIntegral (fun t : Real => c / (c ^ 2 + t ^ 2)) (-T) T
          MeasureTheory.volume =
        2 * Real.arctan (T / c) := by
    calc
      intervalIntegral (fun t : Real => c / (c ^ 2 + t ^ 2)) (-T) T
          MeasureTheory.volume =
          Real.arctan (T / c) - Real.arctan (-T / c) := integral_div_sq_add_sq
      _ = 2 * Real.arctan (T / c) := by
        rw [neg_div, Real.arctan_neg]
        ring
  calc
    intervalIntegral
        (fun t : Real => Inv.inv ((c : Complex) + (t : Complex) * Complex.I))
        (-T) T MeasureTheory.volume =
        intervalIntegral
          (fun t : Real =>
            ((c / (c ^ 2 + t ^ 2) : Real) : Complex) -
              ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I)
          (-T) T MeasureTheory.volume := by
      apply intervalIntegral.integral_congr
      intro t _
      exact inv_ofReal_add_ofReal_mul_I c t
    _ = intervalIntegral
          (fun t : Real => ((c / (c ^ 2 + t ^ 2) : Real) : Complex))
          (-T) T MeasureTheory.volume -
        intervalIntegral
          (fun t : Real =>
            ((t / (c ^ 2 + t ^ 2) : Real) : Complex) * Complex.I)
          (-T) T MeasureTheory.volume := by
      exact intervalIntegral.integral_sub
        (hRealComplexContinuous.intervalIntegrable _ _)
        (hImagComplexContinuous.intervalIntegrable _ _)
    _ = ((2 * Real.arctan (T / c) : Real) : Complex) := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
      rw [hRealIntegral, odd_fraction_integral_eq_zero]
      simp

/-- The endpoint Perron kernel is an arctangent ratio. -/
theorem truncatedPerronKernel_one_eq_arctan
    {c T : Real} (hc : 0 < c) :
    truncatedPerronKernel 1 c T =
      (Real.arctan (T / c) / Real.pi : Complex) := by
  rw [truncatedPerronKernel]
  simp [VIntegral', VIntegral]
  rw [reciprocal_vertical_integral_eq_arctan hc]
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

end BombieriVinogradov.SiegelWalfisz
