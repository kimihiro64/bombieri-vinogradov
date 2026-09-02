import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Positive-base power heads above one

This module evaluates the elementary decaying power integral on a left
half-line used to dominate the horizontal edges of the left Perron contour.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

/-- A real base greater than one has an integrable power head. -/
theorem integrableOn_rpow_Iic
    {y : Real} (hy1 : 1 < y) (c : Real) :
    IntegrableOn (fun x : Real => y ^ x) (Iic c) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  simpa [Real.rpow_def_of_pos hy] using
    integrableOn_exp_mul_Iic (Real.log_pos hy1) c

/-- Exact value of the decaying positive-base power head. -/
theorem integral_rpow_Iic
    {y : Real} (hy1 : 1 < y) (c : Real) :
    integral (volume.restrict (Iic c)) (fun x : Real => y ^ x) =
      y ^ c / abs (Real.log y) := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  rw [show (fun x : Real => y ^ x) =
      fun x : Real => Real.exp (Real.log y * x) by
    funext x
    exact Real.rpow_def_of_pos hy x]
  rw [integral_exp_mul_Iic (Real.log_pos hy1)]
  rw [(Real.rpow_def_of_pos hy c).symm]
  rw [abs_of_pos (Real.log_pos hy1)]

end BombieriVinogradov.SiegelWalfisz
