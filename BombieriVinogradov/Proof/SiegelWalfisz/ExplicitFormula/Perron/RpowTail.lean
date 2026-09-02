import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Positive-base power tails below one

This module evaluates the elementary decaying power tail used to dominate the
horizontal edges of the Perron contour.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace BombieriVinogradov.SiegelWalfisz

/-- A positive real base below one has an integrable power tail. -/
theorem integrableOn_rpow_Ioi
    {y : Real} (hy : 0 < y) (hy1 : y < 1) (c : Real) :
    IntegrableOn (fun x : Real => y ^ x) (Ioi c) := by
  simpa [Real.rpow_def_of_pos hy] using
    integrableOn_exp_mul_Ioi (Real.log_neg hy hy1) c

/-- Exact value of the decaying positive-base power tail. -/
theorem integral_rpow_Ioi
    {y : Real} (hy : 0 < y) (hy1 : y < 1) (c : Real) :
    integral (volume.restrict (Ioi c)) (fun x : Real => y ^ x) =
      y ^ c / abs (Real.log y) := by
  rw [show (fun x : Real => y ^ x) =
      fun x : Real => Real.exp (Real.log y * x) by
    funext x
    exact Real.rpow_def_of_pos hy x]
  rw [integral_exp_mul_Ioi (Real.log_neg hy hy1)]
  rw [(Real.rpow_def_of_pos hy c).symm]
  rw [abs_of_neg (Real.log_neg hy hy1)]
  ring

end BombieriVinogradov.SiegelWalfisz
