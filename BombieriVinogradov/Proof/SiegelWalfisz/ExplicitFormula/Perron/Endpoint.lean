import BombieriVinogradov.Helpers.ComplexAnalysis.ArctanLtSelf
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.EndpointValue

/-!
# Endpoint error for the truncated Perron kernel

This module turns the exact endpoint value into the strict endpoint estimate
in the scalar truncated Perron formula.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- At `y = 1`, the truncated Perron kernel differs from its half-weight by
strictly less than the source error `c / (pi * T)`. -/
theorem norm_truncatedPerronKernel_one_sub_perronStepWeight_lt
    {c T : Real} (hc : 0 < c) (hT : 0 < T) :
    norm
        (truncatedPerronKernel 1 c T -
          (perronStepWeight 1 : Complex)) <
      c / (Real.pi * T) := by
  have hRatio : 0 < T / c := div_pos hT hc
  have hInverse : Inv.inv (T / c) = c / T := by
    field_simp
  have hComplement :
      Real.pi / 2 - Real.arctan (T / c) = Real.arctan (c / T) := by
    rw [hInverse.symm]
    exact (Real.arctan_inv_of_pos hRatio).symm
  have hArctanUpper : Real.arctan (T / c) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hSmall : Real.arctan (c / T) < c / T :=
    Real.arctan_lt_self_of_pos (div_pos hc hT)
  have hDifferenceNeg :
      Real.arctan (T / c) / Real.pi - 1 / 2 < 0 := by
    have hScaledUpper :
        Real.arctan (T / c) / Real.pi < (Real.pi / 2) / Real.pi :=
      div_lt_div_of_pos_right hArctanUpper Real.pi_pos
    have hHalf : (Real.pi / 2) / Real.pi = 1 / 2 := by
      field_simp [ne_of_gt Real.pi_pos]
    rw [hHalf] at hScaledUpper
    exact sub_neg.mpr hScaledUpper
  rw [truncatedPerronKernel_one_eq_arctan hc, perronStepWeight_one]
  rw [(Complex.ofReal_div _ _).symm, (Complex.ofReal_sub _ _).symm,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_neg hDifferenceNeg]
  rw [show
      Real.arctan (T / c) / Real.pi - 1 / 2 =
        -(Real.arctan (c / T) / Real.pi) by
      rw [hComplement.symm]
      field_simp [ne_of_gt Real.pi_pos]
      ring]
  rw [neg_neg]
  have hPi : 0 < Real.pi := Real.pi_pos
  have hScaled : Real.arctan (c / T) / Real.pi < (c / T) / Real.pi :=
    div_lt_div_of_pos_right hSmall hPi
  calc
    Real.arctan (c / T) / Real.pi < (c / T) / Real.pi := hScaled
    _ = c / (Real.pi * T) := by field_simp

end BombieriVinogradov.SiegelWalfisz
