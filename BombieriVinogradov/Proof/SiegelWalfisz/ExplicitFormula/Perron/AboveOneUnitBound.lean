import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.LeftArcBound

/-!
# Unit Perron error above one

This module normalizes the strict full-turn estimate for the complementary
left arc, giving the unit branch of the source Perron error.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- For a base greater than one, the truncated Perron kernel differs from its
residue by strictly less than `y ^ c`. -/
theorem norm_truncatedPerronKernel_sub_one_lt_unit_bound
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T - 1) < y ^ c := by
  let a : Complex := 1 / (2 * Real.pi * Complex.I)
  have hCoeff : norm a = 1 / (2 * Real.pi) := by
    dsimp [a]
    rw [norm_div, norm_one, norm_mul, norm_mul]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  have hCoeffPos : 0 < norm a := by
    rw [hCoeff]
    positivity
  rw [truncatedPerronKernel_sub_one_eq_neg_leftArc hy1 hc hT]
  change norm (-a * perronLeftArcIntegral y c T) < _
  rw [norm_mul, norm_neg]
  calc
    norm a * norm (perronLeftArcIntegral y c T) <
        norm a * (2 * Real.pi * y ^ c) :=
      mul_lt_mul_of_pos_left
        (norm_perronLeftArcIntegral_lt_two_pi_mul hy1 hc hT) hCoeffPos
    _ = y ^ c := by
      rw [hCoeff]
      field_simp [ne_of_gt Real.pi_pos]

end BombieriVinogradov.SiegelWalfisz
