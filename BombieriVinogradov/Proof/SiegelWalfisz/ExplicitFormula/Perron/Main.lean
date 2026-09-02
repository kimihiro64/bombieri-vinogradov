import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.AboveOne
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.BelowOne
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Endpoint

/-!
# Scalar truncated Perron estimate

This module is the thin all-cases consumer for Strombergsson Lemma 13.3.  The
contour, residue, endpoint, and norm arguments remain in their dedicated
modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The complete scalar truncated Perron estimate, including the half-weight
and distinct endpoint error at `y = 1`. -/
theorem norm_truncatedPerronKernel_sub_stepWeight_lt
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedPerronKernel y c T -
      (perronStepWeight y : Complex)) <
      if y = 1 then c / (Real.pi * T)
      else y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  rcases lt_trichotomy y 1 with hy1 | hyeq | hy1
  next =>
    rw [if_neg (ne_of_lt hy1)]
    exact norm_truncatedPerronKernel_sub_stepWeight_lt_of_lt_one
      hy hy1 hc hT
  next =>
    subst y
    rw [if_pos rfl]
    exact norm_truncatedPerronKernel_one_sub_perronStepWeight_lt hc hT
  next =>
    rw [if_neg (ne_of_gt hy1)]
    exact norm_truncatedPerronKernel_sub_stepWeight_lt_of_one_lt hy1 hc hT

end BombieriVinogradov.SiegelWalfisz
