import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Pole
import PrimeNumberTheoremAnd.Rectangle
import PrimeNumberTheoremAnd.Tactic.AdditiveCombination

/-!
# Finite left-shift identity for the Perron kernel

This module specializes the simple-pole rectangle theorem to a finite
leftward shift.  It owns only the exact normalized contour identity; bounds
and passage to infinity are kept in outward modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Shifting left across zero expresses the Perron kernel minus its residue in
terms of the two horizontal edges and the left vertical edge. -/
theorem truncatedPerronKernel_sub_one_eq_left_rectangle_terms
    {y c T R : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hR : 0 < R) :
    truncatedPerronKernel y c T - 1 =
      -HIntegral' (perronKernelIntegrand y) (-R) c (-T) +
        HIntegral' (perronKernelIntegrand y) (-R) c T +
          VIntegral' (perronKernelIntegrand y) (-R) (-T) T := by
  let z : Complex := ((-R : Real) : Complex) -
    Complex.I * (T : Complex)
  let w : Complex := (c : Complex) + Complex.I * (T : Complex)
  have hIm : z.im <= w.im := by
    dsimp [z, w]
    simp
    linarith
  have hRe : z.re <= w.re := by
    dsimp [z, w]
    simp
    linarith
  have hZero : Membership.mem (nhds (0 : Complex)) (Complex.Rectangle z w) := by
    rw [rectangle_mem_nhds_iff]
    simp only [Complex.mem_reProdIm, z, w, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_self, sub_zero, Complex.add_re,
      add_zero, Complex.sub_im, Complex.mul_im, one_mul, zero_add,
      zero_sub, Complex.add_im, Complex.zero_re, Complex.zero_im]
    rw [Set.uIoo_of_lt (by linarith), Set.uIoo_of_lt (by linarith)]
    exact And.intro (And.intro (by linarith) hc)
      (And.intro (by linarith) hT)
  have hResidue := rectangleIntegral'_perron_eq_one hy hRe hIm hZero
  simp only [z, w, RectangleIntegral', RectangleIntegral, smul_eq_mul,
    Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self,
    sub_zero, Complex.add_re, add_zero, Complex.sub_im, Complex.mul_im,
    one_mul, zero_add, zero_sub, Complex.add_im] at hResidue
  simp only [truncatedPerronKernel, HIntegral', VIntegral', smul_eq_mul]
  linear_combination hResidue

end BombieriVinogradov.SiegelWalfisz
