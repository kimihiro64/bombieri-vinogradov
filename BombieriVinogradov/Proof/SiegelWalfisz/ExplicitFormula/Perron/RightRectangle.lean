import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Integrand
import PrimeNumberTheoremAnd.Rectangle
import PrimeNumberTheoremAnd.Tactic.AdditiveCombination

/-!
# Finite right-shift identity for the Perron kernel

This module owns only the Cauchy-theorem identity on a finite rectangle lying
strictly inside the right half-plane.  Bounds and limiting arguments are kept
in outward modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- On a right-half-plane rectangle, the left vertical integral is the two
horizontal integrals plus the right vertical integral. -/
theorem vIntegral_eq_right_rectangle_terms
    {y c T R : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hcR : c <= R) :
    VIntegral (perronKernelIntegrand y) c (-T) T =
      HIntegral (perronKernelIntegrand y) c R (-T) -
        HIntegral (perronKernelIntegrand y) c R T +
          VIntegral (perronKernelIntegrand y) R (-T) T := by
  let z : Complex := (c : Complex) - Complex.I * (T : Complex)
  let w : Complex := (R : Complex) + Complex.I * (T : Complex)
  have hIm : z.im <= w.im := by
    dsimp [z, w]
    simp
    linarith
  have hRe : z.re <= w.re := by
    simpa [z, w] using hcR
  have hSubset : Complex.Rectangle z w <= {s : Complex | 0 < s.re} := by
    intro s hs
    have hCoords := (mem_Rect hRe hIm s).mp hs
    have hLower : c <= s.re := by
      simpa [z, w] using hCoords.1
    exact hc.trans_le hLower
  have hZero : RectangleIntegral (perronKernelIntegrand y) z w = 0 :=
    (holomorphicOn_perronKernelIntegrand hy).vanishesOnRectangle hSubset
  have hExpanded :
      HIntegral (perronKernelIntegrand y) c R (-T) -
          HIntegral (perronKernelIntegrand y) c R T +
          VIntegral (perronKernelIntegrand y) R (-T) T -
          VIntegral (perronKernelIntegrand y) c (-T) T = 0 := by
    simpa [z, w, RectangleIntegral] using hZero
  linear_combination -hExpanded

/-- Normalized form of the finite right-shift identity. -/
theorem truncatedPerronKernel_eq_right_rectangle_terms
    {y c T R : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T)
    (hcR : c <= R) :
    truncatedPerronKernel y c T =
      HIntegral' (perronKernelIntegrand y) c R (-T) -
        HIntegral' (perronKernelIntegrand y) c R T +
          VIntegral' (perronKernelIntegrand y) R (-T) T := by
  simp only [truncatedPerronKernel, HIntegral', VIntegral']
  rw [vIntegral_eq_right_rectangle_terms hy hc hT hcR]
  module

end BombieriVinogradov.SiegelWalfisz
