import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.HorizontalIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RightRectangle
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.RightVerticalDecay

/-!
# Infinite right-shift identity for the Perron kernel

This module passes the finite right-rectangle identity to the limit.  The
original vertical kernel becomes the difference of the two normalized
rightward horizontal integrals.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

/-- For a base below one, shifting the Perron rectangle to positive infinity
leaves exactly the two improper horizontal edges. -/
theorem truncatedPerronKernel_eq_rightHorizontalIntegrals
    {y c T : Real} (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c)
    (hT : 0 < T) :
    truncatedPerronKernel y c T =
      (1 / (2 * Real.pi * Complex.I) : Complex) *
          rightHorizontalIntegral y c (-T) -
        (1 / (2 * Real.pi * Complex.I) : Complex) *
          rightHorizontalIntegral y c T := by
  have hBottom := tendsto_hIntegral'_right_atTop
    (t := -T) hy hy1 hc
  have hTop := tendsto_hIntegral'_right_atTop
    (t := T) hy hy1 hc
  have hRight := tendsto_vIntegral'_perron_right_atTop hy hy1 hT.le
  have hCombined := (hBottom.sub hTop).add hRight
  have hFinite : Filter.Eventually
      (fun R : Real => truncatedPerronKernel y c T =
        HIntegral' (perronKernelIntegrand y) c R (-T) -
          HIntegral' (perronKernelIntegrand y) c R T +
            VIntegral' (perronKernelIntegrand y) R (-T) T) atTop := by
    filter_upwards [eventually_ge_atTop c] with R hR
    exact truncatedPerronKernel_eq_right_rectangle_terms hy hc hT hR
  have hConst : Tendsto (fun _ : Real => truncatedPerronKernel y c T) atTop
      (nhds
        ((1 / (2 * Real.pi * Complex.I) : Complex) *
            rightHorizontalIntegral y c (-T) -
          (1 / (2 * Real.pi * Complex.I) : Complex) *
            rightHorizontalIntegral y c T)) := by
    have hCombined' : Tendsto
        (fun R : Real =>
          HIntegral' (perronKernelIntegrand y) c R (-T) -
            HIntegral' (perronKernelIntegrand y) c R T +
              VIntegral' (perronKernelIntegrand y) R (-T) T)
        atTop
        (nhds
          ((1 / (2 * Real.pi * Complex.I) : Complex) *
              rightHorizontalIntegral y c (-T) -
            (1 / (2 * Real.pi * Complex.I) : Complex) *
              rightHorizontalIntegral y c T)) := by
      simpa using hCombined
    apply hCombined'.congr'
    filter_upwards [hFinite] with R hR
    exact hR.symm
  exact tendsto_nhds_unique tendsto_const_nhds hConst

end BombieriVinogradov.SiegelWalfisz
