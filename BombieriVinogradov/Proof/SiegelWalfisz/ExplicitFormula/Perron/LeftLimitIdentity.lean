import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.LeftHorizontalIntegral
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.LeftRectangle
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.LeftVerticalDecay

/-!
# Infinite left-shift identity for the Perron kernel

This module passes the finite left rectangle to the limit.  The original
kernel minus its residue becomes the signed sum of the two normalized
leftward horizontal integrals.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace BombieriVinogradov.SiegelWalfisz

/-- For a base above one, shifting the Perron rectangle to negative infinity
leaves the two improper horizontal edges after subtracting the residue. -/
theorem truncatedPerronKernel_sub_one_eq_leftHorizontalIntegrals
    {y c T : Real} (hy1 : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    truncatedPerronKernel y c T - 1 =
      -(1 / (2 * Real.pi * Complex.I) : Complex) *
          leftHorizontalIntegral y c (-T) +
        (1 / (2 * Real.pi * Complex.I) : Complex) *
          leftHorizontalIntegral y c T := by
  have hy : 0 < y := lt_trans Real.zero_lt_one hy1
  have hMinusAbs : 0 < abs (-T) :=
    abs_pos.mpr (neg_ne_zero.mpr hT.ne')
  have hPlusAbs : 0 < abs T := abs_pos.mpr hT.ne'
  have hBottom := tendsto_hIntegral'_left_atTop
    (c := c) hy1 hMinusAbs
  have hTop := tendsto_hIntegral'_left_atTop
    (c := c) hy1 hPlusAbs
  have hLeft := tendsto_vIntegral'_perron_left_atTop hy1 hT.le
  have hCombined := (hBottom.neg.add hTop).add hLeft
  have hFinite : Filter.Eventually
      (fun R : Real => truncatedPerronKernel y c T - 1 =
        -HIntegral' (perronKernelIntegrand y) (-R) c (-T) +
          HIntegral' (perronKernelIntegrand y) (-R) c T +
            VIntegral' (perronKernelIntegrand y) (-R) (-T) T) atTop := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with R hR
    exact truncatedPerronKernel_sub_one_eq_left_rectangle_terms hy hc hT hR
  have hConst : Tendsto
      (fun _ : Real => truncatedPerronKernel y c T - 1) atTop
      (nhds
        (-(1 / (2 * Real.pi * Complex.I) : Complex) *
            leftHorizontalIntegral y c (-T) +
          (1 / (2 * Real.pi * Complex.I) : Complex) *
            leftHorizontalIntegral y c T)) := by
    have hCombined' : Tendsto
        (fun R : Real =>
          -HIntegral' (perronKernelIntegrand y) (-R) c (-T) +
            HIntegral' (perronKernelIntegrand y) (-R) c T +
              VIntegral' (perronKernelIntegrand y) (-R) (-T) T)
        atTop
        (nhds
          (-(1 / (2 * Real.pi * Complex.I) : Complex) *
              leftHorizontalIntegral y c (-T) +
            (1 / (2 * Real.pi * Complex.I) : Complex) *
              leftHorizontalIntegral y c T)) := by
      simpa using hCombined
    apply hCombined'.congr'
    filter_upwards [hFinite] with R hR
    exact hR.symm
  exact tendsto_nhds_unique tendsto_const_nhds hConst

end BombieriVinogradov.SiegelWalfisz
