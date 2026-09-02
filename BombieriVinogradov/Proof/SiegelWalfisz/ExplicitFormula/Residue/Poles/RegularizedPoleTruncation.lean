import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.InteriorGeometry
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.CriticalStripZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.RegularizedPoleCriticalStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.RegularizedPoleZero
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues

/-!
# Retained values of regularized contour poles

This module places every retained nonzero regularized pole inside the
deduplicated finite critical-zero value set.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Every retained nonzero regularized pole in an admissible contour is one of
the retained critical-zero values. -/
theorem mem_retainedCriticalZeroValues_of_regularized_pole
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (x : Nat) (hx : 0 < x) (U c T : Real)
    (hU : U < 1) (hT : 0 < T) (hRe : -U <= c)
    (exceptional : Option Complex) {rho : Complex} (hrho : Ne rho 0)
    (hRetained : IsRetainedZero exceptional rho)
    (hrhoRect : Membership.mem
      (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T)) rho)
    (hrhoBorder : Not (Membership.mem
      (RectangleBorder (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T)) rho))
    (hpole : meromorphicOrderAt
      (regularizedExplicitFormulaIntegrand chi x) rho < 0) :
    Membership.mem (retainedCriticalZeroValues chi T exceptional) rho := by
  have hGeometry :=
    neg_one_lt_re_and_abs_im_lt_of_mem_explicitFormulaContour
      U c T hU hT hRe hrhoRect hrhoBorder
  have hStrip :=
    re_mem_Ioo_of_regularizedExplicitFormulaIntegrand_pole
      hchi hPrimitive x hx hrho hGeometry.1 hpole
  have hZero :=
    LFunction_eq_zero_of_regularizedExplicitFormulaIntegrand_pole
      hchi x hx hrho hpole
  have hIndex :=
    exists_mem_criticalStripZeroTruncation_of_LFunction_eq_zero
      hchi hPrimitive hStrip.1 hStrip.2 hGeometry.2 hZero
  let p := hIndex.choose
  have hp := hIndex.choose_spec
  unfold retainedCriticalZeroValues
  apply Finset.mem_image.mpr
  apply Exists.intro p
  exact And.intro
    (by
      rw [mem_retainedCriticalZeroIndices_iff]
      rw [hp.2]
      exact And.intro hp.1 hRetained)
    hp.2

end BombieriVinogradov.SiegelWalfisz
