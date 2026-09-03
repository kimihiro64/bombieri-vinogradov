import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.ResidueDecomposition
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.LFunctionNonvanishing
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.ZeroAvoidance
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.BoundaryDisjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Optimized centered residue decomposition

This module specializes the centered residue decomposition to the admissible
optimized rectangle at one fixed positive height.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem centeredRegularizedContourResidueSum_eq_decomposed_optimized
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {x : Nat} (hx : 2 < x) {T : Real} (hT : 0 < T)
    (c0 : Real) (exceptional : Option Complex)
    (hChoice : IsExceptionalZeroChoice c0 chi exceptional)
    (hTop : forall {s : Complex},
      s.im = T -> -(1 : Real) / 2 <= s.re -> s.re <= 2 ->
        Ne (chi.LFunction s) 0)
    (hBottom : forall {s : Complex},
      s.im = -T -> -(1 : Real) / 2 <= s.re -> s.re <= 2 ->
        Ne (chi.LFunction s) 0) :
    centeredRegularizedContourResidueSum chi x ((1 : Real) / 2)
        (optimizedPerronLine x) T =
      -(lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex) +
        (-centeredTruncatedCriticalZeroSum chi x T exceptional +
          centeredExceptionalResidueSum chi x exceptional) := by
  let z := explicitFormulaContourLowerLeft ((1 : Real) / 2) T
  let w := explicitFormulaContourUpperRight (optimizedPerronLine x) T
  have hZero : Not ((RectangleBorder z w) 0) := by
    simpa [z, w] using
      zero_not_mem_optimizedExplicitFormulaContourBorder hx hT
  have hBorderNonzero : forall p : Complex,
      (RectangleBorder z w) p -> Ne (chi.LFunction p) 0 := by
    intro p hp
    exact LFunction_ne_zero_on_optimizedExplicitFormulaContourBorder
      hchi hPrimitive hx hTop hBottom p (by simpa [z, w] using hp)
  have hxPos : 0 < x := Nat.zero_lt_of_lt hx
  have hPolesX : Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt (explicitFormulaIntegrand chi x) p < 0} :=
    disjoint_explicitFormulaIntegrand_poles_boundary_of_LFunction_ne_zero
      hchi x hxPos z w hZero hBorderNonzero
  have hPolesOne : Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt (explicitFormulaIntegrand chi 1) p < 0} :=
    disjoint_explicitFormulaIntegrand_poles_boundary_of_LFunction_ne_zero
      hchi 1 (by norm_num) z w hZero hBorderNonzero
  have hLine : 1 <= optimizedPerronLine x :=
    (optimizedPerronLine_gt_one hx).le
  simpa [z, w] using
    centeredRegularizedContourResidueSum_eq_decomposed
      hchi hPrimitive x hxPos c0 ((1 : Real) / 2)
        (optimizedPerronLine x) T (by norm_num) (by norm_num)
        hLine hT exceptional hChoice hPolesX hPolesOne hZero

end BombieriVinogradov.SiegelWalfisz
