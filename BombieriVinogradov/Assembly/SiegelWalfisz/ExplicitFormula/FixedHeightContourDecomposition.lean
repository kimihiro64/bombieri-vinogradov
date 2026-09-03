import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.OptimizedContourIdentity
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.OptimizedResidueDecomposition
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.BoundaryDecomposition

/-!
# Fixed-height centered contour decomposition

This module substitutes the optimized residue and three-segment boundary
decompositions into the centered contour identity at one fixed height.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

theorem centeredExplicitFormulaVerticalIntegral_eq_decomposed_optimized
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
    centeredExplicitFormulaVerticalIntegral chi x
        (optimizedPerronLine x) T =
      (-(lFunctionOriginMultiplicity chi : Complex) *
          Complex.log (x : Complex) +
        (-centeredTruncatedCriticalZeroSum chi x T exceptional +
          centeredExceptionalResidueSum chi x exceptional)) +
        (centeredExplicitFormulaBottomBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) T +
          centeredExplicitFormulaLeftBoundaryIntegral chi x
            ((1 : Real) / 2) T +
          centeredExplicitFormulaTopBoundaryIntegral chi x
            ((1 : Real) / 2) (optimizedPerronLine x) T) := by
  rw [centeredExplicitFormulaVerticalIntegral_eq_residue_add_boundary_optimized
    hchi hPrimitive hx hT hTop hBottom]
  rw [centeredRegularizedContourResidueSum_eq_decomposed_optimized
    hchi hPrimitive hx hT c0 exceptional hChoice hTop hBottom]
  rw [centeredBrokenBoundaryIntegral_eq_segments]

end BombieriVinogradov.SiegelWalfisz
