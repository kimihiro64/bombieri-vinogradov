import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLeftLineNonvanishing
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Linarith
import PrimeNumberTheoremAnd.Rectangle

/-!
# L-function nonvanishing on the optimized contour border

This module combines supplied signed horizontal-line data with the established
left-line and right-half-plane results on all four rectangle sides.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem LFunction_ne_zero_on_optimizedExplicitFormulaContourBorder
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {x : Nat} (hx : 2 < x) {T : Real}
    (hTop : forall {s : Complex},
      s.im = T -> -(1 : Real) / 2 <= s.re -> s.re <= 2 ->
        Ne (chi.LFunction s) 0)
    (hBottom : forall {s : Complex},
      s.im = -T -> -(1 : Real) / 2 <= s.re -> s.re <= 2 ->
        Ne (chi.LFunction s) 0)
    (p : Complex)
    (hp : (RectangleBorder
      (explicitFormulaContourLowerLeft ((1 : Real) / 2) T)
      (explicitFormulaContourUpperRight (optimizedPerronLine x) T)) p) :
    Ne (chi.LFunction p) 0 := by
  have hLineLower :
      -((1 : Real) / 2) <= optimizedPerronLine x := by
    linarith [optimizedPerronLine_gt_one hx]
  have hLineUpper : optimizedPerronLine x <= 2 :=
    optimizedPerronLine_le_two hx
  simp only [RectangleBorder, explicitFormulaContourLowerLeft,
    explicitFormulaContourUpperRight] at hp
  exact Or.elim hp
    (fun hThree => Or.elim hThree
      (fun hTwo => Or.elim hTwo
        (fun hBottomCase => by
          have hReMem := hBottomCase.1
          rw [Set.mem_preimage, Set.uIcc_of_le hLineLower] at hReMem
          have hImMem := hBottomCase.2
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hImMem
          have hIm : p.im = -T := by
            exact hImMem
          exact hBottom hIm (by simpa only [neg_div] using hReMem.1)
            (hReMem.2.trans hLineUpper))
        (fun hLeftCase => by
          have hReMem := hLeftCase.1
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hReMem
          have hRe : p.re = -(1 : Real) / 2 := by
            simpa only [neg_div] using hReMem
          exact
            LFunction_ne_zero_of_re_eq_neg_one_half
              hchi hPrimitive hRe))
      (fun hTopCase => by
        have hReMem := hTopCase.1
        rw [Set.mem_preimage, Set.uIcc_of_le hLineLower] at hReMem
        have hImMem := hTopCase.2
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hImMem
        have hIm : p.im = T := by
          exact hImMem
        exact hTop hIm (by simpa only [neg_div] using hReMem.1)
          (hReMem.2.trans hLineUpper)))
    (fun hRightCase => by
      have hReMem := hRightCase.1
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hReMem
      have hRe : p.re = optimizedPerronLine x := by
        exact hReMem
      exact
        chi.LFunction_ne_zero_of_one_le_re (Or.inl hchi)
          (by
            rw [hRe]
            exact (optimizedPerronLine_gt_one hx).le))

end BombieriVinogradov.SiegelWalfisz
