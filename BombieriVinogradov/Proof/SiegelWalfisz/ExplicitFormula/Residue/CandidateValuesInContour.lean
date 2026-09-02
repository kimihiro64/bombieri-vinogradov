import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.CandidateValues
import PrimeNumberTheoremAnd.Rectangle

/-!
# Residue candidates inside the explicit-formula contour

This module proves the geometric inclusion of every finite residue candidate
in an admissible closed contour rectangle.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Every residue candidate lies in the closed explicit-formula contour when
the rectangle contains the critical strip and has positive height. -/
theorem mem_explicitFormulaContour_of_mem_residueCandidateValues
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    {c0 U c T : Real} {exceptional : Option Complex}
    (hU : 0 <= U) (hc : 1 <= c) (hT : 0 < T)
    (hChoice : IsExceptionalZeroChoice c0 chi exceptional)
    {rho : Complex}
    (hrho : Membership.mem
      (explicitFormulaResidueCandidateValues chi T exceptional) rho) :
    Membership.mem
      (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
        (explicitFormulaContourUpperRight c T)) rho := by
  have hCornersRe :
      (explicitFormulaContourLowerLeft U T).re <=
        (explicitFormulaContourUpperRight c T).re := by
    simpa [explicitFormulaContourLowerLeft,
      explicitFormulaContourUpperRight] using
        (show -U <= c by linarith)
  have hCornersIm :
      (explicitFormulaContourLowerLeft U T).im <=
        (explicitFormulaContourUpperRight c T).im := by
    simpa [explicitFormulaContourLowerLeft,
      explicitFormulaContourUpperRight] using
        (show -T <= T by linarith)
  have hStrip : forall z : Complex,
      0 <= z.re -> z.re <= 1 -> abs z.im < T ->
      Membership.mem
        (Complex.Rectangle (explicitFormulaContourLowerLeft U T)
          (explicitFormulaContourUpperRight c T)) z := by
    intro z hzReNonneg hzReLe hzIm
    apply (mem_Rect hCornersRe hCornersIm z).mpr
    have hzImBounds := abs_lt.mp hzIm
    exact And.intro
      (by
        simpa [explicitFormulaContourLowerLeft] using
          (show -U <= z.re by linarith))
      (And.intro
        (by
          simpa [explicitFormulaContourUpperRight] using
            (show z.re <= c by linarith))
        (And.intro
          (by
            simpa [explicitFormulaContourLowerLeft] using hzImBounds.1.le)
          (by
            simpa [explicitFormulaContourUpperRight] using hzImBounds.2.le)))
  rw [mem_explicitFormulaResidueCandidateValues_iff] at hrho
  exact Or.elim hrho
    (fun hzero => by
      subst rho
      exact hStrip 0 (by norm_num) (by norm_num) (by simpa using hT))
    (fun hrest =>
      Or.elim hrest
        (fun hretained => by
          have hWitness := Finset.mem_image.mp hretained
          let p := hWitness.choose
          have hpRetained := hWitness.choose_spec.1
          have hpValue := hWitness.choose_spec.2
          have hpCritical :
              Membership.mem (criticalStripZeroTruncation chi T) p :=
            (mem_retainedCriticalZeroIndices_iff.mp hpRetained).1
          have hpStrip := mem_criticalStripZeroTruncation_iff.mp hpCritical
          rw [<- hpValue]
          exact hStrip _ hpStrip.1.le hpStrip.2.1.le hpStrip.2.2)
        (fun hexceptional => by
          cases exceptional with
          | none =>
            simp [exceptionalZeroValues] at hexceptional
          | some beta =>
            change IsExceptionalZero c0 chi beta at hChoice
            simp only [exceptionalZeroValues, Finset.mem_insert,
              Finset.mem_singleton] at hexceptional
            exact Or.elim hexceptional
              (fun hrhoBeta => by
                subst rho
                exact hStrip beta hChoice.2.2.1.le
                  hChoice.2.2.2.1.le
                  (by
                    rw [hChoice.2.1, abs_zero]
                    exact hT))
              (fun hrhoReflect => by
                subst rho
                exact hStrip (1 - beta)
                  (by
                    change 0 <= 1 - beta.re
                    linarith [hChoice.2.2.2.1])
                  (by
                    change 1 - beta.re <= 1
                    linarith [hChoice.2.2.1])
                  (by simpa [hChoice.2.1] using hT))))

end BombieriVinogradov.SiegelWalfisz
