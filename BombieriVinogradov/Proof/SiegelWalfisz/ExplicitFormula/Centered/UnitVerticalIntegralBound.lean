import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.UnitHalfSum
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Centered.UnitPerronSumBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.SourceBound
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeriesRange
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Definitions
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Unit-point vertical-integral bound

This module controls the finite explicit-formula vertical integral at the
centering point x equals one throughout the Perron strip.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- One positive constant bounds the x equals one vertical integral by
one over the distance from the line to one. -/
theorem exists_norm_explicitFormulaVerticalIntegral_one_le_div :
    Exists fun C : Real => And (0 < C)
      (forall N : Nat, forall [NeZero N],
        forall chi : DirichletCharacter Complex N, forall c T : Real,
          1 < c -> c <= 3 -> 0 < T ->
            norm (explicitFormulaVerticalIntegral chi 1 c T) <=
              C / (c - 1)) := by
  have hExist := exists_vonMangoldtLSeriesNormSum_le_div_le_three
  let C : Real := hExist.choose
  have hSpec := hExist.choose_spec
  refine Exists.intro C (And.intro hSpec.1 ?_)
  intro N hNe chi c T hc hc3 hT
  have hPerron :=
    norm_explicitFormulaVerticalIntegral_sub_halfSum_le_source
      chi (x := 1) (Nat.zero_lt_succ 0) hc hT
  rw [characterChebyshevHalfSum_one] at hPerron
  simp only [sub_zero] at hPerron
  exact hPerron.trans
    ((tsum_sourcePerronErrorMajorantTerm_one_le_vonMangoldtSum hc hT).trans
      (hSpec.2 c hc hc3))

end BombieriVinogradov.SiegelWalfisz
