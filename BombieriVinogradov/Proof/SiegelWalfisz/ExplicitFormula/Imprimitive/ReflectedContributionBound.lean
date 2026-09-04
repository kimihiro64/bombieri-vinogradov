import BombieriVinogradov.Helpers.ComplexAnalysis.ReciprocalRealGap
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ComplexDifferenceQuotient
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ExceptionalGap
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reflected contribution from the larger primitive exceptional window

Split the numerator before estimating: the reciprocal costs log(N)/c,
while the difference quotient costs the quarter-power logarithmic error.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem norm_primitiveExceptional_reflectedContribution_le
    {c : Real} (hc : 0 < c) {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) [NeZero chi.conductor]
    (hchi : Ne chi 1)
    (hData : ExplicitFormulaZeroFreeData c chi.primitiveCharacter)
    (hNone : IsExceptionalZeroChoice c chi none)
    {beta : Complex} (hExceptional : IsExceptionalZero c chi.primitiveCharacter beta)
    {x : Real} (hx : 1 <= x) :
    norm ((x : Complex) ^ (1 - beta) / (1 - beta)) <=
      Real.log N / c + x ^ (1 / 4 : Real) * Real.log x := by
  have hN : 3 <= N :=
    BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hNReal : (3 : Real) <= (N : Real) := Nat.cast_le.mpr hN
  have hLogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hGap : c / Real.log N <= (1 - beta).re := by
    change c / Real.log N <= 1 - beta.re
    exact primitiveExceptional_gap_of_ambient_none chi hchi hNone hExceptional
  have hReciprocal : norm ((1 : Complex) / (1 - beta)) <= Real.log N / c :=
    BombieriVinogradov.ComplexAnalysis.norm_one_div_le_scale_div_of_re_gap
      hc hLogN hGap
  have hFacts := hData.exceptional beta hExceptional
  have hDifference :
      norm (((x : Complex) ^ (1 - beta) - 1) / (1 - beta)) <=
        x ^ (1 / 4 : Real) * Real.log x :=
    norm_reflectedCpowDifferenceQuotient_le
      hx hExceptional.2.1 hFacts.re_lower hExceptional.2.2.2.1
  have hIdentity :
      (x : Complex) ^ (1 - beta) / (1 - beta) =
        (1 : Complex) / (1 - beta) +
          ((x : Complex) ^ (1 - beta) - 1) / (1 - beta) := by
    ring
  rw [hIdentity]
  exact norm_add_le_of_le hReciprocal hDifference

end BombieriVinogradov.SiegelWalfisz
