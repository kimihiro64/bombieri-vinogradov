import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.CriticalStripZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Cutoff.RetainedIndexReflection
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.RetainedZeroRightGap
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.RetainedZeroValues
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroDivisorReflection
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroIndex
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Retained-zero gap from zero
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem retainedCriticalZero_re_gap
    {c : Real} (hc : 0 < c)
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hN : 3 <= N) (hchi : Ne chi 1)
    (hPrimitive : DirichletCharacter.IsPrimitive chi)
    (hRegularGap : forall s : Complex,
      0 < s.re -> chi.LFunction s = 0 ->
        Or (Ne (chi ^ 2) 1) (Ne s.im 0) ->
          c / (Real.log N + Real.log (abs s.im + 2)) <=
            1 - s.re)
    (hRealUnique : forall s t : Complex,
      0 < s.re -> 0 < t.re ->
        chi.LFunction s = 0 -> chi.LFunction t = 0 ->
          s.im = 0 -> t.im = 0 ->
            1 - s.re <= c / Real.log N ->
              1 - t.re <= c / Real.log N -> s = t)
    {exceptional : Option Complex}
    (hChoice : IsExceptionalZeroChoice c chi exceptional)
    {T : Real} {p : SymmetricCompletedZeroIndex chi}
    (hp : (retainedCriticalZeroIndices chi T exceptional :
      Set (SymmetricCompletedZeroIndex chi)) p) :
    c / (Real.log N +
      Real.log (abs (symmetricCompletedZeroValue p).im + 2)) <=
        (symmetricCompletedZeroValue p).re := by
  let pReflected : SymmetricCompletedZeroIndex chi :=
    symmetricCompletedZeroReflection hchi hPrimitive p
  have hpReflected :
      (retainedCriticalZeroIndices chi T exceptional :
        Set (SymmetricCompletedZeroIndex chi)) pReflected := by
    dsimp [pReflected]
    exact symmetricCompletedZeroReflection_mem_retainedCriticalZeroIndices
      hchi hPrimitive hChoice hp
  have hpReflectedData :=
    (mem_retainedCriticalZeroIndices_iff
      (p := pReflected)).mp hpReflected
  have hpReflectedStrip :
      And (0 < (symmetricCompletedZeroValue pReflected).re)
        ((symmetricCompletedZeroValue pReflected).re < 1) := by
    have hRaw :=
      mem_criticalStripZeroTruncation_iff.mp hpReflectedData.1
    exact And.intro hRaw.1 hRaw.2.1
  have hpReflectedZero :
      chi.LFunction (symmetricCompletedZeroValue pReflected) = 0 := by
    simpa [symmetricCompletedZeroValue] using
      LFunction_eq_zero_of_mem_criticalStripZeroTruncation
        hchi hPrimitive hpReflectedData.1
  have hpReflectedRetained :
      IsRetainedZero exceptional
        (symmetricCompletedZeroValue pReflected) := by
    simpa [symmetricCompletedZeroValue] using hpReflectedData.2
  have hRight := retainedLFunctionZero_gap_from_one
    hc hN hRegularGap hRealUnique hChoice
      hpReflectedZero hpReflectedStrip.1 hpReflectedStrip.2
        hpReflectedRetained
  have hReflectedValue :
      symmetricCompletedZeroValue pReflected =
        1 - (starRingEnd Complex) (symmetricCompletedZeroValue p) := by
    dsimp [pReflected]
    exact symmetricCompletedZeroReflection_val hchi hPrimitive p
  simpa [hReflectedValue] using hRight

end BombieriVinogradov.SiegelWalfisz
