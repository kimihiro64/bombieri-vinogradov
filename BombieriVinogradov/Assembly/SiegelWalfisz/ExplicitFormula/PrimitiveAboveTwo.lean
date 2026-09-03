import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.PrimitiveUncenteringBound
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RequestedCutoffResidualSourceScale
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.RetainedUnitSumSourceScale
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.SourceScale.LowerBound
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity

/-!
# The uncentered primitive explicit formula

Both positive constants are selected before every modulus, character and
cutoff. The uniform zero-free data are retained for the endpoint argument.
The natural endpoint x=2 and imprimitive transfer are not asserted here.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitiveExplicitFormula_above_two :
    exists c : Real, And (0 < c)
      (And (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        3 <= N -> Ne chi 1 -> ExplicitFormulaZeroFreeData c chi)
      (exists C : Real, And (0 < C)
        (forall {N : Nat} [NeZero N], 3 <= N ->
          forall {chi : DirichletCharacter Complex N},
            Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {x : Nat}, 2 < x ->
              forall {T : Real}, 2 <= T -> T <= x ->
                forall (exceptional : Option Complex),
                  IsExceptionalZeroChoice c chi exceptional ->
                    norm (characterChebyshevSum x chi +
                      truncatedCriticalZeroSum chi x T exceptional +
                      exceptionalZeroContribution x exceptional) <=
                    C * explicitFormulaRemainderMajorant N x T))) := by
  choose c hc hZeroFree using exists_explicitFormulaZeroFreeData
  choose A hA hCentered using
    exists_norm_centeredExplicitFormula_requestedCutoff_le_sourceScale
  choose B hB hUnit using
    exists_norm_truncatedCriticalZeroSum_one_le_sourceScale hc
  refine Exists.intro c (And.intro hc (And.intro hZeroFree
    (Exists.intro (A + B + 4) (And.intro (by positivity) ?_))))
  intro N inst hN chi hchi hPrimitive x hx T hT hTx exceptional hChoice
  have hData := hZeroFree chi hN hchi
  have hCenteredBound := hCentered hN hchi hPrimitive hx hT hTx hChoice
  have hUnitBound := hUnit hN hchi hPrimitive
    hData.regularGap hData.realUnique exceptional hChoice hx hT hTx
  exact primitiveExplicitFormula_le_of_centered_and_unit_bounds
    hN hchi hPrimitive hx hT hTx hA.le hB.le hData exceptional hChoice
    (one_le_explicitFormula_primaryScale hN hx hT hTx)
    hCenteredBound hUnitBound

end BombieriVinogradov.SiegelWalfisz
