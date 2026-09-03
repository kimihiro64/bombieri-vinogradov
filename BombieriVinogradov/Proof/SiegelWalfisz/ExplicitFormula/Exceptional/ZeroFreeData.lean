import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFacts
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Zero-free data used by the primitive explicit formula

One constant controls retained zeros, uniqueness of exceptional real zeros,
and all facts required of a selected exceptional zero.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

structure ExplicitFormulaZeroFreeData (c : Real)
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) : Prop where
  regularGap : forall s : Complex,
    0 < s.re -> chi.LFunction s = 0 ->
      Or (Ne (chi ^ 2) 1) (Ne s.im 0) ->
        c / (Real.log N + Real.log (abs s.im + 2)) <= 1 - s.re
  realUnique : forall s t : Complex,
    0 < s.re -> 0 < t.re ->
      chi.LFunction s = 0 -> chi.LFunction t = 0 ->
        s.im = 0 -> t.im = 0 ->
          1 - s.re <= c / Real.log N ->
            1 - t.re <= c / Real.log N -> s = t
  exceptional : forall beta : Complex,
    IsExceptionalZero c chi beta -> ExceptionalZeroFacts chi beta

end BombieriVinogradov.SiegelWalfisz
