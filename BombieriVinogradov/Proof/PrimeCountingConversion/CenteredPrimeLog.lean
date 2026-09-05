import BombieriVinogradov.Proof.PrimeCountingConversion.Definitions
import BombieriVinogradov.Proof.PrimeCountingConversion.PrimeLogGlobal
import BombieriVinogradov.Proof.PrimeCountingConversion.PrimeLogProgression
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Centered prime-log weights

The separately verified global and progression identities are combined here.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- Centered prime-log coefficients recover the centered unweighted count. -/
theorem sum_centeredTheta_div_log {N q : Nat} (a : ZMod q) :
    Finset.sum (Finset.Icc 2 N)
      (fun n => centeredThetaCoefficient n q a / Real.log (n : Real)) =
      (primeProgressionNat N q a : Real) -
        (primeGlobalNat N : Real) / (q.totient : Real) := by
  unfold centeredThetaCoefficient
  calc
    Finset.sum (Finset.Icc 2 N) (fun n =>
        ((if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0) -
          (if n.Prime then Real.log (n : Real) else 0) / (q.totient : Real)) /
            Real.log (n : Real)) =
      Finset.sum (Finset.Icc 2 N) (fun n =>
        (if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0) /
          Real.log (n : Real) -
        ((if n.Prime then Real.log (n : Real) else 0) / Real.log (n : Real)) /
          (q.totient : Real)) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = Finset.sum (Finset.Icc 2 N) (fun n =>
        (if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0) /
          Real.log (n : Real)) -
      Finset.sum (Finset.Icc 2 N) (fun n =>
        ((if n.Prime then Real.log (n : Real) else 0) / Real.log (n : Real)) /
          (q.totient : Real)) := by rw [Finset.sum_sub_distrib]
    _ = (primeProgressionNat N q a : Real) -
        (primeGlobalNat N : Real) / (q.totient : Real) := by
      rw [show Finset.sum (Finset.Icc 2 N) (fun n =>
        ((if n.Prime then Real.log (n : Real) else 0) / Real.log (n : Real)) /
          (q.totient : Real)) =
        Finset.sum (Finset.Icc 2 N) (fun n =>
          (if n.Prime then Real.log (n : Real) else 0) / Real.log (n : Real)) /
            (q.totient : Real) from by rw [Finset.sum_div],
        sum_progressionPrimeLog_div_log a, sum_globalPrimeLog_div_log N]

end BombieriVinogradov.PrimeCountingConversion
