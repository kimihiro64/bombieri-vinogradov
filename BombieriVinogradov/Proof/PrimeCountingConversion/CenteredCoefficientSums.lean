import BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import BombieriVinogradov.Proof.PrimeCountingConversion.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Cumulative centered coefficient identities

The coefficient definitions recover exactly the centered psi and theta sums
on every inclusive natural prefix.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- Cumulative centered von Mangoldt coefficients are the centered psi discrepancy. -/
theorem sum_centeredPsiCoefficient (N q : Nat) (a : ZMod q) :
    Finset.sum (Finset.Icc 1 N) (fun n => centeredPsiCoefficient n q a) =
      WeightedBombieriVinogradov.psiProgression N q a -
        WeightedBombieriVinogradov.psiGlobal N / (q.totient : Real) := by
  unfold centeredPsiCoefficient WeightedBombieriVinogradov.psiProgression
    WeightedBombieriVinogradov.psiGlobal
  rw [Finset.sum_sub_distrib, Finset.sum_div]

/-- Cumulative centered prime-log coefficients are the centered theta discrepancy. -/
theorem sum_centeredThetaCoefficient (N q : Nat) (a : ZMod q) :
    Finset.sum (Finset.Icc 1 N) (fun n => centeredThetaCoefficient n q a) =
      thetaProgressionNat N q a - thetaGlobalNat N / (q.totient : Real) := by
  unfold centeredThetaCoefficient thetaProgressionNat thetaGlobalNat
  rw [Finset.sum_sub_distrib, Finset.sum_div]

/-- Both centered coefficient sequences vanish at one. -/
theorem centeredPsiCoefficient_one (q : Nat) (a : ZMod q) :
    centeredPsiCoefficient 1 q a = 0 := by
  simp [centeredPsiCoefficient]

/-- The centered theta coefficient also vanishes at one. -/
theorem centeredThetaCoefficient_one (q : Nat) (a : ZMod q) :
    centeredThetaCoefficient 1 q a = 0 := by
  simp [centeredThetaCoefficient]

end BombieriVinogradov.PrimeCountingConversion
