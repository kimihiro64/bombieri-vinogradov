import BombieriVinogradov.Proof.PrimeCountingConversion.CenteredCoefficientSums
import BombieriVinogradov.Proof.PrimeCountingConversion.CenteredPsiMax
import BombieriVinogradov.Proof.PrimeCountingConversion.GlobalPrimePowerError
import BombieriVinogradov.Proof.PrimeCountingConversion.PrimePowerError
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Centered theta prefix bounds

Each theta prefix differs from its psi prefix only by two nonnegative
higher-prime-power errors controlled at the common real endpoint.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- Centered theta prefixes are bounded by the psi maximum plus the prime-power error. -/
theorem abs_sum_centeredThetaCoefficient_le {X : Real} {q N : Nat}
    (a : Units (ZMod q)) (hX : 3 <= X) (hq : 1 <= q)
    (hN : 1 <= N) (hNX : N <= Nat.floor X) :
    abs (Finset.sum (Finset.Icc 1 N)
      (fun n => centeredThetaCoefficient n q (a : ZMod q))) <=
      WeightedBombieriVinogradov.maximalWeightedDiscrepancy X q +
        4 * Real.sqrt X * Real.log X := by
  have hXPos : 0 < X := by linarith
  have hNPos : (0 : Real) < (N : Real) := by
    have hNRaw : (((1 : Nat) : Real) <= (N : Real)) := Nat.cast_le.mpr hN
    have hNOne : (1 : Real) <= (N : Real) := by
      simpa only [Nat.cast_one] using hNRaw
    linarith
  have hNXCast : (N : Real) <= X := by
    have hFloorCast : (N : Real) <= (Nat.floor X : Real) := Nat.cast_le.mpr hNX
    exact hFloorCast.trans (Nat.floor_le hXPos.le)
  have hErrorScale :
      2 * Real.sqrt (N : Real) * Real.log (N : Real) <=
        2 * Real.sqrt X * Real.log X := by
    gcongr
  have hProgression := progression_primePower_error_bounds N q (a : ZMod q)
  have hProgressionX := (progression_primePower_error_le (a : ZMod q) hN).trans hErrorScale
  have hGlobal := global_primePower_error_bounds hN
  have hGlobalX := hGlobal.2.trans hErrorScale
  have hPhiNat : 1 <= q.totient :=
    Nat.totient_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
  have hPhiRaw : (((1 : Nat) : Real) <= (q.totient : Real)) := Nat.cast_le.mpr hPhiNat
  have hPhiOne : (1 : Real) <= (q.totient : Real) := by
    simpa only [Nat.cast_one] using hPhiRaw
  have hPhiPos : (0 : Real) < (q.totient : Real) := by linarith
  have hGlobalDiv :
      (WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N) /
          (q.totient : Real) <=
        2 * Real.sqrt X * Real.log X :=
    (div_le_self hGlobal.1 hPhiOne).trans hGlobalX
  have hPsi := abs_sum_centeredPsiCoefficient_le_maximal (X := X)
    (q := q) a hNX
  rw [sum_centeredThetaCoefficient]
  rw [sum_centeredPsiCoefficient] at hPsi
  have hRelation : thetaProgressionNat N q (a : ZMod q) -
      thetaGlobalNat N / (q.totient : Real) =
        (WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
          WeightedBombieriVinogradov.psiGlobal N / (q.totient : Real)) -
        (WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
          thetaProgressionNat N q (a : ZMod q)) +
        (WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N) /
          (q.totient : Real) := by ring
  rw [hRelation]
  have hAbs : abs ((WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
        WeightedBombieriVinogradov.psiGlobal N / (q.totient : Real)) -
      (WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
        thetaProgressionNat N q (a : ZMod q)) +
      (WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N) /
        (q.totient : Real)) <=
      abs (WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
        WeightedBombieriVinogradov.psiGlobal N / (q.totient : Real)) +
      (WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
        thetaProgressionNat N q (a : ZMod q)) +
      (WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N) /
        (q.totient : Real) := by
    calc
      _ <= abs ((WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
          WeightedBombieriVinogradov.psiGlobal N / (q.totient : Real)) -
        (WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
          thetaProgressionNat N q (a : ZMod q))) +
        abs ((WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N) /
          (q.totient : Real)) := abs_add_le _ _
      _ <= (abs (WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
          WeightedBombieriVinogradov.psiGlobal N / (q.totient : Real)) +
        abs (WeightedBombieriVinogradov.psiProgression N q (a : ZMod q) -
          thetaProgressionNat N q (a : ZMod q))) +
        abs ((WeightedBombieriVinogradov.psiGlobal N - thetaGlobalNat N) /
          (q.totient : Real)) := by
        exact add_le_add (abs_sub _ _) (le_refl _)
      _ = _ := by
        rw [abs_of_nonneg hProgression.1, abs_div, abs_of_nonneg hGlobal.1,
          abs_of_pos hPhiPos]
  linarith

end BombieriVinogradov.PrimeCountingConversion
