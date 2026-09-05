import BombieriVinogradov.Definitions.WeightedDiscrepancy
import BombieriVinogradov.Proof.PrimeCountingConversion.CenteredCoefficientSums
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Centered psi prefixes lie below the advertised maximum

Each natural prefix is embedded into the exact finite endpoint domain used
by maximalWeightedDiscrepancy.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- Every centered psi prefix is controlled by the maximal weighted discrepancy. -/
theorem abs_sum_centeredPsiCoefficient_le_maximal {X : Real} {q k : Nat}
    (a : Units (ZMod q)) (hk : k <= Nat.floor X) :
    abs (Finset.sum (Finset.Icc 1 k)
      (fun n => centeredPsiCoefficient n q (a : ZMod q))) <=
      WeightedBombieriVinogradov.maximalWeightedDiscrepancy X q := by
  let F : Units (ZMod q) -> Real := fun u =>
    iSup (fun y : Fin (Nat.floor X + 1) =>
      abs (WeightedBombieriVinogradov.psiProgression y.val q (u : ZMod q) -
        WeightedBombieriVinogradov.psiGlobal y.val / (q.totient : Real)))
  let H : Fin (Nat.floor X + 1) -> Real := fun y =>
    abs (WeightedBombieriVinogradov.psiProgression y.val q (a : ZMod q) -
      WeightedBombieriVinogradov.psiGlobal y.val / (q.totient : Real))
  let y : Fin (Nat.floor X + 1) :=
    { val := k, isLt := Nat.lt_succ_of_le hk }
  unfold WeightedBombieriVinogradov.maximalWeightedDiscrepancy
  change abs (Finset.sum (Finset.Icc 1 k)
    (fun n => centeredPsiCoefficient n q (a : ZMod q))) <= iSup F
  calc
    abs (Finset.sum (Finset.Icc 1 k)
      (fun n => centeredPsiCoefficient n q (a : ZMod q))) = H y := by
        dsimp [H, y]
        rw [sum_centeredPsiCoefficient]
    _ <= iSup H := le_ciSup (Set.finite_range H).bddAbove y
    _ = F a := by rfl
    _ <= iSup F := le_ciSup (Set.finite_range F).bddAbove a

end BombieriVinogradov.PrimeCountingConversion
