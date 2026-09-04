import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite weighted prime-counting sums

The progression sum and the global sum use the same inclusive natural
endpoint. Their difference will be centered at the global sum.
-/
set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The global finite von Mangoldt sum through the natural endpoint. -/
noncomputable def psiGlobal (x : Nat) : Real :=
  Finset.sum (Finset.Icc 1 x) ArithmeticFunction.vonMangoldt

/-- The von Mangoldt sum in one residue class through the natural endpoint. -/
noncomputable def psiProgression (x N : Nat) (a : ZMod N) : Real :=
  Finset.sum (Finset.Icc 1 x)
    (fun n => if a = (n : ZMod N) then ArithmeticFunction.vonMangoldt n else 0)

end BombieriVinogradov.WeightedBombieriVinogradov
