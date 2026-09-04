import BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.SetNotation

/-!
# Maximal globally centered Mangoldt discrepancy

Take the supremum over reduced residue classes and all natural endpoints
through the real cutoff, then sum over positive moduli. Endpoint zero is included.
-/

set_option autoImplicit false

namespace BombieriVinogradov.WeightedBombieriVinogradov

/-- The maximum centered weighted discrepancy over reduced classes and endpoints. -/
noncomputable def maximalWeightedDiscrepancy (X : Real) (q : Nat) : Real :=
  iSup (fun a : Units (ZMod q) => iSup (fun y : Fin (Nat.floor X + 1) =>
    abs (psiProgression y.val q (a : ZMod q) - psiGlobal y.val / (q.totient : Real))))

/-- The averaged maximal weighted discrepancy over the positive moduli up to Q. -/
noncomputable def averageWeightedDiscrepancy (X : Real) (Q : Nat) : Real :=
  Finset.sum (Finset.Icc 1 Q) (maximalWeightedDiscrepancy X)

end BombieriVinogradov.WeightedBombieriVinogradov
