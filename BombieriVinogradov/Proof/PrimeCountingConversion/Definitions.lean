import BombieriVinogradov.Definitions.PrimeCounting
import BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite prime-conversion terms

Route-specific theta sums and unweighted prime counts use the same inclusive
natural endpoint and congruence convention as the public definitions.
-/

set_option autoImplicit false

namespace BombieriVinogradov.PrimeCountingConversion

/-- The global prime-logarithm sum through a natural endpoint. -/
noncomputable def thetaGlobalNat (N : Nat) : Real :=
  Finset.sum (Finset.Icc 1 N) (fun n => if n.Prime then Real.log (n : Real) else 0)

/-- The prime-logarithm sum in one residue class. -/
noncomputable def thetaProgressionNat (N q : Nat) (a : ZMod q) : Real :=
  Finset.sum (Finset.Icc 1 N)
    (fun n : Nat => if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0)

/-- The finite unweighted prime count in one residue class. -/
def primeProgressionNat (N q : Nat) (a : ZMod q) : Nat :=
  ((Finset.Icc 1 N).filter (fun n : Nat => And n.Prime ((n : ZMod q) = a))).card

/-- The finite global unweighted prime count. -/
def primeGlobalNat (N : Nat) : Nat :=
  ((Finset.Icc 1 N).filter Nat.Prime).card

/-- The centered von Mangoldt coefficient at one natural index. -/
noncomputable def centeredPsiCoefficient (n q : Nat) (a : ZMod q) : Real :=
  (if a = (n : ZMod q) then ArithmeticFunction.vonMangoldt n else 0) -
    ArithmeticFunction.vonMangoldt n / (q.totient : Real)

/-- The centered prime-logarithm coefficient at one natural index. -/
noncomputable def centeredThetaCoefficient (n q : Nat) (a : ZMod q) : Real :=
  (if And n.Prime ((n : ZMod q) = a) then Real.log (n : Real) else 0) -
    (if n.Prime then Real.log (n : Real) else 0) / (q.totient : Real)

end BombieriVinogradov.PrimeCountingConversion
