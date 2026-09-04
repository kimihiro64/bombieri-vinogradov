import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import BombieriVinogradov.Helpers.ArithmeticFunction.WeightedMangoldtZero
import BombieriVinogradov.Helpers.DirichletCharacter.MaximalChebyshev
import BombieriVinogradov.Helpers.RealAnalysis.LogarithmicEndpoint
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.CharacterReduction.PrimitivePointwise
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith

/-!
# Uniform primitive reduction over all smaller endpoints

The same primitive maximal sums control every natural endpoint
through the real cutoff. Endpoint zero is treated exactly.
-/
set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem abs_psiProgression_sub_psiGlobal_div_totient_le_maximal_primitive
    {X : Real} {N y : Nat} [NeZero N] (a : Units (ZMod N))
    (hX : 2 <= X) (hy : y <= Nat.floor X) :
    abs (psiProgression y N (a : ZMod N) - psiGlobal y / (N.totient : Real)) <=
      Finset.sum N.divisors (fun d =>
        Finset.sum ((LargeSieve.primitiveCharacters d).erase 1)
          (fun chi => VaughanMeanValue.maximalPsiNorm X chi)) / (N.totient : Real) +
      Real.log N * Real.log X / Real.log (2 : Real) := by
  have hX0 : 0 <= X := by linarith
  have hX1 : 1 <= X := by linarith
  have hTotient : (0 : Real) < (N.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos N))
  by_cases hZero : y = 0
  case pos =>
    subst y
    rw [psiProgression_zero, psiGlobal_zero, zero_div, sub_zero, abs_zero]
    exact add_nonneg (div_nonneg
      (Finset.sum_nonneg (fun d _ => Finset.sum_nonneg
        (fun chi _ => VaughanMeanValue.maximalPsiNorm_nonneg X chi))) hTotient.le)
      (RealAnalysis.log_mul_log_div_log_two_nonneg N hX1)
  case neg =>
    apply (abs_psiProgression_sub_psiGlobal_div_totient_le_primitive a
      (Nat.pos_of_ne_zero hZero)).trans
    exact add_le_add (div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun d _ => Finset.sum_le_sum
        (fun chi _ => VaughanMeanValue.norm_psiCharacterSum_le_maximalPsiNorm chi hy)))
      hTotient.le) (RealAnalysis.log_mul_log_nat_le_of_le_floor hX0
        (Nat.pos_of_ne_zero hZero) hy)

end BombieriVinogradov.WeightedBombieriVinogradov
