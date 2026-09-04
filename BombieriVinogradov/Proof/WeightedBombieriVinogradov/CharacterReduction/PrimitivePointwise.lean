import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorSumReindex
import BombieriVinogradov.Helpers.DirichletCharacter.NonprincipalCard
import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveMangoldtBound
import BombieriVinogradov.Helpers.RealAnalysis.FiniteAverageError
import BombieriVinogradov.Proof.WeightedBombieriVinogradov.CharacterReduction.Pointwise
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.Divisors

/-!
# Pointwise reduction to primitive conductors

After averaging, the principal and imprimitive corrections combine
into one logarithmic term. Primitive characters are counted exactly once.
-/
set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem abs_psiProgression_sub_psiGlobal_div_totient_le_primitive
    {N x : Nat} [NeZero N] (a : Units (ZMod N)) (hx : 0 < x) :
    abs (psiProgression x N (a : ZMod N) - psiGlobal x / (N.totient : Real)) <=
      Finset.sum N.divisors (fun d =>
        Finset.sum ((LargeSieve.primitiveCharacters d).erase 1)
          (fun chi => norm (VaughanMeanValue.psiCharacterSum x d chi))) / (N.totient : Real) +
      Real.log N * Real.log x / Real.log (2 : Real) := by
  have hCard :
      ((Finset.univ.erase (1 : _root_.DirichletCharacter Complex N)).card : Real) + 1 =
        (N.totient : Real) := by
    have hCast := congrArg (fun m : Nat => (m : Real))
      (DirichletCharacter.card_nonprincipal_add_one_eq_totient (N := N))
    simpa only [Nat.cast_add, Nat.cast_one] using hCast
  have hTotient : (0 : Real) < (N.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos N))
  have hAverage := RealAnalysis.sum_div_add_error_div_le_sum_div_add_error
    (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
    (fun chi => norm (VaughanMeanValue.psiCharacterSum x N chi))
    (fun chi => norm (VaughanMeanValue.psiCharacterSum x chi.conductor chi.primitiveCharacter))
    hTotient hCard
    (fun chi _ => VaughanMeanValue.norm_psiCharacterSum_le_primitive_add_log_mul_log chi hx)
  simp only [div_div, mul_comm (Real.log (2 : Real)) (N.totient : Real)] at hAverage
  have hCombined := (abs_psiProgression_sub_psiGlobal_div_totient_le a hx).trans hAverage
  rw [DirichletCharacter.sum_nonprincipal_eq_sum_primitive_conductors (N := N)
    (fun d chi => norm (VaughanMeanValue.psiCharacterSum x d chi))] at hCombined
  exact hCombined

end BombieriVinogradov.WeightedBombieriVinogradov
