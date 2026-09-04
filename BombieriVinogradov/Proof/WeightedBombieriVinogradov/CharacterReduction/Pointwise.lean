import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Definitions.WeightedBombieriVinogradov
import BombieriVinogradov.Helpers.ComplexAnalysis.WeightedMangoldtCast
import BombieriVinogradov.Helpers.DirichletCharacter.FiniteResidueNormBound
import BombieriVinogradov.Helpers.DirichletCharacter.PrincipalMangoldtBound
import BombieriVinogradov.Helpers.RealAnalysis.ScaleQuotientBound
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Pointwise globally centered Mangoldt discrepancy

Finite character orthogonality leaves the nonprincipal twists and
a logarithmic principal Euler correction. No principal PNT is assumed.
-/
set_option autoImplicit false
open scoped Classical

namespace BombieriVinogradov.WeightedBombieriVinogradov

theorem abs_psiProgression_sub_psiGlobal_div_totient_le
    {N x : Nat} [NeZero N] (a : Units (ZMod N)) (hx : 0 < x) :
    abs (psiProgression x N (a : ZMod N) - psiGlobal x / (N.totient : Real)) <=
      Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
        (fun chi => norm (VaughanMeanValue.psiCharacterSum x N chi)) / (N.totient : Real) +
      Real.log N * Real.log x / ((N.totient : Real) * Real.log (2 : Real)) := by
  have hFinite := DirichletCharacter.norm_totient_mul_residue_sub_sum_le a
    (Finset.Icc 1 x) (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
  rw [<- ofReal_psiProgression, <- ofReal_psiGlobal] at hFinite
  change norm ((N.totient : Complex) * (psiProgression x N (a : ZMod N) : Complex) -
      (psiGlobal x : Complex)) <=
    Finset.sum (Finset.univ.erase (1 : _root_.DirichletCharacter Complex N))
      (fun chi => norm (VaughanMeanValue.psiCharacterSum x N chi)) +
    norm ((psiGlobal x : Complex) - VaughanMeanValue.psiCharacterSum x N
      (1 : _root_.DirichletCharacter Complex N)) at hFinite
  have hBound := hFinite.trans (add_le_add (le_refl _)
    (DirichletCharacter.norm_psiGlobal_sub_principal_le_log_mul_log hx))
  rw [<- Complex.ofReal_natCast N.totient, <- Complex.ofReal_mul,
    <- Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hBound
  have hTotient : (0 : Real) < (N.totient : Real) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos N))
  have hNormalized := RealAnalysis.abs_sub_div_le_of_abs_mul_sub_le hTotient hBound
  simpa only [add_div, div_div, mul_comm (Real.log (2 : Real)) (N.totient : Real)]
    using hNormalized

end BombieriVinogradov.WeightedBombieriVinogradov
