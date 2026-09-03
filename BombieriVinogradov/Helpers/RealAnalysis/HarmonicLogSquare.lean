import BombieriVinogradov.Helpers.RealAnalysis.HarmonicLogFreeze
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quadratic bound for a logarithmic harmonic sum

This module combines endpoint freezing with harmonic-number growth and
absorbs the harmonic factor into the same endpoint logarithmic scale.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.RealAnalysis

theorem sum_log_add_div_Ico_le_sq
    {L : Real} (hL : 1 <= L) (K : Nat) :
    Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
        (L + Real.log ((k : Real) + 2)) / (k : Real)) <=
      (L + Real.log ((K : Real) + 2)) ^ 2 := by
  have hLNonneg : 0 <= L := le_trans (by norm_num) hL
  have hFreeze := sum_log_add_div_Ico_le_mul_harmonic hLNonneg K
  rcases eq_or_ne K 0 with hZero | hNonzero
  case inl =>
    subst K
    simpa using sq_nonneg (L + Real.log (2 : Real))
  case inr =>
    have hKPosNat : 0 < K := Nat.pos_of_ne_zero hNonzero
    have hKPos : 0 < (K : Real) := (Nat.cast_pos).2 hKPosNat
    have hKLe : (K : Real) <= (K : Real) + 2 := by linarith
    have hLogKLe :
        Real.log (K : Real) <= Real.log ((K : Real) + 2) :=
      Real.log_le_log hKPos hKLe
    have hKNonneg : 0 <= (K : Real) := le_of_lt hKPos
    have hLogEndpointNonneg :
        0 <= Real.log ((K : Real) + 2) :=
      Real.log_nonneg (by linarith)
    have hScaleNonneg :
        0 <= L + Real.log ((K : Real) + 2) := by linarith
    have hHarmonic :
        (harmonic K : Real) <= 1 + Real.log (K : Real) :=
      harmonic_le_one_add_log K
    have hHarmonicLe :
        (harmonic K : Real) <= L + Real.log ((K : Real) + 2) := by
      linarith
    calc
      Finset.sum (Finset.Ico 1 K) (fun k : Nat =>
          (L + Real.log ((k : Real) + 2)) / (k : Real)) <=
        (L + Real.log ((K : Real) + 2)) * (harmonic K : Real) := hFreeze
      _ <= (L + Real.log ((K : Real) + 2)) *
          (L + Real.log ((K : Real) + 2)) :=
        mul_le_mul_of_nonneg_left hHarmonicLe hScaleNonneg
      _ = (L + Real.log ((K : Real) + 2)) ^ 2 := by ring

end BombieriVinogradov.RealAnalysis
