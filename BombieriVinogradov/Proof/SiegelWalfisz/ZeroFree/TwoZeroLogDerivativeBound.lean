import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionLogDerivativeLowerBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PairSubtypeTsum
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.SelectableZeroLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.TwoZeroErrorBudget
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Logarithmic-derivative bound retaining two indexed zeros

This module combines the crude lower logarithmic-derivative estimate with
Lemma 11.3 specialized to two distinct divisor indices.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_twoZero_logDerivative_bound :
    exists K : Real, 0 < K ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi ->
            forall (p q : SymmetricCompletedZeroIndex chi), p ≠ q ->
              forall {sigma : Real}, 1 < sigma -> sigma ≤ 2 ->
                (1 / ((sigma : Complex) -
                    Complex.Hadamard.divisorZeroIndex₀_val p)).re +
                  (1 / ((sigma : Complex) -
                    Complex.Hadamard.divisorZeroIndex₀_val q)).re ≤
                    (sigma - 1)⁻¹ + K * Real.log N := by
  obtain ⟨C, hCNonneg, hLower⟩ :=
    exists_neg_inv_sub_le_neg_re_logDeriv_LFunction
  obtain ⟨A, hAPos, hSelected⟩ :=
    exists_primitive_selectableZero_logDeriv_bound
  let K := A + (C + A * Real.log 2) / Real.log 3
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hConstantNonneg : 0 ≤ C + A * Real.log 2 := by positivity
  have hKPos : 0 < K := by
    dsimp [K]
    exact add_pos_of_pos_of_nonneg hAPos
      (div_nonneg hConstantNonneg hLogThree.le)
  refine Exists.intro K (And.intro hKPos ?_)
  intro N _hN hNLower chi hchi hPrimitive p q hpq sigma hsigma hsigmaUpper
  classical
  have hLowerAt := hLower chi hsigma hsigmaUpper
  have hSelectedAt := hSelected hNLower hchi hPrimitive
    (s := (sigma : Complex)) (by simpa) (by simpa)
    ({p, q} : Set (SymmetricCompletedZeroIndex chi))
  rw [tsum_pair_subtype p q hpq (fun r =>
    (1 / ((sigma : Complex) -
      Complex.Hadamard.divisorZeroIndex₀_val r)).re)] at hSelectedAt
  have hSelectedReal :
      -(logDeriv chi.LFunction sigma).re ≤
        -((1 / ((sigma : Complex) -
            Complex.Hadamard.divisorZeroIndex₀_val p)).re +
          (1 / ((sigma : Complex) -
            Complex.Hadamard.divisorZeroIndex₀_val q)).re) +
          A * (Real.log N + Real.log 2) := by
    simpa using hSelectedAt
  have hRaw :
      (1 / ((sigma : Complex) -
          Complex.Hadamard.divisorZeroIndex₀_val p)).re +
        (1 / ((sigma : Complex) -
          Complex.Hadamard.divisorZeroIndex₀_val q)).re ≤
        (sigma - 1)⁻¹ + (C + A * (Real.log N + Real.log 2)) := by
    linarith
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hBudget := twoZero_error_budget hCNonneg hAPos hLogNLower
  calc
    (1 / ((sigma : Complex) -
        Complex.Hadamard.divisorZeroIndex₀_val p)).re +
      (1 / ((sigma : Complex) -
        Complex.Hadamard.divisorZeroIndex₀_val q)).re ≤
      (sigma - 1)⁻¹ + (C + A * (Real.log N + Real.log 2)) := hRaw
    _ ≤ (sigma - 1)⁻¹ + K * Real.log N := by
      simpa [K] using add_le_add_left hBudget (sigma - 1)⁻¹

end BombieriVinogradov.SiegelWalfisz
