import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ComplexZeroErrorBudget
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.DoubledHeightLog
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.IndexedZeroKernel
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LogDerivativePositivity
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.SelectableZeroLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.SquareLogDerivativeBound

/-!
# Core inequality for a primitive complex-character zero

This module combines Strombergsson Lemma 11.2 with equations (401)--(405).
For one multiplicity-indexed zero, it proves the pre-optimization inequality
that drives the complex-character zero-free region.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_complexZero_core_inequality :
    exists K : Real, 0 < K ∧
      forall {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N},
        chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 ≠ 1 ->
          forall (p : SymmetricCompletedZeroIndex chi) {sigma t : Real},
            1 < sigma -> sigma ≤ 2 ->
              (Complex.Hadamard.divisorZeroIndex₀_val p).im = t ->
                4 * (sigma -
                    (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ ≤
                  3 * (sigma - 1)⁻¹ +
                    K * (Real.log N + Real.log (|t| + 2)) := by
  obtain ⟨C, hCNonneg, hPrincipal⟩ :=
    exists_neg_re_logDeriv_principal_le_inv_add
  obtain ⟨A, hAPos, hSelected⟩ :=
    exists_primitive_selectableZero_logDeriv_bound
  obtain ⟨B, hBPos, hSquare⟩ := exists_square_logDeriv_bound
  let K := 3 * C / Real.log 3 + 4 * A + 2 * B
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hKPos : 0 < K := by
    dsimp [K]
    positivity
  refine Exists.intro K (And.intro hKPos ?_)
  intro N _hN chi hchi hPrimitive hchiSquare p sigma t hsigma hsigmaUpper him
  have hNLower :=
    BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hsOneLower :
      1 < ((sigma : Complex) + Complex.I * t).re := by
    simpa [Complex.mul_re] using hsigma
  have hsOneUpper :
      ((sigma : Complex) + Complex.I * t).re ≤ 2 := by
    simpa [Complex.mul_re] using hsigmaUpper
  have hsTwoLower :
      1 < ((sigma : Complex) + 2 * Complex.I * t).re := by
    simpa [Complex.mul_re] using hsigma
  have hsTwoUpper :
      ((sigma : Complex) + 2 * Complex.I * t).re ≤ 2 := by
    simpa [Complex.mul_re] using hsigmaUpper
  have hPrincipalAt := hPrincipal (N := N) hsigma hsigmaUpper
  have hPrincipalLog :
      -(logDeriv (1 : DirichletCharacter Complex N).LFunction sigma).re ≤
        (sigma - 1)⁻¹ + C := by
    simpa [logDeriv_apply, neg_div] using hPrincipalAt
  have hSelectedRaw := hSelected hNLower hchi hPrimitive
    hsOneLower hsOneUpper (Set.singleton p)
  have hSingleton :
      (∑' q : (Set.singleton p : Set (SymmetricCompletedZeroIndex chi)),
        (1 / (((sigma : Complex) + Complex.I * t) -
          Complex.Hadamard.divisorZeroIndex₀_val q.1)).re) =
        (1 / (((sigma : Complex) + Complex.I * t) -
          Complex.Hadamard.divisorZeroIndex₀_val p)).re := by
    let q0 : (Set.singleton p : Set (SymmetricCompletedZeroIndex chi)) :=
      ⟨p, Set.mem_singleton p⟩
    calc
      (∑' q : (Set.singleton p : Set (SymmetricCompletedZeroIndex chi)),
          (1 / (((sigma : Complex) + Complex.I * t) -
            Complex.Hadamard.divisorZeroIndex₀_val q.1)).re) =
          (1 / (((sigma : Complex) + Complex.I * t) -
            Complex.Hadamard.divisorZeroIndex₀_val q0.1)).re := by
        apply tsum_eq_single q0
        intro q hq
        have hqp : q = q0 := by
          apply Subtype.ext
          change q.val = p
          exact Set.mem_singleton_iff.mp q.property
        exact (hq hqp).elim
      _ = (1 / (((sigma : Complex) + Complex.I * t) -
          Complex.Hadamard.divisorZeroIndex₀_val p)).re := by
        rfl
  rw [hSingleton,
    indexedZeroKernel_re hchi hPrimitive p hsigma him] at hSelectedRaw
  have hSelectedAt :
      -(logDeriv chi.LFunction
        ((sigma : Complex) + Complex.I * t)).re ≤
          -(sigma -
            (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ +
            A * (Real.log N + Real.log (|t| + 2)) := by
    simpa [Complex.mul_im] using hSelectedRaw
  have hSquareRaw := hSquare chi hchiSquare hsTwoLower hsTwoUpper
  have hSquareHeight := log_square_point_height_le sigma t
  have hSquareAt :
      -(logDeriv (chi ^ 2).LFunction
        ((sigma : Complex) + 2 * Complex.I * t)).re ≤
          B * (Real.log N + 2 * Real.log (|t| + 2)) :=
    hSquareRaw.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl hSquareHeight) hBPos.le)
  have hPositivityRaw := logDerivative_combination_nonneg chi hsigma t
  have hPositivity :
      0 ≤
        3 * (-(logDeriv (1 : DirichletCharacter Complex N).LFunction sigma).re) +
        4 * (-(logDeriv chi.LFunction
          ((sigma : Complex) + Complex.I * t)).re) +
        (-(logDeriv (chi ^ 2).LFunction
          ((sigma : Complex) + 2 * Complex.I * t)).re) := by
    simpa [logDeriv_apply, neg_div] using hPositivityRaw
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogHeightNonneg : 0 ≤ Real.log (|t| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg t]
  have hBudget := complexZero_error_budget
    (C := C) (A := A) (B := B)
    (x := Real.log N) (y := Real.log (|t| + 2))
    hCNonneg hBPos.le hLogNLower hLogHeightNonneg
  have hRaw :
      4 * (sigma -
          (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ ≤
        3 * (sigma - 1)⁻¹ +
          (3 * C + 4 * A *
            (Real.log N + Real.log (|t| + 2)) +
            B * (Real.log N + 2 * Real.log (|t| + 2))) := by
    nlinarith
  calc
    4 * (sigma -
        (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ ≤
      3 * (sigma - 1)⁻¹ +
        (3 * C + 4 * A *
          (Real.log N + Real.log (|t| + 2)) +
          B * (Real.log N + 2 * Real.log (|t| + 2))) := hRaw
    _ ≤ 3 * (sigma - 1)⁻¹ +
        K * (Real.log N + Real.log (|t| + 2)) := by
      simpa [K] using add_le_add_left hBudget (3 * (sigma - 1)⁻¹)

end BombieriVinogradov.SiegelWalfisz
