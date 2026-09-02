import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.ComplexZeroErrorBudget
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.DoubledHeightLog
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.DoubledHeightPoleKernel
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.IndexedZeroKernel
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LogDerivativePositivity
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalHighStripLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.PrincipalLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.SelectableZeroLogDerivativeBound

/-!
# Core high-height inequality for a primitive quadratic zero

This module combines Strombergsson Lemma 11.2 with the zeta pole retained in
the principal squared-character term. It is the formal counterpart of the
inequality immediately preceding equation (408).
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_quadratic_highHeight_core_inequality :
    exists K : Real, 0 < K ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 ->
            forall (p : SymmetricCompletedZeroIndex chi) {sigma t : Real},
              1 < sigma -> sigma ≤ 2 ->
                (Complex.Hadamard.divisorZeroIndex₀_val p).im = t ->
                  4 * (sigma -
                    (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ ≤
                    3 * (sigma - 1)⁻¹ +
                      (sigma - 1) /
                        ((sigma - 1) ^ 2 + 4 * t ^ 2) +
                      K * (Real.log N + Real.log (|t| + 2)) := by
  obtain ⟨C, hCNonneg, hPrincipalReal⟩ :=
    exists_neg_re_logDeriv_principal_le_inv_add
  obtain ⟨A, hAPos, hSelected⟩ :=
    exists_primitive_selectableZero_logDeriv_bound
  obtain ⟨B, hBPos, hPrincipalHigh⟩ :=
    exists_neg_re_logDeriv_principal_le_pole_add_logs
  let E : Real := B + 1
  let K : Real := 3 * C / Real.log 3 + 4 * A + 2 * E
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hEPos : 0 < E := by
    dsimp [E]
    linarith
  have hKPos : 0 < K := by
    dsimp [K]
    positivity
  refine Exists.intro K (And.intro hKPos ?_)
  intro N _hN hNLower chi hchi hPrimitive hchiSquare p sigma t
    hsigma hsigmaUpper him
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
  have hPrincipalAt := hPrincipalReal (N := N) hsigma hsigmaUpper
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
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogNNonneg : 0 ≤ Real.log N :=
    hLogThree.le.trans hLogNLower
  have hLogHeightNonneg : 0 ≤ Real.log (|t| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg t]
  have hHighRaw := hPrincipalHigh (N := N) hsTwoLower hsTwoUpper
  rw [doubledHeightPole_re] at hHighRaw
  have hHighHeight := log_square_point_height_le sigma t
  have hHighHeightScaled :
      B * Real.log (|((sigma : Complex) + 2 * Complex.I * t).im| + 2) ≤
        B * (2 * Real.log (|t| + 2)) :=
    mul_le_mul_of_nonneg_left hHighHeight hBPos.le
  have hHighEnvelope :
      Real.log N + B * (2 * Real.log (|t| + 2)) ≤
        E * (Real.log N + 2 * Real.log (|t| + 2)) := by
    dsimp [E]
    nlinarith [mul_nonneg hBPos.le hLogNNonneg,
      mul_nonneg hBPos.le hLogHeightNonneg]
  have hHighAt :
      -(logDeriv (1 : DirichletCharacter Complex N).LFunction
        ((sigma : Complex) + 2 * Complex.I * t)).re ≤
          (sigma - 1) / ((sigma - 1) ^ 2 + 4 * t ^ 2) +
            E * (Real.log N + 2 * Real.log (|t| + 2)) := by
    nlinarith
  have hPositivityRaw := logDerivative_combination_nonneg chi hsigma t
  have hPositivity :
      0 ≤
        3 * (-(logDeriv
          (1 : DirichletCharacter Complex N).LFunction sigma).re) +
        4 * (-(logDeriv chi.LFunction
          ((sigma : Complex) + Complex.I * t)).re) +
        (-(logDeriv (1 : DirichletCharacter Complex N).LFunction
          ((sigma : Complex) + 2 * Complex.I * t)).re) := by
    simpa [logDeriv_apply, neg_div, hchiSquare] using hPositivityRaw
  have hBudget := complexZero_error_budget
    (C := C) (A := A) (B := E)
    (x := Real.log N) (y := Real.log (|t| + 2))
    hCNonneg hEPos.le hLogNLower hLogHeightNonneg
  have hRaw :
      4 * (sigma -
          (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ ≤
        3 * (sigma - 1)⁻¹ +
          (sigma - 1) / ((sigma - 1) ^ 2 + 4 * t ^ 2) +
          (3 * C + 4 * A *
            (Real.log N + Real.log (|t| + 2)) +
            E * (Real.log N + 2 * Real.log (|t| + 2))) := by
    nlinarith
  calc
    4 * (sigma -
        (Complex.Hadamard.divisorZeroIndex₀_val p).re)⁻¹ ≤
      3 * (sigma - 1)⁻¹ +
        (sigma - 1) / ((sigma - 1) ^ 2 + 4 * t ^ 2) +
        (3 * C + 4 * A *
          (Real.log N + Real.log (|t| + 2)) +
          E * (Real.log N + 2 * Real.log (|t| + 2))) := hRaw
    _ ≤ 3 * (sigma - 1)⁻¹ +
        (sigma - 1) / ((sigma - 1) ^ 2 + 4 * t ^ 2) +
        K * (Real.log N + Real.log (|t| + 2)) := by
      simpa [K] using add_le_add_left hBudget
        (3 * (sigma - 1)⁻¹ +
          (sigma - 1) / ((sigma - 1) ^ 2 + 4 * t ^ 2))

end BombieriVinogradov.SiegelWalfisz
