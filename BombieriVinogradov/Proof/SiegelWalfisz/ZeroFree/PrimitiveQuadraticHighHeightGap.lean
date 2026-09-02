import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroStrip
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticHighHeightCoreInequality
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.QuadraticHighHeightOptimization

/-!
# High-height gap for primitive quadratic zeros

This module packages equation (408) and its pure optimization at any fixed
positive threshold measured against `log N`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_primitive_quadratic_highHeight_gap
    (eta : Real) (heta : 0 < eta) :
    exists c : Real, 0 < c ∧
      forall {N : Nat} [NeZero N], 3 ≤ N ->
        forall {chi : DirichletCharacter Complex N},
          chi ≠ 1 -> DirichletCharacter.IsPrimitive chi -> chi ^ 2 = 1 ->
            forall p : SymmetricCompletedZeroIndex chi,
              eta / Real.log N ≤
                (Complex.Hadamard.divisorZeroIndex₀_val p).im ->
                c / (Real.log N + Real.log
                  (|(Complex.Hadamard.divisorZeroIndex₀_val p).im| + 2)) ≤
                  1 - (Complex.Hadamard.divisorZeroIndex₀_val p).re := by
  obtain ⟨K, hKPos, hCore⟩ :=
    exists_quadratic_highHeight_core_inequality
  obtain ⟨c, hcPos, hOptimize⟩ :=
    exists_highHeight_gap_of_core hKPos heta
  refine Exists.intro c (And.intro hcPos ?_)
  intro N _hN hNLower chi hchi hPrimitive hchiSquare p hHeight
  let beta : Real := (Complex.Hadamard.divisorZeroIndex₀_val p).re
  let t : Real := (Complex.Hadamard.divisorZeroIndex₀_val p).im
  let L : Real := Real.log N + Real.log (|t| + 2)
  have hLogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hLogNLower : Real.log 3 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hNLower)
  have hLogNPos : 0 < Real.log N := hLogThree.trans_le hLogNLower
  have hLogHeightNonneg : 0 ≤ Real.log (|t| + 2) := by
    apply Real.log_nonneg
    linarith [abs_nonneg t]
  have hLLower : Real.log 3 ≤ L := by
    dsimp [L]
    linarith
  have hLogNLeL : Real.log N ≤ L := by
    dsimp [L]
    linarith
  have hEtaScale : eta / L ≤ eta / Real.log N :=
    div_le_div_of_nonneg_left heta.le hLogNPos hLogNLeL
  have hEtaHeight : eta / L ≤ t := by
    exact hEtaScale.trans (by simpa [t] using hHeight)
  have hBeta : beta < 1 :=
    (symmetricCompletedLFunction_divisorZeroIndex₀_re_mem_Ioo
      hchi hPrimitive p).2
  have hCoreAt : forall sigma : Real, 1 < sigma -> sigma ≤ 2 ->
      4 * (sigma - beta)⁻¹ ≤
        3 * (sigma - 1)⁻¹ +
          (sigma - 1) / ((sigma - 1) ^ 2 + 4 * t ^ 2) +
          K * L := by
    intro sigma hsigma hsigmaUpper
    exact hCore hNLower hchi hPrimitive hchiSquare p
      hsigma hsigmaUpper rfl
  have hGap := hOptimize hBeta hLLower hEtaHeight hCoreAt
  simpa [beta, t, L] using hGap

end BombieriVinogradov.SiegelWalfisz
