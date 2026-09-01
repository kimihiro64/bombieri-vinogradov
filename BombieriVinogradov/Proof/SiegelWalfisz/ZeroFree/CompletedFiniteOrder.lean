import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedFunctionalEquation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedRightHalfPlaneGrowth
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Basic
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Order
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Exp
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.ExpGrowth

/-!
# Finite order of the symmetric completed Dirichlet L-function

This module uses compact boundedness and the primitive functional equation to extend the
right-half-plane growth estimate to an order-one bound on the whole complex plane.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_entireOfOrderAtMost_one
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi) :
    Complex.Hadamard.EntireOfOrderAtMost (1 : Real)
      (symmetricCompletedLFunction chi) := by
  refine ⟨differentiable_symmetricCompletedLFunction hchi, ?_⟩
  intro epsilon hEpsilon
  have hInverseNe : chi⁻¹ ≠ 1 := by
    intro hInverse
    apply hchi
    calc
      chi = (chi⁻¹)⁻¹ := by simp
      _ = (1 : DirichletCharacter Complex N)⁻¹ := congrArg Inv.inv hInverse
      _ = 1 := by simp
  obtain ⟨Cchi, hCchiPos, hRightChi⟩ :=
    symmetricCompletedLFunction_rightHalfPlane_order_bound chi hchi epsilon hEpsilon
  obtain ⟨Cinv, hCinvPos, hRightInv⟩ :=
    symmetricCompletedLFunction_rightHalfPlane_order_bound chi⁻¹ hInverseNe epsilon hEpsilon
  have hContinuous : ContinuousOn (symmetricCompletedLFunction chi)
      (Metric.closedBall (0 : Complex) 4) :=
    (differentiable_symmetricCompletedLFunction hchi).continuous.continuousOn
  obtain ⟨M, hMNonneg, hM⟩ := Complex.exists_norm_bound_on_closedBall hContinuous
  let exponent : Real := 1 + epsilon
  let scale : Real := (3 : Real) ^ exponent
  let C : Real := M + 1 + ‖chi.rootNumber‖ +
    scale * max Cchi Cinv + 1
  have hExponentNonneg : 0 ≤ exponent := by dsimp [exponent]; linarith
  have hScaleNonneg : 0 ≤ scale := by dsimp [scale]; positivity
  have hCPos : 0 < C := by
    dsimp [C]
    have hMaxPos : 0 < max Cchi Cinv := lt_of_lt_of_le hCchiPos (le_max_left _ _)
    positivity
  refine ⟨C, hCPos, ?_⟩
  intro z
  let base : Real := 1 + ‖z‖
  have hBaseOne : 1 ≤ base := by dsimp [base]; linarith [norm_nonneg z]
  have hBaseNonneg : 0 ≤ base := zero_le_one.trans hBaseOne
  have hBasePowerOne : 1 ≤ base ^ exponent :=
    Real.one_le_rpow hBaseOne hExponentNonneg
  by_cases hSmall : ‖z‖ ≤ 4
  · have hBound := hM z hSmall
    have hMLeC : M ≤ C := by
      have hMaxNonneg : 0 ≤ max Cchi Cinv :=
        (le_max_left Cchi Cinv).trans' hCchiPos.le
      have hScaledNonneg : 0 ≤ scale * max Cchi Cinv :=
        mul_nonneg hScaleNonneg hMaxNonneg
      dsimp [C]
      nlinarith [norm_nonneg chi.rootNumber]
    have hCNonneg : 0 ≤ C := hCPos.le
    have hCLePower : C ≤ C * base ^ exponent := by
      have h := mul_le_mul_of_nonneg_left hBasePowerOne hCNonneg
      simpa using h
    exact hBound.trans hMLeC |>.trans hCLePower |>.trans (Real.le_exp_self _)
  · have hLarge : 1 ≤ ‖z‖ := by linarith
    by_cases hRight : (1 : Real) / 2 ≤ z.re
    · have hBound := hRightChi z hRight hLarge
      have hRadius : 2 + ‖z‖ ≤ 3 * base := by
        dsimp [base]
        nlinarith [norm_nonneg z]
      have hScaleBound :
          Real.exp (Cchi * (2 + ‖z‖) ^ exponent) ≤
            Real.exp ((Cchi * (3 : Real) ^ exponent) * base ^ exponent) :=
        Real.exp_mul_rpow_le_exp_mul_rpow_of_le_mul hCchiPos.le (by norm_num)
          (by positivity) hBaseNonneg hExponentNonneg hRadius
      have hCoeff : Cchi * (3 : Real) ^ exponent ≤ C := by
        have hMax : Cchi ≤ max Cchi Cinv := le_max_left _ _
        have hScaled : scale * Cchi ≤ scale * max Cchi Cinv :=
          mul_le_mul_of_nonneg_left hMax hScaleNonneg
        dsimp [C, scale]
        nlinarith [hScaled, hMNonneg, norm_nonneg chi.rootNumber]
      have hFinalExponent :
          (Cchi * (3 : Real) ^ exponent) * base ^ exponent ≤
            C * base ^ exponent :=
        mul_le_mul_of_nonneg_right hCoeff (Real.rpow_nonneg hBaseNonneg _)
      exact hBound.trans hScaleBound |>.trans
        (Real.exp_le_exp.mpr hFinalExponent)
    · have hLeft : z.re < (1 : Real) / 2 := lt_of_not_ge hRight
      let w : Complex := 1 - z
      have hwRe : (1 : Real) / 2 ≤ w.re := by
        dsimp [w]
        linarith
      have hzNormLe : ‖z‖ ≤ ‖w‖ + 1 := by
        have hzIdentity : z = 1 - w := by dsimp [w]; ring
        rw [hzIdentity]
        calc
          ‖1 - w‖ ≤ ‖(1 : Complex)‖ + ‖w‖ := norm_sub_le _ _
          _ = ‖w‖ + 1 := by norm_num; ring
      have hwNorm : 1 ≤ ‖w‖ := by linarith
      have hBoundInv := hRightInv w hwRe hwNorm
      have hwNormUpper : ‖w‖ ≤ 1 + ‖z‖ := by
        dsimp [w]
        calc
          ‖1 - z‖ ≤ ‖(1 : Complex)‖ + ‖z‖ := norm_sub_le _ _
          _ = 1 + ‖z‖ := by norm_num
      have hRadius : 2 + ‖w‖ ≤ 3 * base := by
        dsimp [base]
        nlinarith [norm_nonneg z, hwNormUpper]
      have hScaleBound :
          Real.exp (Cinv * (2 + ‖w‖) ^ exponent) ≤
            Real.exp ((Cinv * (3 : Real) ^ exponent) * base ^ exponent) :=
        Real.exp_mul_rpow_le_exp_mul_rpow_of_le_mul hCinvPos.le (by norm_num)
          (by positivity) hBaseNonneg hExponentNonneg hRadius
      have hFunctional := symmetricCompletedLFunction_one_sub hPrimitive w
      have hOneSub : 1 - w = z := by dsimp [w]; ring
      rw [hOneSub] at hFunctional
      have hRootExp : ‖chi.rootNumber‖ ≤ Real.exp ‖chi.rootNumber‖ :=
        Real.le_exp_self _
      have hCombined : ‖symmetricCompletedLFunction chi z‖ ≤
          Real.exp (‖chi.rootNumber‖ +
            (Cinv * (3 : Real) ^ exponent) * base ^ exponent) := by
        rw [hFunctional, norm_mul]
        calc
          ‖chi.rootNumber‖ * ‖symmetricCompletedLFunction chi⁻¹ w‖ ≤
              ‖chi.rootNumber‖ *
                Real.exp (Cinv * (2 + ‖w‖) ^ exponent) :=
            mul_le_mul_of_nonneg_left hBoundInv (norm_nonneg _)
          _ ≤ Real.exp ‖chi.rootNumber‖ *
                Real.exp ((Cinv * (3 : Real) ^ exponent) * base ^ exponent) :=
            mul_le_mul hRootExp hScaleBound (Real.exp_pos _).le (Real.exp_pos _).le
          _ = Real.exp (‖chi.rootNumber‖ +
                (Cinv * (3 : Real) ^ exponent) * base ^ exponent) := by
            rw [Real.exp_add]
      have hCoeff : ‖chi.rootNumber‖ +
          Cinv * (3 : Real) ^ exponent ≤ C := by
        have hMax : Cinv ≤ max Cchi Cinv := le_max_right _ _
        have hScaled : scale * Cinv ≤ scale * max Cchi Cinv :=
          mul_le_mul_of_nonneg_left hMax hScaleNonneg
        dsimp [C, scale]
        nlinarith [hScaled, hMNonneg]
      have hRootToPower : ‖chi.rootNumber‖ ≤
          ‖chi.rootNumber‖ * base ^ exponent := by
        have h := mul_le_mul_of_nonneg_left hBasePowerOne (norm_nonneg chi.rootNumber)
        simpa using h
      have hExponentBound : ‖chi.rootNumber‖ +
            (Cinv * (3 : Real) ^ exponent) * base ^ exponent ≤
          C * base ^ exponent := by
        calc
          ‖chi.rootNumber‖ +
              (Cinv * (3 : Real) ^ exponent) * base ^ exponent ≤
            ‖chi.rootNumber‖ * base ^ exponent +
              (Cinv * (3 : Real) ^ exponent) * base ^ exponent :=
            add_le_add hRootToPower (le_refl _)
          _ = (‖chi.rootNumber‖ + Cinv * (3 : Real) ^ exponent) *
              base ^ exponent := by ring
          _ ≤ C * base ^ exponent :=
            mul_le_mul_of_nonneg_right hCoeff (Real.rpow_nonneg hBaseNonneg _)
      exact hCombined.trans (Real.exp_le_exp.mpr hExponentBound)

end BombieriVinogradov.SiegelWalfisz
