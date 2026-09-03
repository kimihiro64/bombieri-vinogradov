import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.LogDerivativeDifference
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Horizontal.ZeroDifferenceRemainderBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroAvoidance
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorHorizontalLogDerivativeBound
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.GammaFactorNearOriginDifferentiability
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.LFunctionTwoLogDerivativeBound
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Local-zero approximation for horizontal logarithmic derivatives

This module assembles the formal analogue of Strombergsson Corollary 12.11
on the contour strip used by the project. It combines separately verified
reference, gamma-factor, and zero-series estimates, without integrating the
horizontal contour or imposing a selected good height.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem exists_norm_logDeriv_LFunction_sub_nearZeroSum_le :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall {chi : DirichletCharacter Complex N},
          Ne chi 1 -> DirichletCharacter.IsPrimitive chi ->
            forall {T : Real} {s : Complex},
              s.im = T ->
              -(1 : Real) / 2 <= s.re ->
              s.re <= 2 ->
              2 <= abs T ->
              Ne (chi.LFunction s) 0 ->
                norm (logDeriv chi.LFunction s -
                  (tsum fun p : SymmetricCompletedZeroIndex chi =>
                    if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
                      1 / (s - symmetricCompletedZeroValue p)
                    else 0)) <=
                      C * (Real.log N + Real.log (abs T + 2))) := by
  choose CReference hCReferencePos hReference using
    exists_norm_logDeriv_LFunction_le_log_of_re_eq_two
  choose CGamma hCGammaPos hGamma using
    exists_norm_logDeriv_gammaFactor_horizontal_strip_le_log
  choose CZero hCZeroPos hZero using
    exists_norm_tsum_zeroDifference_sub_near_le
  let C : Real := CReference + 2 * CGamma + CZero
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  refine Exists.intro C (And.intro hCPos ?_)
  intro N inst hN chi hchi hPrimitive T s hsIm hsLower hsUpper
    hAbsT hLFunctionNe
  let w : Complex :=
    ((2 : Real) : Complex) + (T : Complex) * Complex.I
  let zeroDiff : SymmetricCompletedZeroIndex chi -> Complex := fun p =>
    1 / (s - symmetricCompletedZeroValue p) -
      1 / (w - symmetricCompletedZeroValue p)
  let nearTarget : SymmetricCompletedZeroIndex chi -> Complex := fun p =>
    if abs (T - (symmetricCompletedZeroValue p).im) < 1 then
      1 / (s - symmetricCompletedZeroValue p)
    else 0
  let A : Real := Real.log N + Real.log (abs T + 2)
  have hsAbsIm : 2 <= abs s.im := by
    rw [hsIm]
    exact hAbsT
  have hsNe : Ne s 0 := by
    intro hsZero
    rw [hsZero] at hsAbsIm
    norm_num at hsAbsIm
  have hsNegOne : -1 < s.re := by
    linarith
  have hGammaNe : Ne (chi.gammaFactor s) 0 :=
    DirichletCharacter.gammaFactor_ne_zero_of_neg_one_lt_re_of_ne_zero
      chi hsNegOne hsNe
  have hGammaDifferentiable :
      DifferentiableAt Complex chi.gammaFactor s :=
    DirichletCharacter.differentiableAt_gammaFactor_of_neg_one_lt_re_of_ne_zero
      chi hsNegOne hsNe
  have hsAway : forall p : SymmetricCompletedZeroIndex chi,
      Ne s (symmetricCompletedZeroValue p) :=
    ne_symmetricCompletedZeroValue_of_LFunction_ne_zero
      hchi hLFunctionNe
  have hwRe : w.re = 2 := by
    simp [w, Complex.mul_re]
  have hwIm : w.im = T := by
    simp [w, Complex.mul_im]
  have hwLower : -(1 : Real) / 2 <= w.re := by
    rw [hwRe]
    norm_num
  have hwUpper : w.re <= 2 := by
    rw [hwRe]
  have hwAbsIm : 2 <= abs w.im := by
    rw [hwIm]
    exact hAbsT
  have hExact :
      logDeriv chi.LFunction s =
        logDeriv chi.LFunction w -
          logDeriv chi.gammaFactor s +
          logDeriv chi.gammaFactor w + tsum zeroDiff := by
    simpa [w, zeroDiff] using
      logDeriv_LFunction_eq_reference_add_zero_difference
        hchi hPrimitive hLFunctionNe hGammaNe
          hGammaDifferentiable T
  have hZeroBound :
      norm (tsum zeroDiff - tsum nearTarget) <= CZero * A := by
    simpa [A, w, zeroDiff, nearTarget] using
      hZero hN hchi hPrimitive hsIm hsLower hsUpper hsAway
  have hReferenceRaw :
      norm (logDeriv chi.LFunction w) <=
        CReference * Real.log (abs T + 2) := by
    have hRaw := hReference chi hwRe
    simpa [hwIm] using hRaw
  have hGammaSRaw :
      norm (logDeriv chi.gammaFactor s) <=
        CGamma * Real.log (abs T + 2) := by
    have hRaw := hGamma chi hsLower hsUpper hsAbsIm
    simpa [hsIm] using hRaw
  have hGammaWRaw :
      norm (logDeriv chi.gammaFactor w) <=
        CGamma * Real.log (abs T + 2) := by
    have hRaw := hGamma chi hwLower hwUpper hwAbsIm
    simpa [hwIm] using hRaw
  have hNOne : 1 <= N := le_trans (by norm_num) hN
  have hNCastOne : ((1 : Nat) : Real) <= (N : Real) :=
    Nat.cast_le.mpr hNOne
  have hNReal : (1 : Real) <= (N : Real) := by
    simpa using hNCastOne
  have hLogNNonneg : 0 <= Real.log N :=
    Real.log_nonneg hNReal
  have hLogHeightNonneg : 0 <= Real.log (abs T + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg T])
  have hLogHeightLeA : Real.log (abs T + 2) <= A := by
    dsimp [A]
    exact le_add_of_nonneg_left hLogNNonneg
  have hReferenceBound :
      norm (logDeriv chi.LFunction w) <= CReference * A :=
    hReferenceRaw.trans
      (mul_le_mul_of_nonneg_left hLogHeightLeA hCReferencePos.le)
  have hGammaSBound :
      norm (logDeriv chi.gammaFactor s) <= CGamma * A :=
    hGammaSRaw.trans
      (mul_le_mul_of_nonneg_left hLogHeightLeA hCGammaPos.le)
  have hGammaWBound :
      norm (logDeriv chi.gammaFactor w) <= CGamma * A :=
    hGammaWRaw.trans
      (mul_le_mul_of_nonneg_left hLogHeightLeA hCGammaPos.le)
  have hResidualIdentity :
      logDeriv chi.LFunction s - tsum nearTarget =
        (logDeriv chi.LFunction w - logDeriv chi.gammaFactor s +
          logDeriv chi.gammaFactor w) +
            (tsum zeroDiff - tsum nearTarget) := by
    calc
      logDeriv chi.LFunction s - tsum nearTarget =
          (logDeriv chi.LFunction w - logDeriv chi.gammaFactor s +
            logDeriv chi.gammaFactor w + tsum zeroDiff) -
              tsum nearTarget :=
        congrArg (fun z => z - tsum nearTarget) hExact
      _ =
          (logDeriv chi.LFunction w - logDeriv chi.gammaFactor s +
            logDeriv chi.gammaFactor w) +
              (tsum zeroDiff - tsum nearTarget) := by
        ring
  change norm (logDeriv chi.LFunction s - tsum nearTarget) <= C * A
  rw [hResidualIdentity]
  calc
    norm ((logDeriv chi.LFunction w - logDeriv chi.gammaFactor s +
        logDeriv chi.gammaFactor w) +
          (tsum zeroDiff - tsum nearTarget)) <=
        norm (logDeriv chi.LFunction w - logDeriv chi.gammaFactor s +
          logDeriv chi.gammaFactor w) +
            norm (tsum zeroDiff - tsum nearTarget) :=
      norm_add_le _ _
    _ <= (norm (logDeriv chi.LFunction w -
          logDeriv chi.gammaFactor s) +
        norm (logDeriv chi.gammaFactor w)) +
          norm (tsum zeroDiff - tsum nearTarget) :=
      add_le_add (norm_add_le _ _) le_rfl
    _ <= ((norm (logDeriv chi.LFunction w) +
          norm (logDeriv chi.gammaFactor s)) +
        norm (logDeriv chi.gammaFactor w)) +
          norm (tsum zeroDiff - tsum nearTarget) :=
      add_le_add
        (add_le_add (norm_sub_le _ _) le_rfl)
        le_rfl
    _ <= ((CReference * A + CGamma * A) + CGamma * A) + CZero * A :=
      add_le_add
        (add_le_add (add_le_add hReferenceBound hGammaSBound)
          hGammaWBound)
        hZeroBound
    _ = C * A := by
      dsimp [C]
      ring

end BombieriVinogradov.SiegelWalfisz
