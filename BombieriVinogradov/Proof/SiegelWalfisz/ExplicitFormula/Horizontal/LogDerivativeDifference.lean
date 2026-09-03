import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedLogDerivativeConstant
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedProductLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedRegularLogDerivative
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroCanonicalTermSummable
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedZeroValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Two-point logarithmic-derivative subtraction

This module proves the exact identity behind Strombergsson Corollary 12.11.
The same completed Hadamard constant is evaluated at a regular point and at
the reference point with real part two, then canceled term by term.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem logDeriv_LFunction_eq_reference_add_zero_difference
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {s : Complex}
    (hLFunctionNe : Ne (chi.LFunction s) 0)
    (hGammaNe : Ne (chi.gammaFactor s) 0)
    (hGammaDifferentiable : DifferentiableAt Complex chi.gammaFactor s)
    (T : Real) :
    logDeriv chi.LFunction s =
      logDeriv chi.LFunction
          (((2 : Real) : Complex) + (T : Complex) * Complex.I) -
        logDeriv chi.gammaFactor s +
        logDeriv chi.gammaFactor
          (((2 : Real) : Complex) + (T : Complex) * Complex.I) +
        (tsum fun p : SymmetricCompletedZeroIndex chi =>
          1 / (s - symmetricCompletedZeroValue p) -
            1 / (((2 : Real) : Complex) +
              (T : Complex) * Complex.I -
                symmetricCompletedZeroValue p)) := by
  let w : Complex :=
    ((2 : Real) : Complex) + (T : Complex) * Complex.I
  let canonicalAt :
      Complex -> SymmetricCompletedZeroIndex chi -> Complex :=
    fun z p =>
      1 / (z - symmetricCompletedZeroValue p) +
        1 / symmetricCompletedZeroValue p
  have hwRe : w.re = 2 := by
    simp [w, Complex.mul_re]
  have hwRight : 1 < w.re := by
    rw [hwRe]
    norm_num
  have hNNeOne : Ne N 1 := by
    intro hN
    exact hchi (chi.level_one' hN)
  have hCompletedValue :=
    chi.LFunction_eq_completed_div_gammaFactor s (Or.inr hNNeOne)
  have hCompletedNe : Ne (chi.completedLFunction s) 0 := by
    intro hCompletedZero
    apply hLFunctionNe
    rw [hCompletedValue, hCompletedZero]
    simp
  have hNCast : Ne (N : Complex) 0 := by
    norm_num [NeZero.ne N]
  have hNormalizationNe : Ne ((N : Complex) ^ (s / 2)) 0 := by
    simp [hNCast]
  have hSymmetricNe : Ne (symmetricCompletedLFunction chi s) 0 := by
    unfold symmetricCompletedLFunction
    exact mul_ne_zero hNormalizationNe hCompletedNe
  have hAwayS : forall p : SymmetricCompletedZeroIndex chi,
      Ne s (symmetricCompletedZeroValue p) := by
    intro p hEqual
    apply hSymmetricNe
    rw [hEqual]
    exact symmetricCompletedZeroValue_apply_eq_zero hchi p
  have hAwayW : forall p : SymmetricCompletedZeroIndex chi,
      Ne w (symmetricCompletedZeroValue p) := by
    intro p hEqual
    have hUpper : (symmetricCompletedZeroValue p).re < 1 :=
      (symmetricCompletedZeroValue_re_mem_Ioo hchi hPrimitive p).2
    rw [Eq.symm hEqual, hwRe] at hUpper
    norm_num at hUpper
  choose B hB _hBUnique using
    existsUnique_symmetricCompletedLFunction_hadamardConstant
      hchi hPrimitive
  have hHadamardS :
      logDeriv (symmetricCompletedLFunction chi) s =
        B + tsum (canonicalAt s) := by
    have hRaw :=
      logDeriv_symmetricCompletedLFunction_eq_hadamardConstant_add_tsum
        hchi hPrimitive hB
        (by simpa [symmetricCompletedZeroValue] using hAwayS)
    simpa [canonicalAt, symmetricCompletedZeroValue] using hRaw
  have hHadamardW :
      logDeriv (symmetricCompletedLFunction chi) w =
        B + tsum (canonicalAt w) := by
    have hRaw :=
      logDeriv_symmetricCompletedLFunction_eq_hadamardConstant_add_tsum
        hchi hPrimitive hB
        (by simpa [symmetricCompletedZeroValue] using hAwayW)
    simpa [canonicalAt, symmetricCompletedZeroValue] using hRaw
  have hSummableS : Summable (canonicalAt s) := by
    simpa [canonicalAt] using
      summable_completedZero_canonicalTerm hchi hPrimitive hAwayS
  have hSummableW : Summable (canonicalAt w) := by
    simpa [canonicalAt] using
      summable_completedZero_canonicalTerm hchi hPrimitive hAwayW
  have hTsumDifference :
      tsum (canonicalAt s) - tsum (canonicalAt w) =
        (tsum fun p : SymmetricCompletedZeroIndex chi =>
          1 / (s - symmetricCompletedZeroValue p) -
            1 / (w - symmetricCompletedZeroValue p)) := by
    calc
      tsum (canonicalAt s) - tsum (canonicalAt w) =
          tsum (fun p : SymmetricCompletedZeroIndex chi =>
            canonicalAt s p - canonicalAt w p) :=
        Eq.symm (hSummableS.tsum_sub hSummableW)
      _ = tsum (fun p : SymmetricCompletedZeroIndex chi =>
          1 / (s - symmetricCompletedZeroValue p) -
            1 / (w - symmetricCompletedZeroValue p)) :=
        tsum_congr (fun p => by
          dsimp [canonicalAt]
          ring)
  have hProductS :
      logDeriv (symmetricCompletedLFunction chi) s =
        (Real.log N : Complex) / 2 +
          (logDeriv chi.LFunction s +
            logDeriv chi.gammaFactor s) :=
    logDeriv_symmetricCompletedLFunction_eq_three_factors_of_regular
      hchi hLFunctionNe hGammaNe hGammaDifferentiable
  have hProductW :
      logDeriv (symmetricCompletedLFunction chi) w =
        (Real.log N : Complex) / 2 +
          (logDeriv chi.LFunction w +
            logDeriv chi.gammaFactor w) :=
    logDeriv_symmetricCompletedLFunction_eq_three_factors hchi hwRight
  have hReference :
      B + tsum (canonicalAt w) - (Real.log N : Complex) / 2 -
          logDeriv chi.gammaFactor w =
        logDeriv chi.LFunction w := by
    calc
      B + tsum (canonicalAt w) - (Real.log N : Complex) / 2 -
          logDeriv chi.gammaFactor w =
        logDeriv (symmetricCompletedLFunction chi) w -
            (Real.log N : Complex) / 2 -
          logDeriv chi.gammaFactor w := by
            rw [hHadamardW]
      _ = logDeriv chi.LFunction w := by
        rw [hProductW]
        ring
  rw [show
      (((2 : Real) : Complex) + (T : Complex) * Complex.I) = w by rfl]
  calc
    logDeriv chi.LFunction s =
        logDeriv (symmetricCompletedLFunction chi) s -
            (Real.log N : Complex) / 2 -
          logDeriv chi.gammaFactor s := by
      rw [hProductS]
      ring
    _ = B + tsum (canonicalAt s) - (Real.log N : Complex) / 2 -
          logDeriv chi.gammaFactor s := by
      rw [hHadamardS]
    _ =
        (B + tsum (canonicalAt w) - (Real.log N : Complex) / 2 -
            logDeriv chi.gammaFactor w) -
          logDeriv chi.gammaFactor s +
          logDeriv chi.gammaFactor w +
          (tsum (canonicalAt s) - tsum (canonicalAt w)) := by
      ring
    _ = logDeriv chi.LFunction w - logDeriv chi.gammaFactor s +
          logDeriv chi.gammaFactor w +
          (tsum (canonicalAt s) - tsum (canonicalAt w)) := by
      rw [hReference]
    _ = logDeriv chi.LFunction w - logDeriv chi.gammaFactor s +
          logDeriv chi.gammaFactor w +
          (tsum fun p : SymmetricCompletedZeroIndex chi =>
            1 / (s - symmetricCompletedZeroValue p) -
              1 / (w - symmetricCompletedZeroValue p)) := by
      rw [hTsumDifference]

end BombieriVinogradov.SiegelWalfisz

