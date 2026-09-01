import BombieriVinogradov.Assembly.VaughanMeanValue.MaximalIntegral
import Mathlib.Tactic

/-!
# Vaughan's maximal bilinear character large sieve

This module sums the per-character maximal integral, applies the proved
nonmaximal bilinear large sieve frequency by frequency, and absorbs the exact
spectral integral into the logarithm required by Vaughan's theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset MeasureTheory Real Set
open scoped BigOperators FourierTransform

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve
open BombieriVinogradov.LogCutoff

theorem weightedMaximalBilinear_le_commonIntegral
    (X M N Q : Nat) (a b : Nat -> Complex) (hX : 2 <= X) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi <=
      ∫ xi : Real,
        spectralMajorant
            (Real.log (X : Real) + 3 * integerLogEpsilon X)
            (integerLogEpsilon X) xi *
          twistedBilinearMean xi a b M N Q := by
  calc
    (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi) <=
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ∫ xi : Real,
              spectralMajorant
                  (Real.log (X : Real) + 3 * integerLogEpsilon X)
                  (integerLogEpsilon X) xi *
                ‖bilinearCharacterProduct
                  (fourierTwist xi a) (fourierTwist xi b) M N q chi‖ := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro chi hchi
        exact maximalBilinearNorm_le_commonIntegral X M N a b q chi hX
      · positivity
    _ = ∫ xi : Real,
        spectralMajorant
            (Real.log (X : Real) + 3 * integerLogEpsilon X)
            (integerLogEpsilon X) xi *
          twistedBilinearMean xi a b M N Q := by
      unfold twistedBilinearMean
      symm
      calc
        (∫ xi : Real,
            spectralMajorant
                (Real.log (X : Real) + 3 * integerLogEpsilon X)
                (integerLogEpsilon X) xi *
              ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
                ∑ chi ∈ primitiveCharacters q,
                  ‖bilinearCharacterProduct
                    (fourierTwist xi a) (fourierTwist xi b) M N q chi‖) =
            ∫ xi : Real,
              ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
                ∑ chi ∈ primitiveCharacters q,
                  spectralMajorant
                      (Real.log (X : Real) + 3 * integerLogEpsilon X)
                      (integerLogEpsilon X) xi *
                    ‖bilinearCharacterProduct
                      (fourierTwist xi a) (fourierTwist xi b) M N q chi‖ := by
          apply integral_congr_ae
          filter_upwards with xi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [← Finset.mul_sum]
          ring
        _ = ∑ q ∈ Icc 1 Q,
              ∫ xi : Real, ((q : Real) / (q.totient : Real)) *
                ∑ chi ∈ primitiveCharacters q,
                  spectralMajorant
                      (Real.log (X : Real) + 3 * integerLogEpsilon X)
                      (integerLogEpsilon X) xi *
                    ‖bilinearCharacterProduct
                      (fourierTwist xi a) (fourierTwist xi b) M N q chi‖ := by
          rw [integral_finsetSum]
          intro q hq
          exact (integrable_finsetSum (primitiveCharacters q) (fun chi hchi =>
            commonSpectralBilinearIntegrable X
              (le_trans (by norm_num) hX) a b M N q chi)).const_mul _
        _ = ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
              ∑ chi ∈ primitiveCharacters q,
                ∫ xi : Real,
                  spectralMajorant
                      (Real.log (X : Real) + 3 * integerLogEpsilon X)
                      (integerLogEpsilon X) xi *
                    ‖bilinearCharacterProduct
                      (fourierTwist xi a) (fourierTwist xi b) M N q chi‖ := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [integral_const_mul]
          rw [integral_finsetSum]
          intro chi hchi
          exact commonSpectralBilinearIntegrable X
            (le_trans (by norm_num) hX) a b M N q chi

theorem weightedMaximalBilinear_le_cutoffFactor
    (X M N Q : Nat) (a b : Nat -> Complex)
    (hX : 2 <= X) (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi <=
      (16 + 4 * Real.log ((X : Real) + 1)) *
        (Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) *
            positiveCoefficientMass a M) *
          Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
            positiveCoefficientMass b N)) := by
  let A : Real := Real.log (X : Real) + 3 * integerLogEpsilon X
  let eps : Real := integerLogEpsilon X
  let K : Real :=
    Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) *
        positiveCoefficientMass a M) *
      Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
        positiveCoefficientMass b N)
  have hX1 : 1 <= X := le_trans (by norm_num) hX
  have heps : 0 < eps := by simpa [eps] using integerLogEpsilon_pos X hX1
  have hA : 0 < A := by
    dsimp [A]
    linarith [log_nat_nonneg X hX1, integerLogEpsilon_pos X hX1]
  have hepsA : eps <= A := by
    dsimp [A, eps]
    linarith [log_nat_nonneg X hX1, integerLogEpsilon_pos X hX1]
  have hK : 0 <= K := by dsimp [K]; positivity
  have hnonmax (xi : Real) : twistedBilinearMean xi a b M N Q <= K := by
    unfold twistedBilinearMean
    simpa only [positiveCoefficientMass_fourierTwist] using
      nonmaximalBilinearLargeSieve M N Q
        (fourierTwist xi a) (fourierTwist xi b) hQ
  have hmajorant := spectralMajorant_integrable A eps hA heps
  have hintegral : ∫ xi : Real, spectralMajorant A eps xi <=
      16 + 4 * Real.log ((X : Real) + 1) := by
    calc
      (∫ xi : Real, spectralMajorant A eps xi) =
          4 + 2 * Real.log (A / eps) :=
        integral_spectralMajorant A eps hA heps hepsA
      _ <= 16 + 4 * Real.log ((X : Real) + 1) := by
        dsimp [A, eps]
        linarith [log_integerLogCutoff_ratio_le X hX1]
  calc
    (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi) <=
        ∫ xi : Real, spectralMajorant A eps xi *
          twistedBilinearMean xi a b M N Q := by
      simpa [A, eps] using
        weightedMaximalBilinear_le_commonIntegral X M N Q a b hX
    _ <= ∫ xi : Real, spectralMajorant A eps xi * K := by
      apply integral_mono
        (by simpa [A, eps] using
          commonSpectralTwistedMeanIntegrable X M N Q a b hX1)
        (hmajorant.mul_const K)
      intro xi
      exact mul_le_mul_of_nonneg_left (hnonmax xi)
        (spectralMajorant_nonneg A eps xi hA.le heps.le)
    _ = (∫ xi : Real, spectralMajorant A eps xi) * K :=
      integral_mul_const K _
    _ <= (16 + 4 * Real.log ((X : Real) + 1)) * K :=
      mul_le_mul_of_nonneg_right hintegral hK
    _ = (16 + 4 * Real.log ((X : Real) + 1)) *
        (Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) *
            positiveCoefficientMass a M) *
          Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
            positiveCoefficientMass b N)) := by rfl

theorem cutoffFactor_le_log_product (X M N : Nat)
    (hX : 2 <= X) (hM : 1 <= M) (hN : 1 <= N) :
    16 + 4 * Real.log ((X : Real) + 1) <=
      40 * Real.log ((X * M * N : Nat) : Real) := by
  have hZNat : X <= X * M * N := by
    simpa [mul_assoc] using
      Nat.mul_le_mul (Nat.mul_le_mul_left X hM) hN
  have hXReal : (2 : Real) <= (X : Real) := by exact_mod_cast hX
  have hZReal : (X : Real) <= ((X * M * N : Nat) : Real) := by
    exact_mod_cast hZNat
  have hZPos : 0 < ((X * M * N : Nat) : Real) := by linarith
  have hXp1Zsq : (X : Real) + 1 <= ((X * M * N : Nat) : Real) ^ 2 := by
    have hXsq : (X : Real) + 1 <= (X : Real) ^ 2 := by nlinarith
    have hsq : (X : Real) ^ 2 <= ((X * M * N : Nat) : Real) ^ 2 := by
      nlinarith
    exact hXsq.trans hsq
  have hlogXp1 : Real.log ((X : Real) + 1) <=
      2 * Real.log ((X * M * N : Nat) : Real) := by
    calc
      Real.log ((X : Real) + 1) <=
          Real.log (((X * M * N : Nat) : Real) ^ 2) :=
        Real.log_le_log (by linarith) hXp1Zsq
      _ = 2 * Real.log ((X * M * N : Nat) : Real) := by
        rw [Real.log_pow]
        norm_num
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogTwoZ : Real.log 2 <= Real.log ((X * M * N : Nat) : Real) :=
    Real.log_le_log (by norm_num) (hXReal.trans hZReal)
  have hhalfLogZ : (1 / 2 : Real) <=
      Real.log ((X * M * N : Nat) : Real) := hhalfLogTwo.trans hlogTwoZ
  linarith

theorem coefficientMass_nonneg (a : Nat -> Complex) (M : Nat) :
    0 <= coefficientMass a M := by
  unfold coefficientMass
  positivity

theorem sqrt_thirtySix_mul_product (U V : Real) (hU : 0 <= U) :
    Real.sqrt (36 * U) * Real.sqrt (36 * V) =
      36 * Real.sqrt (U * V) := by
  calc
    Real.sqrt (36 * U) * Real.sqrt (36 * V) =
        Real.sqrt ((36 * U) * (36 * V)) := by
      rw [Real.sqrt_mul (by positivity : 0 <= 36 * U)]
    _ = Real.sqrt (36 ^ 2 * (U * V)) := by
      congr 1
      ring
    _ = Real.sqrt (36 ^ 2) * Real.sqrt (U * V) := by
      rw [Real.sqrt_mul (sq_nonneg (36 : Real))]
    _ = 36 * Real.sqrt (U * V) := by norm_num

theorem maximalBilinearLargeSieve : MaximalBilinearLargeSieveStatement := by
  refine ⟨1440, by norm_num, ?_⟩
  intro X M N Q a b hX hM hN hQ
  have hraw := weightedMaximalBilinear_le_cutoffFactor X M N Q a b hX hQ
  rw [positiveCoefficientMass_eq_coefficientMass,
    positiveCoefficientMass_eq_coefficientMass] at hraw
  have hMterm : 0 <= ((M : Real) + (Q : Real) ^ 2) * coefficientMass a M := by
    exact mul_nonneg (by positivity) (coefficientMass_nonneg a M)
  have hsqrt :
      Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) * coefficientMass a M) *
          Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * coefficientMass b N) =
        36 * Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
          ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass a M * coefficientMass b N) := by
    rw [show 36 * ((M : Real) + (Q : Real) ^ 2) * coefficientMass a M =
        36 * (((M : Real) + (Q : Real) ^ 2) * coefficientMass a M) by ring,
      show 36 * ((N : Real) + (Q : Real) ^ 2) * coefficientMass b N =
        36 * (((N : Real) + (Q : Real) ^ 2) * coefficientMass b N) by ring,
      sqrt_thirtySix_mul_product
      (((M : Real) + (Q : Real) ^ 2) * coefficientMass a M)
      (((N : Real) + (Q : Real) ^ 2) * coefficientMass b N)
      hMterm]
    congr 2
    ring
  have hcutoff := cutoffFactor_le_log_product X M N hX hM hN
  calc
    (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi) <=
        (16 + 4 * Real.log ((X : Real) + 1)) *
          (Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) * coefficientMass a M) *
            Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * coefficientMass b N)) :=
      hraw
    _ = (16 + 4 * Real.log ((X : Real) + 1)) *
        (36 * Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
          ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass a M * coefficientMass b N)) := by rw [hsqrt]
    _ <= (40 * Real.log ((X * M * N : Nat) : Real)) *
        (36 * Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
          ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass a M * coefficientMass b N)) := by
      exact mul_le_mul_of_nonneg_right hcutoff (by positivity)
    _ = 1440 * Real.log ((X * M * N : Nat) : Real) *
        Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
          ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass a M * coefficientMass b N) := by ring

end BombieriVinogradov.VaughanMeanValue
