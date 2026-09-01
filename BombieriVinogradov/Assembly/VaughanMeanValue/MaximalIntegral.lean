import BombieriVinogradov.Assembly.VaughanMeanValue.CommonMajorant
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic

/-!
# Maximal bilinear sums as one frequency integral

This module bounds every character's maximum by the common spectral integral
and proves the integrability needed to exchange that integral with the finite
modulus and character sums.
-/

set_option autoImplicit false

noncomputable section

open Complex Finset MeasureTheory Real Set
open scoped BigOperators FourierTransform

namespace BombieriVinogradov.VaughanMeanValue

open BombieriVinogradov.LargeSieve
open BombieriVinogradov.LogCutoff

theorem norm_positiveCharacterSum_fourierTwist_le (xi : Real)
    (a : Nat -> Complex) (M q : Nat) (chi : DirichletCharacter Complex q) :
    ‖positiveCharacterSum (fourierTwist xi a) M q chi‖ <=
      ∑ m ∈ Icc 1 M, ‖a m‖ := by
  rw [positiveCharacterSum_eq_sum_nat]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  rw [norm_mul, norm_fourierTwist]
  exact mul_le_of_le_one_right (norm_nonneg _) (chi.norm_le_one _)

theorem norm_bilinearCharacterProduct_fourierTwist_le (xi : Real)
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
      M N q chi‖ <=
      (∑ m ∈ Icc 1 M, ‖a m‖) * (∑ n ∈ Icc 1 N, ‖b n‖) := by
  rw [bilinearCharacterProduct, norm_mul]
  exact mul_le_mul
    (norm_positiveCharacterSum_fourierTwist_le xi a M q chi)
    (norm_positiveCharacterSum_fourierTwist_le xi b N q chi)
    (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem continuous_bilinearCharacterProduct_fourierTwist
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    Continuous (fun xi : Real =>
      bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi) := by
  rw [show (fun xi : Real =>
      bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi) = fun xi : Real =>
      ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
        Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
          (a m * b n * chi ((m * n : Nat) : ZMod q)) by
    funext xi
    exact bilinearCharacterProduct_fourierTwist xi a b M N q chi]
  fun_prop

theorem commonSpectralBilinearIntegrable (X : Nat) (hX : 1 <= X)
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    Integrable (fun xi : Real =>
      spectralMajorant
          (Real.log (X : Real) + 3 * integerLogEpsilon X)
          (integerLogEpsilon X) xi *
        ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
          M N q chi‖) := by
  have heps := integerLogEpsilon_pos X hX
  have hA : 0 < Real.log (X : Real) + 3 * integerLogEpsilon X := by
    linarith [log_nat_nonneg X hX]
  have hmajorant := spectralMajorant_integrable
    (Real.log (X : Real) + 3 * integerLogEpsilon X)
    (integerLogEpsilon X) hA heps
  have hmeas : AEStronglyMeasurable (fun xi : Real =>
      ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi‖) :=
    (continuous_bilinearCharacterProduct_fourierTwist a b M N q chi).norm
      |>.aestronglyMeasurable
  exact hmajorant.mul_bdd hmeas (Filter.Eventually.of_forall fun xi =>
    by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        norm_bilinearCharacterProduct_fourierTwist_le xi a b M N q chi)

theorem fourierBilinearIntegrable (Y : Nat) (hY : 1 <= Y)
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    Integrable (fun xi : Real =>
      𝓕 (integerLogCutoff Y) xi *
        bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
          M N q chi) := by
  have hfourier := fourier_integerLogCutoff_integrable Y hY
  have hmeas : AEStronglyMeasurable (fun xi : Real =>
      bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi) :=
    (continuous_bilinearCharacterProduct_fourierTwist a b M N q chi)
      |>.aestronglyMeasurable
  exact hfourier.mul_bdd hmeas (Filter.Eventually.of_forall fun xi =>
    norm_bilinearCharacterProduct_fourierTwist_le xi a b M N q chi)

theorem maximalBilinearNorm_le_commonIntegral
    (X M N : Nat) (a b : Nat -> Complex) (q : Nat)
    (chi : DirichletCharacter Complex q) (hX : 2 <= X) :
    maximalBilinearNorm a b M N X chi <=
      ∫ xi : Real,
        spectralMajorant
            (Real.log (X : Real) + 3 * integerLogEpsilon X)
            (integerLogEpsilon X) xi *
          ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
            M N q chi‖ := by
  have hX1 : 1 <= X := le_trans (by norm_num) hX
  have hepsX := integerLogEpsilon_pos X hX1
  have hAX : 0 <= Real.log (X : Real) + 3 * integerLogEpsilon X := by
    have := log_nat_nonneg X hX1
    positivity
  unfold maximalBilinearNorm
  apply Finset.sup'_le (by simp) _
  intro Y hYrange
  have hYX : Y <= X := Nat.le_of_lt_succ (Finset.mem_range.mp hYrange)
  by_cases hYzero : Y = 0
  · subst Y
    have hrestricted : restrictedBilinearCharacterSum a b M N 0 q chi = 0 := by
      rw [restrictedBilinearCharacterSum]
      apply Finset.sum_eq_zero
      intro m hm
      apply Finset.sum_eq_zero
      intro n hn
      have hmpos : 0 < m := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hm).1
      have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1
      simp [Nat.not_le_of_lt (Nat.mul_pos hmpos hnpos)]
    rw [hrestricted, norm_zero]
    apply integral_nonneg
    intro xi
    exact mul_nonneg (spectralMajorant_nonneg _ _ _ hAX hepsX.le) (norm_nonneg _)
  · have hY1 : 1 <= Y := Nat.one_le_iff_ne_zero.mpr hYzero
    rw [restrictedBilinearCharacterSum_fourier a b M N Y q chi hY1]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono
      (fourierBilinearIntegrable Y hY1 a b M N q chi).norm
      (commonSpectralBilinearIntegrable X hX1 a b M N q chi)
    intro xi
    simpa only [norm_mul] using
      mul_le_mul_of_nonneg_right
        (norm_fourier_integerLogCutoff_le_commonSpectralMajorant hY1 hYX xi)
        (norm_nonneg (bilinearCharacterProduct
          (fourierTwist xi a) (fourierTwist xi b) M N q chi))

def twistedBilinearMean (xi : Real) (a b : Nat -> Complex)
    (M N Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi‖

theorem commonSpectralTwistedMeanIntegrable (X M N Q : Nat)
    (a b : Nat -> Complex) (hX : 1 <= X) :
    Integrable (fun xi : Real =>
      spectralMajorant
          (Real.log (X : Real) + 3 * integerLogEpsilon X)
          (integerLogEpsilon X) xi *
        twistedBilinearMean xi a b M N Q) := by
  unfold twistedBilinearMean
  simpa only [Finset.mul_sum] using
    integrable_finsetSum (Icc 1 Q) (fun q hq => by
      exact integrable_finsetSum (primitiveCharacters q) (fun chi hchi => by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          (commonSpectralBilinearIntegrable X hX a b M N q chi).const_mul
            ((q : Real) / (q.totient : Real))))

end BombieriVinogradov.VaughanMeanValue
