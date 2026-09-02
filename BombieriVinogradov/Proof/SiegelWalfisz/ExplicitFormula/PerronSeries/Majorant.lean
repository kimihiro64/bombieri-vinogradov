import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.ContinuousMap

/-!
# Uniform majorant for the Perron series

This module bounds each vertical summand uniformly in height and proves that
the resulting compact sup norms form a summable sequence.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace BombieriVinogradov.SiegelWalfisz

/-- The norm of a vertical Perron summand is bounded by its value on the real
axis times the uniform factor `x ^ c / c`. -/
theorem norm_perronSeriesFunction_le
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c : Real} (hc : 1 < c) (t : Real) :
    norm (perronSeriesFunction chi x n c t) <=
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [perronSeriesFunction, explicitFormulaDirichletTerm,
      LSeries.term_def]
  case neg =>
    have hcPos : 0 < c := lt_trans zero_lt_one hc
    have hcNe : Ne c 0 := ne_of_gt hcPos
    have hReNe : Ne (((c : Complex) + t * Complex.I).re) 0 := by
      simpa using hcNe
    have hNormLower : c <= norm ((c : Complex) + t * Complex.I) := by
      calc
        c = abs (((c : Complex) + t * Complex.I).re) := by
          simp [abs_of_pos hcPos]
        _ <= norm ((c : Complex) + t * Complex.I) :=
          Complex.abs_re_le_norm _
    simp only [perronSeriesFunction, explicitFormulaDirichletTerm,
      LSeries.term_def, hn, if_false, norm_mul, norm_div]
    rw [Complex.norm_natCast_cpow_of_re_ne_zero n hReNe,
      Complex.norm_natCast_cpow_of_re_ne_zero x hReNe,
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using hcNe)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, sub_self, add_zero]
    have hNormPos : 0 < norm ((c : Complex) + t * Complex.I) :=
      lt_of_lt_of_le hcPos hNormLower
    have hxPowNonneg : 0 <= (x : Real) ^ c :=
      Real.rpow_nonneg (Nat.cast_nonneg x) c
    have hCoeffNonneg :
        0 <= norm (twistedMangoldtSequence chi n) / (n : Real) ^ c :=
      div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) c)
    calc
      norm (twistedMangoldtSequence chi n) / (n : Real) ^ c *
          ((x : Real) ^ c / norm ((c : Complex) + t * Complex.I)) <=
          norm (twistedMangoldtSequence chi n) / (n : Real) ^ c *
            ((x : Real) ^ c / c) := by
        gcongr
      _ = (x : Real) ^ c / c *
          (norm (twistedMangoldtSequence chi n) / (n : Real) ^ c) := by
        ring

/-- Restricting a vertical summand to any compact height interval preserves
the same height-independent majorant. -/
theorem norm_restrict_perronSeriesContinuousMap_le
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c T : Real} (hc : 1 < c) :
    norm ((perronSeriesContinuousMap chi hx n hc).restrict
      (TopologicalSpace.Compacts.mk (uIcc (-T) T) isCompact_uIcc)) <=
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) := by
  have hcPos : 0 < c := lt_trans zero_lt_one hc
  have hMajorantNonneg : 0 <=
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) :=
    mul_nonneg
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) c) (le_of_lt hcPos))
      (norm_nonneg _)
  apply (ContinuousMap.norm_le _ hMajorantNonneg).mpr
  intro t
  simpa [perronSeriesContinuousMap] using
    norm_perronSeriesFunction_le chi hx n hc t.1

/-- The compact sup norms of the vertical Perron summands are summable. -/
theorem summable_norm_restrict_perronSeriesContinuousMap
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) :
    Summable (fun n : Nat =>
      norm ((perronSeriesContinuousMap chi hx n hc).restrict
        (TopologicalSpace.Compacts.mk (uIcc (-T) T) isCompact_uIcc))) := by
  have hSequence : twistedMangoldtSequence chi =
      (fun n : Nat => chi n) *
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    funext n
    rfl
  have hLSeries : LSeriesSummable (twistedMangoldtSequence chi) (c : Complex) := by
    rw [hSequence]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hc)
  have hMajorant : Summable (fun n : Nat =>
      ((x : Real) ^ c / c) *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c / c)
  apply Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => norm_restrict_perronSeriesContinuousMap_le chi hx n hc)
    hMajorant

end BombieriVinogradov.SiegelWalfisz
