import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.LevelTransfer
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.ZeroExclusion.PrincipalCase

/-!
# Siegel zero exclusion

This module assembles the primitive, level-transfer, and principal branches of
Strombergsson's Theorem 16.2. For principal characters it states nonvanishing
at regular points; this excludes only the total-function value that Lean assigns
at the meromorphic pole `s = 1`.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

/--
Strombergsson's Theorem 16.2, expressed at every regular real point of the
Dirichlet L-function represented as a total function in Mathlib.
-/
theorem siegelZeroExclusion :
    ∀ epsilon > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N),
        chi ^ 2 = 1 -> ∀ t : ℝ,
          1 - c * (N : ℝ) ^ (-epsilon) < t ->
            (Ne chi 1 ∨ Ne t 1) -> Ne (chi.LFunction t) 0 := by
  intro epsilon hepsilon
  obtain ⟨primitiveCoefficient, hprimitiveCoefficientPos,
    hprimitiveCoefficientSmall, hprimitive⟩ :=
      exists_primitiveQuadratic_zeroExclusionCoefficient epsilon hepsilon
  obtain ⟨eta, heta, hzeta⟩ := exists_riemannZeta_neg_left
  let c := min primitiveCoefficient eta
  have hcPos : 0 < c := lt_min hprimitiveCoefficientPos heta
  have hcPrimitive : c ≤ primitiveCoefficient := min_le_left _ _
  have hcEta : c ≤ eta := min_le_right _ _
  have hcSmall : c ≤ 1 / 16 := hcPrimitive.trans hprimitiveCoefficientSmall
  refine ⟨c, hcPos, ?_⟩
  intro N _ chi hchiSquare t ht hregular
  by_cases hchi : chi = 1
  · subst chi
    have htNe : Ne t 1 := by simpa using hregular
    exact principal_zeroExclusion_of_zetaInterval hepsilon hcPos hcSmall hcEta
      hzeta N t ht htNe
  · have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.pos N
    have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
    have hpowerNonneg : 0 ≤ (N : ℝ) ^ (-epsilon) :=
      Real.rpow_nonneg hNpos.le _
    have hwidthCompare :
        c * (N : ℝ) ^ (-epsilon) ≤
          primitiveCoefficient * (N : ℝ) ^ (-epsilon) :=
      mul_le_mul_of_nonneg_right hcPrimitive hpowerNonneg
    exact nonprincipalQuadratic_zeroExclusion_of_primitive hepsilon
      hprimitiveCoefficientPos hprimitiveCoefficientSmall hprimitive
      N chi hchiSquare hchi t (by linarith)

/-- The directly consumable nonprincipal form of Siegel zero exclusion. -/
theorem siegelZeroExclusion_nonprincipal :
    ∀ epsilon > (0 : ℝ), ∃ c > (0 : ℝ),
      ∀ (N : ℕ) [NeZero N] (chi : DirichletCharacter ℂ N),
        chi ^ 2 = 1 -> Ne chi 1 -> ∀ t : ℝ,
          1 - c * (N : ℝ) ^ (-epsilon) < t ->
            Ne (chi.LFunction t) 0 := by
  intro epsilon hepsilon
  obtain ⟨c, hc, hzero⟩ := siegelZeroExclusion epsilon hepsilon
  refine ⟨c, hc, ?_⟩
  intro N _ chi hchiSquare hchi t ht
  exact hzero N chi hchiSquare t ht (.inl hchi)

end BombieriVinogradov.SiegelWalfisz
