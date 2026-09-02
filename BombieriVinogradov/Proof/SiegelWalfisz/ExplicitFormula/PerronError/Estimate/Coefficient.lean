import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Definitions

/-!
# Removing the character coefficient

This module bounds a twisted von Mangoldt coefficient by the underlying von
Mangoldt weight and transfers that inequality to the Perron majorant.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- A Dirichlet character has norm at most one, so twisting cannot increase a
von Mangoldt coefficient. -/
theorem norm_twistedMangoldtSequence_le_vonMangoldt
    {N : Nat} (chi : DirichletCharacter Complex N) (n : Nat) :
    norm (twistedMangoldtSequence chi n) <= ArithmeticFunction.vonMangoldt n := by
  unfold twistedMangoldtSequence
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
    (chi.norm_le_one n)

/-- The character-dependent exact majorant is bounded termwise by the source
von Mangoldt majorant. -/
theorem scalarPerronErrorMajorantTerm_le_source
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (hT : 0 < T) (n : Nat) :
    scalarPerronErrorMajorantTerm chi x c T n <=
      sourcePerronErrorMajorantTerm x c T n := by
  by_cases hn : n = 0
  case pos =>
    simp [scalarPerronErrorMajorantTerm, sourcePerronErrorMajorantTerm, hn]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      simp only [scalarPerronErrorMajorantTerm,
        sourcePerronErrorMajorantTerm, hn, hRatio, if_false, if_true]
      apply mul_le_mul_of_nonneg_right
        (norm_twistedMangoldtSequence_le_vonMangoldt chi n)
      positivity
    case neg =>
      simp only [scalarPerronErrorMajorantTerm,
        sourcePerronErrorMajorantTerm, hn, hRatio, if_false]
      apply mul_le_mul_of_nonneg_right
        (norm_twistedMangoldtSequence_le_vonMangoldt chi n)
      have hReciprocal : 0 <= 1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))) := by
        positivity
      exact mul_nonneg (Real.rpow_nonneg hRatioPos.le c)
        (le_min zero_le_one hReciprocal)

end BombieriVinogradov.SiegelWalfisz
