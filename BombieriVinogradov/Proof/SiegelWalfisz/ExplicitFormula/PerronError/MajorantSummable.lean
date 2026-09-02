import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.ErrorDefinitions

/-!
# Summability of the Perron error majorant

This module dominates the exact source majorant by an absolutely convergent
twisted von Mangoldt L-series plus a single endpoint term.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The exact majorant is bounded by an L-series norm term plus a singleton
endpoint correction. -/
theorem scalarPerronErrorMajorantTerm_le_summable
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (n : Nat) :
    scalarPerronErrorMajorantTerm chi x c T n <=
      (x : Real) ^ c *
          norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n) +
        if n = x then
          norm (twistedMangoldtSequence chi n) * (c / (Real.pi * T))
        else 0 := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [scalarPerronErrorMajorantTerm, LSeries.term_def,
      (Nat.ne_of_gt hx).symm]
  case neg =>
    have hnRealNe : Ne (n : Real) 0 := by exact_mod_cast hn
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      have hxnReal : (x : Real) = (n : Real) :=
        (div_eq_one_iff_eq hnRealNe).mp hRatio
      have hxn : x = n := by exact_mod_cast hxnReal
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_pos hRatio,
        if_pos hxn.symm]
      exact le_add_of_nonneg_left (mul_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg x) c) (norm_nonneg _))
    case neg =>
      have hnx : Ne n x := by
        intro h
        subst n
        apply hRatio
        exact div_self (by exact_mod_cast (Nat.ne_of_gt hx))
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_neg hRatio,
        if_neg hnx]
      calc
        norm (twistedMangoldtSequence chi n) *
            (((x : Real) / (n : Real)) ^ c *
              min 1 (1 / (Real.pi * T *
                abs (Real.log ((x : Real) / (n : Real)))))) <=
            norm (twistedMangoldtSequence chi n) *
              (((x : Real) / (n : Real)) ^ c * 1) := by
          gcongr
          exact min_le_left _ _
        _ = (x : Real) ^ c *
            norm (LSeries.term (twistedMangoldtSequence chi)
              (c : Complex) n) := by
          rw [LSeries.term_def, if_neg hn, norm_div,
            Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using ne_of_gt hc),
            Real.div_rpow (Nat.cast_nonneg x) (Nat.cast_nonneg n) c]
          simp only [Complex.ofReal_re, mul_one]
          ring
        _ = (x : Real) ^ c *
              norm (LSeries.term (twistedMangoldtSequence chi)
                (c : Complex) n) + 0 := by
          ring

/-- Every exact scalar Perron error majorant is nonnegative. -/
theorem scalarPerronErrorMajorantTerm_nonneg
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 0 < c) (hT : 0 < T) (n : Nat) :
    0 <= scalarPerronErrorMajorantTerm chi x c T n := by
  by_cases hn : n = 0
  case pos =>
    simp [scalarPerronErrorMajorantTerm, hn]
  case neg =>
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hRatioPos : 0 < (x : Real) / (n : Real) :=
      div_pos (by exact_mod_cast hx) (by exact_mod_cast hnPos)
    by_cases hRatio : (x : Real) / (n : Real) = 1
    case pos =>
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_pos hRatio]
      positivity
    case neg =>
      rw [scalarPerronErrorMajorantTerm, if_neg hn, if_neg hRatio]
      have hReciprocal : 0 <= 1 / (Real.pi * T *
          abs (Real.log ((x : Real) / (n : Real)))) := by
        positivity
      exact mul_nonneg (norm_nonneg _)
        (mul_nonneg (Real.rpow_nonneg hRatioPos.le c)
          (le_min zero_le_one hReciprocal))

/-- The exact scalar Perron error majorants form a summable sequence. -/
theorem summable_scalarPerronErrorMajorantTerm
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) (hT : 0 < T) :
    Summable (scalarPerronErrorMajorantTerm chi x c T) := by
  have hSequence : twistedMangoldtSequence chi =
      (fun n : Nat => chi n) *
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    funext n
    rfl
  have hLSeries : LSeriesSummable (twistedMangoldtSequence chi) (c : Complex) := by
    rw [hSequence]
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi (by simpa using hc)
  have hBase : Summable (fun n : Nat =>
      (x : Real) ^ c *
        norm (LSeries.term (twistedMangoldtSequence chi) (c : Complex) n)) :=
    hLSeries.norm.mul_left ((x : Real) ^ c)
  have hEndpoint : Summable (fun n : Nat =>
      if n = x then
        norm (twistedMangoldtSequence chi n) * (c / (Real.pi * T))
      else 0) := by
    have hFunction : (fun n : Nat =>
        if n = x then
          norm (twistedMangoldtSequence chi n) * (c / (Real.pi * T))
        else 0) = fun n : Nat =>
          if n = x then
            norm (twistedMangoldtSequence chi x) * (c / (Real.pi * T))
          else 0 := by
      funext n
      by_cases hnx : n = x
      case pos =>
        subst n
        rfl
      case neg =>
        simp [hnx]
    rw [hFunction]
    exact (hasSum_ite_eq x
      (norm (twistedMangoldtSequence chi x) * (c / (Real.pi * T)))).summable
  apply Summable.of_nonneg_of_le
    (fun n => scalarPerronErrorMajorantTerm_nonneg chi hx
      (lt_trans zero_lt_one hc) hT n)
    (fun n => scalarPerronErrorMajorantTerm_le_summable chi hx
      (lt_trans zero_lt_one hc) n)
    (hBase.add hEndpoint)

end BombieriVinogradov.SiegelWalfisz
