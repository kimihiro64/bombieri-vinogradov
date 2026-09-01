import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor

/-!
# Constructing a multiplicity-aware divisor index from a zero

This reusable analytic helper packages an ordinary nonzero zero of a nonzero
entire function as one of PNTAnd's divisor indices.
-/

set_option autoImplicit false

namespace BombieriVinogradov

theorem exists_divisorZeroIndex₀_val_eq_of_apply_eq_zero
    {f : Complex → Complex} (hf : Differentiable Complex f)
    (hnot : exists w : Complex, f w ≠ 0) {z : Complex}
    (hz : z ≠ 0) (hfz : f z = 0) :
    exists p : Complex.Hadamard.divisorZeroIndex₀ f (Set.univ : Set Complex),
      Complex.Hadamard.divisorZeroIndex₀_val p = z := by
  have hnotTop : analyticOrderAt f z ≠ ⊤ :=
    Complex.Hadamard.analyticOrderAt_ne_top_of_exists_ne_zero hf hnot z
  have hOrderNe : analyticOrderNatAt f z ≠ 0 := by
    intro hOrder
    have hENat : (analyticOrderNatAt f z : ENat) = 0 := by
      simp [hOrder]
    have hOrderZero : analyticOrderAt f z = 0 := by
      have hCast : (analyticOrderNatAt f z : ENat) = analyticOrderAt f z :=
        Nat.cast_analyticOrderNatAt (f := f) (z₀ := z) hnotTop
      simpa [hCast] using hENat
    have hAnalytic : AnalyticAt Complex f z :=
      Differentiable.analyticAt (f := f) hf z
    exact ((hAnalytic.analyticOrderAt_eq_zero).1 hOrderZero) hfz
  have hCardPos :
      0 < (Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := f) z).card := by
    have hCard :=
      Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
        (hf := hf) (z₀ := z) hz
    have hOrderPos : 0 < analyticOrderNatAt f z := Nat.pos_of_ne_zero hOrderNe
    simpa [hCard] using hOrderPos
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hCardPos
  exact Exists.intro p
    ((Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
      (f := f) (z₀ := z) p).1 hp)

end BombieriVinogradov
