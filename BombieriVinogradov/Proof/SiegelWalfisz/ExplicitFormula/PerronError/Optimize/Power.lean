import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Line

/-!
# Power identity on the optimized Perron line

This module evaluates `x ^ c` exactly at `c = 1 + 1 / log x`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- At the optimized line, `x ^ c` is exactly `x * exp 1`. -/
theorem rpow_optimizedPerronLine_eq {x : Nat} (hx : 2 < x) :
    (x : Real) ^ optimizedPerronLine x =
      (x : Real) * Real.exp 1 := by
  have hxPos : 0 < x := lt_trans zero_lt_two hx
  have hxReal : 0 < (x : Real) := by exact_mod_cast hxPos
  have hxNeOne : Ne (x : Real) 1 := by
    have hxThree : (3 : Real) <= (x : Real) := by exact_mod_cast hx
    linarith
  unfold optimizedPerronLine
  rw [Real.rpow_add hxReal, Real.rpow_one, one_div]
  rw [Real.rpow_inv_log hxReal hxNeOne]

end BombieriVinogradov.SiegelWalfisz
