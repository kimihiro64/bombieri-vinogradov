import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Definitions

/-!
# Perron endpoint bound

This module isolates the single `n = x` term, which uses the endpoint branch
of the truncated Perron estimate rather than a logarithmic denominator.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The singleton endpoint contribution to the source Perron majorant. -/
def endpointPerronBound (x : Nat) (c T : Real) (n : Nat) : Real :=
  if n = x then
    ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T))
  else 0

/-- At `n = x`, the source majorant is exactly the endpoint contribution. -/
theorem sourcePerronErrorMajorantTerm_self
    {x : Nat} (hx : 0 < x) (c T : Real) :
    sourcePerronErrorMajorantTerm x c T x =
      ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := by
  have hxNe : Ne (x : Real) 0 := by exact_mod_cast Nat.ne_of_gt hx
  rw [sourcePerronErrorMajorantTerm, if_neg (Nat.ne_of_gt hx),
    if_pos (div_self hxNe)]

/-- The endpoint bound is nonnegative when `c` and `T` are positive. -/
theorem endpointPerronBound_nonneg
    (x : Nat) {c T : Real} (hc : 0 <= c) (hT : 0 < T) (n : Nat) :
    0 <= endpointPerronBound x c T n := by
  unfold endpointPerronBound
  split
  case isTrue =>
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (div_nonneg hc (mul_nonneg Real.pi_pos.le hT.le))
  case isFalse =>
    exact le_refl 0

/-- The endpoint bound is a summable singleton. -/
theorem summable_endpointPerronBound (x : Nat) (c T : Real) :
    Summable (endpointPerronBound x c T) := by
  exact (hasSum_ite_eq x
    (ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)))).summable

/-- The endpoint bound sums to its value at `x`. -/
theorem tsum_endpointPerronBound_eq (x : Nat) (c T : Real) :
    tsum (endpointPerronBound x c T) =
      ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)) := by
  exact (hasSum_ite_eq x
    (ArithmeticFunction.vonMangoldt x * (c / (Real.pi * T)))).tsum_eq

end BombieriVinogradov.SiegelWalfisz
