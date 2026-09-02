import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The complex-power difference quotient at the origin

This module owns the first-order cancellation in the positive-base Perron
kernel. It proves that `((x^s)-1)/s` has a finite punctured limit and
nonnegative meromorphic order at zero.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The difference quotient that removes the constant term of `x^s` at
zero. -/
def originCpowDifferenceQuotient (x : Nat) (s : Complex) : Complex :=
  ((x : Complex) ^ s - 1) / s

/-- The positive-base complex-power difference quotient is meromorphic. -/
theorem meromorphic_originCpowDifferenceQuotient
    (x : Nat) (hx : 0 < x) :
    Meromorphic (originCpowDifferenceQuotient x) := by
  have hxC : Ne (x : Complex) 0 := by
    exact_mod_cast hx.ne'
  intro s
  have hPow :
      AnalyticAt Complex (fun z : Complex => (x : Complex) ^ z) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hxC]
    fun_prop
  have hNum :
      MeromorphicAt (fun z : Complex => (x : Complex) ^ z - 1) s :=
    (hPow.sub (by fun_prop)).meromorphicAt
  have hDen : MeromorphicAt (fun z : Complex => z) s := by
    fun_prop
  exact hNum.div hDen

/-- The punctured limit of `((x^s)-1)/s` at zero is `log x`. -/
theorem tendsto_originCpowDifferenceQuotient_zero
    (x : Nat) (hx : 0 < x) :
    Filter.Tendsto (originCpowDifferenceQuotient x)
      (nhdsWithin 0 (Set.compl ({0} : Set Complex)))
      (nhds (Complex.log (x : Complex))) := by
  have hxC : Ne (x : Complex) 0 := by
    exact_mod_cast hx.ne'
  have hDeriv :
      HasDerivAt (fun z : Complex => (x : Complex) ^ z)
        (Complex.log (x : Complex)) 0 := by
    simpa using
      (Complex.hasStrictDerivAt_const_cpow
        (x := (x : Complex)) (y := (0 : Complex)) (Or.inl hxC)).hasDerivAt
  have hFunction :
      originCpowDifferenceQuotient x =
        slope (fun z : Complex => (x : Complex) ^ z) 0 := by
    funext z
    simp [originCpowDifferenceQuotient, slope, smul_eq_mul, div_eq_mul_inv,
      mul_comm]
  rw [hFunction]
  exact hDeriv.tendsto_slope

/-- The removable difference quotient has nonnegative meromorphic order at
zero. -/
theorem meromorphicOrderAt_originCpowDifferenceQuotient_zero_nonneg
    (x : Nat) (hx : 0 < x) :
    0 <= meromorphicOrderAt (originCpowDifferenceQuotient x) 0 := by
  apply (tendsto_nhds_iff_meromorphicOrderAt_nonneg
    (meromorphic_originCpowDifferenceQuotient x hx 0)).mp
  exact Exists.intro (Complex.log (x : Complex))
    (tendsto_originCpowDifferenceQuotient_zero x hx)

end BombieriVinogradov.SiegelWalfisz
