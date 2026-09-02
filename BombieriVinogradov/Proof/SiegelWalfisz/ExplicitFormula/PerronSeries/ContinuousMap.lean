import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Expansion

/-!
# Continuous Perron-series summands

This module packages each vertical-line Dirichlet summand as a continuous map
of the height parameter. The positive real part keeps both complex-power
bases and the Perron denominator away from zero.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- One Perron-series summand along the vertical line with real part `c`. -/
def perronSeriesFunction {N : Nat}
    (chi : DirichletCharacter Complex N) (x n : Nat) (c : Real) (t : Real) : Complex :=
  explicitFormulaDirichletTerm chi x n (c + t * Complex.I)

/-- Every Perron-series summand is continuous in the vertical parameter when
`x` is positive and the vertical line lies to the right of `1`. -/
theorem perronSeriesFunction_continuous
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c : Real} (hc : 1 < c) :
    Continuous (perronSeriesFunction chi x n c) := by
  by_cases hn : n = 0
  case pos =>
    subst n
    change Continuous (fun t : Real =>
      explicitFormulaDirichletTerm chi x 0 (c + t * Complex.I))
    simpa [explicitFormulaDirichletTerm, LSeries.term_def] using
      (continuous_const : Continuous (fun _ : Real => (0 : Complex)))
  case neg =>
    have hnC : Ne (n : Complex) 0 := by exact_mod_cast hn
    have hxC : Ne (x : Complex) 0 := by exact_mod_cast (Nat.ne_of_gt hx)
    have hsNe : forall t : Real, Ne ((c : Complex) + t * Complex.I) 0 := by
      intro t h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        mul_one, sub_self, add_zero, Complex.zero_re] at hre
      linarith
    have hpath : Continuous (fun t : Real =>
        (c : Complex) + t * Complex.I) := by
      fun_prop
    have hnPow : Continuous (fun t : Real =>
        (n : Complex) ^ ((c : Complex) + t * Complex.I)) :=
      hpath.const_cpow (Or.inl hnC)
    have hxPow : Continuous (fun t : Real =>
        (x : Complex) ^ ((c : Complex) + t * Complex.I)) :=
      hpath.const_cpow (Or.inl hxC)
    change Continuous (fun t : Real =>
      explicitFormulaDirichletTerm chi x n (c + t * Complex.I))
    simp only [explicitFormulaDirichletTerm, LSeries.term_def, hn, if_false]
    exact (continuous_const.div hnPow (fun _ =>
        Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))).mul
      (hxPow.div hpath hsNe)

/-- A Perron-series summand packaged in the continuous-map normed space. -/
def perronSeriesContinuousMap
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    (n : Nat) {c : Real} (hc : 1 < c) : C(Real, Complex) :=
  ContinuousMap.mk (perronSeriesFunction chi x n c)
    (perronSeriesFunction_continuous chi hx n hc)

end BombieriVinogradov.SiegelWalfisz
