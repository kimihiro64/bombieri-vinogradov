import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Unit-point Perron source-term bound

At the centering point x equals one, each source Perron majorant term is
bounded by the corresponding von Mangoldt L-series norm term.
-/
set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- Pointwise domination of the x equals one Perron source majorant. -/
theorem sourcePerronErrorMajorantTerm_one_le_vonMangoldtTerm
    (c T : Real) (n : Nat) :
    sourcePerronErrorMajorantTerm 1 c T n <=
      norm (LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (c : Complex) n) := by
  rw [norm_LSeriesTerm_vonMangoldt_eq]
  by_cases hnZero : n = 0
  case pos =>
    subst n
    simp [sourcePerronErrorMajorantTerm]
  case neg =>
    by_cases hnOne : n = 1
    case pos =>
      subst n
      simp [sourcePerronErrorMajorantTerm]
    case neg =>
      have hnCastZero : Ne (n : Real) 0 := Nat.cast_ne_zero.mpr hnZero
      have hRatio : Ne (((1 : Nat) : Real) / (n : Real)) 1 := by
        intro h
        have hEq : ((1 : Nat) : Real) = (n : Real) :=
          (div_eq_one_iff_eq hnCastZero).mp h
        have hnCastOne : (n : Real) = 1 := by simpa using hEq.symm
        exact (Nat.cast_ne_one.mpr hnOne) hnCastOne
      rw [sourcePerronErrorMajorantTerm, if_neg hnZero, if_neg hRatio]
      rw [Nat.cast_one]
      rw [Real.div_rpow zero_le_one (Nat.cast_nonneg n) c]
      rw [Real.one_rpow]
      have hScale : 0 <= 1 / (n : Real) ^ c :=
        div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg n) c)
      have hMin :
          min 1 (1 / (Real.pi * T *
            abs (Real.log ((1 : Real) / (n : Real))))) <= 1 :=
        min_le_left 1 _
      have hInner :
          1 / (n : Real) ^ c *
              min 1 (1 / (Real.pi * T *
                abs (Real.log ((1 : Real) / (n : Real))))) <=
            1 / (n : Real) ^ c := by
        calc
          1 / (n : Real) ^ c *
                min 1 (1 / (Real.pi * T *
                  abs (Real.log ((1 : Real) / (n : Real))))) <=
              (1 / (n : Real) ^ c) * 1 :=
            mul_le_mul_of_nonneg_left hMin hScale
          _ = 1 / (n : Real) ^ c := mul_one _
      exact mul_le_mul_of_nonneg_left (by simpa using hInner)
        ArithmeticFunction.vonMangoldt_nonneg

end BombieriVinogradov.SiegelWalfisz
