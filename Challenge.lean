import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting

set_option autoImplicit false

/-!
# Bombieri--Vinogradov challenge

This boundary reproduces the exact proposition consumed by `PrimeGapsLib`
commit `1faa7b14e82ddebc2772dfb9153922f01b106477`, using only direct Mathlib
imports.
-/

open Finset Nat Real

noncomputable def Real.primeCountingZMod (x : ℝ) (q : ℕ) (a : ZMod q) : ℕ :=
  {p : ℕ | p.Prime ∧ (p : ZMod q) = a ∧ p ≤ x}.ncard

noncomputable def pi (x : ℝ) : ℝ :=
  ⌊x⌋₊.primeCounting

def BombieriVinogradov : Prop :=
  ∀ theta < (1 / 2 : ℝ), ∀ A ≥ (1 : ℝ), ∃ c > (0 : ℝ), ∀ x ≥ (3 : ℝ),
    ∑ q ∈ Icc (1 : ℕ) ⌊x ^ theta⌋₊,
      ⨆ a : (ZMod q)ˣ,
        |((Real.primeCountingZMod x q a : ℝ) - pi x / q.totient : ℝ)| ≤
          c * x / x.log ^ A

namespace BombieriVinogradov

theorem bombieriVinogradov : _root_.BombieriVinogradov := by
  sorry

end BombieriVinogradov
