import BombieriVinogradov.Assembly.SiegelWalfisz.CharacterEstimate.PrimitiveMain
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.ImprimitiveTransfer
import BombieriVinogradov.Proof.SiegelWalfisz.CharacterEstimate.UniformData
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Definitions
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.FaithfulChoice
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Exceptional.ZeroFreeData
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The complete uniform exceptional character estimate

All constants are fixed before the modulus, nonprincipal character,
endpoint and faithful choice. Primitive estimates and both correction
bounds share the same zero-free constant and exponential rate.
-/
set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem characterChebyshevExceptional :
    exists c a C : Real, CharacterEstimateData c a C := by
  classical
  choose c a C0 hc ha hHalf hRate hC0 hData hPrimitive using
    primitiveCharacterChebyshevExceptional
  have hC : 0 < C0 + 48 / Real.log (2 : Real) + 4 / 3 := by
    have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    positivity
  have hRateWeak : a <= c / 4 := by linarith
  refine Exists.intro c (Exists.intro a
    (Exists.intro (C0 + 48 / Real.log (2 : Real) + 4 / 3) ?_))
  refine {
    c_pos := hc
    a_pos := ha
    a_half := hHalf
    a_gap := hRate
    C_pos := hC
    zeroFree := hData
    estimate := ?_
  }
  intro N inst chi hchi x hx hMod e hChoice
  let _ : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  have hN := BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one chi hchi
  have hPrimitiveNe : Ne chi.primitiveCharacter 1 :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hConductor : (chi.conductor : Real) <= (N : Real) := Nat.cast_le.mpr
    (BombieriVinogradov.DirichletCharacter.conductor_le_level chi)
  have hPrimitiveMod : (chi.conductor : Real) <=
      Real.exp (Real.sqrt (Real.log x)) := hConductor.trans hMod
  choose ep hPrimitiveChoice using exists_faithfulExceptionalChoice c chi.primitiveCharacter
  have hPrimitiveBound := hPrimitive hPrimitiveNe chi.primitiveCharacter_isPrimitive
    hx hPrimitiveMod ep hPrimitiveChoice
  exact characterChebyshevExceptional_of_primitive_bound hc hHalf hRateWeak hN
    chi hchi (hData chi.primitiveCharacter hPrimitiveNe) e ep hChoice
      hPrimitiveChoice hx hMod hPrimitiveBound

end BombieriVinogradov.SiegelWalfisz
