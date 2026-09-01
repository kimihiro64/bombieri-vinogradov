import BombieriVinogradov.Helpers.DirichletCharacter.PrimitiveInverseFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedConjugation
import BombieriVinogradov.Proof.SiegelWalfisz.ZeroFree.CompletedHadamardConstantEndpointRelation

/-!
# Complex conjugation of completed-function Hadamard constants

This module combines the logarithmic-derivative conjugation identity with the
characterization of the canonical Hadamard constant as the value at zero.
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace BombieriVinogradov.SiegelWalfisz

theorem symmetricCompletedLFunction_hadamardConstant_inv_eq_conj
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : chi ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive chi)
    {Bchi Binv : Complex}
    (hBchi : IsCompletedLFunctionHadamardConstant chi Bchi)
    (hBinv : IsCompletedLFunctionHadamardConstant chi⁻¹ Binv) :
    Binv = conj Bchi := by
  have hInverseNe : chi⁻¹ ≠ 1 :=
    BombieriVinogradov.DirichletCharacter.inv_ne_one_of_ne_one hchi
  have hPrimitiveInv : DirichletCharacter.IsPrimitive chi⁻¹ :=
    BombieriVinogradov.DirichletCharacter.IsPrimitive.inv hPrimitive
  have hBchiValue :
      logDeriv (symmetricCompletedLFunction chi) 0 = Bchi :=
    logDeriv_symmetricCompletedLFunction_zero_eq_hadamardConstant
      hchi hPrimitive hBchi
  have hBinvValue :
      logDeriv (symmetricCompletedLFunction chi⁻¹) 0 = Binv :=
    logDeriv_symmetricCompletedLFunction_zero_eq_hadamardConstant
      hInverseNe hPrimitiveInv hBinv
  calc
    Binv = logDeriv (symmetricCompletedLFunction chi⁻¹) 0 := hBinvValue.symm
    _ = conj (logDeriv (symmetricCompletedLFunction chi) (conj 0)) :=
      logDeriv_symmetricCompletedLFunction_inv_eq_conj_conj hchi 0
    _ = conj (logDeriv (symmetricCompletedLFunction chi) 0) := by norm_num
    _ = conj Bchi := by rw [hBchiValue]

end BombieriVinogradov.SiegelWalfisz
