import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.LogDerivativeRemainder
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Origin logarithmic-derivative remainder value

This module packages the canonical finite punctured limit of the logarithmic
derivative after its exact origin principal part is removed.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The canonical finite value approached by the origin logarithmic-derivative
remainder on the punctured neighborhood of zero. -/
def lFunctionOriginLogDerivativeRemainderValue
    {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N) : Complex :=
  Filter.limUnder (nhdsWithin 0 (Compl.compl ({0} : Set Complex)))
    (lFunctionOriginLogDerivativeRemainder chi)

/-- The origin logarithmic-derivative remainder converges to its canonical
finite value on the punctured neighborhood of zero. -/
theorem tendsto_lFunctionOriginLogDerivativeRemainder_zero
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) :
    Filter.Tendsto (lFunctionOriginLogDerivativeRemainder chi)
      (nhdsWithin 0 (Compl.compl ({0} : Set Complex)))
      (nhds (lFunctionOriginLogDerivativeRemainderValue chi)) := by
  have hex :
      exists c, Filter.Tendsto (lFunctionOriginLogDerivativeRemainder chi)
        (nhdsWithin 0 (Compl.compl ({0} : Set Complex))) (nhds c) :=
    tendsto_nhds_of_meromorphicOrderAt_nonneg
      (meromorphicAt_lFunctionOriginLogDerivativeRemainder hchi)
      (meromorphicOrderAt_lFunctionOriginLogDerivativeRemainder_nonneg hchi)
  simpa [lFunctionOriginLogDerivativeRemainderValue] using
    tendsto_nhds_limUnder hex

end BombieriVinogradov.SiegelWalfisz
