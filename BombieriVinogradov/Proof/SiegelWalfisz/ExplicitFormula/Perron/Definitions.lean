import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Truncated Perron data

This module owns the source step weight and normalized finite vertical integral
for the unsmoothed Perron kernel `y^s / s`.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The source step weight, including the half-weight at the endpoint. -/
def perronStepWeight (y : Real) : Real :=
  if y < 1 then 0 else if y = 1 then 1 / 2 else 1

/-- The normalized finite vertical integral of the unsmoothed Perron kernel. -/
def truncatedPerronKernel (y c T : Real) : Complex :=
  VIntegral' (fun s : Complex => (y : Complex) ^ s / s) c (-T) T

@[simp] theorem perronStepWeight_one : perronStepWeight 1 = 1 / 2 := by
  simp [perronStepWeight]

end BombieriVinogradov.SiegelWalfisz
