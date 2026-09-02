import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronSeries.Majorant

/-!
# Interchange of the Perron series and finite vertical integration

The summable compact sup-norm majorant permits termwise integration of the
twisted von Mangoldt series along every finite vertical segment.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The series of vertical integrals equals the vertical integral of the
twisted von Mangoldt series. -/
theorem tsum_intervalIntegral_perronSeriesFunction
    {N : Nat} (chi : DirichletCharacter Complex N) {x : Nat} (hx : 0 < x)
    {c T : Real} (hc : 1 < c) :
    tsum (fun n : Nat => intervalIntegral
      (perronSeriesFunction chi x n c) (-T) T MeasureTheory.volume) =
      intervalIntegral (fun t : Real =>
        tsum (fun n : Nat => perronSeriesFunction chi x n c t))
        (-T) T MeasureTheory.volume := by
  exact intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (summable_norm_restrict_perronSeriesContinuousMap chi hx hc)

end BombieriVinogradov.SiegelWalfisz
