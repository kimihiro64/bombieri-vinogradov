import BombieriVinogradov.Assembly.PrimeCountingConversion.Main
import BombieriVinogradov.Assembly.ResearchMode
import BombieriVinogradov.Assembly.SiegelWalfisz.Main
import BombieriVinogradov.Assembly.VaughanMeanValue.All
import BombieriVinogradov.Assembly.VaughanMeanValue.RealEndpoint.Main
import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor
import BombieriVinogradov.Helpers.LogCutoff.Integer
import BombieriVinogradov.Proof.LargeSieve.All
import BombieriVinogradov.Proof.SiegelWalfisz.All
import BombieriVinogradov.Proof.VaughanIdentity.Main

/-!
# Public library root

This module exports the source-aligned target definitions, the proved large
sieve, Vaughan identity and mean-value theorems, and the complete
character-form Siegel-Walfisz theorem with an absolute exponential rate.
The intermediate Siegel lower bound, quadratic zero exclusion, explicit
formula and finite contour results remain available through the proof facade.
-/
