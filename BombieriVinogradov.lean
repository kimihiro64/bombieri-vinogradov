import BombieriVinogradov.Assembly.ResearchMode
import BombieriVinogradov.Assembly.VaughanMeanValue.All
import BombieriVinogradov.Assembly.VaughanMeanValue.RealEndpoint.Main
import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Definitions.Statement
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor
import BombieriVinogradov.Helpers.LogCutoff.Integer
import BombieriVinogradov.Proof.LargeSieve.All
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.Main
import BombieriVinogradov.Proof.VaughanIdentity.Main

/-!
# Public library root

This module exports the source-aligned target definitions, the proved large
sieve and Vaughan identity branches, the Vaughan mean-value theorem, and the
coefficient, analytic-product, and pole-subtraction theorems from Siegel's proof.
It also exports the uniform source-circle and Taylor-coefficient bounds for the
pole-subtracted product.
-/
