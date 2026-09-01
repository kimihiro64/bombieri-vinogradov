import BombieriVinogradov.Assembly.ResearchMode
import BombieriVinogradov.Assembly.VaughanMeanValue.Bilinear
import BombieriVinogradov.Assembly.VaughanMeanValue.MaximalBilinear
import BombieriVinogradov.Assembly.VaughanMeanValue.PolyaVinogradov
import BombieriVinogradov.Assembly.VaughanMeanValue.TypeIIBlock
import BombieriVinogradov.Assembly.VaughanMeanValue.TypeIOne
import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Definitions.Statement
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.LogCutoff.Integer
import BombieriVinogradov.Proof.LargeSieve.All
import BombieriVinogradov.Proof.VaughanIdentity.Main

/-!
# Public library root

This module exports the source-aligned target definitions, the proved large
sieve and Vaughan identity branches, and the maximal bilinear large-sieve
assembly used in Vaughan's mean-value theorem.
-/
