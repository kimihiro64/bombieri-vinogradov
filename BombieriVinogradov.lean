import BombieriVinogradov.Assembly.ResearchMode
import BombieriVinogradov.Assembly.VaughanMeanValue.All
import BombieriVinogradov.Assembly.VaughanMeanValue.RealEndpoint.Main
import BombieriVinogradov.Definitions.CharacterSums
import BombieriVinogradov.Definitions.Statement
import BombieriVinogradov.Definitions.VaughanMeanValue
import BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor
import BombieriVinogradov.Helpers.LogCutoff.Integer
import BombieriVinogradov.Proof.LargeSieve.All
import BombieriVinogradov.Proof.SiegelWalfisz.All
import BombieriVinogradov.Proof.VaughanIdentity.Main

/-!
# Public library root

This module exports the source-aligned target definitions, the proved large
sieve and Vaughan identity branches, the Vaughan mean-value theorem, and the
coefficient, analytic-product, and pole-subtraction theorems from Siegel's proof.
It also exports Strombergsson's source-form positivity lemma near the pole,
including its coefficient, residue, truncation, and tail infrastructure, and
the resulting non-effective lower bound and zero exclusion for quadratic
Dirichlet L-functions. The explicit-formula branch additionally exports the
optimized Perron approximation and its exact finite contour decomposition.
-/
