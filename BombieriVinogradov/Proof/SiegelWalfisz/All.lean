import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Contour.Main
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Optimize.Main
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.Main
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Origin.KernelDifference
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.Finite
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.IntegrandSimpleAwayZero
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.LogDerivativeSimple
import BombieriVinogradov.Proof.SiegelWalfisz.Siegel.All
import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Positivity.Main

/-!
# Siegel-Walfisz proof exports

This declaration-free facade exports the independent zero-free,
Siegel-product, Perron, contour, and explicit-formula meromorphicity and finite
pole-set branches, including finite L-function order and simple poles for the
logarithmic derivative and the full integrand away from zero, without coupling
their internal proof modules. It also exports the first-order kernel
cancellation needed to regularize the origin.
-/
