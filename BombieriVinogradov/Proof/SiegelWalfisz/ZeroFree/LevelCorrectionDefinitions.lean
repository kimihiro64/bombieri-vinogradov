import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Euler factors for changing a Dirichlet-character level

These definitions isolate the finite Euler product removed when a character is
replaced by its primitive inducing character.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

noncomputable def levelCorrectionFactor {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (p : Nat) (s : Complex) : Complex :=
  1 - chi.primitiveCharacter p * (p : Complex) ^ (-s)

noncomputable def levelCorrection {N : Nat} [NeZero N]
    (chi : _root_.DirichletCharacter Complex N) (s : Complex) : Complex :=
  ∏ p ∈ N.primeFactors, levelCorrectionFactor chi p s

end BombieriVinogradov.SiegelWalfisz
