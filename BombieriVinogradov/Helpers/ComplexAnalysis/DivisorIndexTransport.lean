import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Defs
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorIndex

/-!
# Transporting a nonzero divisor index at equal multiplicity

The complex value is preserved while its finite multiplicity label is
cast along an exact equality. No equality of unfiltered zero sets is assumed.
-/
set_option autoImplicit false

namespace BombieriVinogradov.ComplexAnalysis

theorem exists_nonzeroDivisorIndex_of_multiplicity_eq
    {f g : Complex -> Complex}
    (p : {q : Complex.Hadamard.divisorZeroIndex f (Set.univ : Set Complex) //
      Ne q.1 0})
    (h : Int.toNat (MeromorphicOn.divisor f (Set.univ : Set Complex) p.1.1) =
      Int.toNat (MeromorphicOn.divisor g (Set.univ : Set Complex) p.1.1)) :
    exists q : {q : Complex.Hadamard.divisorZeroIndex g (Set.univ : Set Complex) //
      Ne q.1 0}, q.1.1 = p.1.1 := by
  exact Exists.intro
    (Subtype.mk (Sigma.mk p.1.1 (Fin.cast h p.1.2)) p.2) rfl

end BombieriVinogradov.ComplexAnalysis
