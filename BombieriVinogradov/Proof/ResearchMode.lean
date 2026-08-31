import BombieriVinogradov.Helpers.ResearchMode

/-!
# Research-mode proof wiring

No Bombieri-Vinogradov proof is advertised from this module.
-/

namespace BombieriVinogradov

/-- Proof-side wiring for the explicitly temporary research placeholder. -/
theorem researchPlaceholderProof : FormalizationTargetPending := by
  exact formalizationTargetPending

end BombieriVinogradov
