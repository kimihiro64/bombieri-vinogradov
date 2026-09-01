import BombieriVinogradov.Assembly.VaughanMeanValue.VaughanMeanAggregate

/-!
# Real-to-natural endpoint identity

The real-cutoff primitive-character mean is definitionally the natural
endpoint mean at `floor x`. Majorant comparison and theorem assembly are owned
by separate modules.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.VaughanMeanValue

theorem maximalPsiNorm_eq_naturalEndpoint
    (x : Real) (q : Nat) (chi : DirichletCharacter Complex q) :
    maximalPsiNorm x chi = maximalMangoldtCharacterNorm (Nat.floor x) q chi := by
  rfl

theorem primitivePsiMean_eq_vaughanMean (x : Real) (Q : Nat) :
    primitivePsiMean x Q = vaughanMean (Nat.floor x) Q := by
  rfl

end BombieriVinogradov.VaughanMeanValue
