import BombieriVinogradov.Proof.SiegelWalfisz.SiegelProduct.Cauchy.CharacterBlockSeries

/-!
# Summability of shifted character-block norms

This module owns only the summability input for the positive-index tail.
-/

set_option autoImplicit false

namespace BombieriVinogradov.SiegelWalfisz

theorem characterLBlock_norm_summable_on_domain {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1) {s : ℂ}
    (hsDomain : s ∈ siegelAnalyticDomain) :
    Summable (fun k : ℕ ↦ ‖characterLBlock chi k s‖) :=
  (characterLBlockMajorant_summable N).of_nonneg_of_le
    (fun _k ↦ norm_nonneg _) fun k ↦ norm_characterLBlock_le chi hchi k hsDomain

theorem characterLBlock_tail_norm_summable {N : ℕ} [NeZero N]
    (chi : DirichletCharacter ℂ N) (hchi : Ne chi 1) {s : ℂ}
    (hsDomain : s ∈ siegelAnalyticDomain) :
    Summable (fun k : ℕ ↦ ‖characterLBlock chi (k + 1) s‖) :=
  (characterLBlock_norm_summable_on_domain chi hchi hsDomain).comp_injective
    (fun a b h ↦ by omega)

end BombieriVinogradov.SiegelWalfisz
