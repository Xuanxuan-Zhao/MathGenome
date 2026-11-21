import MathGenome.Internal.Specs.D07.Ch22.NoetherianEquivalences
import MathGenome.Internal.D07.Ch16.MapsSubmodules

/-!
The three Noetherian conditions and the ring criterion from
K07.22.noetherian_equivalences (paper.tex:6944–6972).
The library equivalences are transported from order homomorphisms and
the absence of a strictly larger member to the explicit source conditions.
-/

universe u v

namespace D07.Ch22.NoetherianEquivalences

open Specs.D07.Ch22.NoetherianEquivalences

theorem noetherianCharacterization : NoetherianCharacterization.{u, v} := by
  intro R _ M _ _
  constructor
  · intro h U hU
    obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr h
      (⟨U, hU⟩ : ℕ →o Submodule R M)
    exact ⟨n, fun m hm => (hn m hm).symm⟩
  · intro h
    apply monotone_stabilizes_iff_noetherian.mp
    intro U
    obtain ⟨n, hn⟩ := h U U.monotone
    exact ⟨n, fun m hm => (hn m hm).symm⟩

theorem chainConditionIffFiniteGeneration :
    ChainConditionIffFiniteGeneration.{u, v} := by
  intro R _ M _ _
  exact (noetherianCharacterization R M).symm.trans isNoetherian_def

theorem finiteGenerationIffMaximalMember :
    FiniteGenerationIffMaximalMember.{u, v} := by
  intro R _ M _ _
  constructor
  · intro h S hS
    obtain ⟨U, hUS, hU⟩ := set_has_maximal_iff_noetherian.mpr
      (isNoetherian_def.mpr h) S hS
    refine ⟨U, hUS, fun V hVS hUV => ?_⟩
    exact (eq_of_le_of_not_lt hUV (hU V hVS)).symm
  · intro h
    apply isNoetherian_def.mp
    apply set_has_maximal_iff_noetherian.mp
    intro S hS
    obtain ⟨U, hUS, hU⟩ := h S hS
    refine ⟨U, hUS, fun V hVS hUV => ?_⟩
    exact hUV.ne' (hU V hVS hUV.le)

theorem noetherianRingRegularModule : NoetherianRingRegularModule.{u} := by
  intro R _
  exact isNoetherianRing_iff

theorem noetherianRingIffIdealsFG : NoetherianRingIffIdealsFG.{u} := by
  intro R _
  exact isNoetherianRing_iff_ideal_fg R

end D07.Ch22.NoetherianEquivalences
