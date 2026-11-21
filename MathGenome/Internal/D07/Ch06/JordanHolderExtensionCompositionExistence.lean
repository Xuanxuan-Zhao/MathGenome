import MathGenome.Internal.Specs.D07.Ch06.JordanHolderExtensionCompositionExistence
import MathGenome.Internal.D07.Ch06.CompositionSeriesDefinition
import MathGenome.Internal.D07.Ch04.CorrespondenceTheorem
import Mathlib.Data.SetLike.Fintype
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.RelSeries

/-!
Existence of composition series, paper.tex:1137–1143.
For every nontrivial subgroup choose a maximal proper normal subgroup.
Correspondence makes its quotient simple. Well-founded induction on the
finite subgroup lattice and appending one term then constructs the chain.
Normality is required only in the next term, never in the ambient group.
-/

namespace D07.Ch06.JordanHolderExtensionCompositionExistence

open Specs.D07.Ch06.CompositionSeriesDefinition

universe u

/-- A maximal proper normal subgroup has a nontrivial simple quotient. -/
theorem simple_quotient_of_maximal_normal {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal]
    (hN : Maximal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊤) N) :
    IsSimpleGroup (G ⧸ N) := by
  haveI : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hN.1.2
  refine ⟨fun L hL => ?_⟩
  let K := L.comap (QuotientGroup.mk' N)
  have hNK : N ≤ K :=
    D07.Ch04.CorrespondenceTheorem.inverse_image_contains G N L
  have hKn : K.Normal := hL.comap (QuotientGroup.mk' N)
  by_cases hKt : K = ⊤
  · right
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective N)
    simpa only [Subgroup.comap_top] using hKt
  · left
    have hKN : K ≤ N := hN.2 ⟨hKn, hKt⟩ hNK
    have heq : K = N := le_antisymm hKN hNK
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective N)
    simpa only [MonoidHom.comap_bot, QuotientGroup.ker_mk'] using heq

/-- In a nontrivial finite group the set of proper normal subgroups is
nonempty and finite, so it has a maximal element. -/
theorem exists_maximal_normal (G : Type u) [Group G] [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, Maximal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊤) N := by
  obtain ⟨N, _, hN⟩ := Finite.exists_le_maximal
    (p := fun K : Subgroup G => K.Normal ∧ K ≠ ⊤)
    (a := ⊥) ⟨inferInstance, bot_ne_top⟩
  exact ⟨N, hN⟩

/-- The relation for one step of an ambient subgroup chain. -/
private def compositionStep {G : Type u} [Group G] : SetRel (Subgroup G) (Subgroup G) :=
  {p | p.1 < p.2 ∧ ∃ hn : (p.1.subgroupOf p.2).Normal,
    letI := hn
    IsSimpleGroup (p.2 ⧸ p.1.subgroupOf p.2)}

/-- Every nontrivial subgroup admits a proper predecessor with simple quotient. -/
private theorem exists_step {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : H ≠ ⊥) :
    ∃ K : Subgroup G, (K, H) ∈ compositionStep := by
  haveI : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hH
  obtain ⟨N, hN⟩ := exists_maximal_normal H
  letI : N.Normal := hN.1.1
  let K : Subgroup G := N.map H.subtype
  have hsub : K.subgroupOf H = N :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  have hlt : K < H := by
    have h := (Subgroup.map_lt_map_iff_of_injective H.subtype_injective).mpr
      (lt_top_iff_ne_top.mpr hN.1.2)
    simpa only [Subgroup.map_top, H.range_subtype] using h
  refine ⟨K, hlt, ?_⟩
  rw [hsub]
  exact ⟨inferInstance, simple_quotient_of_maximal_normal N hN⟩

/-- Induction on the finite subgroup lattice produces a chain ending at H. -/
private theorem exists_chain {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    ∃ s : RelSeries (@compositionStep G _), s.head = ⊥ ∧ s.last = H := by
  induction H using WellFoundedLT.induction with
  | ind H ih =>
    by_cases hH : H = ⊥
    · subst H
      exact ⟨RelSeries.singleton _ ⊥, rfl, rfl⟩
    · obtain ⟨K, hKH⟩ := exists_step H hH
      obtain ⟨s, hs0, hsK⟩ := ih K hKH.1
      have hlast : (s.last, H) ∈ compositionStep := hsK ▸ hKH
      exact ⟨s.snoc H hlast, by simpa using hs0, RelSeries.last_snoc ..⟩

/-- Every finite group has a composition series, including the trivial group. -/
theorem composition_series_exists (G : Type u) [Group G] [Finite G] :
    Nonempty (Series G) := by
  obtain ⟨s, hs0, hsG⟩ := exists_chain (⊤ : Subgroup G)
  exact ⟨{
    length := s.length
    term := s
    first_eq_bot := hs0
    last_eq_top := hsG
    strictMono := Fin.strictMono_iff_lt_succ.mpr (fun i => (s.step i).1)
    normal := fun i => (s.step i).2.choose
    simple := fun i => (s.step i).2.choose_spec }⟩

theorem trivial_composition_series (G : Type u) [Group G] [Finite G] [Subsingleton G] :
    ∃ s : Series G, s.length = 0 ∧ factorListValue s = [] :=
  D07.Ch06.CompositionSeriesDefinition.trivial_series G

end D07.Ch06.JordanHolderExtensionCompositionExistence
