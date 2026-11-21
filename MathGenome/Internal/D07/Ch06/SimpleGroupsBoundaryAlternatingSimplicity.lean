import MathGenome.Internal.Specs.D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-! Simplicity and noncommutativity of the alternating group on n ≥ 5 letters. -/

namespace D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity

universe u

theorem alternating_simple :
    Specs.D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity.AlternatingSimple.{u} := by
  classical
  intro X _ n hcard hn
  exact alternatingGroup.isSimpleGroup (by omega)

theorem alternating_nonabelian :
    Specs.D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity.AlternatingNonabelian.{u} := by
  classical
  intro X _ n hcard hn
  by_contra h
  have hcomm : ∀ σ τ : alternatingGroup X, σ * τ = τ * σ := by
    simpa only [not_exists, not_not] using h
  have hsmall : Nat.card X ≤ 3 :=
    alternatingGroup.isMulCommutative_iff_card_le_three.mp ⟨⟨hcomm⟩⟩
  omega

theorem nontrivial_normal_subgroup_eq_top :
    Specs.D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity.NontrivialNormalSubgroupEqTop.{u} := by
  classical
  intro X _ n hcard hn N hnormal hN
  have : N.Normal := hnormal
  have : IsSimpleGroup (alternatingGroup X) := alternating_simple X n hcard hn
  exact (Subgroup.Normal.eq_bot_or_eq_top N).resolve_left hN

end D07.Ch06.SimpleGroupsBoundaryAlternatingSimplicity
