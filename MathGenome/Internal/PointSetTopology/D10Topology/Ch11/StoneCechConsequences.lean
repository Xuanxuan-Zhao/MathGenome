import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.StoneCechConsequences
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.StoneCechUniversal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.RealAndEuclideanCompactness

/-!
Consequences of the universal property for the actual evaluation closure.
A bounded real map is first extended into a closed bounded interval.
The compact image of an extended compactification embedding is closed and
contains its dense image, hence is the entire compactification. Coordinate
reindexing defines betaMap; density proves its full extension uniqueness.
-/

open Set Topology
universe u v w

namespace D10Topology.Ch11

abbrev betaMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Beta X → Beta Y :=
  Specs.D10Topology.Ch11.StoneCechConsequences.betaMap f

theorem bounded_real_extension {X : Type u} [TopologicalSpace X]
    (hX : Ch07.Tychonoff X) (f : X → ℝ) (hf : Continuous f)
    (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    ∃! F : Beta X → ℝ, Continuous F ∧ F ∘ betaUnit = f := by
  obtain ⟨M, hM⟩ := hb
  let R := max M 0
  let J := Icc (-R) R
  let fJ : X → J := fun x => ⟨f x, by
    have h := (hM x).trans (le_max_left M 0)
    exact abs_le.mp h⟩
  have hfJ : Continuous fJ := hf.subtype_mk _
  let : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨G, hG, _⟩ := stoneCech_universal hX fJ hfJ
  let F : Beta X → ℝ := Subtype.val ∘ G
  have hF : Continuous F := continuous_subtype_val.comp hG.1
  have hExt : F ∘ betaUnit = f := by
    funext x
    exact congrArg Subtype.val (congr_fun hG.2 x)
  refine ⟨F, ⟨hF, hExt⟩, ?_⟩
  intro F' hF'
  exact stoneCech_extension_unique F' F hF'.1 hF (hF'.2.trans hExt.symm)

theorem compactification_image {X : Type u} {K : Type v}
    [TopologicalSpace X] [TopologicalSpace K]
    (hX : Ch07.Tychonoff X) (i : X → K) (hi : HausdorffCompactification i) :
    ∃ F : Beta X → K, Continuous F ∧ Function.Surjective F ∧ F ∘ betaUnit = i := by
  let : CompactSpace K := hi.2.2.1
  let : T2Space K := hi.2.2.2
  obtain ⟨F, hF, _⟩ := stoneCech_universal hX i hi.1.continuous
  have hc : IsClosed (range F) := (isCompact_range hF.1).isClosed
  have hsub : range i ⊆ range F := by
    rintro _ ⟨x, rfl⟩
    exact ⟨betaUnit x, congr_fun hF.2 x⟩
  have hfull : range F = univ := by
    apply univ_subset_iff.mp
    rw [← hi.2.1.closure_range]
    exact closure_minimal hsub hc
  exact ⟨F, hF.1, range_eq_univ.mp hfull, hF.2⟩

theorem betaMap_continuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    Continuous (betaMap f) := by
  exact (continuous_pi (fun g => (continuous_apply (g.comp f)).comp
    continuous_subtype_val)).subtype_mk _

theorem betaMap_unit {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    betaMap f ∘ betaUnit = betaUnit ∘ f := by
  funext x
  rfl

theorem betaMap_unique {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (_hX : Ch07.Tychonoff X) (_hY : Ch07.Tychonoff Y)
    (f : C(X, Y)) (F : Beta X → Beta Y) (hF : Continuous F)
    (hext : F ∘ betaUnit = betaUnit ∘ f) : F = betaMap f :=
  stoneCech_extension_unique F (betaMap f) hF (betaMap_continuous f)
    (hext.trans (betaMap_unit f).symm)

theorem betaMap_extension {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (hX : Ch07.Tychonoff X) (hY : Ch07.Tychonoff Y)
    (f : X → Y) (hf : Continuous f) :
    ∃! F : Beta X → Beta Y, Continuous F ∧ F ∘ betaUnit = betaUnit ∘ f := by
  let fc : C(X, Y) := ⟨f, hf⟩
  exact ⟨betaMap fc, ⟨betaMap_continuous fc, betaMap_unit fc⟩,
    fun F hF => betaMap_unique hX hY fc F hF.1 hF.2⟩

theorem betaMap_id (X : Type u) [TopologicalSpace X] :
    betaMap (ContinuousMap.id X) = id := by
  funext b
  apply Subtype.ext
  funext g
  rfl

theorem betaMap_comp {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    betaMap (g.comp f) = betaMap g ∘ betaMap f := by
  funext b
  apply Subtype.ext
  funext h
  rfl

theorem compact_betaSet_eq_range (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] :
    betaSet X = range (Ch10.evaluationMap (X := X)) := by
  exact (isCompact_range Ch10.tychonoff_cube_evaluation_continuous).isClosed.closure_eq

theorem compact_betaUnit_surjective (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] : Function.Surjective (betaUnit (X := X)) := by
  intro b
  have hb : b.val ∈ range (Ch10.evaluationMap (X := X)) := by
    rw [← compact_betaSet_eq_range X]
    exact b.property
  obtain ⟨x, hx⟩ := hb
  exact ⟨x, Subtype.ext hx⟩

theorem empty_beta_space (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    IsEmpty (Beta X) := empty_beta X

end D10Topology.Ch11
