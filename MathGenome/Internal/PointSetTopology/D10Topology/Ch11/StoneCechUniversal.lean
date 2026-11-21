import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.StoneCechUniversal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.StoneCechConstruction
import Mathlib.Topology.Homeomorph.Lemmas

/-!
The extension uses the coordinate reindexing in the source proof:
t ↦ (v ↦ t (v ∘ f)). Its restriction to Beta X takes values in the
closed evaluation image of the compact Hausdorff target. The inverse
of that target's evaluation embedding then gives the extension, with
no inhabitance assumption, including when the target is empty.
-/

open Set Topology
universe u v

namespace D10Topology.Ch11

theorem stoneCech_extension_unique {X : Type u} {H : Type v}
    [TopologicalSpace X] [TopologicalSpace H] [T2Space H]
    (g h : Beta X → H) (hg : Continuous g) (hh : Continuous h)
    (heq : g ∘ betaUnit = h ∘ betaUnit) : g = h := by
  apply hg.ext_on betaUnit_dense hh
  rintro _ ⟨x, rfl⟩
  exact congr_fun heq x

theorem stoneCech_universal {X : Type u} {H : Type v}
    [TopologicalSpace X] [TopologicalSpace H] [CompactSpace H] [T2Space H]
    (_hX : Ch07.Tychonoff X) (f : X → H) (hf : Continuous f) :
    ∃! g : Beta X → H, Continuous g ∧ g ∘ betaUnit = f := by
  let T : Ch10.Cube (Ch10.EvaluationIndex X) →
      Ch10.Cube (Ch10.EvaluationIndex H) :=
    fun t v => t ⟨v ∘ f, v.continuous.comp hf⟩
  have hT : Continuous T :=
    continuous_pi (fun v => continuous_apply
      (⟨v ∘ f, v.continuous.comp hf⟩ : Ch10.EvaluationIndex X))
  have hH := Ch10.compact_hausdorff_evaluation_image
    ((Ch05.coverCompact_iff_compactSpace H).mpr inferInstance)
  have hmem (b : Beta X) : T b.val ∈ range (Ch10.evaluationMap (X := H)) := by
    have hpre : IsClosed (T ⁻¹' range (Ch10.evaluationMap (X := H))) :=
      hH.2.2.preimage hT
    have hsub : range (Ch10.evaluationMap (X := X)) ⊆
        T ⁻¹' range (Ch10.evaluationMap (X := H)) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨f x, rfl⟩
    exact closure_minimal hsub hpre b.property
  let R : Beta X → range (Ch10.evaluationMap (X := H)) :=
    fun b => ⟨T b.val, hmem b⟩
  have hR : Continuous R := (hT.comp continuous_subtype_val).subtype_mk _
  let e : H ≃ₜ range (Ch10.evaluationMap (X := H)) := hH.1.toHomeomorph
  let g : Beta X → H := e.symm ∘ R
  have hg : Continuous g := e.symm.continuous.comp hR
  have hext : g ∘ betaUnit = f := by
    funext x
    change e.symm (R (betaUnit x)) = f x
    have hx : R (betaUnit x) = e (f x) := by
      apply Subtype.ext
      rfl
    rw [hx, e.symm_apply_apply]
  refine ⟨g, ⟨hg, hext⟩, ?_⟩
  intro h hh
  exact stoneCech_extension_unique h g hh.1 hg (hh.2.trans hext.symm)

theorem stoneCech_empty_target {X : Type u} {H : Type v}
    [TopologicalSpace X] [IsEmpty H] (f : X → H) :
    IsEmpty X ∧ IsEmpty (Beta X) := by
  let : IsEmpty X := ⟨fun x => isEmptyElim (f x)⟩
  exact ⟨inferInstance, empty_beta X⟩

theorem stoneCech_characterization {X : Type u} {K : Type v}
    [TopologicalSpace X] [TopologicalSpace K]
    (hX : Ch07.Tychonoff X) (i : X → K) (hi : HausdorffCompactification i)
    (hUniversal : ∀ (H : Type u) [TopologicalSpace H] [CompactSpace H] [T2Space H]
      (f : X → H), Continuous f →
      ∃! g : K → H, Continuous g ∧ g ∘ i = f) :
    ∃! e : Beta X ≃ₜ K, ∀ x, e (betaUnit x) = i x := by
  let : CompactSpace K := hi.2.2.1
  let : T2Space K := hi.2.2.2
  obtain ⟨F, hF, _⟩ := stoneCech_universal hX i hi.1.continuous
  obtain ⟨G, hG, _⟩ := hUniversal (Beta X) betaUnit betaUnit_continuous
  have hGF : G ∘ F = id := by
    apply stoneCech_extension_unique _ _ (hG.1.comp hF.1) continuous_id
    funext x
    change G (F (betaUnit x)) = betaUnit x
    exact (congrArg G (congr_fun hF.2 x)).trans (congr_fun hG.2 x)
  have hFG : F ∘ G = id := by
    apply (hF.1.comp hG.1).ext_on hi.2.1 continuous_id
    rintro _ ⟨x, rfl⟩
    change F (G (i x)) = i x
    exact (congrArg F (congr_fun hG.2 x)).trans (congr_fun hF.2 x)
  let e : Beta X ≃ₜ K :=
    { toFun := F
      invFun := G
      left_inv := congr_fun hGF
      right_inv := congr_fun hFG
      continuous_toFun := hF.1
      continuous_invFun := hG.1 }
  refine ⟨e, (fun x => congr_fun hF.2 x), ?_⟩
  intro e' he'
  have heq : (e' : Beta X → K) = e :=
    stoneCech_extension_unique _ _ e'.continuous e.continuous (by
      funext x
      exact (he' x).trans (congr_fun hF.2 x).symm)
  exact Homeomorph.ext (congr_fun heq)

end D10Topology.Ch11
