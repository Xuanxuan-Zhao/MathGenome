import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.OpenMapping
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.IdentityTheorem
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalMappingNormalForm

/-!
Open mapping from the identity theorem and the local power normal form.
The chosen open subset need not be connected, and may be empty; the
nonconstant-germ argument uses connectedness of the original domain.
-/

open Filter Set
open scoped Topology

namespace D12Complex.OpenMapping

theorem not_locally_constant_of_nonconstant :
    Specs.D12Complex.Ch05.OpenMapping.not_locally_constant_of_nonconstant_type := by
  intro Ω f hΩ hf hnc a ha hconst
  let S : Set ℂ := {z | z ∈ Ω ∧ f z = f a}
  have hmem : ∀ᶠ z in 𝓝 a, z ∈ Ω := hΩ.2.1.mem_nhds ha
  have hevent : ∀ᶠ z in 𝓝[≠] a, z ∈ S :=
    (hmem.and hconst).filter_mono nhdsWithin_le_nhds
  have hacc : AccPt a (𝓟 S) :=
    accPt_iff_frequently_nhdsNE.mpr hevent.frequently
  have heq : EqOn f (fun _ => f a) Ω :=
    IdentityTheorem.identity_of_accPt Ω S f (fun _ => f a) a hΩ hf
      ⟨hf.1, fun _ _ => differentiableAt_const _⟩
      (fun _ hz => hz.1) ha hacc (fun _ hz => hz.2)
  exact hnc ⟨f a, heq⟩

theorem exists_image_ball_of_nonconstant :
    Specs.D12Complex.Ch05.OpenMapping.exists_image_ball_of_nonconstant_type := by
  intro Ω f hΩ hf hnc U hU hUΩ a ha
  have hrestriction : HolomorphicOn U f :=
    ⟨hU, fun z hz => hf.2 z (hUΩ hz)⟩
  have hgerm := not_locally_constant_of_nonconstant Ω f hΩ hf hnc a (hUΩ ha)
  obtain ⟨m, hm, r, hr, V, φ, ψ, haV, hVU, hpair, hφ0, hform, himage, hrest⟩ :=
    LocalMappingNormalForm.local_mapping_normal_form U f a hrestriction ha hgerm
  refine ⟨r ^ m, pow_pos hr m, ?_⟩
  rw [← himage]
  exact image_mono hVU

theorem image_open_of_nonconstant :
    Specs.D12Complex.Ch05.OpenMapping.image_open_of_nonconstant_type := by
  intro Ω f hΩ hf hnc U hU hUΩ
  apply Metric.isOpen_iff.mpr
  rintro _ ⟨a, ha, rfl⟩
  exact exists_image_ball_of_nonconstant Ω f hΩ hf hnc U hU hUΩ a ha

theorem isOpenMap_of_nonconstant :
    Specs.D12Complex.Ch05.OpenMapping.isOpenMap_of_nonconstant_type := by
  intro Ω f hΩ hf hnc S hS
  have hopen : IsOpen (Subtype.val '' S : Set ℂ) :=
    hΩ.2.1.isOpenMap_subtype_val S hS
  have hsub : (Subtype.val '' S : Set ℂ) ⊆ Ω := by
    rintro z ⟨a, _, rfl⟩
    exact a.property
  simpa only [image_image] using
    image_open_of_nonconstant Ω f hΩ hf hnc (Subtype.val '' S) hopen hsub

end D12Complex.OpenMapping
