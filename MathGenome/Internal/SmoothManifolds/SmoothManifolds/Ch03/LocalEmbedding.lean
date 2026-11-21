import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.LocalEmbedding
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.BoundaryImmersion

namespace SmoothManifolds.LocalEmbedding
open ModelData AtlasData MapData FiniteRegularityData MapClassData Set Filter
open scoped Topology ContDiff
universe u v

/-- Ambient straightening gives a topological embedding even if the target
chart takes values in a half-space. Only its subspace inclusion is used. -/
theorem exists_isEmbedding_restriction {m n : ℕ} {a b : ModelKind}
    {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f)
    (p : M) (hi : IsImmersionAt S T f p) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧
      Topology.IsEmbedding (fun x : V => f x.val) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  obtain ⟨U, hU, hepU, g, hg, heq⟩ := (hf p).2 e he d hd hp hfp
  have hdg := ((hg.contDiffAt (hU.mem_nhds hepU)).differentiableAt
    (by simp : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hderiv : chartDerivative e d f p = fderiv ℝ g (e p).val :=
    FiniteRegularity.coordinateDerivative_eq e _ p hp _ ⟨g, hdg, heq⟩
  have hgi : Function.Injective (fderiv ℝ g (e p).val) := by
    rw [← hderiv]
    exact ((MapClasses.chart_invariants S T f hf p e d he hd hp hfp).2.1).mp hi
  obtain ⟨_, h, _, _, O, hO, hepO, hform⟩ :=
    BoundaryImmersion.euclidean_immersion 1 (by rfl) g U hU hg (e p).val hepU _ hdg hgi
  have hdp : (d (f p)).val ∈ h.source := by
    rw [← heq.eq_of_nhds]
    exact (hform _ hepO).1
  let W : Set N := {y | y ∈ d.source ∧ (d y).val ∈ h.source}
  have hW : IsOpen W :=
    (continuous_subtype_val.comp_continuousOn d.continuousOn).isOpen_inter_preimage
      d.open_source h.open_source
  have hfpW : f p ∈ W := ⟨hfp, hdp⟩
  have hecont : ContinuousAt (fun y => (e y).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  have hnhds : ∀ᶠ y in 𝓝 p, y ∈ e.source ∧ f y ∈ W ∧
      (e y).val ∈ O ∧ g (e y).val = (d (f y)).val := by
    filter_upwards [e.open_source.mem_nhds hp,
      (hf p).1.preimage_mem_nhds (hW.mem_nhds hfpW),
      hecont.preimage_mem_nhds (hO.mem_nhds hepO), heq] with y hy hfy hyO heqy
    exact ⟨hy, hfy, hyO, heqy⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hnhds
  let fV : V → W := fun x => ⟨f x.val, (hVsub x.property).2.1⟩
  let k : W → Euclidean m × Euclidean (n - m) := fun y => h (d y.val).val
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  have hfV : Continuous fV := (hfcont.comp continuous_subtype_val).subtype_mk _
  have hdc : Continuous (fun y : W => (d y.val).val) :=
    continuous_subtype_val.comp (d.continuousOn.comp_continuous continuous_subtype_val
      (fun y => y.property.1))
  have hk : Continuous k :=
    h.continuousOn.comp_continuous hdc (fun y => y.property.2)
  have heV : Topology.IsEmbedding (fun x : V => e x.val) := by
    exact e.toPartialHomeomorph.isEmbedding_restrict.comp
      (Topology.IsEmbedding.subtypeVal.codRestrict
        e.source (fun x : V => (hVsub x.property).1))
  have hcoord : Topology.IsEmbedding (fun x : V => ((e x.val).val, (0 : Euclidean (n-m)))) :=
    (isEmbedding_prodMkLeft (0 : Euclidean (n-m))).comp
      (Topology.IsEmbedding.subtypeVal.comp heV)
  have hcomp : k ∘ fV = fun x : V => ((e x.val).val, (0 : Euclidean (n-m))) := by
    funext x
    obtain ⟨_, _, hxO, heqx⟩ := hVsub x.property
    change h (d (f x.val)).val = _
    rw [← heqx]
    exact (hform _ hxO).2
  have hfVe : Topology.IsEmbedding fV :=
    Topology.IsEmbedding.of_comp hfV hk (hcomp.symm ▸ hcoord)
  exact ⟨V, hV, hpV, Topology.IsEmbedding.subtypeVal.comp hfVe⟩

/-- The full local embedding assertion, with the actual homeomorphism onto
the image, valid for all source and target boundary configurations. -/
theorem local_embedding :
    Specs.SmoothManifolds.Ch03.LocalEmbedding.local_embeddingType.{u,v} := by
  intro m n a b M N _ _ S T f hf hi p
  have hf1 : ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f :=
    manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf
  obtain ⟨U, hU, hpU, hE⟩ := exists_isEmbedding_restriction S T f hf1 p (hi p)
  have hsm : ManifoldContDiff (⊤ : ℕ∞) (openSubsetAtlas S.smoothStructure.val U hU)
      T.smoothStructure.val (fun x : U => f x.val) :=
    (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ f U hU).mp (fun x _ => hf x)
  exact ⟨U, hU, hpU, hE, hsm, (fun x => hi x.val), hE.toHomeomorph, fun _ => rfl⟩

end SmoothManifolds.LocalEmbedding
