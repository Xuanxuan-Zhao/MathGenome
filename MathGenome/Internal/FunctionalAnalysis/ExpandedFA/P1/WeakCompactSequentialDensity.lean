import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakCompactSequentialDensity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EberleinSmulian
import Batteries.Tactic.OpenPrivate

/-! Sequential density in relatively weakly compact sets. The finite norming
construction from Eberlein–Šmulian is applied to the specified evaluation J x.
Its tests force a weak subsequential limit to equal x. -/
namespace ExpandedFA.P1.WeakCompactSequentialDensity

universe u v
open Filter Set
open scoped Topology
noncomputable section

open private NormingStage NormingStage.points NormingStage.tests
  NormingStage.test_norm NormingStage.norms norming_construction norming_closure_separates
  from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.WeakSequentialRelativeCompact

theorem sequential_density : Spec.SequentialDensity.{u,v} := by
  intro 𝕜 E _ _ _ A hA x hx
  classical
  let J := C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E
  have hJ := C13Embedding.canonicalEvaluation_weak_embedding 𝕜 E
  have hJx : J x ∈ @closure _
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜)) (J '' A) := by
    let : TopologicalSpace ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
      C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜)
    let : TopologicalSpace E := Spec.weakTopology 𝕜 E
    exact closure_subset_preimage_closure_image hJ.continuous hx
  obtain ⟨s, p, hsA, hp, ht, hsp, happrox⟩ :=
    norming_construction 𝕜 E A (J x) hJx
  let M : ℕ → Submodule 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) := fun n =>
    Submodule.span 𝕜 (insert (J x) (J '' (NormingStage.points (p n) : Set E)))
  have hM : Monotone M := fun _ _ h =>
    Submodule.span_mono (insert_subset_insert (image_mono (hp h)))
  let : ContinuousAdd ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    @IsTopologicalAddGroup.toContinuousAdd ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      inferInstance inferInstance inferInstance
  let N := (⨆ n, M n).topologicalClosure
  have hxN : J x ∈ N := (⨆ n, M n).le_topologicalClosure
    (Submodule.mem_iSup_of_mem 0 (Submodule.subset_span (mem_insert _ _)))
  have hsN : ∀ n, J (s n) ∈ N := fun n =>
    (⨆ n, M n).le_topologicalClosure (Submodule.mem_iSup_of_mem (n+1)
      (Submodule.subset_span (mem_insert_of_mem _ (mem_image_of_mem J (hsp n)))))
  let P : Submodule 𝕜 E := N.comap J.toLinearMap
  have hP : IsClosed (P : Set E) :=
    (⨆ n, M n).isClosed_topologicalClosure.preimage J.continuous
  have hPw := C12ConvexClosure.isWeaklyClosed_of_isClosed_submodule 𝕜 E P hP
  obtain ⟨y, r, hr, hy⟩ := EberleinSmulian.compact_implies_subsequences 𝕜 E A hA s hsA
  have hyN : J y ∈ N := by
    let : TopologicalSpace E := Spec.weakTopology 𝕜 E
    exact hPw.mem_of_tendsto hy (.of_forall fun n => hsN (r n))
  have hvalues : ∀ m f, f ∈ NormingStage.tests (p m) → f y = J x f := by
    intro m f hf
    have hlim : Tendsto (fun n => f (s n)) atTop (𝓝 (J x f)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero' (.of_forall fun n => norm_nonneg _) _
        tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop m] with n hn
      exact (happrox n f (ht hn hf)).le
    exact tendsto_nhds_unique
      (C12BoundedSequences.weak_evaluation_tendsto 𝕜 E (s ∘ r) y hy f)
      (hlim.comp hr.tendsto_atTop)
  have heq : J x - J y = 0 := norming_closure_separates 𝕜 (E →L[𝕜] 𝕜) M hM
    (fun n => NormingStage.tests (p n)) (fun n => NormingStage.test_norm (p n))
    (fun n => NormingStage.norms (p n)) (J x - J y) (@Submodule.sub_mem 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      inferInstance inferInstance inferInstance N (J x) (J y) hxN hyN) (by
      intro n f hf
      change J x f - f y = 0
      exact sub_eq_zero.mpr (hvalues n f hf).symm)
  have hxy : x = y :=
    C05BidualIsometry.canonicalEvaluation_injective 𝕜 E (sub_eq_zero.mp heq)
  exact ⟨s ∘ r, fun n => hsA (r n), hxy.symm ▸ hy⟩

/-- Compactness of K gives relative compactness for the ambient image of every
subset of K. The ambient sequential limit lifts to the subspace topology. -/
theorem compact_frechetUrysohn : Spec.CompactFrechetUrysohn.{u,v} := by
  intro 𝕜 E _ _ _ K
  have he := @Topology.IsEmbedding.mk E (WeakSpace 𝕜 E)
    (Spec.weakTopology 𝕜 E) (instTopologicalSpaceWeakSpace 𝕜 E)
    (toWeakSpace 𝕜 E)
    (@Topology.IsInducing.mk E (WeakSpace 𝕜 E)
      (Spec.weakTopology 𝕜 E) (instTopologicalSpaceWeakSpace 𝕜 E)
      (toWeakSpace 𝕜 E) (dualPairTopology_weakSpace 𝕜 E))
    (toWeakSpace 𝕜 E).injective
  let : TopologicalSpace E := Spec.weakTopology 𝕜 E
  intro hK
  let : T2Space E := he.t2Space
  constructor
  intro S x hx
  have hx' : x.val ∈ closure (Subtype.val '' S) :=
    closure_subset_preimage_closure_image continuous_subtype_val hx
  have hcompact : IsCompact (closure (Subtype.val '' S)) :=
    hK.of_isClosed_subset isClosed_closure
      (closure_minimal (by rintro _ ⟨y, _, rfl⟩; exact y.property) hK.isClosed)
  obtain ⟨s, hs, hlim⟩ := sequential_density 𝕜 E (Subtype.val '' S) hcompact x.val hx'
  choose t htS hts using hs
  refine ⟨t, htS, ?_⟩
  apply tendsto_subtype_rng.mpr
  rw [show (fun n => (t n).val) = s from funext hts]
  exact hlim

end
end ExpandedFA.P1.WeakCompactSequentialDensity
