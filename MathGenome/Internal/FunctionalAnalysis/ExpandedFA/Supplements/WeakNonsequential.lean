import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.WeakNonsequential
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01FiniteDimension
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.EquivFin

/-! The sphere-union counterexample to sequential determination of the weak
 topology. A finite-test kernel proves weak density at zero; norm bounds on
 convergent sequences reduce sequential closedness to a finite compact union.
 No completeness or separability assumption is imposed on the ambient space.
-/

namespace ExpandedFA.Supplements.WeakNonsequential

universe u v
open Filter
open scoped Topology
noncomputable section

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Choose countably many distinct members of an infinite Hamel basis. -/
theorem exists_sphereChain : Spec.ChainExistence := by
  intro 𝕜 E _ _ _ hInf
  classical
  let b := Module.Free.chooseBasis 𝕜 E
  have : Infinite (Module.Free.ChooseBasisIndex 𝕜 E) := by
    apply not_finite_iff_infinite.mp
    intro hf
    exact hInf b.finiteDimensional_of_finite
  let e := Infinite.natEmbedding (Module.Free.ChooseBasisIndex 𝕜 E)
  let w : ℕ → E := fun n => b (e n)
  have hw : LinearIndependent 𝕜 w := b.linearIndependent.comp e e.injective
  let V : ℕ → Submodule 𝕜 E := fun n =>
    Submodule.span 𝕜 (Set.range (fun i : Fin n => w i))
  refine ⟨V, ?_, ?_⟩
  · intro m n hmn
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hmn⟩, rfl⟩
  · intro n
    refine ⟨FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _), ?_⟩
    simpa only [V, Function.comp_def, Fintype.card_fin] using
      finrank_span_eq_card (hw.comp (fun i : Fin n => (i : ℕ)) Fin.val_injective)

/-- Norm compact sets are weakly closed, using Hahn–Banach separation of points. -/
theorem isWeakClosed_of_isCompact (K : Set E) (hK : IsCompact K) :
    @IsClosed E (weakTopology 𝕜 E) K := by
  have h : IsCompact ((toWeakSpace 𝕜 E) '' K) :=
    hK.image (toWeakSpaceCLM 𝕜 E).continuous
  have hclosed := h.isClosed
  unfold weakTopology
  rw [P1.dualPairTopology_weakSpace 𝕜 E]
  rw [← Set.preimage_image_eq K (toWeakSpace 𝕜 E).injective]
  exact @IsClosed.preimage E (WeakSpace 𝕜 E)
    (TopologicalSpace.induced (toWeakSpace 𝕜 E) (instTopologicalSpaceWeakSpace 𝕜 E))
    (instTopologicalSpaceWeakSpace 𝕜 E) (toWeakSpace 𝕜 E)
    continuous_induced_dom _ hclosed

/-- Each displayed finite-dimensional sphere is compact in the original norm. -/
theorem isCompact_subspace_sphere (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M] (r : ℝ) :
    IsCompact {x : E | x ∈ M ∧ ‖x‖ = r} := by
  let := FiniteDimensional.proper_rclike 𝕜 M
  have h := (isCompact_sphere (0 : M) r).image M.subtypeL.continuous
  have heq : M.subtypeL '' Metric.sphere (0 : M) r = {x : E | x ∈ M ∧ ‖x‖ = r} := by
    ext x
    simp only [Set.mem_image, Metric.mem_sphere, dist_zero_right, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hr⟩
      exact ⟨⟨x, hx⟩, hr, rfl⟩
  rwa [heq] at h

/-- A convergent sequence in the union stays inside a finite union of spheres. -/
theorem sphereUnion_isSeqClosed (V : ℕ → Submodule 𝕜 E) (hV : SphereChain 𝕜 E V) :
    @IsSeqClosed E (weakTopology 𝕜 E) (sphereUnion 𝕜 E V) := by
  intro s x hs hx
  obtain ⟨C, _, hC⟩ := P1.C12BoundedSequences.weak_sequence_bounded 𝕜 E s x hx
  obtain ⟨N, hN⟩ := exists_nat_gt C
  let K : Set E := ⋃ n ∈ Finset.Icc 1 N, {y : E | y ∈ V n ∧ ‖y‖ = (n : ℝ)}
  have hK : IsCompact K := by
    apply Finset.isCompact_biUnion
    intro n _
    have := (hV.2 n).1
    exact isCompact_subspace_sphere (V n) n
  have hsK : ∀ k, s k ∈ K := by
    intro k
    obtain ⟨n, hn, hsn, hnorm⟩ := hs k
    have hnN : n ≤ N := by
      have hlt : (n : ℝ) < (N : ℝ) := hnorm ▸ (hC k).trans_lt hN
      exact le_of_lt (Nat.cast_lt.mp hlt)
    exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_Icc.mpr ⟨hn, hnN⟩, hsn, hnorm⟩
  have hxK : x ∈ K := @IsClosed.mem_of_tendsto E (weakTopology 𝕜 E) ℕ x K s
    atTop inferInstance (isWeakClosed_of_isCompact K hK) hx (Eventually.of_forall hsK)
  obtain ⟨n, hn, hxn, hnorm⟩ := Set.mem_iUnion₂.mp hxK
  exact ⟨n, (Finset.mem_Icc.mp hn).1, hxn, hnorm⟩

/-- More dimensions than scalar tests leave a nonzero common kernel vector,
which can be scaled to the prescribed radius. -/
theorem sphere_meets_common_kernel (V : ℕ → Submodule 𝕜 E)
    (hV : SphereChain 𝕜 E V) (s : Finset (E →L[𝕜] 𝕜)) (n : ℕ) (hn : s.card < n) :
    ∃ x : E, x ∈ V n ∧ ‖x‖ = (n : ℝ) ∧ ∀ f ∈ s, f x = 0 := by
  classical
  have := (hV.2 n).1
  let T : V n →ₗ[𝕜] (s → 𝕜) :=
    LinearMap.pi (fun f => f.val.toLinearMap.comp (V n).subtype)
  have hdim : Module.finrank 𝕜 (s → 𝕜) < Module.finrank 𝕜 (V n) := by
    simpa only [Module.finrank_pi, Fintype.card_coe, (hV.2 n).2] using hn
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := T) hdim)
  have htests : ∀ f ∈ s, f (y : E) = 0 := by
    intro f hf
    exact congrFun (LinearMap.mem_ker.mp hy) ⟨f, hf⟩
  have hyE : (y : E) ≠ 0 := fun h => hy0 (Subtype.ext h)
  let a : 𝕜 := ((n : ℝ) / ‖(y : E)‖ : ℝ)
  refine ⟨a • (y : E), (V n).smul_mem a y.property, ?_, ?_⟩
  · rw [norm_smul]
    change ‖(((n : ℝ) / ‖(y : E)‖ : ℝ) : 𝕜)‖ * ‖(y : E)‖ = _
    rw [RCLike.norm_ofReal, abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (norm_nonneg _))]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hyE)
  · intro f hf
    simp only [map_smul, htests f hf, smul_zero]

/-- Every finite-test weak neighborhood of zero meets the specified sphere union. -/
theorem zero_mem_weakClosure (V : ℕ → Submodule 𝕜 E) (hV : SphereChain 𝕜 E V) :
    (0 : E) ∈ @closure E (weakTopology 𝕜 E) (sphereUnion 𝕜 E V) := by
  have hb := P1.dualPairTopology_nhds_basis 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E) 0
  apply (@mem_closure_iff_nhds_basis E (weakTopology 𝕜 E) _ 0
    (sphereUnion 𝕜 E V) _ _ hb).mpr
  intro p hp
  obtain ⟨x, hxV, hxnorm, htests⟩ := sphere_meets_common_kernel V hV p.1 (p.1.card + 1)
    (Nat.lt_succ_self _)
  refine ⟨x, ⟨p.1.card + 1, Nat.succ_pos _, hxV, hxnorm⟩, ?_⟩
  change ∀ f ∈ p.1, ‖f (x - 0)‖ < p.2
  intro f hf
  simpa only [sub_zero, htests f hf, norm_zero] using hp

/-- The excluded zero point witnesses failure of weak closedness. -/
theorem zero_not_mem_sphereUnion (V : ℕ → Submodule 𝕜 E) :
    (0 : E) ∉ sphereUnion 𝕜 E V := by
  rintro ⟨n, hn, _, hnorm⟩
  have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact hpos.ne' (by simpa only [norm_zero] using hnorm.symm)

theorem sphereUnion_properties : Spec.SphereUnionProperties := by
  intro 𝕜 E _ _ _ V hV
  have hc := zero_mem_weakClosure V hV
  have hn := zero_not_mem_sphereUnion V
  refine ⟨sphereUnion_isSeqClosed V hV, hc, hn, ?_⟩
  intro hclosed
  exact hn ((@IsClosed.closure_eq E (weakTopology 𝕜 E) _ hclosed) ▸ hc)

theorem weak_nonsequential : Spec.MainResult := by
  intro 𝕜 E _ _ _ hInf
  obtain ⟨V, hV⟩ := exists_sphereChain 𝕜 E hInf
  exact ⟨V, hV, sphereUnion_properties 𝕜 E V hV⟩

end
end ExpandedFA.Supplements.WeakNonsequential
