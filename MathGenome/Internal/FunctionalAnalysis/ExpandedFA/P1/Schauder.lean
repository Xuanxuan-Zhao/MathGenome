import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Schauder
import MathGenome.PointSetTopology.Topics.D10Topology.Ch17
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Analysis.Convex.StdSimplex

/-! Schauder--Tychonoff in the given Hausdorff locally convex topology.
We apply finite-dimensional Brouwer to barycentric weights, then use
closedness of the compact residual image to obtain an exact fixed point. -/

noncomputable section

open Set Filter
open scoped Topology BigOperators

universe u v

namespace ExpandedFA.P1.Schauder

/-- Approximate fixed points with error in any prescribed convex zero
neighborhood. The finite-dimensional space used by Brouwer consists of
barycentric weights, so the ambient space needs no norm. -/
theorem approximate_fixed_point
    {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (K : Set E) (hne : K.Nonempty) (hcompact : IsCompact K)
    (hconvex : Convex ℝ K) (T : K → K) (hT : Continuous T)
    (V : Set E) (hV : V ∈ 𝓝 (0 : E)) (hVconvex : Convex ℝ V) :
    ∃ x : K, (x : E) - (T x : E) ∈ V := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  letI : Nonempty K := hne.to_subtype
  obtain ⟨O, hOV, hOopen, hOzero⟩ := mem_nhds_iff.mp hV
  let W : K → Set K := fun q => {x | (q : E) - (x : E) ∈ O}
  have hWopen : ∀ q, IsOpen (W q) := fun q =>
    hOopen.preimage (continuous_const.sub continuous_subtype_val)
  have hWcover : (univ : Set K) ⊆ ⋃ q, W q := by
    intro x _
    exact mem_iUnion.mpr ⟨x, by simpa [W] using hOzero⟩
  obtain ⟨s, hscover⟩ := isCompact_univ.elim_finite_subcover W hWopen hWcover
  have hsne : s.Nonempty := by
    obtain ⟨q, hq, _⟩ := mem_iUnion₂.mp (hscover (mem_univ (Classical.arbitrary K)))
    exact ⟨q, hq⟩
  letI : Nonempty s := hsne.to_subtype
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate
    (s := (univ : Set K)) isClosed_univ (fun q : s => W q.val)
    (fun q => hWopen q.val) (by
      intro x hx
      obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hscover hx)
      exact mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩)
  have hsum (x : K) : ∑ q : s, ρ q x = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)
  let a : K → stdSimplex ℝ s := fun x =>
    ⟨fun q => ρ q x, fun q => ρ.nonneg q x, hsum x⟩
  have ha : Continuous a :=
    (continuous_pi fun q => (ρ q).continuous).subtype_mk _
  let b : stdSimplex ℝ s → K := fun t =>
    ⟨∑ q : s, t.val q • (q.val : E),
      hconvex.sum_mem (fun q _ => t.property.1 q) t.property.2
        (fun q _ => q.val.property)⟩
  have hb : Continuous b := by
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ (fun q _ =>
      ((continuous_apply q).comp continuous_subtype_val).smul continuous_const)
  obtain ⟨t, ht⟩ := D10Topology.Ch17.brouwer_finiteDimensional (s → ℝ)
    (stdSimplex ℝ s) ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary s)⟩
    (isCompact_stdSimplex ℝ s) (convex_stdSimplex ℝ s)
    (a ∘ T ∘ b) (ha.comp (hT.comp hb))
  refine ⟨b t, ?_⟩
  have herr (x : K) : (b (a x) : E) - (x : E) ∈ V := by
    have h := hVconvex.finsum_mem (fun q => ρ.nonneg q x)
      (ρ.sum_eq_one (mem_univ x)) (z := fun q : s => (q.val : E) - (x : E)) ?_
    · simpa only [finsum_eq_sum_of_fintype, smul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_smul, hsum, one_smul, b, a] using h
    · intro q hq
      exact hOV (hρ q (subset_closure (show x ∈ Function.support (ρ q) from hq)))
  have heq : a (T (b t)) = t := ht
  simpa only [heq] using herr (T (b t))

/-- Schauder--Tychonoff for both manuscript scalar fields, using real
convexity and the original Hausdorff locally convex topology. -/
theorem schauder_tychonoff : Spec.SchauderTychonoff.{u, v} := by
  intro 𝕜 E _ _ _ _ _ _ _ hLCS K hne hcompact hconvex T hT
  letI : IsTopologicalAddGroup E := hLCS.1.1
  letI : ContinuousSMul 𝕜 E := hLCS.1.2
  letI : LocallyConvexSpace ℝ E := hLCS.2
  letI : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let r : K → E := fun x => (x : E) - (T x : E)
  have hr : Continuous r := continuous_subtype_val.sub (continuous_subtype_val.comp hT)
  have hclosed : IsClosed (range r) := by
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
    exact (isCompact_range hr).isClosed
  have hzero : (0 : E) ∈ closure (range r) := by
    rw [mem_closure_iff]
    intro O hO hz
    obtain ⟨V, hV, hVconvex, hVO⟩ :=
      (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mp hLCS.2 O (hO.mem_nhds hz)
    obtain ⟨x, hx⟩ := approximate_fixed_point K hne hcompact hconvex T hT V hV hVconvex
    exact ⟨r x, hVO hx, mem_range_self x⟩
  rw [hclosed.closure_eq] at hzero
  obtain ⟨x, hx⟩ := hzero
  exact ⟨x, Subtype.ext (sub_eq_zero.mp hx).symm⟩

end ExpandedFA.P1.Schauder
