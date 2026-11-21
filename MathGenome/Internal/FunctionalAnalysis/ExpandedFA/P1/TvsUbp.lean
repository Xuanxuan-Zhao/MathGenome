import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsUbp
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BalancedBounded
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07Baire
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

open Set Filter TopologicalSpace
open scoped Topology Pointwise Uniformity

namespace ExpandedFA.P1

/-- The category argument works over the underlying real field, without
local convexity or a Baire assumption on the whole domain. -/
theorem equicontinuousAtZero_of_nonmeagre_bounded_orbits
    {E F ι : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ E] [ContinuousSMul ℝ F]
    (A : ι → E →L[ℝ] F)
    (h : ¬ IsMeagre {x : E | Bounded (range fun i => A i x)}) :
    ∀ V ∈ 𝓝 (0 : F), ∃ U ∈ 𝓝 (0 : E), ∀ i, A i '' U ⊆ V := by
  intro V hV
  obtain ⟨W, hW, hclosed, hneg, hadd⟩ :=
    exists_closed_nhds_zero_neg_eq_add_subset hV
  have hsub : W - W ⊆ V := by
    simpa only [sub_eq_add_neg, hneg] using hadd
  let C : ℕ → Set E := fun n =>
    {x | ∀ i, ((n : ℝ) + 1)⁻¹ • A i x ∈ W}
  have hCclosed (n : ℕ) : IsClosed (C n) := by
    simp only [C, ofPred_forall]
    exact isClosed_iInter fun i =>
      hclosed.preimage ((A i).continuous.const_smul _)
  have hcover : {x : E | Bounded (range fun i => A i x)} ⊆ ⋃ n, C n := by
    intro x hx
    obtain ⟨s, hs, hscale⟩ := hx W hW
    obtain ⟨n, hn⟩ := exists_nat_ge s
    refine mem_iUnion.mpr ⟨n, fun i => ?_⟩
    have hr : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    exact (mem_smul_set_iff_inv_smul_mem₀ hr W _).mp
      (hscale _ (by linarith) (mem_range_self i))
  have hinterior : ∃ n, (interior (C n)).Nonempty := by
    by_contra! hn
    apply h
    apply IsMeagre.mono hcover
    apply isMeagre_iUnion
    intro n
    apply IsNowhereDense.isMeagre
    change interior (closure (C n)) = ∅
    rw [(hCclosed n).closure_eq]
    exact hn n
  obtain ⟨n, x, hx⟩ := hinterior
  have hxC : x ∈ C n := interior_subset hx
  have hxnhds : C n ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  let r : ℝ := (n : ℝ) + 1
  have hr : r ≠ 0 := ne_of_gt (by dsimp [r]; positivity)
  let U : Set E := (fun u => x + r • u) ⁻¹' C n
  have hU : U ∈ 𝓝 (0 : E) := by
    have hc : Continuous (fun u : E => x + r • u) :=
      continuous_const.add (continuous_id.const_smul r)
    apply hc.continuousAt.preimage_mem_nhds
    simpa only [smul_zero, add_zero] using hxnhds
  refine ⟨U, hU, fun i y hy => ?_⟩
  obtain ⟨u, hu, rfl⟩ := hy
  have hxu : r⁻¹ • A i (x + r • u) ∈ W := hu i
  have hxi : r⁻¹ • A i x ∈ W := hxC i
  have heq : r⁻¹ • A i (x + r • u) - r⁻¹ • A i x = A i u := by
    simp only [map_add, map_smul, smul_add, smul_smul, inv_mul_cancel₀ hr,
      one_smul, add_sub_cancel_left]
  rw [← heq]
  exact hsub (sub_mem_sub hxu hxi)

/-- Uniform control at zero sends every bounded source set into a single
bounded set containing all its images. -/
theorem bounded_iUnion_image_of_equicontinuousAtZero
    {E F ι : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] [TopologicalSpace E] [TopologicalSpace F]
    (A : ι → E →L[ℝ] F)
    (hA : ∀ V ∈ 𝓝 (0 : F), ∃ U ∈ 𝓝 (0 : E), ∀ i, A i '' U ⊆ V)
    {B : Set E} (hB : Bounded B) : Bounded (⋃ i, A i '' B) := by
  intro V hV
  obtain ⟨U, hU, hAU⟩ := hA V hV
  obtain ⟨s, hs, hscale⟩ := hB U hU
  refine ⟨s, hs, fun t ht y hy => ?_⟩
  obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hy
  obtain ⟨u, hu, rfl⟩ := hscale t ht hx
  rw [map_smul]
  exact smul_mem_smul_set (hAU i (mem_image_of_mem _ hu))

/-- Topological Banach–Steinhaus, including boundedness of every orbit. -/
theorem topological_banach_steinhaus : TvsUbpSpec.TopologicalBanachSteinhaus := by
  intro 𝕜 E F ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A h
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  let B : ι → E →L[ℝ] F := fun i => (A i).restrictScalars ℝ
  have heq := equicontinuousAtZero_of_nonmeagre_bounded_orbits B h
  refine ⟨?_, heq⟩
  intro x
  have hx : Bounded ({x} : Set E) :=
    (bounded_iff_isVonNBounded _).mpr (Bornology.isVonNBounded_singleton (𝕜 := ℝ) x)
  simpa only [B, ContinuousLinearMap.coe_restrictScalars', image_singleton,
    iUnion_singleton_eq_range] using
    bounded_iUnion_image_of_equicontinuousAtZero B heq hx

/-- The F-space corollary uses completeness of the translation uniformity,
not completeness of an arbitrarily selected compatible metric. -/
theorem fspace_banach_steinhaus : TvsUbpSpec.FSpaceBanachSteinhaus := by
  intro 𝕜 E F ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE A hA
  obtain ⟨_, _, hmet, hcomplete⟩ := hE
  let : MetrizableSpace E := hmet
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomplete
  let : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let : BaireSpace E := inferInstance
  have hnonmeagre : ¬ IsMeagre {x : E | Bounded (range fun i => A i x)} := by
    have hset : {x : E | Bounded (range fun i => A i x)} = univ := eq_univ_of_forall hA
    rw [hset]
    exact not_isMeagre_of_isOpen isOpen_univ ⟨0, mem_univ _⟩
  exact (topological_banach_steinhaus 𝕜 E F ι A hnonmeagre).2

end ExpandedFA.P1
