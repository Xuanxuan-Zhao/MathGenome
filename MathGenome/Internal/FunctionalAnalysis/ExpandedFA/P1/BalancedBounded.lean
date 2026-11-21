import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.TvsDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BalancedBounded

/-! Elementary neighborhoods and bounded sets, paper.tex:1759–1767. -/

open Set Filter
open scoped Topology Pointwise BigOperators

namespace ExpandedFA.P1

/-- The manuscript uses only positive real dilations. On a real TVS this is
exactly von Neumann boundedness: first shrink to a balanced neighborhood,
then replace an arbitrary real dilation by its absolute value. -/
theorem bounded_iff_isVonNBounded {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousSMul ℝ E] (A : Set E) :
    Bounded A ↔ Bornology.IsVonNBounded ℝ A := by
  constructor
  · intro h U hU
    obtain ⟨V, ⟨hV, hbal⟩, hVU⟩ := (nhds_basis_balanced ℝ E).mem_iff.mp hU
    obtain ⟨s, hs, hscale⟩ := h V hV
    apply Absorbs.of_norm
    refine ⟨s, fun c hc => ?_⟩
    calc
      A ⊆ ‖c‖ • V := hscale ‖c‖ hc
      _ = c • V := hbal.smul_congr (by simp)
      _ ⊆ c • U := smul_set_mono hVU
  · intro h U hU
    obtain ⟨s, hs, hscale⟩ := (h hU).exists_pos
    refine ⟨s, hs, fun t ht => hscale t ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (hs.trans_le ht)] using ht

/-- Real convex hulls preserve balance over the original scalar field. -/
theorem balanced_real_convexHull {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    {A : Set E} (hA : Balanced 𝕜 A) : Balanced 𝕜 (convexHull ℝ A) := by
  have hc : Convex ℝ {x : E | ∀ a : 𝕜, ‖a‖ ≤ 1 → a • x ∈ convexHull ℝ A} := by
    intro x hx y hy u v hu hv huv a ha
    rw [smul_add, ← smul_comm u, ← smul_comm v]
    exact convex_convexHull ℝ A (hx a ha) (hy a ha) hu hv huv
  rw [balanced_iff_smul_mem] at hA ⊢
  intro a ha x hx
  have hsub : A ⊆ {y : E | ∀ a : 𝕜, ‖a‖ ≤ 1 → a • y ∈ convexHull ℝ A} := by
    intro y hy a ha
    exact subset_convexHull ℝ A (hA ha hy)
  exact convexHull_min hsub hc hx a ha

theorem balanced_neighborhood_basis : BalancedBoundedSpec.BalancedNeighborhoodBasis := by
  intro 𝕜 E _ _ _ _ _ _ _ U hU
  obtain ⟨V, ⟨hV, hopen, hbal⟩, hVU⟩ :=
    (nhds_basis_open_balanced 𝕜 E).mem_iff.mp hU
  exact ⟨V, hV, hopen, hbal, hVU⟩

theorem absolutely_convex_neighborhood_basis :
    BalancedBoundedSpec.AbsolutelyConvexNeighborhoodBasis := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ hlc U hU
  let := hlc
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨W, ⟨hW, hconv⟩, hWU⟩ :=
    (LocallyConvexSpace.convex_basis_zero ℝ E).mem_iff.mp hU
  let C := convexHull ℝ (balancedCore 𝕜 W)
  have hC : C ∈ 𝓝 (0 : E) :=
    mem_of_superset (balancedCore_mem_nhds_zero hW) (subset_convexHull ℝ _)
  have hbal : Balanced 𝕜 C := balanced_real_convexHull (balancedCore.balanced W)
  have hconvC : Convex ℝ C := convex_convexHull ℝ _
  have hCU : C ⊆ U := (convexHull_min (balancedCore_subset W) hconv).trans hWU
  refine ⟨interior C, interior_mem_nhds.mpr hC, isOpen_interior,
    hbal.interior (mem_interior_iff_mem_nhds.mpr hC), hconvC.interior,
    interior_subset.trans hCU⟩

theorem neighborhood_absorbing : BalancedBoundedSpec.NeighborhoodAbsorbing := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ U hU x
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨s, hs, hscale⟩ := (absorbent_nhds_zero (𝕜 := ℝ) hU x).exists_pos
  refine ⟨s, hs, ?_⟩
  exact hscale s (by simp only [Real.norm_eq_abs, abs_of_pos hs, le_refl]) (mem_singleton x)

theorem compact_bounded : BalancedBoundedSpec.CompactBounded := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ A hA
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  exact (bounded_iff_isVonNBounded A).mpr (hA.isVonNBounded ℝ)

theorem convergent_sequence_bounded : BalancedBoundedSpec.ConvergentSequenceBounded := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ x a hx
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  exact (bounded_iff_isVonNBounded _).mpr (hx.isVonNBounded_range ℝ)

theorem bounded_closure : BalancedBoundedSpec.BoundedClosure := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ A hA
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  exact (bounded_iff_isVonNBounded _).mpr ((bounded_iff_isVonNBounded A).mp hA).closure

theorem bounded_finite_union : BalancedBoundedSpec.BoundedFiniteUnion := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ ι I hI A hA
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  exact (bounded_iff_isVonNBounded _).mpr
    ((Bornology.isVonNBounded_biUnion hI).mpr fun i hi =>
      (bounded_iff_isVonNBounded _).mp (hA i hi))

theorem bounded_finite_sum : BalancedBoundedSpec.BoundedFiniteSum := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ ι I A hA
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  classical
  apply (bounded_iff_isVonNBounded _).mpr
  induction I using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    change Bornology.IsVonNBounded ℝ ({0} : Set E)
    exact Bornology.isVonNBounded_singleton (𝕜 := ℝ) (0 : E)
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    exact ((bounded_iff_isVonNBounded _).mp (hA i (Finset.mem_insert_self i I))).add
      (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

theorem bounded_scalar_multiple : BalancedBoundedSpec.BoundedScalarMultiple := by
  intro 𝕜 E _ _ _ _ _ _ _ _ _ c A hA
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let T : E →L[ℝ] E :=
    { toFun := fun x => c • x
      map_add' := smul_add c
      map_smul' := fun r x => smul_comm c r x
      cont := continuous_const_smul c }
  exact (bounded_iff_isVonNBounded _).mpr
    (((bounded_iff_isVonNBounded _).mp hA).image T)

theorem linear_continuous_iff_at_zero : BalancedBoundedSpec.LinearContinuityAtZero := by
  intro 𝕜 E F _ _ _ _ _ _ _ _ _ _ _ _ _ T
  exact ⟨fun h => h.continuousAt, fun h => continuous_of_continuousAt_zero T h⟩

theorem continuous_linear_image_bounded :
    BalancedBoundedSpec.ContinuousLinearImageBounded := by
  intro 𝕜 E F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T hT A hA
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  let : ContinuousSMul ℝ F := IsScalarTower.continuousSMul 𝕜
  let S : E →L[ℝ] F := ⟨T.restrictScalars ℝ, hT⟩
  exact (bounded_iff_isVonNBounded _).mpr
    (((bounded_iff_isVonNBounded _).mp hA).image S)

end ExpandedFA.P1
