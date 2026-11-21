import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertTotalityBoundary
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.PreHilbertBesselParseval

noncomputable section
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
namespace ExpandedFA.Hilbert.PreHilbertTotalityBoundary
universe u v w

theorem expansions : Spec.Expansions.{u,v,w} :=
  ⟨PreHilbertBesselParseval.finite_projection_identity,
   PreHilbertBesselParseval.bessel,
   PreHilbertBesselParseval.countable_coefficient_support,
   PreHilbertBesselParseval.closedSpan_iff_net_convergence,
   PreHilbertBesselParseval.net_convergence_iff_parseval,
   PreHilbertBesselParseval.total_iff_parseval⟩

theorem dense_implies_zero_annihilator : Spec.DenseImpliesZeroAnnihilator.{u,v} := by
  intro 𝕜 E _ _ _ M hM
  rw [← M.orthogonal_closure, hM, Submodule.top_orthogonal_eq_bot]

theorem hilbert_converse : Spec.HilbertConverse.{u,v} := by
  intro 𝕜 E _ _ _ _ M hM
  rw [← M.orthogonal_orthogonal_eq_closure, hM, Submodule.bot_orthogonal_eq_top]

section Graph
variable {𝕜 : Type u} [RCLike 𝕜]

@[simp] theorem graphGenerator_none (n : ℕ) : graphGenerator 𝕜 n none = 1 := by
  simp [graphGenerator, lp.single_apply]

@[simp] theorem graphGenerator_some (n j : ℕ) :
    graphGenerator 𝕜 n (some j) = if j = n then 1 else 0 := by
  simp [graphGenerator, lp.single_apply, Pi.single_apply]

@[simp] theorem graphMap_none (a : ℕ →₀ 𝕜) :
    graphMap 𝕜 a none = a.sum (fun _ c => c) := by
  change (lp.evalₗ (𝕜 := 𝕜) (fun _ : Option ℕ => 𝕜) 2 none) (graphMap 𝕜 a) = _
  simp [graphMap, Finsupp.linearCombination_apply, Finsupp.sum]

@[simp] theorem graphMap_some (a : ℕ →₀ 𝕜) (n : ℕ) : graphMap 𝕜 a (some n) = a n := by
  classical
  change (lp.evalₗ (𝕜 := 𝕜) (fun _ : Option ℕ => 𝕜) 2 (some n)) (graphMap 𝕜 a) = _
  simp [graphMap, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.mem_support_iff]
  exact fun h => h.symm

@[simp] theorem firstCoordinate_apply (x : GraphSpace 𝕜) : firstCoordinate 𝕜 x = x.val none := rfl

@[simp] theorem firstCoordinate_generator (n : ℕ) : firstCoordinate 𝕜 (generator 𝕜 n) = 1 := by
  simp [generator]

end Graph

theorem graph_coordinates : Spec.GraphCoordinates.{u} := by
  intro 𝕜 _ f
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, graphMap_none a, graphMap_some a⟩
  · rintro ⟨a, h₀, ha⟩
    refine ⟨a, ?_⟩
    apply lp.ext
    funext i
    cases i with
    | none => simpa using h₀.symm
    | some n => simpa using (ha n).symm

theorem graph_norm : Spec.GraphNorm.{u} := by
  intro 𝕜 _ a
  classical
  have hn : ‖graphMap 𝕜 a‖ ^ 2 = ∑' i : Option ℕ, ‖graphMap 𝕜 a i‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (graphMap 𝕜 a)
  rw [hn, tsum_eq_sum (s := insert none (a.support.image some))]
  · simp [Finset.sum_image]
  · intro i hi
    cases i with
    | none => exact False.elim (hi (Finset.mem_insert_self _ _))
    | some n =>
      have hmem : n ∉ a.support := by
        intro h
        exact hi (Finset.mem_insert_of_mem (Finset.mem_image_of_mem some h))
      simp [Finsupp.notMem_support_iff.mp hmem]

theorem zero_sum_coordinates : Spec.ZeroSumCoordinates.{u} := by
  intro 𝕜 _ x
  constructor
  · intro hx
    have hx0 : x.val none = 0 := hx
    obtain ⟨a, h₀, ha⟩ := (graph_coordinates 𝕜 x.val).mp x.property
    exact ⟨a, hx0, h₀.symm.trans hx0, ha⟩
  · rintro ⟨a, hx0, _, _⟩
    exact hx0

theorem closed_proper : Spec.ClosedProper.{u} := by
  intro 𝕜 _
  refine ⟨(firstCoordinate 𝕜).isClosed_ker, ?_⟩
  intro h
  have hmem : generator 𝕜 0 ∈ zeroSumSpace 𝕜 := by rw [h]; trivial
  have : firstCoordinate 𝕜 (generator 𝕜 0) = 0 := hmem
  simp only [firstCoordinate_generator, one_ne_zero] at this

section Annihilator
variable {𝕜 : Type u} [RCLike 𝕜]

theorem inner_generator (n : ℕ) (x : GraphSpace 𝕜) :
    ⟪generator 𝕜 n, x⟫_𝕜 = x.val none + x.val (some n) := by
  change ⟪graphGenerator 𝕜 n, x.val⟫_𝕜 = _
  simp [graphGenerator, inner_add_left, lp.inner_single_left]

theorem generator_sub_mem (n j : ℕ) :
    generator 𝕜 n - generator 𝕜 j ∈ zeroSumSpace 𝕜 := by
  change firstCoordinate 𝕜 (_ - _) = 0
  simp only [map_sub, firstCoordinate_generator, sub_self]

end Annihilator

theorem zero_annihilator : Spec.ZeroAnnihilator.{u} := by
  intro 𝕜 _
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨k, hk⟩ := a.support.exists_notMem
  have hak : a k = 0 := Finsupp.notMem_support_iff.mp hk
  have htail (n : ℕ) : x.val (some n) = x.val (some k) := by
    have h := (Submodule.mem_orthogonal _ _).mp hx
      (generator 𝕜 n - generator 𝕜 k) (generator_sub_mem n k)
    rw [inner_sub_left, inner_generator, inner_generator] at h
    exact add_left_cancel (sub_eq_zero.mp h)
  have haz : a = 0 := by
    ext n
    have h := htail n
    rw [← ha, graphMap_some, graphMap_some, hak] at h
    exact h
  have hxz : x = 0 := by
    apply Subtype.ext
    rw [← ha, haz, map_zero]
    rfl
  exact hxz

theorem incomplete : Spec.Incomplete.{u} := by
  intro 𝕜 _ hc
  let := hc
  have hd := hilbert_converse 𝕜 (GraphSpace 𝕜) (zeroSumSpace 𝕜) (zero_annihilator 𝕜)
  have hclosed := (closed_proper 𝕜).1
  have heq : (zeroSumSpace 𝕜).topologicalClosure = zeroSumSpace 𝕜 :=
    hclosed.submodule_topologicalClosure_eq
  exact (closed_proper 𝕜).2 (heq.symm.trans hd)

section GramSchmidt
variable {𝕜 : Type u} [RCLike 𝕜]

def tailCoordinate (n : ℕ) : GraphSpace 𝕜 →ₗ[𝕜] 𝕜 :=
  (lp.evalₗ (𝕜 := 𝕜) (fun _ : Option ℕ => 𝕜) 2 (some n)).comp
    (graphSpace 𝕜).subtype

@[simp] theorem tailCoordinate_generator (n j : ℕ) :
    tailCoordinate n (generator 𝕜 j) = if n = j then 1 else 0 := by
  exact graphGenerator_some j n

@[simp] theorem tailCoordinate_difference (n j : ℕ) :
    tailCoordinate n (differenceSequence 𝕜 j) =
      (if n = j then 1 else 0) - (if n = j + 1 then 1 else 0) := by
  simp only [differenceSequence, map_sub, tailCoordinate_generator]

theorem combination_difference_zero (a : ℕ →₀ 𝕜) :
    tailCoordinate 0 (Finsupp.linearCombination 𝕜 (differenceSequence 𝕜) a) = a 0 := by
  classical
  simp [Finsupp.linearCombination_apply, Finsupp.sum]
  exact fun h => h.symm

theorem combination_difference_succ (a : ℕ →₀ 𝕜) (n : ℕ) :
    tailCoordinate (n + 1) (Finsupp.linearCombination 𝕜 (differenceSequence 𝕜) a) =
      a (n + 1) - a n := by
  classical
  simp [Finsupp.linearCombination_apply, Finsupp.sum, mul_sub, Finset.sum_sub_distrib,
    Nat.add_right_cancel_iff]
  split_ifs <;> simp_all

theorem differences_independent : LinearIndependent 𝕜 (differenceSequence 𝕜) := by
  apply linearIndependent_iff.mpr
  intro a ha
  have hz : a 0 = 0 := by
    have := congrArg (tailCoordinate 0) ha
    simpa only [combination_difference_zero, map_zero] using this
  have hs (n : ℕ) : a (n + 1) - a n = 0 := by
    have := congrArg (tailCoordinate (n + 1)) ha
    simpa only [combination_difference_succ, map_zero] using this
  ext n
  change a n = 0
  induction n with
  | zero => exact hz
  | succ n hn => simpa only [hn, sub_zero] using hs n

/-- Each generator difference is a finite telescoping sum of adjacent differences. -/
theorem generator_sub_zero_mem_span (n : ℕ) :
    generator 𝕜 n - generator 𝕜 0 ∈
      Submodule.span 𝕜 (Set.range (differenceSequence 𝕜)) := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hd : differenceSequence 𝕜 n ∈
        Submodule.span 𝕜 (Set.range (differenceSequence 𝕜)) :=
      Submodule.subset_span (Set.mem_range_self n)
    have heq : generator 𝕜 (n + 1) - generator 𝕜 0 =
        (generator 𝕜 n - generator 𝕜 0) - differenceSequence 𝕜 n := by
      unfold differenceSequence
      abel
    rw [heq]
    exact Submodule.sub_mem _ hn hd

theorem generator_combination (a : ℕ →₀ 𝕜) :
    (a.sum (fun n c => c • generator 𝕜 n) : GraphSpace 𝕜).val = graphMap 𝕜 a := by
  simp only [graphMap, Finsupp.linearCombination_apply, Finsupp.sum,
    Submodule.coe_sum, Submodule.coe_smul, generator]

theorem differences_span :
    Submodule.span 𝕜 (Set.range (differenceSequence 𝕜)) = zeroSumSpace 𝕜 := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact generator_sub_mem n (n + 1)
  · intro x hx
    obtain ⟨a, ha⟩ := x.property
    have hsum : a.sum (fun _ c => c) = 0 := by
      have h : firstCoordinate 𝕜 x = 0 := hx
      rw [firstCoordinate_apply, ← ha, graphMap_none] at h
      exact h
    have heq : a.sum (fun n c => c • generator 𝕜 n) = x := by
      apply Subtype.ext
      rw [generator_combination, ha]
    have heq' : a.sum (fun n c => c • (generator 𝕜 n - generator 𝕜 0)) = x := by
      rw [Finsupp.sum, Finset.sum_congr rfl (fun _ _ => smul_sub _ _ _),
        Finset.sum_sub_distrib, ← Finset.sum_smul]
      change a.sum (fun n c => c • generator 𝕜 n) -
        a.sum (fun _ c => c) • generator 𝕜 0 = x
      rw [hsum, zero_smul, sub_zero, heq]
    rw [← heq', Finsupp.sum]
    exact Submodule.sum_mem _ (fun n _ =>
      Submodule.smul_mem _ _ (generator_sub_zero_mem_span n))

end GramSchmidt

theorem gram_schmidt_boundary : Spec.GramSchmidtBoundary.{u} := by
  intro 𝕜 _
  have hs : Submodule.span 𝕜 (Set.range (normalizedSequence 𝕜)) = zeroSumSpace 𝕜 := by
    rw [normalizedSequence, InnerProductSpace.span_gramSchmidtNormed_range,
      InnerProductSpace.span_gramSchmidt, differences_span]
  refine ⟨differences_independent,
    InnerProductSpace.gramSchmidtNormed_orthonormal differences_independent,
    differences_span, hs, ?_, ?_⟩
  · rw [hs]
    exact (closed_proper 𝕜).1.submodule_topologicalClosure_eq
  · rw [hs]
    exact zero_annihilator 𝕜

end ExpandedFA.Hilbert.PreHilbertTotalityBoundary
