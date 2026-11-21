import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.IndependencePolytope
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.Models
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.GreedyBasis
import MathGenome.Internal.ExtremalOptimization.P205.Convex.FiniteHullSupport
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The first assertion of paper.tex, Theorem 9.4 (W46).
The reverse inclusion bounds every signed objective. Greedy prefix ranks bound
its nonnegative part, and deleting nonpositive elements of the greedy basis
realizes that bound with an independent indicator. The finite-hull support
lemma then applies after transporting coordinate functions to Euclidean space.
-/
namespace P205.Matroids
open scoped BigOperators
noncomputable section
universe u

/-- Summing coordinates over a prefix is summing its list, without repetitions. -/
private theorem prefix_sum {α : Type u} (M : Matroid α) [M.Finite]
    (l : List M.E) (hn : l.Nodup) (x : Coordinates M) (k : ℕ) :
    ((l.take k).map x).sum = subsetSum M x (greedyPrefix M l k) := by
  classical
  let := M.ground_finite.fintype
  rw [← List.sum_toFinset _ hn.take]
  change (∑ e ∈ (l.take k).toFinset, x e) =
    ∑ e : M.E, if (e : α) ∈ greedyPrefix M l k then x e else 0
  have hmem (e : M.E) : (e : α) ∈ greedyPrefix M l k ↔ e ∈ l.take k := by
    constructor
    · rintro ⟨f, hf, he⟩
      exact (Subtype.ext he) ▸ hf
    · intro he
      exact ⟨e, he, rfl⟩
  simp_rw [hmem]
  have hfin : (l.take k).toFinset = Finset.univ.filter (fun e => e ∈ l.take k) := by
    ext e; simp
  rw [hfin, Finset.sum_filter]

private theorem full_list_sum {α : Type u} (M : Matroid α) [M.Finite]
    [Fintype M.E] (l : List M.E) (hn : l.Nodup) (hall : ∀ e, e ∈ l) (x : Coordinates M) :
    (l.map x).sum = ∑ e : M.E, x e := by
  classical
  have h : l.toFinset = Finset.univ := by ext e; simp [hall]
  rw [← List.sum_toFinset _ hn, h]

private theorem list_sum_difference {β : Type*} (l : List β) (f g : β → ℝ) :
    (l.map (fun e => f e - g e)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Every signed linear objective is bounded by an independent indicator. -/
theorem independent_support {α : Type u} (M : Matroid α) [M.Finite]
    (x : Coordinates M) (hx : x ∈ rankInequalities M) (w : Coordinates M) :
    ∃ I : Set α, M.Indep I ∧ dot M w x ≤ dot M w (indicator M I) := by
  classical
  let := M.ground_finite.fintype
  let v : Coordinates M := fun e => max (w e) 0
  let tie : LinearOrder M.E :=
    LinearOrder.lift' (Fintype.equivFin M.E) (Fintype.equivFin M.E).injective
  let S := FiniteCombinatorics.Matroid.fromMatroid M
  let l := FiniteCombinatorics.Matroid.greedyEnumeration S v tie
  have hn : l.Nodup := FiniteCombinatorics.Matroid.greedyEnumeration_nodup S v tie
  have hall : ∀ e, e ∈ l := FiniteCombinatorics.Matroid.greedyEnumeration_mem S v tie
  have hs : l.Pairwise (fun a b => v b ≤ v a) :=
    (FiniteCombinatorics.Matroid.greedyEnumeration_pairwise S v tie).imp (by
      intro a b h; rcases h with h | h; exact h.le; exact h.1.symm.le)
  have hl : GreedyOrdering M v l := ⟨hn, hall, hs⟩
  let G := greedyOutput M l
  have hG : M.IsBase G := (greedy_basis_optimal M v l hl).1
  let d : Coordinates M := fun e => indicator M G e - x e
  have hp : ∀ k ≤ l.length, 0 ≤ ((l.take k).map d).sum := by
    intro k _
    have hP : greedyPrefix M l k ⊆ M.E := by
      rintro a ⟨e, _, rfl⟩; exact e.property
    have hbound := hx.2 (greedyPrefix M l k) hP
    have hcard := greedy_prefix_rank M v l hl k
    have heq : subsetSum M (indicator M G) (greedyPrefix M l k) =
        (rank M (greedyPrefix M l k) : ℝ) := by
      change Specs.P205.Matroids.subsetSumValue M (Specs.P205.Matroids.indicatorValue M G) _ = _
      rw [indicator_sum]
      have hset : G ∩ greedyPrefix M l k ∩ M.E = G ∩ greedyPrefix M l k :=
        Set.inter_eq_left.mpr (Set.inter_subset_left.trans hG.subset_ground)
      rw [hset]
      exact_mod_cast hcard
    change 0 ≤ ((l.take k).map (fun e => indicator M G e - x e)).sum
    rw [list_sum_difference, prefix_sum M l hn, prefix_sum M l hn]
    exact sub_nonneg.mpr (hbound.trans_eq heq.symm)
  have hv := FiniteCombinatorics.Matroid.list_weighted_prefix_lower_bound l v d 0 hs
    (fun e _ => le_max_right _ _) hp
  have hweighted : dot M v x ≤ dot M v (indicator M G) := by
    simp only [zero_mul] at hv
    rw [full_list_sum M l hn hall] at hv
    change 0 ≤ ∑ e : M.E, v e * (indicator M G e - x e) at hv
    simp_rw [mul_sub] at hv
    rw [Finset.sum_sub_distrib] at hv
    exact sub_nonneg.mp hv
  let I : Set α := {a | a ∈ G ∧ ∃ h : a ∈ M.E, 0 < w ⟨a, h⟩}
  refine ⟨I, hG.indep.subset (fun _ h => h.1), ?_⟩
  have hwv : dot M w x ≤ dot M v x := by
    apply Finset.sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hx.1 e)
  have hrestrict : dot M v (indicator M G) = dot M w (indicator M I) := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases hGmem : (e : α) ∈ G
    · by_cases hw : 0 < w e
      · simp [indicator, Specs.P205.Matroids.indicatorValue, I, hGmem, hw, v,
          max_eq_left hw.le]
      · have hw' : w e ≤ 0 := le_of_not_gt hw
        simp [indicator, Specs.P205.Matroids.indicatorValue, I, hGmem, hw, v,
          max_eq_right hw']
    · simp [indicator, Specs.P205.Matroids.indicatorValue, I, hGmem]
  exact hwv.trans (hweighted.trans_eq hrestrict)

/-- Independent indicators satisfy every ground-subset inequality. -/
theorem indicator_mem_rankInequalities {α : Type u} (M : Matroid α) [M.Finite]
    {I : Set α} (hI : M.Indep I) : indicator M I ∈ rankInequalities M := by
  classical
  constructor
  · intro e
    change 0 ≤ if (e : α) ∈ I then (1 : ℝ) else 0
    split_ifs <;> norm_num
  · intro S hS
    have hle := (rank_maximum M S hS).2 (I ∩ S ∩ M.E)
      (fun _ h => h.1.2) (hI.subset (fun _ h => h.1.1))
    change Specs.P205.Matroids.subsetSumValue M (Specs.P205.Matroids.indicatorValue M I) S ≤ _
    rw [indicator_sum]
    exact_mod_cast hle

private theorem subsetSum_combination {α : Type u} (M : Matroid α) [M.Finite]
    (x y : Coordinates M) (a b : ℝ) (S : Set α) :
    subsetSum M (a • x + b • y) S = a * subsetSum M x S + b * subsetSum M y S := by
  classical
  let := M.ground_finite.fintype
  change (∑ e : M.E, if (e : α) ∈ S then a * x e + b * y e else 0) = _
  have h (e : M.E) :
      (if (e : α) ∈ S then a * x e + b * y e else 0) =
        a * (if (e : α) ∈ S then x e else 0) +
        b * (if (e : α) ∈ S then y e else 0) := by split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- The rank constraints form a convex set. -/
theorem convex_rankInequalities {α : Type u} (M : Matroid α) [M.Finite] :
    Convex ℝ (rankInequalities M) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro e
    change 0 ≤ a * x e + b * y e
    exact add_nonneg (mul_nonneg ha (hx.1 e)) (mul_nonneg hb (hy.1 e))
  · intro S hS
    change subsetSum M (a • x + b • y) S ≤ (rank M S : ℝ)
    rw [subsetSum_combination]
    calc
      _ ≤ a * (rank M S : ℝ) + b * (rank M S : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left (hx.2 S hS) ha)
          (mul_le_mul_of_nonneg_left (hy.2 S hS) hb)
      _ = (rank M S : ℝ) := by rw [← add_mul, hab, one_mul]

/-- The independent indicators form a finite family on the actual ground. -/
private theorem independentIndicators_finite {α : Type u} (M : Matroid α) [M.Finite] :
    (independentIndicators M).Finite := by
  have hf : {I : Set α | M.Indep I}.Finite :=
    M.ground_finite.finite_subsets.subset (fun I hI => hI.subset_ground)
  have heq : independentIndicators M = indicator M '' {I : Set α | M.Indep I} := by
    ext x
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨I, hI, rfl⟩
    · rintro ⟨I, hI, rfl⟩
      exact ⟨I, hI, rfl⟩
  rw [heq]
  exact hf.image _

/-- The Euclidean finite-hull lemma transported to ordinary real coordinate functions. -/
private theorem coordinate_hull_support {ι : Type*} [Fintype ι]
    (F : Set (ι → ℝ)) (hf : F.Finite) (hne : F.Nonempty) (x : ι → ℝ)
    (hbound : ∀ w : ι → ℝ, ∃ z ∈ F,
      (∑ i, w i * x i) ≤ ∑ i, w i * z i) : x ∈ convexHull ℝ F := by
  classical
  let e := WithLp.linearEquiv 2 ℝ (ι → ℝ)
  let G : Finset (EuclideanSpace ℝ ι) := hf.toFinset.image e.symm
  have hG : G.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨e.symm z, Finset.mem_image.mpr ⟨z, hf.mem_toFinset.mpr hz, rfl⟩⟩
  have hx : e.symm x ∈ convexHull ℝ (G : Set (EuclideanSpace ℝ ι)) := by
    apply P205.finiteHullSupport (EuclideanSpace ℝ ι) G hG (e.symm x)
    intro w
    obtain ⟨z, hz, hle⟩ := hbound (e w)
    have hmem : e.symm z ∈ G :=
      Finset.mem_image.mpr ⟨z, hf.mem_toFinset.mpr hz, rfl⟩
    have hinner : inner ℝ w (e.symm x) ≤ inner ℝ w (e.symm z) := by
      simpa [PiLp.inner_apply, mul_comm, e] using hle
    exact hinner.trans (Finset.le_sup' (fun z => inner ℝ w z) hmem)
  have himage : e '' (G : Set (EuclideanSpace ℝ ι)) = F := by
    ext z
    simp only [Set.mem_image, Finset.mem_coe, G, Finset.mem_image]
    constructor
    · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
      simpa using hf.mem_toFinset.mp ha
    · intro hz
      exact ⟨e.symm z, ⟨z, hf.mem_toFinset.mpr hz, rfl⟩, e.apply_symm_apply z⟩
  have hm := Set.mem_image_of_mem (f := e) hx
  have hmap : e '' convexHull ℝ (G : Set (EuclideanSpace ℝ ι)) = convexHull ℝ F := by
    calc
      _ = convexHull ℝ (e '' (G : Set (EuclideanSpace ℝ ι))) :=
        e.toLinearMap.image_convexHull _
      _ = _ := congrArg (convexHull ℝ) himage
  rw [hmap] at hm
  simpa using hm

/-- The independence polytope of every finite matroid is given by its rank inequalities. -/
theorem independence_polytope : Specs.P205.Matroids.IndependencePolytope := by
  intro α M _
  change convexHull ℝ (independentIndicators M) = rankInequalities M
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_rankInequalities M)
    rintro x ⟨I, hI, rfl⟩
    exact indicator_mem_rankInequalities M hI
  · intro x hx
    let := M.ground_finite.fintype
    apply coordinate_hull_support (independentIndicators M) (independentIndicators_finite M)
      ⟨indicator M ∅, ∅, M.empty_indep, rfl⟩ x
    intro w
    obtain ⟨I, hI, hbound⟩ := independent_support M x hx w
    exact ⟨indicator M I, ⟨I, hI, rfl⟩, hbound⟩

end
end P205.Matroids
