import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.BasePolytope
import MathGenome.Internal.ExtremalOptimization.P205.Matroids.GreedyBasis
import MathGenome.Internal.ExtremalOptimization.P205.Convex.FiniteHullSupport
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Tactic.NormNum

namespace P205.Matroids
open scoped BigOperators
noncomputable section
universe u
variable {α : Type u} (M : Matroid α) [M.Finite]

theorem subsetSum_add (x y : Coordinates M) (S : Set α) :
    subsetSum M (x + y) S = subsetSum M x S + subsetSum M y S := by
  classical
  simp only [subsetSum, Specs.P205.Matroids.subsetSumValue, Pi.add_apply,
    ite_add_ite, ← Finset.sum_add_distrib]
  simp

theorem subsetSum_smul (a : ℝ) (x : Coordinates M) (S : Set α) :
    subsetSum M (a • x) S = a * subsetSum M x S := by
  classical
  simp only [subsetSum, Specs.P205.Matroids.subsetSumValue, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero]

theorem convex_baseInequalities : Convex ℝ (baseInequalities M) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨⟨hx0, hxS⟩, hxE⟩
  rcases hy with ⟨⟨hy0, hyS⟩, hyE⟩
  refine ⟨⟨fun e => add_nonneg (mul_nonneg ha (hx0 e))
    (mul_nonneg hb (hy0 e)), ?_⟩, ?_⟩
  · intro S hS
    change subsetSum M (a • x + b • y) S ≤ (rank M S : ℝ)
    rw [subsetSum_add, subsetSum_smul, subsetSum_smul]
    calc
      _ ≤ a * (rank M S : ℝ) + b * (rank M S : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left (hxS S hS) ha)
          (mul_le_mul_of_nonneg_left (hyS S hS) hb)
      _ = _ := by rw [← add_mul, hab, one_mul]
  · change subsetSum M x M.E = (rank M M.E : ℝ) at hxE
    change subsetSum M y M.E = (rank M M.E : ℝ) at hyE
    change subsetSum M (a • x + b • y) M.E = (rank M M.E : ℝ)
    rw [subsetSum_add, subsetSum_smul, subsetSum_smul, hxE, hyE,
      ← add_mul, hab, one_mul]

theorem basis_indicator_mem {B : Set α} (hB : M.IsBase B) :
    indicator M B ∈ baseInequalities M := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro e
    change 0 ≤ if (e : α) ∈ B then (1 : ℝ) else 0
    split_ifs <;> norm_num
  · intro S hS
    change subsetSum M (indicator M B) S ≤ (rank M S : ℝ)
    have hsum := indicator_sum M B S
    change subsetSum M (indicator M B) S = _ at hsum
    rw [hsum, Set.inter_eq_left.mpr
      ((Set.inter_subset_right : B ∩ S ⊆ S).trans hS)]
    exact Nat.cast_le.mpr ((rank_maximum M S hS).2 _ Set.inter_subset_right
      (hB.indep.subset Set.inter_subset_left))
  · change subsetSum M (indicator M B) M.E = (rank M M.E : ℝ)
    have hsum := indicator_sum M B M.E
    change subsetSum M (indicator M B) M.E = _ at hsum
    rw [hsum, Set.inter_eq_left.mpr hB.subset_ground,
      Set.inter_eq_left.mpr hB.subset_ground, (base_rank M B).mp hB |>.2]
    rfl

theorem basisIndicators_finite : (basisIndicators M).Finite := by
  apply (M.ground_finite.finite_subsets.image (indicator M)).subset
  rintro x ⟨B, hB, rfl⟩
  exact ⟨B, hB.subset_ground, rfl⟩

omit [M.Finite] in
theorem basisIndicators_nonempty : (basisIndicators M).Nonempty := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  exact ⟨indicator M B, B, hB, rfl⟩

theorem list_coordinate_sum (l : List M.E) (hn : l.Nodup) (x : Coordinates M) :
    (l.map x).sum = subsetSum M x {a | ∃ e ∈ l, (e : α) = a} := by
  classical
  let := M.ground_finite.fintype
  have he (e : M.E) : (∃ d ∈ l, (d : α) = (e : α)) ↔ e ∈ l := by
    simp only [Subtype.val_inj, exists_eq_right]
  unfold subsetSum Specs.P205.Matroids.subsetSumValue
  simp only [Set.mem_ofPred_eq, he]
  rw [← List.sum_toFinset x hn, ← Finset.sum_filter]
  congr 1
  ext e
  simp

theorem list_coordinate_sum_full (l : List M.E) (hn : l.Nodup)
    (hall : ∀ e, e ∈ l) (x : Coordinates M) :
    (l.map x).sum = subsetSum M x M.E := by
  rw [list_coordinate_sum M l hn]
  congr 1
  ext a
  exact ⟨fun ⟨e, _, he⟩ => he ▸ e.property, fun ha => ⟨⟨a, ha⟩, hall _, rfl⟩⟩

private theorem list_sum_sub {β : Type*} (l : List β) (f g : β → ℝ) :
    (l.map (fun e => f e - g e)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Prefix dominance and equal total sums imply dominance in every signed,
nonincreasing weight direction. In particular the last weight may be negative. -/
theorem dot_le_of_prefix (w x y : Coordinates M) (l : List M.E)
    (hl : GreedyOrdering M w l)
    (hp : ∀ i, subsetSum M x (greedyPrefix M l i) ≤
      subsetSum M y (greedyPrefix M l i))
    (ht : subsetSum M x M.E = subsetSum M y M.E) : dot M w x ≤ dot M w y := by
  have hn := hl.1
  have hall := hl.2.1
  have hs := hl.2.2
  let d : M.E → ℝ := fun e => y e - x e
  have hprefix : ∀ k ≤ l.length, 0 ≤ ((l.take k).map d).sum := by
    intro k _
    rw [show d = (fun e => y e - x e) from rfl, list_sum_sub,
      list_coordinate_sum M _ hn.take, list_coordinate_sum M _ hn.take]
    exact sub_nonneg.mpr (hp k)
  have htotal : (l.map d).sum = 0 := by
    rw [show d = (fun e => y e - x e) from rfl, list_sum_sub,
      list_coordinate_sum_full M l hn hall, list_coordinate_sum_full M l hn hall, ht,
      sub_self]
  have h := FiniteCombinatorics.Matroid.list_weighted_prefix_nonneg l w d hs hprefix htotal
  have hdot : (l.map (fun e => w e * d e)).sum = dot M w y - dot M w x := by
    rw [list_coordinate_sum_full M l hn hall]
    classical
    simp [subsetSum, Specs.P205.Matroids.subsetSumValue, dot,
      Specs.P205.Matroids.dotValue, d, mul_sub, Finset.sum_sub_distrib]
  rw [hdot] at h
  exact sub_nonneg.mp h

/-- The greedy basis bounds every feasible vector in every real direction. -/
theorem baseInequalities_support (x : Coordinates M) (hx : x ∈ baseInequalities M)
    (w : Coordinates M) :
    ∃ B : Set α, M.IsBase B ∧ dot M w x ≤ dot M w (indicator M B) := by
  classical
  let := M.ground_finite.fintype
  let tie : LinearOrder M.E := LinearOrder.lift' (Fintype.equivFin M.E)
    (Fintype.equivFin M.E).injective
  let S := FiniteCombinatorics.Matroid.fromMatroid M
  let l := FiniteCombinatorics.Matroid.greedyEnumeration S w tie
  have hl : GreedyOrdering M w l := by
    refine ⟨FiniteCombinatorics.Matroid.greedyEnumeration_nodup S w tie,
      FiniteCombinatorics.Matroid.greedyEnumeration_mem S w tie, ?_⟩
    exact (FiniteCombinatorics.Matroid.greedyEnumeration_pairwise S w tie).imp
      (by
        intro a b h
        rcases h with h | h
        · exact h.le
        · exact h.1.symm.le)
  let B := greedyOutput M l
  have hB : M.IsBase B := (greedy_basis_optimal M w l hl).1
  refine ⟨B, hB, dot_le_of_prefix M w x (indicator M B) l hl ?_ ?_⟩
  · intro i
    have hP : greedyPrefix M l i ⊆ M.E := by
      rintro a ⟨e, _, rfl⟩
      exact e.property
    have hsum : subsetSum M (indicator M B) (greedyPrefix M l i) =
        ((B ∩ greedyPrefix M l i).ncard : ℝ) := by
      have h := indicator_sum M B (greedyPrefix M l i)
      change subsetSum M (indicator M B) (greedyPrefix M l i) = _ at h
      exact h.trans (congrArg (fun n : ℕ => (n : ℝ))
        (congrArg Set.ncard (Set.inter_eq_left.mpr (Set.inter_subset_right.trans hP))))
    have hr : (B ∩ greedyPrefix M l i).ncard = rank M (greedyPrefix M l i) :=
      greedy_prefix_rank M w l hl i
    rw [hsum, hr]
    exact hx.1.2 _ hP
  · have hy := basis_indicator_mem M hB
    exact hx.2.trans hy.2.symm

/-- The inequality description is exactly the ordinary hull of basis indicators. -/
theorem base_polytope_eq : Specs.P205.Matroids.BasePolytopeEquality := by
  intro α M _
  change convexHull ℝ (basisIndicators M) = baseInequalities M
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_baseInequalities M)
    rintro x ⟨B, hB, rfl⟩
    exact basis_indicator_mem M hB
  · intro x hx
    classical
    let := M.ground_finite.fintype
    let e : Coordinates M ≃ₗ[ℝ] EuclideanSpace ℝ M.E :=
      (WithLp.linearEquiv 2 ℝ (Coordinates M)).symm
    have hfinite := (basisIndicators_finite M).image e
    let F := hfinite.toFinset
    have hF : F.Nonempty := hfinite.toFinset_nonempty.mpr
      ((basisIndicators_nonempty M).image e)
    have hi (v : EuclideanSpace ℝ M.E) (y : Coordinates M) :
        inner ℝ v (e y) = dot M (e.symm v) y := by
      simp [e, dot, Specs.P205.Matroids.dotValue, PiLp.inner_apply, mul_comm]
    have hmem : e x ∈ convexHull ℝ (F : Set (EuclideanSpace ℝ M.E)) := by
      apply P205.finiteHullSupport _ F hF (e x)
      intro v
      obtain ⟨B, hB, hle⟩ := baseInequalities_support M x hx (e.symm v)
      have hz : e (indicator M B) ∈ F := by
        apply hfinite.mem_toFinset.mpr
        exact ⟨indicator M B, ⟨B, hB, rfl⟩, rfl⟩
      exact (hi v x ▸ hle).trans (by
        rw [← hi v (indicator M B)]
        exact Finset.le_sup' (fun z => inner ℝ v z) hz)
    have hFset : (F : Set (EuclideanSpace ℝ M.E)) = e '' basisIndicators M :=
      hfinite.coe_toFinset
    have heq : e '' convexHull ℝ (basisIndicators M) =
        convexHull ℝ (e '' basisIndicators M) :=
      e.toLinearMap.image_convexHull (basisIndicators M)
    rw [hFset, ← heq] at hmem
    obtain ⟨y, hy, he⟩ := hmem
    exact e.injective he ▸ hy

/-- Every basis indicator is a vertex: it is already a vertex of the enclosing
unit cube. This argument also applies when the coordinate type is empty. -/
theorem basis_indicator_extreme {B : Set α} (hB : M.IsBase B) :
    indicator M B ∈ (convexHull ℝ (basisIndicators M)).extremePoints ℝ := by
  let C : Set (Coordinates M) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)
  have hcube : convexHull ℝ (basisIndicators M) ⊆ C := by
    apply convexHull_min _ (convex_pi (fun _ _ => convex_Icc (0 : ℝ) 1))
    rintro x ⟨D, _, rfl⟩ e _
    classical
    change (if (e : α) ∈ D then (1 : ℝ) else 0) ∈ Set.Icc 0 1
    split_ifs <;> norm_num
  have hvertex : indicator M B ∈ C.extremePoints ℝ := by
    rw [show C = Set.univ.pi (fun _ : M.E => Set.Icc (0 : ℝ) 1) from rfl,
      extremePoints_pi]
    intro e _
    rw [Set.extremePoints_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    classical
    change (if (e : α) ∈ B then (1 : ℝ) else 0) ∈ ({0, 1} : Set ℝ)
    split_ifs <;> simp
  exact inter_extremePoints_subset_extremePoints_of_subset hcube
    ⟨subset_convexHull ℝ (basisIndicators M) ⟨B, hB, rfl⟩, hvertex⟩

theorem base_polytope_extremePoints : Specs.P205.Matroids.BasePolytopeExtremePoints := by
  intro α M _
  change (baseInequalities M).extremePoints ℝ = basisIndicators M
  have heq : convexHull ℝ (basisIndicators M) = baseInequalities M := base_polytope_eq M
  rw [← heq]
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  rintro x ⟨B, hB, rfl⟩
  exact basis_indicator_extreme M hB

theorem base_polytope_zeroOne : Specs.P205.Matroids.BasePolytopeZeroOne := by
  intro α M _ x hx e
  have heq : (baseInequalities M).extremePoints ℝ = basisIndicators M :=
    base_polytope_extremePoints M
  change x ∈ (baseInequalities M).extremePoints ℝ at hx
  rw [heq] at hx
  obtain ⟨B, _, rfl⟩ := hx
  classical
  change (if (e : α) ∈ B then (1 : ℝ) else 0) = 0 ∨
    (if (e : α) ∈ B then (1 : ℝ) else 0) = 1
  split_ifs <;> simp

theorem base_polytope_integral : Specs.P205.Matroids.BasePolytopeIntegral := by
  intro α M _ x hx
  classical
  refine ⟨fun e => if x e = 0 then 0 else 1, ?_⟩
  intro e
  rcases base_polytope_zeroOne M x hx e with h | h
  · simp [h]
  · simp [h]

end
end P205.Matroids
