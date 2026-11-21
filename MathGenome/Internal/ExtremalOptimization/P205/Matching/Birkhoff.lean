import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.Birkhoff
import Mathlib.Analysis.Convex.Birkhoff

open Finset Matrix

namespace P205.Matching.Birkhoff

theorem unrestricted_decomposition : Specs.P205.Matching.Birkhoff.UnrestrictedDecomposition := by
  intro n _ _ M hM
  exact exists_eq_sum_perm_of_mem_doublyStochastic hM

theorem unrestricted_hull : Specs.P205.Matching.Birkhoff.UnrestrictedHull := by
  intro n _ _
  exact doublyStochastic_eq_convexHull_permMatrix

theorem unrestricted_extreme_points :
    Specs.P205.Matching.Birkhoff.UnrestrictedExtremePoints := by
  intro n _ _
  exact extremePoints_doublyStochastic

/-- Nonnegative terms cannot cancel at a zero coordinate. -/
theorem zero_support_bridge : Specs.P205.Matching.Birkhoff.ZeroSupportBridge := by
  intro n _ _ M w hw hsum σ hσ i j hij
  have hs : ∑ τ, w τ * τ.permMatrix ℝ i j = 0 := by
    have h := congrArg (fun N : Matrix n n ℝ => N i j) hsum
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hij] using h
  have ht : w σ * σ.permMatrix ℝ i j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ =>
      mul_nonneg (hw τ) (nonneg_of_mem_doublyStochastic permMatrix_mem_doublyStochastic))).1 hs
      σ (Finset.mem_univ σ)
  exact (mul_eq_zero.mp ht).resolve_left hσ

theorem restricted_decomposition : Specs.P205.Matching.Birkhoff.RestrictedDecomposition := by
  intro n _ _ allowed M hM
  obtain ⟨w, hw, hw1, hsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM.1
  refine ⟨w, hw, hw1, hsum, ?_⟩
  intro σ hσ i
  by_contra hnot
  have hz := zero_support_bridge n M w hw hsum σ hσ i (σ i) (hM.2 i (σ i) hnot)
  simp [Equiv.toPEquiv_apply] at hz

/-- Prescribing zero entries preserves convexity. -/
lemma convex_restricted {n : Type*} [Fintype n] [DecidableEq n]
    (allowed : n → n → Prop) : Convex ℝ (restrictedDoublyStochastic allowed) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_doublyStochastic hx.1 hy.1 ha hb hab, ?_⟩
  intro i j hij
  simp [Matrix.add_apply, Matrix.smul_apply, hx.2 i j hij, hy.2 i j hij]

lemma supported_permutation_mem {n : Type*} [Fintype n] [DecidableEq n]
    {allowed : n → n → Prop} {M : Matrix n n ℝ}
    (hM : M ∈ supportedPermutationMatrices allowed) :
    M ∈ restrictedDoublyStochastic allowed := by
  obtain ⟨σ, hσ, rfl⟩ := hM
  refine ⟨permMatrix_mem_doublyStochastic, ?_⟩
  intro i j hij
  have hne : σ i ≠ j := fun h => hij (h ▸ hσ i)
  simp [Equiv.toPEquiv_apply, hne]

theorem restricted_hull : Specs.P205.Matching.Birkhoff.RestrictedHull := by
  intro n _ _ allowed
  classical
  apply Set.Subset.antisymm
  · intro M hM
    obtain ⟨w, hw, hw1, hsum, hsupp⟩ := restricted_decomposition n allowed M hM
    let s : Set (Equiv.Perm n) := {σ | w σ ≠ 0}
    have hw1' : ∑ σ : s, w σ = 1 := by
      rw [← Finset.sum_congr_set s w (fun σ : s => w σ) (by intros; rfl)
        (by intro σ hσ; simpa [s] using hσ)]
      exact hw1
    have hsum' : ∑ σ : s, w σ • (σ : Equiv.Perm n).permMatrix ℝ = M := by
      rw [← Finset.sum_congr_set s (fun σ => w σ • σ.permMatrix ℝ)
        (fun σ : s => w σ • (σ : Equiv.Perm n).permMatrix ℝ) (by intros; rfl)
        (by
          intro σ hσ
          have hz : w σ = 0 := by simpa [s] using hσ
          simp [hz])]
      exact hsum
    exact mem_convexHull_of_exists_fintype (fun σ : s => w σ)
      (fun σ : s => (σ : Equiv.Perm n).permMatrix ℝ) (fun σ => hw σ) hw1'
      (fun σ => ⟨σ, hsupp σ σ.property, rfl⟩) hsum'
  · exact convexHull_min (fun _ hM => supported_permutation_mem hM) (convex_restricted allowed)

theorem restricted_extreme_points : Specs.P205.Matching.Birkhoff.RestrictedExtremePoints := by
  intro n _ _ allowed
  apply Set.Subset.antisymm
  · rw [restricted_hull n allowed]
    exact extremePoints_convexHull_subset
  · intro M hM
    have hM' : M ∈ Set.extremePoints ℝ (doublyStochastic ℝ n : Set (Matrix n n ℝ)) := by
      rw [extremePoints_doublyStochastic]
      obtain ⟨σ, _, rfl⟩ := hM
      exact ⟨σ, rfl⟩
    exact inter_extremePoints_subset_extremePoints_of_subset
      (fun _ h => h.1) ⟨supported_permutation_mem hM, hM'⟩

theorem infeasible_allowed_relation : Specs.P205.Matching.Birkhoff.InfeasibleAllowedRelation := by
  intro n _ _ allowed hnone
  have hempty : supportedPermutationMatrices allowed = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro M ⟨σ, hσ, _⟩
    exact hnone ⟨σ, hσ⟩
  have hhull : convexHull ℝ (supportedPermutationMatrices allowed) = ∅ := by
    rw [hempty, convexHull_empty]
  have hrestricted : restrictedDoublyStochastic allowed = ∅ := by
    rw [restricted_hull n allowed, hhull]
  exact ⟨hrestricted, hhull, by rw [hrestricted, extremePoints_empty]⟩

end P205.Matching.Birkhoff
