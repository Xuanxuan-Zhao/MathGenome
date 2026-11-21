import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InvariantSubspace.TransitiveCompactLemma
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24Schauder
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Algebra.BigOperators.Field

open Set Metric
open scoped Topology BigOperators

namespace ExpandedFA.InvariantSubspace.TransitiveCompactLemma

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The orbit of every nonzero vector under a transitive unital algebra is
dense, without any closure hypothesis on the algebra. -/
theorem dense_orbit (𝒜 : Subalgebra ℂ (X →L[ℂ] X)) (h𝒜 : Spec.IsTransitive 𝒜)
    (y : X) (hy : y ≠ 0) : Dense {z : X | ∃ A ∈ 𝒜, A y = z} := by
  let O : Submodule ℂ X :=
    { carrier := {z : X | ∃ A ∈ 𝒜, A y = z}
      zero_mem' := ⟨0, 𝒜.zero_mem, by simp⟩
      add_mem' := by
        rintro x z ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
        exact ⟨A + B, 𝒜.add_mem hA hB, by simp⟩
      smul_mem' := by
        rintro c x ⟨A, hA, rfl⟩
        exact ⟨c • A, 𝒜.smul_mem hA c, by simp⟩ }
  have hyO : y ∈ O := ⟨1, 𝒜.one_mem, by simp⟩
  have hinv : ∀ A ∈ 𝒜, ∀ z ∈ O.topologicalClosure, A z ∈ O.topologicalClosure := by
    intro A hA z hz
    change A z ∈ closure (O : Set X)
    apply closure_minimal (t := A ⁻¹' closure (O : Set X)) ?_
      (isClosed_closure.preimage A.continuous) hz
    rintro w ⟨B, hB, rfl⟩
    apply subset_closure
    exact ⟨A * B, 𝒜.mul_mem hA hB, by simp⟩
  rcases h𝒜 O.topologicalClosure O.isClosed_topologicalClosure hinv with hbot | htop
  · have hyM := O.le_topologicalClosure hyO
    exact (hy (by simpa [hbot] using hyM)).elim
  · exact (Submodule.dense_iff_topologicalClosure_eq_top).mpr htop

/-- A finite continuous average of algebra members sends a compact set avoiding
zero into any prescribed ball of positive radius. Each value is still an
algebra-orbit point, because the algebra is closed under finite linear sums. -/
theorem averaging_map (𝒜 : Subalgebra ℂ (X →L[ℂ] X)) (h𝒜 : Spec.IsTransitive 𝒜)
    (Q : Set X) (hQ : IsCompact Q) (hQ0 : (0 : X) ∉ Q)
    (x₀ : X) (r : ℝ) (hr : 0 < r) :
    ∃ f : Q → X, Continuous f ∧
      (∀ y, f y ∈ closedBall x₀ r) ∧
      (∀ y : Q, ∃ A ∈ 𝒜, A (y : X) = f y) := by
  classical
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ ℂ X
  let U : 𝒜 → Set X := fun A => {y | ‖(A : X →L[ℂ] X) y - x₀‖ < r}
  have hU : ∀ A, IsOpen (U A) := by
    intro A
    exact isOpen_lt (((A : X →L[ℂ] X).continuous.sub continuous_const).norm)
      continuous_const
  have hcover : Q ⊆ ⋃ A, U A := by
    intro y hy
    have hy0 : y ≠ 0 := fun h => hQ0 (h ▸ hy)
    obtain ⟨_, ⟨A, hA, rfl⟩, hAy⟩ :=
      (dense_orbit 𝒜 h𝒜 y hy0).exists_mem_open isOpen_ball
        ⟨x₀, mem_ball_self hr⟩
    exact mem_iUnion.mpr ⟨⟨A, hA⟩, by simpa [U, mem_ball, dist_eq_norm] using hAy⟩
  obtain ⟨s, hs⟩ := hQ.elim_finite_subcover U hU hcover
  let w : s → Q → ℝ := fun A y => max 0 (r - ‖((A : 𝒜) : X →L[ℂ] X) y - x₀‖)
  have hw : ∀ A y, 0 ≤ w A y := fun _ _ => le_max_left _ _
  have hwcont : ∀ A, Continuous (w A) := by
    intro A
    exact continuous_const.max (continuous_const.sub
      (((((A : 𝒜) : X →L[ℂ] X).continuous.comp continuous_subtype_val).sub
        continuous_const).norm))
  let W : Q → ℝ := fun y => ∑ A : s, w A y
  have hW : ∀ y, 0 < W y := by
    intro y
    obtain ⟨A, hA, hyA⟩ := mem_iUnion₂.mp (hs y.property)
    have hpos : 0 < w ⟨A, hA⟩ y := lt_max_of_lt_right (sub_pos.mpr hyA)
    exact Finset.sum_pos' (fun A _ => hw A y)
      ⟨⟨A, hA⟩, Finset.mem_univ _, hpos⟩
  have hWcont : Continuous W := continuous_finsetSum _ (fun A _ => hwcont A)
  let a : s → Q → ℝ := fun A y => w A y / W y
  have ha : ∀ A y, 0 ≤ a A y := fun A y => div_nonneg (hw A y) (hW y).le
  have hasum : ∀ y, ∑ A : s, a A y = 1 := by
    intro y
    dsimp [a]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (hW y))
  have hacont : ∀ A, Continuous (a A) := by
    intro A
    exact (hwcont A).div hWcont (fun y => ne_of_gt (hW y))
  let f : Q → X := fun y => ∑ A : s, a A y • (((A : 𝒜) : X →L[ℂ] X) y)
  refine ⟨f, ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ (fun A _ => (hacont A).smul
      (((A : 𝒜) : X →L[ℂ] X).continuous.comp continuous_subtype_val))
  · intro y
    apply ball_subset_closedBall
    have h := (convex_ball x₀ r).finsum_mem (fun A => ha A y)
      (by simpa only [finsum_eq_sum_of_fintype] using hasum y)
      (z := fun A : s => ((A : 𝒜) : X →L[ℂ] X) y) ?_
    · simpa only [finsum_eq_sum_of_fintype] using h
    · intro A hA
      have hweight : w A y ≠ 0 := by
        intro hz
        exact hA (by simp [a, hz])
      have hdist : ‖((A : 𝒜) : X →L[ℂ] X) y - x₀‖ < r := by
        by_contra hn
        exact hweight (max_eq_left (sub_nonpos.mpr (le_of_not_gt hn)))
      simpa [mem_ball, dist_eq_norm] using hdist
  · intro y
    let A : X →L[ℂ] X := ∑ B : s, (a B y : ℂ) • ((B : 𝒜) : X →L[ℂ] X)
    refine ⟨A, ?_, ?_⟩
    · exact 𝒜.sum_mem (fun B _ => 𝒜.smul_mem (B : 𝒜).property _)
    · simp only [A, f, sum_apply, smul_apply]
      rfl

/-- Lomonosov's transitive-algebra lemma. We apply the compact-convex
Schauder theorem to `closure (K '' S)`: it is already convex, so no
compact-map extension or closed-convex-hull theorem is needed. -/
theorem transitive_compact : Spec.LomonosovLemma.{u} := by
  intro X _ _ _ 𝒜 h𝒜 K hcompact hK
  classical
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ ℂ X
  have hc : IsCompactOperator K.toLinearMap :=
    (Compactness.compact_iff_isCompactOperator K.toLinearMap).mp hcompact
  obtain ⟨x₀, hx₀⟩ : ∃ x : X, K x ≠ 0 := by
    by_contra hn
    apply hK
    ext x
    simpa using not_exists.mp hn x
  let δ : ℝ := ‖K x₀‖ / 2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr hx₀)
  have hn : {x : X | δ < ‖K x‖} ∈ 𝓝 x₀ := by
    apply (isOpen_lt continuous_const K.continuous.norm).mem_nhds
    change ‖K x₀‖ / 2 < ‖K x₀‖
    linarith [norm_pos_iff.mpr hx₀]
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hn
  let S : Set X := closedBall x₀ r
  let Q : Set X := closure (K '' S)
  have hQ : IsCompact Q :=
    hc.isCompact_closure_image_of_bounded Metric.isBounded_closedBall
  have hQ0 : (0 : X) ∉ Q := by
    have hbound : Q ⊆ {y : X | δ ≤ ‖y‖} := by
      apply closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
      rintro _ ⟨x, hx, rfl⟩
      exact (show δ < ‖K x‖ from hball hx).le
    intro hz
    have hh := hbound hz
    simp only [mem_ofPred_eq, norm_zero] at hh
    exact (not_le_of_gt hδ) hh
  have hQconvex : Convex ℝ Q :=
    ((convex_closedBall x₀ r).linear_image (K.restrictScalars ℝ).toLinearMap).closure
  have hQne : Q.Nonempty :=
    ⟨K x₀, subset_closure ⟨x₀, mem_closedBall_self hr.le, rfl⟩⟩
  obtain ⟨f, hf, hfS, hfA⟩ := averaging_map 𝒜 h𝒜 Q hQ hQ0 x₀ r hr
  let T : Q → Q := fun y => ⟨K (f y), subset_closure ⟨f y, hfS y, rfl⟩⟩
  have hT : Continuous T := (K.continuous.comp hf).subtype_mk _
  obtain ⟨y, hy⟩ := P1.C24Schauder.schauder X Q hQne hQ hQconvex T hT
  have hKy : K (f y) = (y : X) := congrArg Subtype.val hy
  obtain ⟨A, hA, hAy⟩ := hfA y
  refine ⟨A, hA, f y, ?_, ?_⟩
  · intro hzero
    have hyzero : (y : X) = 0 := by rw [← hKy, hzero, map_zero]
    exact hQ0 (hyzero ▸ y.property)
  · rw [hKy]
    exact hAy

end ExpandedFA.InvariantSubspace.TransitiveCompactLemma
