import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24Faces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24FaceOperations
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Face operations and maximizing faces

Lemma `fa2:p1:c24:face-operations` (paper.tex:4944–4967) of the manuscript. All combinations use
real coefficients. No norm, metric, or sequential compactness is used.
-/

universe u

namespace ExpandedFA.P1

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

theorem isFace_singleton_iff (K : Set E) (x : E) :
    IsFace K {x} ↔ x ∈ extremePoints K := by
  rw [isFace_iff_native, extremePoints_eq_native]
  simp only [Set.singleton_nonempty, convex_singleton, true_and, isExtreme_singleton]

theorem isFace_sInter (K : Set E) (S : Set (Set E)) (hS : S.Nonempty)
    (hfaces : ∀ F ∈ S, IsFace K F) (hne : (⋂₀ S).Nonempty) :
    IsFace K (⋂₀ S) := by
  apply (isFace_iff_native K (⋂₀ S)).mpr
  refine ⟨hne, convex_sInter (fun F hF => (hfaces F hF).2.1), ?_⟩
  exact isExtreme_sInter hS fun F hF => ((isFace_iff_native K F).mp (hfaces F hF)).2.2

theorem isFace_inter_sInter (K : Set E) (S : Set (Set E)) (hK : Convex ℝ K)
    (hfaces : ∀ F ∈ S, IsFace K F) (hne : (K ∩ ⋂₀ S).Nonempty) :
    IsFace K (K ∩ ⋂₀ S) := by
  refine ⟨hne, hK.inter (convex_sInter fun F hF => (hfaces F hF).2.1),
    Set.inter_subset_left, ?_⟩
  intro y hy z hz t ht0 ht1 hcomb
  refine ⟨⟨hy, Set.mem_sInter.mpr ?_⟩, ⟨hz, Set.mem_sInter.mpr ?_⟩⟩
  · intro F hF
    exact ((hfaces F hF).2.2.2 y hy z hz t ht0 ht1
      (Set.mem_sInter.mp hcomb.2 F hF)).1
  · intro F hF
    exact ((hfaces F hF).2.2.2 y hy z hz t ht0 ht1
      (Set.mem_sInter.mp hcomb.2 F hF)).2

protected theorem IsFace.trans {K F G : Set E} (hKF : IsFace K F)
    (hFG : IsFace F G) : IsFace K G := by
  refine ⟨hFG.1, hFG.2.1, hFG.2.2.1.trans hKF.2.2.1, ?_⟩
  intro y hy z hz t ht0 ht1 hcomb
  obtain ⟨hyF, hzF⟩ := hKF.2.2.2 y hy z hz t ht0 ht1 (hFG.2.2.1 hcomb)
  exact hFG.2.2.2 y hyF z hzF t ht0 ht1 hcomb

/-- A strictly weighted average of two values bounded above by `m` can equal
`m` only when both values equal `m`. -/
private theorem eq_max_of_weighted_average {a b m t : ℝ}
    (ha : a ≤ m) (hb : b ≤ m) (ht0 : 0 < t) (ht1 : t < 1)
    (havg : t * a + (1 - t) * b = m) : a = m ∧ b = m := by
  have hta : 0 ≤ t * (m - a) := mul_nonneg ht0.le (sub_nonneg.mpr ha)
  have htb : 0 ≤ (1 - t) * (m - b) :=
    mul_nonneg (sub_pos.mpr ht1).le (sub_nonneg.mpr hb)
  constructor
  · apply le_antisymm ha
    by_contra h
    have hpos := mul_pos ht0 (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  · apply le_antisymm hb
    by_contra h
    have hpos := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr (lt_of_not_ge h))
    nlinarith

theorem exists_maximizing_compactFace [TopologicalSpace E] (K : Set E)
    (hne : K.Nonempty) (hcompact : IsCompact K) (hconv : Convex ℝ K)
    (ℓ : E →L[ℝ] ℝ) : ∃ x₀ ∈ K,
      (∀ x ∈ K, ℓ x ≤ ℓ x₀) ∧
        IsCompactFace K {x | x ∈ K ∧ ℓ x = ℓ x₀} := by
  obtain ⟨x₀, hx₀, hmax⟩ := hcompact.exists_isMaxOn hne ℓ.continuous.continuousOn
  refine ⟨x₀, hx₀, hmax, ?_⟩
  have hlevel : Convex ℝ {x : E | ℓ x = ℓ x₀} :=
    (convex_singleton (ℓ x₀)).linear_preimage ℓ.toLinearMap
  refine ⟨⟨⟨x₀, hx₀, rfl⟩, hconv.inter hlevel, fun _ hx => hx.1, ?_⟩, ?_⟩
  · intro y hy z hz t ht0 ht1 hcomb
    have havg : t * ℓ y + (1 - t) * ℓ z = ℓ x₀ := by
      simpa only [map_add, map_smul, smul_eq_mul] using hcomb.2
    obtain ⟨hymax, hzmax⟩ := eq_max_of_weighted_average (hmax hy) (hmax hz) ht0 ht1 havg
    exact ⟨⟨hy, hymax⟩, ⟨hz, hzmax⟩⟩
  · exact hcompact.inter_right (isClosed_eq ℓ.continuous continuous_const)

end ExpandedFA.P1
