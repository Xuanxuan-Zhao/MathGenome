import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05RealHahnBanach
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.PositiveExtension

/-!
Positive extension from a majorizing subspace, `paper.tex:6342–6361`.

We use the algebraic Riesz extension theorem. In Mathlib a `PointedCone`
means a cone containing zero, not a cone satisfying antisymmetry (the latter
is called `Salient`). Thus this use places no extra order assumption on the
source cone. The compact-function specialization uses constants as majorants
and the two inequalities `-‖g‖ • 1 ≤ g ≤ ‖g‖ • 1` for boundedness.
-/

universe u

namespace ExpandedFA.Supplements

/-- A positive functional on a majorizing subspace extends positively.
The cone need not be closed or salient, and the space is purely algebraic. -/
theorem positive_extension {E : Type u} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (h0 : (0 : E) ∈ C)
    (hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C)
    (hsmul : ∀ (t : ℝ), 0 ≤ t → ∀ x ∈ C, t • x ∈ C)
    (Y : Submodule ℝ E) (hmajor : ∀ x : E, ∃ y : Y, (y : E) - x ∈ C)
    (f : Y →ₗ[ℝ] ℝ) (hf : ∀ y : Y, (y : E) ∈ C → 0 ≤ f y) :
    ∃ F : E →ₗ[ℝ] ℝ,
      (∀ y : Y, F (y : E) = f y) ∧ (∀ x ∈ C, 0 ≤ F x) := by
  let cone : PointedCone ℝ E :=
    { carrier := C
      zero_mem' := h0
      add_mem' := fun hx hy => hadd _ hx _ hy
      smul_mem' := fun t x hx => hsmul t t.property x hx }
  apply riesz_extension cone (LinearPMap.mk Y f) hf
  intro x
  obtain ⟨y, hy⟩ := hmajor (-x)
  refine ⟨y, ?_⟩
  change (y : E) + x ∈ C
  simpa only [sub_neg_eq_add] using hy

/-- Positivity on continuous real functions gives the sharp sup-norm bound.
This estimate also holds when the compact domain is empty. -/
theorem norm_apply_le_value_one {K : Type u} [TopologicalSpace K] [CompactSpace K]
    (F : C(K, ℝ) →ₗ[ℝ] ℝ)
    (hF : ∀ g : C(K, ℝ), (∀ x : K, 0 ≤ g x) → 0 ≤ F g)
    (g : C(K, ℝ)) : ‖F g‖ ≤ F 1 * ‖g‖ := by
  have hmono : ∀ u v : C(K, ℝ), (∀ x, u x ≤ v x) → F u ≤ F v := by
    intro u v huv
    have h := hF (v - u) (fun x => sub_nonneg.mpr (huv x))
    simpa only [map_sub, sub_nonneg] using h
  have hu := hmono g (‖g‖ • (1 : C(K, ℝ))) (by
    intro x
    simpa using g.apply_le_norm x)
  have hl := hmono (-(‖g‖ • (1 : C(K, ℝ)))) g (by
    intro x
    simpa using g.neg_norm_le_apply x)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · simpa only [map_neg, map_smul, smul_eq_mul, mul_comm] using hl
  · simpa only [map_smul, smul_eq_mul, mul_comm] using hu

/-- A positive functional on a subspace of `C(K, ℝ)` containing the constants
has a positive continuous extension of norm `f(1)`, also for empty `K`. -/
theorem positive_extension_continuousMap {K : Type u} [TopologicalSpace K]
    [CompactSpace K] [T2Space K]
    (Y : Submodule ℝ C(K, ℝ)) (h1 : (1 : C(K, ℝ)) ∈ Y)
    (f : Y →ₗ[ℝ] ℝ)
    (hf : ∀ y : Y, (∀ x : K, 0 ≤ (y : C(K, ℝ)) x) → 0 ≤ f y) :
    ∃ F : C(K, ℝ) →L[ℝ] ℝ,
      (∀ y : Y, F (y : C(K, ℝ)) = f y) ∧
      (∀ g : C(K, ℝ), (∀ x : K, 0 ≤ g x) → 0 ≤ F g) ∧
      ‖F‖ = f ⟨1, h1⟩ := by
  let C : Set C(K, ℝ) := {g | ∀ x, 0 ≤ g x}
  have hmajor : ∀ g : C(K, ℝ), ∃ y : Y, (y : C(K, ℝ)) - g ∈ C := by
    intro g
    refine ⟨⟨‖g‖ • 1, Y.smul_mem ‖g‖ h1⟩, ?_⟩
    intro x
    simpa using sub_nonneg.mpr (g.apply_le_norm x)
  obtain ⟨F, hext, hpos⟩ := positive_extension C
    (fun _ => le_rfl)
    (fun _ hu _ hv x => add_nonneg (hu x) (hv x))
    (fun t ht _ hu x => mul_nonneg ht (hu x)) Y hmajor f hf
  have hone : F 1 = f ⟨1, h1⟩ := hext ⟨1, h1⟩
  have hnonneg : 0 ≤ F 1 := hpos 1 (fun _ => zero_le_one)
  have hbound := norm_apply_le_value_one F hpos
  let G := F.mkContinuous (F 1) hbound
  refine ⟨G, hext, hpos, le_antisymm ?_ ?_⟩
  · rw [← hone]
    exact F.mkContinuous_norm_le hnonneg hbound
  · by_cases hK : Nonempty K
    · let := hK
      have h := G.unit_le_opNorm (x := (1 : C(K, ℝ))) (by simp)
      change ‖F 1‖ ≤ ‖G‖ at h
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hone] at h
      exact h
    · have : IsEmpty K := not_nonempty_iff.mp hK
      have hzero : (⟨1, h1⟩ : Y) = 0 := Subtype.ext (Subsingleton.elim _ _)
      rw [hzero, map_zero]
      exact norm_nonneg G

end ExpandedFA.Supplements
