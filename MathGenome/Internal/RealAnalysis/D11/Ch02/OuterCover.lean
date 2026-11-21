import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.OuterCover

/-! # Outer measures and covering costs

This uses the native outer-measure structure. Its stored subadditivity field
only tests disjoint sequences; `axioms_iff` checks the equivalence to the
paper's unrestricted countable subadditivity. Extending a cost by infinity
off its family lets the native `ofFunction` construction supply all three
axioms, and `coveringOuterMeasure_apply` proves its exact covering formula.
-/

open Set MeasureTheory
open scoped ENNReal

universe u

namespace D11.Ch02.OuterCover

abbrev outerMeasure (α : Type u) : Type u := OuterMeasure α

theorem axioms_iff :
  ∀ {α : Type u} (m : Set α → ℝ≥0∞),
    (∃ μ : OuterMeasure α, ∀ E, μ E = m E) ↔
      m ∅ = 0 ∧ Monotone m ∧
        ∀ E : ℕ → Set α, m (⋃ n, E n) ≤ ∑' n, m (E n) := by
  intro α m
  constructor
  · rintro ⟨μ, hμ⟩
    have hm : m = (fun E => μ E) := (funext hμ).symm
    subst m
    exact ⟨measure_empty, fun _ _ h => measure_mono h, fun E => measure_iUnion_le E⟩
  · rintro ⟨h0, hmono, hsub⟩
    exact ⟨⟨m, h0, fun h => hmono h, fun E _ => hsub E⟩, fun _ => rfl⟩

/-- The paper's infimum over costs of countable covers. -/
noncomputable def coveringCost {α : Type u} (C : Set (Set α)) (ρ : C → ℝ≥0∞)
    (E : Set α) : ℝ≥0∞ :=
  ⨅ (F : ℕ → Set α) (hF : ∀ n, F n ∈ C)
    (_ : E ⊆ ⋃ n, F n), ∑' n, ρ ⟨F n, hF n⟩

/-- Extend costs by infinity outside the family, then apply the native covering
construction. The whole-space membership is retained from the source. -/
noncomputable def coveringOuterMeasure {α : Type u} (C : Set (Set α))
    (h0 : ∅ ∈ C) (_hU : Set.univ ∈ C) (ρ : C → ℝ≥0∞)
    (hρ : ρ ⟨∅, h0⟩ = 0) : OuterMeasure α :=
  OuterMeasure.ofFunction (fun s => ⨅ hs : s ∈ C, ρ ⟨s, hs⟩)
    (by simpa only [iInf_pos h0] using hρ)

theorem coveringOuterMeasure_apply :
  ∀ {α : Type u} (C : Set (Set α)) (h0 : ∅ ∈ C) (hU : Set.univ ∈ C)
    (ρ : C → ℝ≥0∞) (hρ : ρ ⟨∅, h0⟩ = 0) (E : Set α),
    coveringOuterMeasure C h0 hU ρ hρ E = coveringCost C ρ E := by
  intro α C h0 hU ρ hρ E
  unfold coveringOuterMeasure
  rw [OuterMeasure.ofFunction_eq_iInf_mem _ _ (P := fun s => s ∈ C)
    (fun s hs => by simp [hs])]
  unfold coveringCost
  apply iInf_congr
  intro F
  apply iInf_congr
  intro hF
  apply iInf_congr
  intro _
  congr 1
  funext n
  simp only [iInf_pos (hF n)]

theorem coveringCost_eq_sInf :
  ∀ {α : Type u} (C : Set (Set α)) (ρ : C → ℝ≥0∞) (E : Set α),
    coveringCost C ρ E = sInf {r : ℝ≥0∞ |
      ∃ (F : ℕ → Set α) (hF : ∀ n, F n ∈ C),
        E ⊆ ⋃ n, F n ∧ r = ∑' n, ρ ⟨F n, hF n⟩} := by
  intro α C ρ E
  apply le_antisymm
  · apply le_sInf
    rintro r ⟨F, hF, hE, rfl⟩
    exact iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le hE le_rfl))
  · apply le_iInf
    intro F
    apply le_iInf
    intro hF
    apply le_iInf
    intro hE
    exact sInf_le ⟨F, hF, hE, rfl⟩

theorem coveringCost_empty :
  ∀ {α : Type u} (C : Set (Set α)) (h0 : ∅ ∈ C) (hU : Set.univ ∈ C)
    (ρ : C → ℝ≥0∞), ρ ⟨∅, h0⟩ = 0 → coveringCost C ρ ∅ = 0 := by
  intro α C h0 hU ρ hρ
  rw [← coveringOuterMeasure_apply C h0 hU ρ hρ]
  exact measure_empty

theorem coveringCost_mono :
  ∀ {α : Type u} (C : Set (Set α)) (h0 : ∅ ∈ C) (hU : Set.univ ∈ C)
    (ρ : C → ℝ≥0∞), ρ ⟨∅, h0⟩ = 0 → Monotone (coveringCost C ρ) := by
  intro α C h0 hU ρ hρ A B hAB
  rw [← coveringOuterMeasure_apply C h0 hU ρ hρ A,
    ← coveringOuterMeasure_apply C h0 hU ρ hρ B]
  exact measure_mono hAB

theorem coveringCost_iUnion_le :
  ∀ {α : Type u} (C : Set (Set α)) (h0 : ∅ ∈ C) (hU : Set.univ ∈ C)
    (ρ : C → ℝ≥0∞), ρ ⟨∅, h0⟩ = 0 → ∀ E : ℕ → Set α,
    coveringCost C ρ (⋃ n, E n) ≤ ∑' n, coveringCost C ρ (E n) := by
  intro α C h0 hU ρ hρ E
  simp_rw [← coveringOuterMeasure_apply C h0 hU ρ hρ]
  exact measure_iUnion_le E

theorem coveringCost_eq_top_of_no_cover :
  ∀ {α : Type u} (C : Set (Set α)) (ρ : C → ℝ≥0∞) (E : Set α),
    (∀ F : ℕ → Set α, (∀ n, F n ∈ C) → ¬ E ⊆ ⋃ n, F n) →
      coveringCost C ρ E = ∞ := by
  intro α C ρ E h
  apply iInf_eq_top.mpr
  intro F
  apply iInf_eq_top.mpr
  intro hF
  apply iInf_eq_top.mpr
  intro hE
  exact False.elim (h F hF hE)

end D11.Ch02.OuterCover
