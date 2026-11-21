import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.SetSystems
import Mathlib.MeasureTheory.OuterMeasure.OfFunction

open Set MeasureTheory
open scoped ENNReal

universe u

/-! Independent types and values for paper.tex:507–536. The canonical outer
measure is Mathlib's native type, and the covering infimum ranges over all
natural-number indexed covers by members of the given family. No topology,
measurable structure, finiteness, or nonemptiness assumption is imposed. -/

namespace Specs.D11.Ch02.OuterCover

def outerMeasure_type : Type (u + 1) := Type u → Type u

def outerMeasure_value : outerMeasure_type.{u} := fun α => OuterMeasure α

def axioms_iff : Prop :=
  ∀ {α : Type u} (m : Set α → ℝ≥0∞),
    (∃ μ : OuterMeasure α, ∀ E, μ E = m E) ↔
      m ∅ = 0 ∧ Monotone m ∧
        ∀ E : ℕ → Set α, m (⋃ n, E n) ≤ ∑' n, m (E n)

def coveringCost_type : Type (u + 1) :=
  {α : Type u} → (C : Set (Set α)) → (C → ℝ≥0∞) → Set α → ℝ≥0∞

noncomputable def coveringCost_value : coveringCost_type.{u} :=
  fun C ρ E => ⨅ (F : ℕ → Set _) (hF : ∀ n, F n ∈ C)
    (_ : E ⊆ ⋃ n, F n), ∑' n, ρ ⟨F n, hF n⟩

def coveringOuterMeasure_type : Type (u + 1) :=
  {α : Type u} → (C : Set (Set α)) → (h0 : ∅ ∈ C) →
    (Set.univ ∈ C) → (ρ : C → ℝ≥0∞) → (ρ ⟨∅, h0⟩ = 0) → OuterMeasure α

noncomputable def coveringOuterMeasure_value : coveringOuterMeasure_type.{u} :=
  fun C h0 _hU ρ hρ =>
    OuterMeasure.ofFunction (fun s => ⨅ hs : s ∈ C, ρ ⟨s, hs⟩)
      (by simpa only [iInf_pos h0] using hρ)

def coveringOuterMeasure_apply : Prop :=
  ∀ {α : Type u} (C : Set (Set α)) (h0 : ∅ ∈ C) (hU : Set.univ ∈ C)
    (ρ : C → ℝ≥0∞) (hρ : ρ ⟨∅, h0⟩ = 0) (E : Set α),
    coveringOuterMeasure_value C h0 hU ρ hρ E = coveringCost_value C ρ E

def coveringCost_eq_sInf : Prop :=
  ∀ {α : Type u} (C : Set (Set α)) (ρ : C → ℝ≥0∞) (E : Set α),
    coveringCost_value C ρ E = sInf {r : ℝ≥0∞ |
      ∃ (F : ℕ → Set α) (hF : ∀ n, F n ∈ C),
        E ⊆ ⋃ n, F n ∧ r = ∑' n, ρ ⟨F n, hF n⟩}

def coveringCost_empty : Prop :=
  ∀ {α : Type u} (C : Set (Set α)) (h0 : ∅ ∈ C) (hU : Set.univ ∈ C)
    (ρ : C → ℝ≥0∞), ρ ⟨∅, h0⟩ = 0 → coveringCost_value C ρ ∅ = 0

def coveringCost_mono : Prop :=
  ∀ {α : Type u} (C : Set (Set α)) (h0 : ∅ ∈ C) (hU : Set.univ ∈ C)
    (ρ : C → ℝ≥0∞), ρ ⟨∅, h0⟩ = 0 → Monotone (coveringCost_value C ρ)

def coveringCost_iUnion_le : Prop :=
  ∀ {α : Type u} (C : Set (Set α)) (h0 : ∅ ∈ C) (hU : Set.univ ∈ C)
    (ρ : C → ℝ≥0∞), ρ ⟨∅, h0⟩ = 0 → ∀ E : ℕ → Set α,
    coveringCost_value C ρ (⋃ n, E n) ≤ ∑' n, coveringCost_value C ρ (E n)

def coveringCost_eq_top_of_no_cover : Prop :=
  ∀ {α : Type u} (C : Set (Set α)) (ρ : C → ℝ≥0∞) (E : Set α),
    (∀ F : ℕ → Set α, (∀ n, F n ∈ C) → ¬ E ⊆ ⋃ n, F n) →
      coveringCost_value C ρ E = ∞

end Specs.D11.Ch02.OuterCover
