import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.RadonCaratheodoryLocalization
import Mathlib.Order.Zorn

/-! Independent statements for the disjoint-compact and gluing stage of
paper.tex, the proof of `d11:20:local-null-endpoint-specialization`.
All measurable sets and functions use the full Carathéodory domain of the
specified Borel Radon measure. No countability of the compact family is imposed. -/
open Set MeasureTheory
open scoped ENNReal
namespace Specs.D11.Ch20.RadonDisjointCompactLocalization
universe u v

abbrev M {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)) :=
  RadonCaratheodoryLocalization.measurableSpace_value μ
noncomputable abbrev m {X : Type u} [TopologicalSpace X] (μ : @Measure X (borel X)) :=
  RadonCaratheodoryLocalization.measure_value μ

/-- A positive compact with full support for its restricted measure. -/
def SupportedCompact {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) (K : Set X) : Prop :=
  IsCompact K ∧ 0 < m μ K ∧
    ∀ U : Set X, IsOpen U → (U ∩ K).Nonempty → 0 < m μ (U ∩ K)

/-- A family of pairwise disjoint positive full-support compacts. -/
def DisjointFamily {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) (C : Set (Set X)) : Prop :=
  (∀ K ∈ C, SupportedCompact μ K) ∧ C.Pairwise Disjoint

/-- Maximality is among all such families, including the empty family. -/
abbrev MaximalFamily {X : Type u} [TopologicalSpace X]
    (μ : @Measure X (borel X)) (C : Set (Set X)) : Prop :=
  Maximal (DisjointFamily μ) C

/-- The subfamily that actually meets a set, not merely in positive measure. -/
def meeting {X : Type u} (C : Set (Set X)) (A : Set X) : Set (Set X) :=
  {K | K ∈ C ∧ (A ∩ K).Nonempty}

def compact_full_support : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonCaratheodoryLocalization.Radon μ →
    ∀ K : Set X, IsCompact K → 0 < m μ K →
    ∃ K₀ : Set X, K₀ ⊆ K ∧ m μ K₀ = m μ K ∧ SupportedCompact μ K₀

def exists_maximal_family : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonCaratheodoryLocalization.Radon μ →
    ∃ C : Set (Set X), MaximalFamily μ C

def finite_decomposition : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonCaratheodoryLocalization.Radon μ →
    ∀ C : Set (Set X), MaximalFamily μ C →
    ∀ A : Set X, MeasurableSet[M μ] A → m μ A < ∞ →
      (meeting C A).Countable ∧
      MeasurableSet[M μ] (A \ ⋃₀ meeting C A) ∧ m μ (A \ ⋃₀ meeting C A) = 0

def measurable_iff : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonCaratheodoryLocalization.Radon μ →
    ∀ C : Set (Set X), MaximalFamily μ C → ∀ B : Set X,
      MeasurableSet[M μ] B ↔ ∀ K ∈ C, MeasurableSet[M μ] (B ∩ K)

/-- Scalar gluing follows from this stronger version for any measurable
codomain with a distinguished zero. Subtypes have the induced measurable space. -/
def measurable_gluing : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (μ : @Measure X (borel X)), RadonCaratheodoryLocalization.Radon μ →
    ∀ C : Set (Set X), MaximalFamily μ C →
    letI : MeasurableSpace X := M μ
    ∀ (Y : Type v) [MeasurableSpace Y] [Zero Y]
      (f : ∀ K : Set X, K ∈ C → K → Y),
      (∀ K (hK : K ∈ C), Measurable (f K hK)) →
      ∃ g : X → Y, Measurable g ∧
        (∀ K (hK : K ∈ C) (x : K), g x = f K hK x) ∧
        (∀ x : X, (∀ K ∈ C, x ∉ K) → g x = 0)

end Specs.D11.Ch20.RadonDisjointCompactLocalization
