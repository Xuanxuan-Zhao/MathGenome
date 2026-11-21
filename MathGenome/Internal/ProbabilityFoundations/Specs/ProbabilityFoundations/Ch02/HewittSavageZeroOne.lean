import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.LawsAndTransfer
import Mathlib.MeasureTheory.Constructions.Cylinders

/-! Independent statement of paper.tex:749–789. The measurable space on S is
arbitrary and the space of sequences has exactly its product sigma-algebra.
Finite permutations are described by finiteness of their moved-point set.
Invariance is in measure, with a separate null set allowed for each permutation. -/
open MeasureTheory Set
open scoped symmDiff ENNReal

namespace Specs.ProbabilityFoundations.Ch02.HewittSavageZeroOne
universe u v

def finiteBlockApproximationType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (μ : Measure (ℕ → S)) [IsFiniteMeasure μ]
    (A : Set (ℕ → S)), MeasurableSet A → ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ (m : ℕ) (B : Set (ℕ → S)),
      MeasurableSet[MeasureTheory.cylinderEvents (X := fun _ : ℕ => S) (Iio m)] B ∧
      μ (A ∆ B) < ε

def permutationInvarianceType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ],
    ProbabilityTheory.iIndepFun (fun i (x : ℕ → S) => x i) μ →
    (∀ i j, μ.map (fun x => x i) = μ.map (fun x => x j)) →
    ∀ σ : Equiv.Perm ℕ, μ.map (fun x i => x (σ i)) = μ

def hewittSavageCoordinateType : Prop :=
  ∀ {S : Type u} [MeasurableSpace S] (μ : Measure (ℕ → S)) [IsProbabilityMeasure μ],
    ProbabilityTheory.iIndepFun (fun i (x : ℕ → S) => x i) μ →
    (∀ i j, μ.map (fun x => x i) = μ.map (fun x => x j)) →
    ∀ A : Set (ℕ → S), MeasurableSet A →
    (∀ σ : Equiv.Perm ℕ, {i | σ i ≠ i}.Finite →
      μ (A ∆ ((fun x i => x (σ i)) ⁻¹' A)) = 0) → μ A = 0 ∨ μ A = 1

def hewittSavageType : Prop :=
  ∀ {Ω : Type u} {S : Type v} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → S),
    (∀ i, Measurable (X i)) →
    IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ i j, Ch01.LawsAndTransfer.lawValue P (X i) = Ch01.LawsAndTransfer.lawValue P (X j)) →
    ∀ A : Set (ℕ → S), MeasurableSet A →
    (∀ σ : Equiv.Perm ℕ, {i | σ i ≠ i}.Finite →
      Ch01.LawsAndTransfer.jointLawValue P X (A ∆ ((fun x i => x (σ i)) ⁻¹' A)) = 0) →
    Ch01.LawsAndTransfer.jointLawValue P X A = 0 ∨
      Ch01.LawsAndTransfer.jointLawValue P X A = 1

end Specs.ProbabilityFoundations.Ch02.HewittSavageZeroOne
