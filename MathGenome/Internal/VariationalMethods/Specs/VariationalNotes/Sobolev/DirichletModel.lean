import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces

/-! The scalar Dirichlet model, paper.tex:3920–3944.
Scalar values are the single coordinate of the canonical Euclidean target.
No boundary regularity or nonemptiness is imposed on the open domain. -/
noncomputable section
open MeasureTheory TopologicalSpace Set

namespace VariationalNotes.Sobolev.Dirichlet

abbrev Source {d : ℕ} (Ω : Opens (Domain d)) := Lp ℝ 2 (domainMeasure Ω)

def energy {d : ℕ} (Ω : Opens (Domain d)) (b : Source Ω) (u : H1 Ω 1) : ℝ :=
  (1 / 2 : ℝ) * (∫ x, ‖gradient Ω 1 Exponent.two u x‖ ^ 2 ∂domainMeasure Ω) -
    ∫ x, b x * value Ω 1 Exponent.two u x 0 ∂domainMeasure Ω

def Stationary {d : ℕ} (Ω : Opens (Domain d)) (b : Source Ω) (u : H1 Ω 1) : Prop :=
  ∀ φ : H1Zero Ω 1,
    (∫ x, frobenius (gradient Ω 1 Exponent.two u x)
      (gradient Ω 1 Exponent.two φ.val x) ∂domainMeasure Ω) =
    ∫ x, b x * value Ω 1 Exponent.two φ.val x 0 ∂domainMeasure Ω

/-- Membership is written as the defining subtraction condition of `affineClass`. -/
def Minimizer {d : ℕ} (Ω : Opens (Domain d)) (u₀ : H1 Ω 1) (b : Source Ω)
    (u : H1 Ω 1) : Prop :=
  u - u₀ ∈ zeroSubmodule Ω 1 Exponent.two ∧
    ∀ v, v - u₀ ∈ zeroSubmodule Ω 1 Exponent.two → energy Ω b u ≤ energy Ω b v

namespace Expected

def ExistenceUnique : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)), 0 < d → Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (u₀ : H1 Ω 1) (b : Source Ω), ∃! u, Minimizer Ω u₀ b u

def Characterization : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)), 0 < d → Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (u₀ : H1 Ω 1) (b : Source Ω) (u : H1 Ω 1),
      u - u₀ ∈ zeroSubmodule Ω 1 Exponent.two →
      (Minimizer Ω u₀ b u ↔ Stationary Ω b u)

def EnergyDifference : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)) (b : Source Ω) (u : H1 Ω 1),
    Stationary Ω b u → ∀ φ : H1Zero Ω 1,
      energy Ω b (u + φ.val) - energy Ω b u =
        ‖gradient Ω 1 Exponent.two φ.val‖ ^ 2 / 2

def WeakDirichletPrinciple : Prop :=
  ∀ {d : ℕ} (Ω : Opens (Domain d)), 0 < d → Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ u₀ : H1 Ω 1,
      (∃! u, Minimizer Ω u₀ 0 u) ∧
      ∀ u, u - u₀ ∈ zeroSubmodule Ω 1 Exponent.two →
        (Minimizer Ω u₀ 0 u ↔
          ∀ φ : H1Zero Ω 1,
            (∫ x, frobenius (gradient Ω 1 Exponent.two u x)
              (gradient Ω 1 Exponent.two φ.val x) ∂domainMeasure Ω) = 0)

end Expected
end VariationalNotes.Sobolev.Dirichlet
