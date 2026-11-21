import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch06.DiskAutomorphisms

/-! Independent Schwarz–Pick statements, paper.tex:1492–1525.
The functions are total representatives of maps on the open unit disk.
Holomorphy and biholomorphy are the canonical predicates, with no extra
regularity or assumed analytic certificates. -/
noncomputable section
namespace Specs.D12Complex.Ch06.SchwarzPick
open _root_.D12Complex Metric Set

def value_le_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn (ball 0 1) f →
    MapsTo f (ball 0 1) (ball 0 1) → ∀ a ∈ ball (0 : ℂ) 1,
    ∀ z ∈ ball (0 : ℂ) 1,
    ‖(f z - f a) / (1 - star (f a) * f z)‖ ≤
      ‖(z - a) / (1 - star a * z)‖

def derivative_le_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn (ball 0 1) f →
    MapsTo f (ball 0 1) (ball 0 1) → ∀ a ∈ ball (0 : ℂ) 1,
    ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) ≤ 1 / (1 - ‖a‖ ^ 2)

/-- Equality at each fixed distinct admissible pair is equivalent to biholomorphy. -/
def value_eq_iff_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn (ball 0 1) f →
    MapsTo f (ball 0 1) (ball 0 1) → ∀ a ∈ ball (0 : ℂ) 1,
    ∀ z ∈ ball (0 : ℂ) 1, z ≠ a →
    (‖(f z - f a) / (1 - star (f a) * f z)‖ =
      ‖(z - a) / (1 - star a * z)‖ ↔
      IsBiholomorphism (ball 0 1) (ball 0 1) f)

def derivative_eq_iff_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn (ball 0 1) f →
    MapsTo f (ball 0 1) (ball 0 1) → ∀ a ∈ ball (0 : ℂ) 1,
    (‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2) ↔
      IsBiholomorphism (ball 0 1) (ball 0 1) f)

/-- Both equalities for every disk automorphism, including the diagonal pair. -/
def automorphism_equalities_type : Prop :=
  ∀ f : ℂ → ℂ, IsBiholomorphism (ball 0 1) (ball 0 1) f →
    ∀ a ∈ ball (0 : ℂ) 1,
    (∀ z ∈ ball (0 : ℂ) 1,
      ‖(f z - f a) / (1 - star (f a) * f z)‖ =
        ‖(z - a) / (1 - star a * z)‖) ∧
    ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2)

/-- The source's existential formulations of both equality cases. -/
def equality_cases_type : Prop :=
  ∀ f : ℂ → ℂ, HolomorphicOn (ball 0 1) f →
    MapsTo f (ball 0 1) (ball 0 1) →
    ((∃ a ∈ ball (0 : ℂ) 1, ∃ z ∈ ball (0 : ℂ) 1, z ≠ a ∧
      ‖(f z - f a) / (1 - star (f a) * f z)‖ =
        ‖(z - a) / (1 - star a * z)‖) ↔
      IsBiholomorphism (ball 0 1) (ball 0 1) f) ∧
    ((∃ a ∈ ball (0 : ℂ) 1,
      ‖deriv f a‖ / (1 - ‖f a‖ ^ 2) = 1 / (1 - ‖a‖ ^ 2)) ↔
      IsBiholomorphism (ball 0 1) (ball 0 1) f)

end Specs.D12Complex.Ch06.SchwarzPick
