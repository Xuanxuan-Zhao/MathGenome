import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.NewtonHessian
import MathGenome.Internal.LinearPDE.P201Specs.Potential.DerivativesLiouville

/-! Independent statements for the interior Poisson Schauder theorem and the
scaled-ball estimate, paper.tex:1781–1821. Derivatives, the Laplacian, and the
Newton kernel are the shared spatial objects. All Hölder seminorms run over
all distinct pairs, even when the set is disconnected. Real suprema below
are used in estimates only with explicit boundedness hypotheses. -/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.NewtonHessian
open P201Specs.Elliptic.HolderCancellation

/-- Supremum norm, with the empty supremum totalized in ℝ. -/
def supNormOn {n : ℕ} (g : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ s, r = ‖g x‖}

/-- All-pairs Hölder seminorm, rather than a pointwise Hölder condition. -/
def holderSeminormOn {n : ℕ} (α : ℝ) (g : Space n → ℝ)
    (s : Set (Space n)) : ℝ :=
  sSup {r : ℝ | ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ r = ‖g x - g y‖ / dist x y ^ α}

/-- This hypothesis gives genuine finiteness before a real supremum is used. -/
def IsBoundedOn {n : ℕ} (g : Space n → ℝ) (s : Set (Space n)) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, ‖g x‖ ≤ M

/-- The source's local C⁰,α condition on an open domain. -/
def IsHolderLoc {n : ℕ} (α : ℝ) (f : Space n → ℝ) (Ω : Domain n) : Prop :=
  ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ (Ω : Set _) ∧
    IsHolderOn α f (ball x r)

/-- The bounded C²,α class, with finite bounds for every derivative order. -/
def IsC2HolderOn {n : ℕ} (α : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) : Prop :=
  ContDiffOn ℝ 2 u s ∧ IsBoundedOn u s ∧
    (∀ i : Fin n, IsBoundedOn (multiPartial u {i}) s) ∧
    ∀ i j : Fin n, IsHolderOn α (multiPartial u {i, j}) s

/-- Local C²,α uses actual classical derivatives on open neighborhoods. -/
def IsC2HolderLocOn {n : ℕ} (α : ℝ) (u : Space n → ℝ) (Ω : Domain n) : Prop :=
  ContDiffOn ℝ 2 u Ω ∧ ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧
    ball x r ⊆ (Ω : Set _) ∧
    ∀ i j : Fin n, IsHolderOn α (multiPartial u {i, j}) (ball x r)

/-- Coordinate derivative sums are an ordinary finite-dimensional norm choice. -/
def firstDerivativeNormOn {n : ℕ} (u : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  ∑ i : Fin n, supNormOn (multiPartial u {i}) s

def secondDerivativeNormOn {n : ℕ} (u : Space n → ℝ) (s : Set (Space n)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, supNormOn (multiPartial u {i, j}) s

def secondDerivativeSeminormOn {n : ℕ} (α : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, holderSeminormOn α (multiPartial u {i, j}) s

/-- The four terms on the left of the source's rescaled estimate. -/
def scaledSolutionNorm {n : ℕ} (α r : ℝ) (u : Space n → ℝ)
    (s : Set (Space n)) : ℝ :=
  supNormOn u s + r * firstDerivativeNormOn u s +
    r ^ 2 * secondDerivativeNormOn u s +
    r ^ (2 + α) * secondDerivativeSeminormOn α u s

/-- The three terms on the right; in particular no logarithmic additive term. -/
def scaledDataNorm {n : ℕ} (α r : ℝ) (u f : Space n → ℝ)
    (s : Set (Space n)) : ℝ :=
  supNormOn u s + r ^ 2 * supNormOn f s + r ^ (2 + α) * holderSeminormOn α f s

/-- Qualitative regularity has no global boundedness hypothesis on u or f. -/
def LocalRegularityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ (Ω : Domain n) (u f : Space n → ℝ), ContDiffOn ℝ 2 u Ω →
      IsHolderLoc α f Ω → (∀ x ∈ Ω, -laplacian u x = f x) →
      IsC2HolderLocOn α u Ω

/-- The constant is fixed before u and f. Ω′ is bounded open and its closure
lies in Ω″. No boundary regularity, connectedness, or boundedness of Ω″ is
required. Finiteness on Ω″ is explicit, so unbounded real suprema cannot
make the estimate vacuous. -/
def InteriorEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ Ω Ω' Ω'' : Domain n, Bornology.IsBounded (Ω' : Set (Space n)) →
      closure (Ω' : Set (Space n)) ⊆ (Ω'' : Set _) → Ω'' ≤ Ω →
      ∃ C : ℝ, 0 < C ∧ ∀ u f : Space n → ℝ,
        ContDiffOn ℝ 2 u Ω → IsHolderLoc α f Ω →
        (∀ x ∈ Ω, -laplacian u x = f x) →
        IsBoundedOn u Ω'' → IsHolderOn α f Ω'' →
        IsC2HolderOn α u Ω' ∧
        c2HolderNormOn α u Ω' ≤ C * (supNormOn u Ω'' + holderNormOn α f Ω'')

/-- Uniform in the center and radius, and applicable to a classical solution
on B₂ᵣ itself. Includes n=1 and the n=2 logarithmic fundamental solution. -/
def ScaledBallEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Space n) (r : ℝ), 0 < r →
      ∀ u f : Space n → ℝ, ContDiffOn ℝ 2 u (ball a (2 * r)) →
        IsBoundedOn u (ball a (2 * r)) → IsHolderOn α f (ball a (2 * r)) →
        (∀ x ∈ ball a (2 * r), -laplacian u x = f x) →
        IsC2HolderOn α u (ball a r) ∧
        scaledSolutionNorm α r u (ball a r) ≤
          C * scaledDataNorm α r u f (ball a (2 * r))

/-- Upstream potential regularity must also be connected to the equation:
the actual Newton integral solves -Δw=F pointwise on Hölder compact data. -/
def PotentialEquationStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ F : Space n → ℝ, HasCompactSupport F → IsHolder α F →
      ∀ x, -laplacian (holderPotential F) x = F x

end P201Specs.Elliptic.PoissonSchauder
