import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.VectorLatticeStone
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
Independent specification of paper.tex:6190–6192,
`d11:23:elementary-integral`.

`V` is the same subspace of actual finite real functions as in
`VectorLatticeStone`. The predicate below records the functional conditions;
the vector-lattice and Stone predicates remain separate hypotheses on `V`.
Real linearity is supplied by `LinearMap`. Decrease and convergence are at
every point of `X`, including when `X` is empty.
-/

universe u

open Filter Topology

namespace D11.Ch23.Specs

/-- Positivity and sequential continuity from above at zero, on the given
subspace. No measurable structure or topology on the subspace is needed. -/
def IsElementaryIntegral {X : Type u} (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) : Prop :=
  (∀ f : V, (∀ x : X, 0 ≤ (f : X → ℝ) x) → 0 ≤ L f) ∧
  (∀ f : ℕ → V,
    (∀ x : X, Antitone (fun n => (f n : X → ℝ) x)) →
    (∀ x : X, Tendsto (fun n => (f n : X → ℝ) x) atTop (𝓝 0)) →
    Tendsto (fun n => L (f n)) atTop (𝓝 0))

def ElementaryIntegralPredicateType :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)), (V →ₗ[ℝ] ℝ) → Prop

/-- The complete unbundled reading of the elementary-integral condition. -/
def ElementaryIntegralIff : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)) (L : V →ₗ[ℝ] ℝ),
    IsElementaryIntegral V L ↔
      (∀ f : V, (∀ x : X, 0 ≤ (f : X → ℝ) x) → 0 ≤ L f) ∧
      (∀ f : ℕ → V,
        (∀ x : X, Antitone (fun n => (f n : X → ℝ) x)) →
        (∀ x : X, Tendsto (fun n => (f n : X → ℝ) x) atTop (𝓝 0)) →
        Tendsto (fun n => L (f n)) atTop (𝓝 0))

def ElementaryIntegralNonneg : Prop :=
  ∀ {X : Type u} {V : Submodule ℝ (X → ℝ)} {L : V →ₗ[ℝ] ℝ},
    IsElementaryIntegral V L →
    ∀ f : V, (∀ x : X, 0 ≤ (f : X → ℝ) x) → 0 ≤ L f

def ElementaryIntegralTendstoZero : Prop :=
  ∀ {X : Type u} {V : Submodule ℝ (X → ℝ)} {L : V →ₗ[ℝ] ℝ},
    IsElementaryIntegral V L →
    ∀ f : ℕ → V,
      (∀ x : X, Antitone (fun n => (f n : X → ℝ) x)) →
      (∀ x : X, Tendsto (fun n => (f n : X → ℝ) x) atTop (𝓝 0)) →
      Tendsto (fun n => L (f n)) atTop (𝓝 0)

/-- Every value of a linear functional on an empty domain is zero. -/
def EmptyDomainIntegralValue : Prop :=
  ∀ {X : Type u} [IsEmpty X] (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ) (f : V), L f = 0

/-- The elementary-integral conditions include the empty-domain case. -/
def EmptyDomainElementaryIntegral : Prop :=
  ∀ {X : Type u} [IsEmpty X] (V : Submodule ℝ (X → ℝ))
    (L : V →ₗ[ℝ] ℝ), IsElementaryIntegral V L

end D11.Ch23.Specs
