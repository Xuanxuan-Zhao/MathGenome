import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.CanonicalProjection
import Mathlib.Algebra.Exact.Basic

open scoped BigOperators

universe u v w z t

namespace RepTheorySurvey.Invariants.Specs

set_option linter.checkUnivs false in
def FiniteAverageType :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [Finite G], Representation k G V → (V →ₗ[k] V)

section

variable {k : Type u} {G : Type v} {V : Type w} {W : Type z}
  [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The averaging endomorphism, with the sum taken over the whole finite group. -/
noncomputable def finiteAverage [Finite G] (ρ : Representation k G V) : V →ₗ[k] V :=
  letI := Fintype.ofFinite G
  (Nat.card G : k)⁻¹ • ∑ g : G, ρ g

/-- The restriction of an equivariant linear map to fixed vectors. -/
noncomputable def mapInvariants (ρ : Representation k G V) (σ : Representation k G W)
    (f : V →ₗ[k] W) (hf : ρ.IsIntertwiningMap σ f) : ρ.invariants →ₗ[k] σ.invariants :=
  (f.comp ρ.invariants.subtype).codRestrict σ.invariants fun x g ↦ by
    change σ g (f (x : V)) = f (x : V)
    rw [← hf.isIntertwining g, x.property g]

end

def FiniteAverageFormula : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Fintype G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (x : V),
    finiteAverage ρ x = (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g x

def FiniteAverageNatural : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} {W : Type z} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W)
    (f : V →ₗ[k] W), ρ.IsIntertwiningMap σ f →
      ∀ x : V, finiteAverage σ (f x) = f (finiteAverage ρ x)

def FiniteAverageProjection : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V), (Nat.card G : k) ≠ 0 →
    LinearMap.IsProj ρ.invariants (finiteAverage ρ)

def FiniteGroupLinearlyReductive : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G] [Finite G],
    (Nat.card G : k) ≠ 0 → groupLinearlyReductive.{u,v,w} k G

/-- The explicit average gives the equivariant retraction onto fixed vectors
and equals the canonical projection of Proposition 3.2. -/
def FiniteAverageCanonical : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V), (Nat.card G : k) ≠ 0 →
    ∃ R : V →ₗ[k] ρ.invariants, (∀ x : V, (R x : V) = finiteAverage ρ x) ∧
      IsGroupProjection ρ R ∧
      ∀ P : V →ₗ[k] ρ.invariants, HasGroupProjectionBehavior ρ P → P = R

/-- Fixed vectors preserve exactness in the middle and both ends of any
short exact sequence of representations. -/
def FiniteInvariantsExact : Prop :=
  ∀ {k : Type u} {G : Type v} {U : Type t} {V : Type w} {W : Type z}
    [Field k] [Group G] [Finite G] [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W],
    (Nat.card G : k) ≠ 0 →
    ∀ (τ : Representation k G U) (ρ : Representation k G V) (σ : Representation k G W)
      (f : U →ₗ[k] V) (g : V →ₗ[k] W)
      (hf : τ.IsIntertwiningMap ρ f) (hg : ρ.IsIntertwiningMap σ g),
      (Function.Exact f g → Function.Exact (mapInvariants τ ρ f hf) (mapInvariants ρ σ g hg)) ∧
      (Function.Injective f → Function.Injective (mapInvariants τ ρ f hf)) ∧
      (Function.Surjective g → Function.Surjective (mapInvariants ρ σ g hg))

def FiniteAverageReynolds : Prop :=
  ∀ {k : Type u} {G : Type v} {A : Type w} [Field k] [Group G] [Finite G]
    [Ring A] [Algebra k A] (ρ : GroupAlgebraAction k G A), (Nat.card G : k) ≠ 0 →
    ∃ R : A →ₗ[k] groupFixedSubalgebra ρ, groupIsReynolds ρ R ∧
      ∀ x : A, (R x : A) = finiteAverage (groupRepresentation ρ) x

/-- Averaging preserves every stable component, hence every specified grading
whose homogeneous submodules are stable. -/
def FiniteAveragePreservesGrading : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} {ι : Type z}
    [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (grade : ι → Submodule k V),
    (∀ (g : G) (i : ι) (x : V), x ∈ grade i → ρ g x ∈ grade i) →
    ∀ (i : ι) (x : V), x ∈ grade i → finiteAverage ρ x ∈ grade i

end RepTheorySurvey.Invariants.Specs
