import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions

open LinearAlgebraicGroups

universe u v w z

namespace RepTheorySurvey.Invariants.Specs

section Group

variable {k : Type u} {G : Type v} {V : Type w}
  [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Fixing the invariants and vanishing on simple subrepresentations with nontrivial action
characterize the canonical projection as a linear map. -/
def HasGroupProjectionBehavior (ρ : Representation k G V) (P : V →ₗ[k] ρ.invariants) : Prop :=
  (∀ x : ρ.invariants, P (x : V) = x) ∧
    ∀ S : Subrepresentation ρ, IsAtom S → ¬ S.toSubmodule ≤ ρ.invariants →
      ∀ x : S.toSubmodule, P (x : V) = 0

def IsGroupProjection (ρ : Representation k G V) (P : V →ₗ[k] ρ.invariants) : Prop :=
  ρ.IsIntertwiningMap (Representation.trivial k G ρ.invariants) P ∧
    HasGroupProjectionBehavior ρ P

end Group

def GroupProjection : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V],
    groupLinearlyReductive.{u,v,w} k G → ∀ ρ : Representation k G V,
      groupLocallyFinite ρ → ∃ P : V →ₗ[k] ρ.invariants, IsGroupProjection ρ P ∧
        ∀ Q : V →ₗ[k] ρ.invariants, HasGroupProjectionBehavior ρ Q → Q = P

def GroupProjectionNatural : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} {W : Type z} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W],
    groupLinearlyReductive.{u,v,w} k G →
    ∀ (ρ : Representation k G V) (σ : Representation k G W),
      groupLocallyFinite ρ → groupLocallyFinite σ →
      ∀ (P : V →ₗ[k] ρ.invariants) (Q : W →ₗ[k] σ.invariants),
        IsGroupProjection ρ P → IsGroupProjection σ Q →
        ∀ (f : V →ₗ[k] W), ρ.IsIntertwiningMap σ f →
          ∀ x : V, (Q (f x) : W) = f (P x : V)

/-- Under the inclusion of a finite-dimensional subrepresentation, its projection agrees
with the ambient projection on every vector. -/
def GroupProjectionRestriction : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V],
    groupLinearlyReductive.{u,v,w} k G → ∀ ρ : Representation k G V,
      groupLocallyFinite ρ → ∀ (S : Subrepresentation ρ) [FiniteDimensional k S.toSubmodule]
        (P : V →ₗ[k] ρ.invariants)
        (Q : S.toSubmodule →ₗ[k] S.toRepresentation.invariants),
        IsGroupProjection ρ P → IsGroupProjection S.toRepresentation Q →
        ∀ x : S.toSubmodule, (P (x : V) : V) = ((Q x : S.toSubmodule) : V)

def GroupProjectionReynolds : Prop :=
  ∀ {k : Type u} {G : Type v} {A : Type w} [Field k] [Group G] [Ring A] [Algebra k A],
    groupLinearlyReductive.{u,v,w} k G →
    ∀ ρ : GroupAlgebraAction k G A, groupLocallyFinite (groupRepresentation ρ) →
      ∀ P : A →ₗ[k] groupFixedSubalgebra ρ,
        IsGroupProjection (groupRepresentation ρ) P → groupIsReynolds ρ P

section Rational

variable {k : Type u} [Field k] {H : HopfAlgebraCategory k} {V : Type u}
  [AddCommGroup V] [Module k V]

/-- The linear-map characterization for right comodules. -/
def HasRationalProjectionBehavior (ρ : RightComodule k H V)
    (P : V →ₗ[k] RationalRepresentations.invariants H ρ) : Prop :=
  (∀ x : RationalRepresentations.invariants H ρ, P (x : V) = x) ∧
    ∀ S : Submodule k V, rationalIsSimpleSubcomodule ρ S →
      ¬ S ≤ RationalRepresentations.invariants H ρ → ∀ x : S, P (x : V) = 0

def IsRationalProjection (ρ : RightComodule k H V)
    (P : V →ₗ[k] RationalRepresentations.invariants H ρ) : Prop :=
  isComoduleMap ρ (rationalTrivial H) P ∧ HasRationalProjectionBehavior ρ P

end Rational

def RationalProjection : Prop :=
  ∀ {k V : Type u} [Field k] {H : HopfAlgebraCategory k} [AddCommGroup V] [Module k V],
    rationalLinearlyReductive H → ∀ ρ : RightComodule k H V,
      ∃ P : V →ₗ[k] RationalRepresentations.invariants H ρ, IsRationalProjection ρ P ∧
        ∀ Q : V →ₗ[k] RationalRepresentations.invariants H ρ,
          HasRationalProjectionBehavior ρ Q → Q = P

def RationalProjectionNatural : Prop :=
  ∀ {k V W : Type u} [Field k] {H : HopfAlgebraCategory k}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W],
    rationalLinearlyReductive H → ∀ (ρ : RightComodule k H V) (σ : RightComodule k H W)
      (P : V →ₗ[k] RationalRepresentations.invariants H ρ)
      (Q : W →ₗ[k] RationalRepresentations.invariants H σ),
      IsRationalProjection ρ P → IsRationalProjection σ Q →
        ∀ (f : V →ₗ[k] W), isComoduleMap ρ σ f → ∀ x : V, (Q (f x) : W) = f (P x : V)

/-- The inclusion is a comodule map for the induced coaction on the subspace. -/
def RationalProjectionRestriction : Prop :=
  ∀ {k V : Type u} [Field k] {H : HopfAlgebraCategory k} [AddCommGroup V] [Module k V],
    rationalLinearlyReductive H → ∀ (ρ : RightComodule k H V)
      (S : Submodule k V) [FiniteDimensional k S] (σ : RightComodule k H S),
      isComoduleMap σ ρ S.subtype →
      ∀ (P : V →ₗ[k] RationalRepresentations.invariants H ρ)
        (Q : S →ₗ[k] RationalRepresentations.invariants H σ),
        IsRationalProjection ρ P → IsRationalProjection σ Q →
        ∀ x : S, (P (x : V) : V) = ((Q x : S) : V)

def RationalProjectionReynolds : Prop :=
  ∀ {k A : Type u} [Field k] {H : HopfAlgebraCategory k} [Ring A] [Algebra k A],
    rationalLinearlyReductive H →
    ∀ (ρ : RationalAlgebraAction H A) (P : A →ₗ[k] rationalFixedSubalgebra ρ),
      IsRationalProjection (rationalToRightComodule ρ) P → rationalIsReynolds ρ P

end RepTheorySurvey.Invariants.Specs
