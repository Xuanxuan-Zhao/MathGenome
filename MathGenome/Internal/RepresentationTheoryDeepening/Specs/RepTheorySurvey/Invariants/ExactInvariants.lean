import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.CanonicalProjection
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.RationalActionComparison
import Mathlib.Algebra.Exact.Basic

open AlgebraicGeometry CategoryTheory LinearAlgebraicGroups
open RationalRepresentations
open scoped TensorProduct

universe u v w z

namespace RepTheorySurvey.Invariants.Specs.ExactInvariants

noncomputable section

variable {k : Type u} [Field k]

/-- The underlying sequence of vector spaces is short exact. -/
def ShortExact {U V W : Type w} [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (f : U →ₗ[k] V) (g : V →ₗ[k] W) : Prop :=
  Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g

/-- Restrict an equivariant linear map to the chosen fixed subspaces. -/
def fixedMap {V W : Type w} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (I : Submodule k V) (J : Submodule k W)
    (f : V →ₗ[k] W) (hf : I ≤ J.comap f) : I →ₗ[k] J :=
  (f.comp I.subtype).codRestrict J fun x ↦ hf x.property

section Group

variable {G : Type v} [Group G]
  {V W : Type w} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem group_preserves_fixed {ρ : Representation k G V} {σ : Representation k G W}
    {f : V →ₗ[k] W} (hf : ρ.IsIntertwiningMap σ f) :
    ρ.invariants ≤ σ.invariants.comap f := by
  intro x hx g
  rw [← hf.isIntertwining g x, hx g]

/-- Exactness of fixed vectors on the full subcategory selected by `P`. -/
def GroupExact (G : Type v) [Group G]
    (P : ∀ {V : Type w} [AddCommGroup V] [Module k V], Representation k G V → Prop) : Prop :=
  ∀ {U V W : Type w} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (τ : Representation k G U) (ρ : Representation k G V) (σ : Representation k G W),
    P τ → P ρ → P σ → ∀ (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (hf : τ.IsIntertwiningMap ρ f) (hg : ρ.IsIntertwiningMap σ g),
    ShortExact f g →
      ShortExact (fixedMap _ _ f (group_preserves_fixed hf))
        (fixedMap _ _ g (group_preserves_fixed hg))

def GroupLocallyFiniteExact : Prop :=
  ∀ (k : Type u) (G : Type v) [Field k] [Group G],
    groupLinearlyReductive.{u,v,w} k G → GroupExact.{u,v,w} (k := k) G groupLocallyFinite

def GroupFiniteExactConverse : Prop :=
  ∀ (k : Type u) (G : Type v) [Field k] [Group G],
    GroupExact (k := k) G (fun {V : Type w} _ _ _ ↦ FiniteDimensional k V) →
    groupLinearlyReductive.{u,v,w} k G

end Group

section Rational

variable {H : HopfAlgebraCategory k} {V W : Type u}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem mem_rational_fixed (ρ : RightComodule k H V) (x : V) :
    x ∈ invariants H ρ ↔ ρ.coaction x = x ⊗ₜ[k] (1 : H) := by
  change ρ.coaction x - x ⊗ₜ[k] (1 : H) = 0 ↔ _
  exact sub_eq_zero

theorem rational_preserves_fixed {ρ : RightComodule k H V} {σ : RightComodule k H W}
    {f : V →ₗ[k] W} (hf : isComoduleMap ρ σ f) :
    invariants H ρ ≤ (invariants H σ).comap f := by
  intro x hx
  apply (mem_rational_fixed σ _).mpr
  have eq : f.rTensor H (ρ.coaction x) = σ.coaction (f x) := DFunLike.congr_fun hf x
  rw [← eq, (mem_rational_fixed ρ x).mp hx, LinearMap.rTensor_tmul]

def RationalExact (H : HopfAlgebraCategory k)
    (P : ∀ {V : Type u} [AddCommGroup V] [Module k V], RightComodule k H V → Prop) : Prop :=
  ∀ {U V W : Type u} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (τ : RightComodule k H U) (ρ : RightComodule k H V) (σ : RightComodule k H W),
    P τ → P ρ → P σ → ∀ (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (hf : isComoduleMap τ ρ f) (hg : isComoduleMap ρ σ g),
    ShortExact f g →
      ShortExact (fixedMap _ _ f (rational_preserves_fixed hf))
        (fixedMap _ _ g (rational_preserves_fixed hg))

def RationalExactOfReductive : Prop :=
  ∀ {k : Type u} [Field k] (H : HopfAlgebraCategory k),
    rationalLinearlyReductive H → RationalExact H (fun {_} _ _ _ ↦ True)

def RationalFiniteExactConverse : Prop :=
  ∀ {k : Type u} [Field k] (H : HopfAlgebraCategory k),
    RationalExact H (fun {V} _ _ _ ↦ FiniteDimensional k V) →
    rationalLinearlyReductive H

end Rational

section Geometric

open RationalActionComparison

variable (G : GroupScheme k)

/-- Complete reducibility for finite-dimensional rational actions on the (k)-points. -/
def RegularLinearlyReductive : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k (KPoints G) V), HasRegularOrbits ρ →
    ∃ (n : ℕ) (S : Fin n → Subrepresentation ρ),
      (∀ i, IsAtom (S i)) ∧ DirectSum.IsInternal (fun i ↦ (S i).toSubmodule)

def RegularlyExact : Prop :=
  GroupExact (k := k) (KPoints G) (fun {_} _ _ ρ ↦ HasRegularOrbits ρ)

def RegularFiniteExact : Prop :=
  GroupExact (k := k) (KPoints G)
    (fun {V} _ _ ρ ↦ FiniteDimensional k V ∧ HasRegularOrbits ρ)

def RegularComparison : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : GroupScheme k)
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom]
    (H : GlobalFunctions.Specs.GlobalHopf G) (a : G ⟶ H.spectrum),
    a.hom.hom = GlobalFunctions.unit G.X →
    (RegularLinearlyReductive G ↔ rationalLinearlyReductive H.hopf) ∧
    (RegularlyExact G ↔ RationalExact H.hopf (fun {_} _ _ _ ↦ True)) ∧
    (RegularFiniteExact G ↔
      RationalExact H.hopf (fun {V} _ _ _ ↦ FiniteDimensional k V))

def RegularExactCharacterization : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : GroupScheme k)
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom],
    (RegularLinearlyReductive G → RegularlyExact G) ∧
    (RegularFiniteExact G → RegularLinearlyReductive G)

def RegularProjection : Prop :=
  ∀ {k V : Type u} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom],
    RegularLinearlyReductive G → ∀ ρ : Representation k (KPoints G) V,
      HasRegularOrbits ρ → ∃ P : V →ₗ[k] ρ.invariants, IsGroupProjection ρ P ∧
        ∀ Q : V →ₗ[k] ρ.invariants, HasGroupProjectionBehavior ρ Q → Q = P

def RegularProjectionNatural : Prop :=
  ∀ {k V W : Type u} [Field k] [IsAlgClosed k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom],
    RegularLinearlyReductive G → ∀ (ρ : Representation k (KPoints G) V)
      (σ : Representation k (KPoints G) W), HasRegularOrbits ρ → HasRegularOrbits σ →
      ∀ (P : V →ₗ[k] ρ.invariants) (Q : W →ₗ[k] σ.invariants),
        IsGroupProjection ρ P → IsGroupProjection σ Q →
        ∀ (f : V →ₗ[k] W), ρ.IsIntertwiningMap σ f →
          ∀ x : V, (Q (f x) : W) = f (P x : V)

def RegularProjectionReynolds : Prop :=
  ∀ {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom],
    RegularLinearlyReductive G → ∀ ρ : GroupAlgebraAction k (KPoints G) A,
      HasRegularOrbits (groupRepresentation ρ) → ∀ P : A →ₗ[k] groupFixedSubalgebra ρ,
        IsGroupProjection (groupRepresentation ρ) P → groupIsReynolds ρ P

end Geometric

/-- The projection, exactness, and converse for abstract group actions. -/
def AbstractGroupProposition : Prop :=
  GroupProjection.{u,v,w} ∧ GroupProjectionNatural.{u,v,w,z} ∧ GroupProjectionReynolds.{u,v,w} ∧
    GroupLocallyFiniteExact.{u,v,w} ∧ GroupFiniteExactConverse.{u,v,w}

/-- The projection, exactness, and converse for rational actions of a commutative Hopf algebra. -/
def RationalProposition : Prop :=
  RationalProjection.{u} ∧ RationalProjectionNatural.{u} ∧ RationalProjectionReynolds.{u} ∧
    RationalExactOfReductive.{u} ∧ RationalFiniteExactConverse.{u}

/-- The proposition for rational actions of smooth algebraic groups on their (k)-points. -/
def SmoothGroupProposition : Prop :=
  RegularProjection.{u} ∧ RegularProjectionNatural.{u} ∧ RegularProjectionReynolds.{u} ∧
    RegularExactCharacterization.{u}


end

end RepTheorySurvey.Invariants.Specs.ExactInvariants
