import Mathlib.RepresentationTheory.Intertwining

/-! Canonical objects for Chapter 8, over arbitrary fields and arbitrary groups.
There are no dimension or nonzero hypotheses on the vector spaces. -/
noncomputable section
universe u v w x
namespace P103.Ch08
open scoped MonoidAlgebra

variable (k G V : Type*) [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A unital group algebra module on the given additive group, restricting to
its specified scalar multiplication. -/
structure CompatibleModule where
  module : Module k[G] V
  scalar : ∀ (c : k) (v : V), (letI := module; algebraMap k k[G] c • v) = c • v

namespace CompatibleModule
variable {k G V}
def act (M : CompatibleModule k G V) (a : k[G]) (v : V) : V :=
  letI := M.module
  a • v

noncomputable def representation (M : CompatibleModule k G V) : Representation k G V :=
  letI := M.module
  letI : IsScalarTower k k[G] V := IsScalarTower.of_algebraMap_smul M.scalar
  Representation.ofModule' V
end CompatibleModule

/-- The standard group algebra action, on the same vector space. -/
noncomputable def representationModule (ρ : Representation k G V) : CompatibleModule k G V where
  module := ρ.instModuleMonoidAlgebraAsModule
  scalar c v := by
    exact (ρ.asModuleEquiv_symm_map_smul c v).symm

/-- Nonzero and with no proper nonzero invariant subspace. -/
def Irreducible (ρ : Representation k G V) : Prop :=
  Nontrivial V ∧ ∀ U : Subrepresentation ρ, U = ⊥ ∨ U = ⊤

namespace Specs
variable {k G V}

/-- The basis convention fixes multiplication and the finite-support model. -/
def basisProduct : Prop := ∀ g h : G,
  (MonoidAlgebra.single g (1 : k)) * MonoidAlgebra.single h 1 =
    MonoidAlgebra.single (g * h) 1

/-- A group representation in the automorphism definition and the library
endomorphism definition are equivalent, preserving evaluation. -/
def automorphismCorrespondence : Prop :=
  ∃ E : (G →* (V ≃ₗ[k] V)) ≃ Representation k G V,
    (∀ (ρ : G →* (V ≃ₗ[k] V)) g v, E ρ g v = ρ g v) ∧
    (∀ (ρ : Representation k G V) g v, E.symm ρ g v = ρ g v)

/-- Mutually inverse actions on exactly V, with the finite-sum formula. -/
def moduleCorrespondence : Prop :=
  ∃ E : Representation k G V ≃ CompatibleModule k G V,
    (∀ ρ, E ρ = representationModule k G V ρ) ∧
    (∀ M, E.symm M = M.representation) ∧
    (∀ ρ (a : k[G]) v,
      (E ρ).act a v = a.coeff.sum (fun g c => c • ρ g v)) ∧
    (∀ M g v, E.symm M g v = M.act (MonoidAlgebra.single g 1) v)

variable {W : Type*} [AddCommGroup W] [Module k W]

/-- The actual maps are preserved in both directions.  `asModule` is the
identity type synonym; its algebra action is `representationModule.module`. -/
def intertwinerCorrespondence (ρ : Representation k G V) (σ : Representation k G W) : Prop :=
  ∃ E : ρ.IntertwiningMap σ ≃ (ρ.asModule →ₗ[k[G]] σ.asModule),
    (∀ f v, E f (ρ.asModuleEquiv.symm v) = σ.asModuleEquiv.symm (f v)) ∧
    (∀ f v, E.symm f v = σ.asModuleEquiv (f (ρ.asModuleEquiv.symm v)))

/-- Membership preservation identifies invariant vector subspaces and algebra submodules. -/
def subspaceCorrespondence (ρ : Representation k G V) : Prop :=
  ∃ E : Subrepresentation ρ ≃o Submodule k[G] ρ.asModule,
    ∀ U v, ρ.asModuleEquiv.symm v ∈ E U ↔ v ∈ U

/-- Restriction has the inherited algebra action, on the same subtype. -/
def restrictionCompatibility (ρ : Representation k G V) : Prop :=
  ∀ U : Subrepresentation ρ, ∀ (a : k[G]) (v : U.toSubmodule),
    ((representationModule k G U.toSubmodule U.toRepresentation).act a v : V) =
      (representationModule k G V ρ).act a v

/-- Quotients carry the induced algebra action; the generator action is
`g(v+U) = gv+U`, and the same formula holds for every algebra element. -/
def quotientCompatibility (ρ : Representation k G V) : Prop :=
  ∀ U : Subrepresentation ρ,
    (∀ g v, U.quotient g (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (ρ g v)) ∧
    (∀ (a : k[G]) v,
      (representationModule k G (V ⧸ U.toSubmodule) U.quotient).act a
        (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((representationModule k G V ρ).act a v))

/-- The invariant kernel and image have exactly the algebra-linear kernel and
image, and their restrictions carry the inherited action. -/
def kernelImageCompatibility (ρ : Representation k G V) (σ : Representation k G W) : Prop :=
  ∀ f : ρ.IntertwiningMap σ,
    f.ker.asSubmodule = LinearMap.ker (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) ∧
    f.range.asSubmodule = LinearMap.range (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f)

/-- The convention explicitly excludes the zero representation. -/
def irreducibleConvention (ρ : Representation k G V) : Prop :=
  Irreducible k G V ρ ↔
    Nontrivial V ∧ ∀ U : Subrepresentation ρ, U = ⊥ ∨ U = ⊤


/-! Closed expected theorem types for independent checking. -/
def extendRepresentationType : Type (max (u + 1) (v + 1) (w + 1)) :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V), CompatibleModule k G V

/-- Independently specified standard extension of the given representation. -/
def extendRepresentationValue : extendRepresentationType.{u,v,w} :=
  fun {k G V} _ _ _ _ ρ => representationModule k G V ρ

def basisProductType : Prop :=
  ∀ {k : Type u} {G : Type v} [Field k] [Group G], basisProduct (k := k) (G := G)

def automorphismCorrespondenceType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V], automorphismCorrespondence (k := k) (G := G) (V := V)

def moduleCorrespondenceType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V], moduleCorrespondence (k := k) (G := G) (V := V)

def intertwinerCorrespondenceType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] {W : Type x} [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W), intertwinerCorrespondence ρ σ

def subspaceCorrespondenceType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V), subspaceCorrespondence ρ

def restrictionCompatibilityType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V), restrictionCompatibility ρ

def quotientCompatibilityType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V), quotientCompatibility ρ

def kernelImageCompatibilityType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] {W : Type x} [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W), kernelImageCompatibility ρ σ

def irreducibleConventionType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V), irreducibleConvention ρ

end Specs
end P103.Ch08
