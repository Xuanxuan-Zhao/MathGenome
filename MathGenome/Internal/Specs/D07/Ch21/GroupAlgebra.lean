import MathGenome.Internal.Specs.D07.Ch17.SubrepresentationsQuotients
import MathGenome.Internal.Specs.D07.Ch17.IntertwinersEquivalence
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
Independent specification for K07.21.group_algebra, paper.tex:6163–6193.
The algebra is the canonical complex monoid algebra, with its convolution
product. No dimension or nonzero hypothesis is imposed on a representation.
`CompatibleModule` records precisely a unital module structure whose restriction
to the scalar subalgebra is the already specified complex vector space action.
-/
namespace Specs.D07.Ch21.GroupAlgebra

universe u v w

noncomputable section

/-- Unital group-algebra modules on a fixed complex vector space, with the
specified scalar action, rather than an independently chosen scalar action. -/
@[ext] structure CompatibleModule (G : Type u) (V : Type v) [Group G]
    [AddCommGroup V] [Module ℂ V] where
  module : Module (MonoidAlgebra ℂ G) V
  scalar_eq : letI := module
    ∀ (c : ℂ) (x : V), (algebraMap ℂ (MonoidAlgebra ℂ G) c) • x = c • x

/-- The action associated to the explicitly supplied module structure. -/
def CompatibleModule.act {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] (m : CompatibleModule G V)
    (a : MonoidAlgebra ℂ G) (x : V) : V :=
  letI := m.module
  a • x

def BasisDescription : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    ∃ b : Module.Basis G ℂ (MonoidAlgebra ℂ G),
      (∀ g, b g = MonoidAlgebra.single g 1) ∧
      (∀ a, b.repr a = a.coeff) ∧
      (∀ (a : MonoidAlgebra ℂ G), a = ∑ g : G, a.coeff g • MonoidAlgebra.single g 1)

def AlgebraLaws : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    (∀ (g h : G) (c d : ℂ),
      MonoidAlgebra.single g c * MonoidAlgebra.single h d =
        MonoidAlgebra.single (g * h) (c * d)) ∧
    MonoidAlgebra.single (1 : G) (1 : ℂ) = 1 ∧
    MonoidAlgebra.single (1 : G) (1 : ℂ) ≠ 0 ∧
    (∀ a b c : MonoidAlgebra ℂ G, (a * b) * c = a * (b * c)) ∧
    (∀ a b c : MonoidAlgebra ℂ G, (a + b) * c = a * c + b * c) ∧
    (∀ a b c : MonoidAlgebra ℂ G, a * (b + c) = a * b + a * c) ∧
    (∀ (c : ℂ) (a b : MonoidAlgebra ℂ G),
      (c • a) * b = c • (a * b) ∧ a * (c • b) = c • (a * b)) ∧
    (∀ (c : ℂ) (a : MonoidAlgebra ℂ G),
      algebraMap ℂ (MonoidAlgebra ℂ G) c = MonoidAlgebra.single 1 c ∧
      MonoidAlgebra.single 1 c * a = a * MonoidAlgebra.single 1 c)

def Dimension : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    Module.Finite ℂ (MonoidAlgebra ℂ G) ∧
    Module.finrank ℂ (MonoidAlgebra ℂ G) = Fintype.card G

/-- The universal property specifies the image of every basis vector. -/
def ExtensionUnique : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    ∃! F : MonoidAlgebra ℂ G →ₐ[ℂ] Module.End ℂ V,
      ∀ g, F (MonoidAlgebra.single g 1) = ρ g

/-- Explicit linear extension, including its action on vectors and products. -/
def ExtensionFormula : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    (∀ a, ρ.asAlgebraHom a = ∑ g : G, a.coeff g • ρ g) ∧
    (∀ a x, ρ.asAlgebraHom a x = ∑ g : G, a.coeff g • ρ g x) ∧
    (∀ a b, ρ.asAlgebraHom (a * b) =
      ∑ g : G, ∑ h : G, (a.coeff g * b.coeff h) • ρ (g * h))

/-- The two constructions are inverse on the fixed vector space, and both
preserve the actual action, including its scalar action. -/
def ModuleCorrespondence : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V],
    ∃ e : Representation ℂ G V ≃ CompatibleModule G V,
      (∀ ρ a x, (e ρ).act a x = ρ.asAlgebraHom a x) ∧
      (∀ m g x, e.symm m g x = m.act (MonoidAlgebra.single g 1) x) ∧
      (∀ (m : CompatibleModule G V) (g : G) (x : V),
        m.act (MonoidAlgebra.single g 1)
            (m.act (MonoidAlgebra.single g⁻¹ 1) x) = x ∧
        m.act (MonoidAlgebra.single g⁻¹ 1)
            (m.act (MonoidAlgebra.single g 1) x) = x)

def InvariantIffAlgebraStable : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (U : Submodule ℂ V),
    Specs.D07.Ch17.SubrepresentationsQuotients.invariantValue ℂ G V ρ U ↔
      ∀ (a : MonoidAlgebra ℂ G) (x : V), x ∈ U → ρ.asAlgebraHom a x ∈ U

/-- The invariant subspace is the underlying subspace of an actual unique
module submodule, with the original elements and scalar operations. -/
def SubmoduleCorrespondence : Prop :=
  ∀ (G : Type u) (V : Type v) [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (U : Submodule ℂ V),
    Specs.D07.Ch17.SubrepresentationsQuotients.invariantValue ℂ G V ρ U ↔
      ∃! W : Submodule (MonoidAlgebra ℂ G) ρ.asModule,
        ∀ x, x ∈ W ↔ ρ.asModuleEquiv x ∈ U

/-- Equivariance is exactly commuting with every element of the group algebra. -/
def EquivariantIffAlgebraLinear : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G] [Fintype G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (T : V →ₗ[ℂ] W),
    ρ.IsIntertwiningMap σ T ↔
      ∀ a x, T (ρ.asAlgebraHom a x) = σ.asAlgebraHom a (T x)

/-- Equivariant maps are precisely actual module linear maps. -/
def ModuleMapCorrespondence : Prop :=
  ∀ (G : Type u) (V : Type v) (W : Type w) [Group G] [Fintype G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (T : V →ₗ[ℂ] W),
    ρ.IsIntertwiningMap σ T ↔
      ∃! f : ρ.asModule →ₗ[MonoidAlgebra ℂ G] σ.asModule,
        ∀ x, σ.asModuleEquiv (f x) = T (ρ.asModuleEquiv x)

/-- For a one-element group the identification with ℂ is an algebra
isomorphism, with the prescribed scalar basis element as its inverse. -/
def TrivialGroupAlgebra : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G] [Subsingleton G],
    ∃ e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ℂ,
      (∀ a, e a = a.coeff 1) ∧
      (∀ c, e.symm c = MonoidAlgebra.single 1 c)

end
end Specs.D07.Ch21.GroupAlgebra
