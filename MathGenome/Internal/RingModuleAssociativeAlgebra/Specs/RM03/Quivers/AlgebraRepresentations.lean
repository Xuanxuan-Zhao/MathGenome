import Mathlib.Algebra.MonoidAlgebra.Basic

namespace RM03.Quivers.AlgebraRepresentations

open scoped MonoidAlgebra

universe u v w x

/-- A left module structure on the given additive group, with its original field
action recovered by restriction along the algebra map. -/
structure CompatibleModule (k : Type u) (A : Type v) (V : Type w)
    [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] where
  module : Module A V
  scalar : ∀ (c : k) (z : V), (letI := module; algebraMap k A c • z) = c • z

section
variable {k : Type u} {A : Type v} {V : Type w} {W : Type x}
  [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- Evaluate the chosen algebra action on the original vector space. -/
def CompatibleModule.act (M : CompatibleModule k A V) (a : A) (z : V) : V :=
  letI := M.module
  a • z

/-- The given linear map is also linear for the two specified algebra actions. -/
def IsModuleLinear (M : CompatibleModule k A V) (N : CompatibleModule k A W)
    (f : V →ₗ[k] W) : Prop :=
  letI := M.module
  letI := N.module
  ∃ F : V →ₗ[A] W, ∀ z, F z = f z

end

namespace Specs

def correspondenceType : Prop :=
  ∀ {k : Type u} {A : Type v} {V : Type w}
    [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V],
    ∃ E : (A →ₐ[k] Module.End k V) ≃ CompatibleModule k A V,
      (∀ ρ a z, (E ρ).act a z = ρ a z) ∧
      (∀ M a z, E.symm M a z = M.act a z)

def intertwinesIffModuleLinearType : Prop :=
  ∀ {k : Type u} {A : Type v} {V : Type w} {W : Type x}
    [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (ρ : A →ₐ[k] Module.End k V) (σ : A →ₐ[k] Module.End k W)
    (M : CompatibleModule k A V) (N : CompatibleModule k A W),
    (∀ a z, M.act a z = ρ a z) → (∀ a z, N.act a z = σ a z) →
    ∀ f : V →ₗ[k] W, (∀ a z, f (ρ a z) = σ a (f z)) ↔ IsModuleLinear M N f

def groupAlgebraExtensionType : Prop :=
  ∀ {k : Type u} {G : Type v} {V : Type w}
    [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : G →* (V ≃ₗ[k] V)),
    ∃ (extension : k[G] →ₐ[k] Module.End k V) (M : CompatibleModule k k[G] V),
      (∀ a z, extension a z = M.act a z) ∧
      (∀ (a : k[G]) z, M.act a z = a.coeff.sum (fun g c => c • ρ g z)) ∧
      (∀ g z, M.act (MonoidAlgebra.of k G g) z = ρ g z)

end Specs
end RM03.Quivers.AlgebraRepresentations
