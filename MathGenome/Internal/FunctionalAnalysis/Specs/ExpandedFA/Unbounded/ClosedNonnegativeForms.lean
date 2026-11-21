import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Closed nonnegative forms, paper.tex:13742–13779. The scalar field is real
or complex. A nonnegative form is Hermitian (symmetric in the real case),
conjugate-linear in its test variable, and linear in its unknown. Its form
domain is an actual submodule of the ambient Hilbert space. The separate type
`EnergySpace` carries the form norm, rather than the ambient subspace norm.
No boundedness in the ambient norm is assumed. -/
noncomputable section
open scoped ComplexConjugate
universe u v
namespace ExpandedFA.Unbounded.ClosedNonnegativeForms
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

structure NonnegativeForm (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] where
  domain : Submodule 𝕜 H
  dense : Dense (domain : Set H)
  form : domain →ₗ⋆[𝕜] domain →ₗ[𝕜] 𝕜
  hermitian : ∀ x y, conj (form y x) = form x y
  nonneg : ∀ x, 0 ≤ RCLike.re (form x x)

namespace NonnegativeForm
variable (q : NonnegativeForm 𝕜 H)

/-- A copy of V, whose norm is the form norm. -/
def EnergySpace : Type v := q.domain
instance : AddCommGroup q.EnergySpace := inferInstanceAs (AddCommGroup q.domain)
instance : Module 𝕜 q.EnergySpace := inferInstanceAs (Module 𝕜 q.domain)

def toDomain (x : q.EnergySpace) : q.domain := x

@[instance_reducible] def energyCore : InnerProductSpace.Core 𝕜 q.EnergySpace where
  inner x y := q.form (q.toDomain x) (q.toDomain y) +
    inner 𝕜 (q.toDomain x : H) (q.toDomain y : H)
  conj_inner_symm x y := by
    simp only [map_add, q.hermitian, inner_conj_symm]
  re_inner_nonneg x := by
    rw [map_add]
    exact add_nonneg (q.nonneg _) (inner_self_nonneg (𝕜 := 𝕜))
  add_left x y z := by
    change q.form (q.toDomain x + q.toDomain y) (q.toDomain z) +
      inner 𝕜 ((q.toDomain x : H) + (q.toDomain y : H)) (q.toDomain z : H) = _
    simp only [map_add, LinearMap.add_apply, inner_add_left]
    abel
  smul_left x y c := by
    change q.form (c • q.toDomain x) (q.toDomain y) +
      inner 𝕜 (c • (q.toDomain x : H)) (q.toDomain y : H) = _
    simp only [map_smulₛₗ, LinearMap.smul_apply, inner_smul_left]
    exact (mul_add _ _ _).symm
  definite x hx := by
    have h := congrArg RCLike.re hx
    simp only [map_add, map_zero, ← norm_sq_eq_re_inner] at h
    have hn := q.nonneg (q.toDomain x)
    have hz : ‖(q.toDomain x : H)‖ = 0 := by nlinarith [sq_nonneg ‖(q.toDomain x : H)‖]
    exact Subtype.ext (norm_eq_zero.mp hz)

instance energyNormedAddCommGroup : NormedAddCommGroup q.EnergySpace :=
  letI : InnerProductSpace.Core 𝕜 q.EnergySpace := q.energyCore
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := 𝕜)

instance energyInnerProductSpace : InnerProductSpace 𝕜 q.EnergySpace :=
  InnerProductSpace.ofCore { q.energyCore with }

/-- Closedness means completeness for precisely q(u,u)+‖u‖². -/
def IsClosed : Prop := CompleteSpace q.EnergySpace

/-- Exact graph of the associated operator, specifying both its domain and action. -/
def Associated (A : Operator 𝕜 H H) : Prop :=
  ∀ u f : H, (u, f) ∈ A.graph ↔
    ∃ hu : u ∈ q.domain, ∀ v : q.domain, q.form v ⟨u, hu⟩ = inner 𝕜 (v : H) f

end NonnegativeForm

namespace Spec
/-- Type and independent value of the closed-form predicate. -/
def ClosedFormPredicateType :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H], NonnegativeForm 𝕜 H → Prop

def closedFormPredicateValue (q : NonnegativeForm 𝕜 H) : Prop :=
  CompleteSpace q.EnergySpace

/-- The explicit identity also records the actual norm used by closedness. -/
def EnergyNormIdentity : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (q : NonnegativeForm 𝕜 H) (x : q.EnergySpace),
    ‖x‖ ^ 2 = RCLike.re (q.form (q.toDomain x) (q.toDomain x)) + ‖(q.toDomain x : H)‖ ^ 2

def Representation : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (q : NonnegativeForm 𝕜 H), q.IsClosed →
    ∃! A : Operator 𝕜 H H,
      q.Associated A ∧ Dense (A.domain : Set H) ∧ A = HilbertAdjointSpec.adjointValue A ∧
      (∀ x : A.domain, 0 ≤ RCLike.re (inner 𝕜 (x : H) (A x)))

def ExactDomain : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (q : NonnegativeForm 𝕜 H) (A : Operator 𝕜 H H), q.Associated A →
    ∀ u : H, u ∈ A.domain ↔
      ∃ hu : u ∈ q.domain, ∃ f : H, ∀ v : q.domain,
        q.form v ⟨u, hu⟩ = inner 𝕜 (v : H) f
end Spec
end ExpandedFA.Unbounded.ClosedNonnegativeForms
