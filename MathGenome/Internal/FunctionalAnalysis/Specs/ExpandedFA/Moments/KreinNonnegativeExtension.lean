import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.FriedrichsExtension

/-! The unshifted energy construction in fa2:p3:krein-resolvent-order.
`Completion` of a seminormed space first identifies vectors at distance zero;
thus `W` is the Hilbert completion of D(S) modulo the null vectors of q,
including when q is identically zero. Inner products are conjugate-linear first. -/
noncomputable section
open scoped ComplexConjugate
open UniformSpace
universe u
namespace ExpandedFA.Moments.KreinNonnegativeExtension
open ExpandedFA.Unbounded ExpandedFA.Unbounded.FriedrichsExtension
open ExpandedFA.Unbounded.ClosedNonnegativeForms
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A separate copy of the original domain with the unshifted energy seminorm. -/
def EnergyCore (S : Operator ℂ H H) (_h : SemiboundedSymmetric S 0) : Type u := S.domain
instance (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0) : AddCommGroup (EnergyCore S h) :=
  inferInstanceAs (AddCommGroup S.domain)
instance (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0) : Module ℂ (EnergyCore S h) :=
  inferInstanceAs (Module ℂ S.domain)

@[instance_reducible] def energyCore (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0) :
    PreInnerProductSpace.Core ℂ (EnergyCore S h) where
  inner x y := inner ℂ ((show S.domain from x) : H) (S (show S.domain from y))
  conj_inner_symm x y := (inner_conj_symm _ _).trans
    (h.symmetric (show S.domain from x) (show S.domain from y))
  re_inner_nonneg x := by simpa using h.lower x
  add_left x y z := inner_add_left _ _ _
  smul_left x y c := inner_smul_left _ _ _

instance energySeminormed (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0) :
    SeminormedAddCommGroup (EnergyCore S h) :=
  letI := energyCore S h
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance energyInner (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0) :
    InnerProductSpace ℂ (EnergyCore S h) := InnerProductSpace.ofCore (energyCore S h)

abbrev W (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0) :=
  Completion (EnergyCore S h)

def classMap (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0) :
    S.domain →ₗ[ℂ] W S h :=
  (Completion.toComplL : EnergyCore S h →L[ℂ] W S h).toLinearMap

/-- The pullback form on precisely the domain of a densely defined R. -/
def pullbackForm {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (R : Operator ℂ H V) (hd : Dense (R.domain : Set H)) : NonnegativeForm ℂ H where
  domain := R.domain
  dense := hd
  form := ((innerₛₗ ℂ).compl₂ R.toFun).comp R.toFun
  hermitian _x _y := inner_conj_symm _ _
  nonneg _x := inner_self_nonneg

/-- All data and semantic properties of the manuscript construction. -/
structure Construction (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0)
    [CompleteSpace H] where
  R : Operator ℂ H (W S h)
  graph_iff : ∀ x w, (x, w) ∈ R.graph ↔
    ∀ y : S.domain, inner ℂ w (classMap S h y) = inner ℂ x (S y)
  bounded_domain : ∀ x, x ∈ R.domain ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : S.domain,
      ‖inner ℂ x (S y)‖ ≤ C * ‖classMap S h y‖
  core_domain : S.domain ≤ R.domain
  on_core : ∀ y : S.domain, R ⟨y, core_domain y.property⟩ = classMap S h y
  dense : Dense (R.domain : Set H)
  closed : R.IsClosed
  closed_form : (pullbackForm R dense).IsClosed
  extension : Operator ℂ H H
  associated : (pullbackForm R dense).Associated extension
  extends_operator : S ≤ extension
  extension_dense : Dense (extension.domain : Set H)
  selfAdjoint : extension = HilbertAdjointSpec.adjointValue extension
  nonnegative : ∀ x : extension.domain,
    0 ≤ RCLike.re (inner ℂ (x : H) (extension x))

namespace Spec
/-- No strictly positive lower bound. The source assumes closedness of S. -/
def KreinConstruction : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0), S.IsClosed →
    Nonempty (Construction S h)
end Spec
end ExpandedFA.Moments.KreinNonnegativeExtension
