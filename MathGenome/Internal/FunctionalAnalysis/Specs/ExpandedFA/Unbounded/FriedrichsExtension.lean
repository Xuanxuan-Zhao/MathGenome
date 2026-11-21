import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.ClosedNonnegativeForms
import Mathlib.Analysis.InnerProductSpace.Completion

/-! Friedrichs extension, paper.tex, fa2:p3:friedrichs. Inner products are
conjugate-linear in the first variable. The shift is by a real scalar and the
form completion uses q(u,u)+‖u‖², equivalently the strictly positive shifted
operator S+(1-c)I. No completeness of the original operator domain is assumed. -/
noncomputable section
open scoped ComplexConjugate Topology
open Filter UniformSpace
universe u v
namespace ExpandedFA.Unbounded.FriedrichsExtension
open ClosedNonnegativeForms
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Addition of a real scalar multiple of I on exactly the original domain. -/
def realShift (A : Operator 𝕜 H H) (c : ℝ) : Operator 𝕜 H H :=
  { domain := A.domain
    toFun := A.toFun + (c : 𝕜) • A.domain.subtype }

/-- Precisely the density, symmetry and semiboundedness hypotheses. -/
structure SemiboundedSymmetric (S : Operator 𝕜 H H) (c : ℝ) : Prop where
  dense : Dense (S.domain : Set H)
  symmetric : S.IsFormalAdjoint S
  lower : ∀ x : S.domain, c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (x : H) (S x))

/-- The nonnegative form of S-cI before closure. -/
def operatorForm (S : Operator 𝕜 H H) (c : ℝ) (h : SemiboundedSymmetric S c) :
    NonnegativeForm 𝕜 H where
  domain := S.domain
  dense := h.dense
  form := ((innerₛₗ 𝕜).compl₂ (realShift S (-c)).toFun).comp S.domain.subtype
  hermitian x y := by
    change conj (inner 𝕜 (y : H) (S x + ((-c : ℝ) : 𝕜) • (x : H))) =
      inner 𝕜 (x : H) (S y + ((-c : ℝ) : 𝕜) • (y : H))
    simp only [inner_add_right, inner_smul_right, map_add, map_mul,
      RCLike.conj_ofReal, inner_conj_symm]
    rw [h.symmetric x y]
  nonneg x := by
    change 0 ≤ RCLike.re (inner 𝕜 (x : H) (S x + ((-c : ℝ) : 𝕜) • (x : H)))
    simp only [inner_add_right, inner_smul_right, map_add, RCLike.re_ofReal_mul,
      ← norm_sq_eq_re_inner]
    linarith [h.lower x]

/-- A closed form obtained from the actual Hilbert completion, including its
injective continuous inclusion, dense original core and full form identity.
The on-core identity fixes the embedding uniquely by continuity; the final
identity fixes the closed form on its entire domain. -/
structure FormClosure (q : NonnegativeForm 𝕜 H) where
  embedding : Completion q.EnergySpace →L[𝕜] H
  injective : Function.Injective embedding
  on_core : ∀ x : q.EnergySpace, embedding (x : Completion q.EnergySpace) = (q.toDomain x : H)
  contractive : ∀ x, ‖embedding x‖ ≤ ‖x‖
  closedForm : NonnegativeForm 𝕜 H
  closed : closedForm.IsClosed
  equivalence : Completion q.EnergySpace ≃ₗ[𝕜] closedForm.domain
  inclusion : ∀ x, (equivalence x : H) = embedding x
  energy_identity : ∀ x y,
    closedForm.form (equivalence x) (equivalence y) + inner 𝕜 (embedding x) (embedding y) =
      inner 𝕜 x y

/-- Sequential criterion for closability in the shifted form norm. -/
def FormClosable (q : NonnegativeForm 𝕜 H) : Prop :=
  ∀ x : ℕ → q.EnergySpace, CauchySeq x →
    Tendsto (fun n => (q.toDomain (x n) : H)) atTop (𝓝 0) → Tendsto x atTop (𝓝 0)

namespace Spec

def CompletionEmbedding : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : Operator 𝕜 H H) (c : ℝ) (h : SemiboundedSymmetric S c),
    Nonempty (FormClosure (operatorForm S c h))

def Closability : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : Operator 𝕜 H H) (c : ℝ) (h : SemiboundedSymmetric S c),
    FormClosable (operatorForm S c h)

/-- The extension is uniquely selected by the closure of its shifted quadratic
form. Associated specifies its exact graph, not merely a one-sided identity. -/
def Extension : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : Operator 𝕜 H H) (c : ℝ) (h : SemiboundedSymmetric S c)
    (F : FormClosure (operatorForm S c h)),
    ∃! A : Operator 𝕜 H H,
      F.closedForm.Associated (realShift A (-c)) ∧ S ≤ A ∧
      Dense (A.domain : Set H) ∧ A = HilbertAdjointSpec.adjointValue A ∧
      ∀ x : A.domain, c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (x : H) (A x))
/-- The unconditional source theorem: both the form closure and the canonical
extension are constructed from the original operator hypotheses alone. -/
def Friedrichs : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : Operator 𝕜 H H) (c : ℝ) (h : SemiboundedSymmetric S c),
    ∃ F : FormClosure (operatorForm S c h),
      ∃! A : Operator 𝕜 H H,
        F.closedForm.Associated (realShift A (-c)) ∧ S ≤ A ∧
        Dense (A.domain : Set H) ∧ A = HilbertAdjointSpec.adjointValue A ∧
        ∀ x : A.domain, c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (x : H) (A x))

/-- The associated operator depends on the original form, not on the witnesses
used to realize its completed domain in H. -/
def Canonical : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (q : NonnegativeForm 𝕜 H) (F G : FormClosure q) (A : Operator 𝕜 H H),
    F.closedForm.Associated A ↔ G.closedForm.Associated A
end Spec
end ExpandedFA.Unbounded.FriedrichsExtension
