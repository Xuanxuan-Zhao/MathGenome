import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ClosedForm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.FriedrichsExtension

/-! The abstract Friedrichs assertion in `pde:elliptic-friedrichs`, together
with its independently quantified closed-form assertion. The original operator
domain carries its form norm only through `EnergySpace`; it need not be complete.
-/
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open UniformSpace
universe u v
namespace P201.Elliptic
open ExpandedFA.Unbounded

namespace FriedrichsData

/-- Reverse the library's test-first slots into the manuscript's slots. -/
def paperForm {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (q : ClosedNonnegativeForms.NonnegativeForm 𝕜 H) : DenseForm 𝕜 H where
  domain := q.domain
  dense := q.dense
  form := q.form.flip

/-- These data contain exactly the manuscript's three operator hypotheses.
The swapped symmetry identity implements the inner-product convention bridge. -/
theorem hypotheses {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (T : Operator 𝕜 H H) (m : ℝ)
    (hd : Dense (T.domain : Set H))
    (hs : ∀ x y : T.domain,
      paperInner (𝕜 := 𝕜) (T x) (y : H) = paperInner (𝕜 := 𝕜) (x : H) (T y))
    (hl : ∀ x : T.domain,
      m * ‖(x : H)‖ ^ 2 ≤ RCLike.re (paperInner (𝕜 := 𝕜) (T x) (x : H))) :
    FriedrichsExtension.SemiboundedSymmetric T m where
  dense := hd
  symmetric x y := (hs y x).symm
  lower := hl

end FriedrichsData

namespace FriedrichsExpected
open FriedrichsExtension FriedrichsData

/-- The closure and extension are conclusions, not assumed certificates.
`FormClosure` specifies an injective continuous embedding of the actual Hilbert
completion, closedness, and its full energy identity. The dense range below
uses the energy norm of the closed form, and hence records the original form
core. Equality to the shared canonical operator fixes the full shifted graph.
-/
def Extension : Prop :=
  ∀ {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : Operator 𝕜 H H) (m : ℝ)
    (hd : Dense (T.domain : Set H))
    (hs : ∀ x y : T.domain,
      paperInner (𝕜 := 𝕜) (T x) (y : H) = paperInner (𝕜 := 𝕜) (x : H) (T y))
    (hl : ∀ x : T.domain,
      m * ‖(x : H)‖ ^ 2 ≤ RCLike.re (paperInner (𝕜 := 𝕜) (T x) (x : H))),
    let h := hypotheses T m hd hs hl
    let q := operatorForm T m h
    (∀ x y : T.domain, q.form y x =
      paperInner (𝕜 := 𝕜) (T x) (y : H) -
        (m : 𝕜) * paperInner (𝕜 := 𝕜) (x : H) (y : H)) ∧
    (∀ x : q.EnergySpace, ‖x‖ ^ 2 =
      RCLike.re (paperInner (𝕜 := 𝕜)
        (realShift T (1 - m) (q.toDomain x)) (q.toDomain x : H))) ∧
    FormClosable q ∧
    ∃ F : FormClosure q,
      DenseRange (fun x : q.EnergySpace =>
        (show F.closedForm.EnergySpace from F.equivalence (x : Completion q.EnergySpace))) ∧
      (∀ x y : q.EnergySpace,
        F.closedForm.form (F.equivalence (y : Completion q.EnergySpace))
          (F.equivalence (x : Completion q.EnergySpace)) = q.form (q.toDomain y) (q.toDomain x)) ∧
      ∃ A : Operator 𝕜 H H,
        realShift A (-m) = (paperForm F.closedForm).associatedOperator ∧
        T ≤ A ∧ Dense (A.domain : Set H) ∧ A = A.adjoint ∧
        (∀ x : A.domain,
          m * ‖(x : H)‖ ^ 2 ≤ RCLike.re (paperInner (𝕜 := 𝕜) (A x) (x : H)))

/-- The two assertions quantify their original data independently. -/
def ClosedFormsAndFriedrichs : Prop :=
  ClosedFormExpected.ClosedForm.{u, v} ∧ Extension.{u, v}

end FriedrichsExpected
end P201.Elliptic
