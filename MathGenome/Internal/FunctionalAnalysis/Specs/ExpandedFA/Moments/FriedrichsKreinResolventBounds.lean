import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.KreinNonnegativeExtension
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Independent statement of paper.tex, fa2:p3:krein-resolvent-order.
An isometric linear inclusion of a complete Hilbert space has closed range.
Its adjoint is the orthogonal projection back to the original space.
The positive resolvent below uses (A+a I)⁻¹, rather than (z I-A)⁻¹. -/
noncomputable section
universe u v
namespace ExpandedFA.Moments.FriedrichsKreinResolventBounds
open ExpandedFA.Unbounded ExpandedFA.Unbounded.FriedrichsExtension
open ExpandedFA.Unbounded.ClosedNonnegativeForms
open ExpandedFA.Moments.KreinNonnegativeExtension

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An everywhere defined bounded inverse on precisely the operator domain,
including bounded self-adjointness and nonnegativity. -/
structure PositiveResolvent (A : Operator ℂ H H) (a : ℝ) where
  inverse : H →L[ℂ] H
  mem_domain : ∀ f, inverse f ∈ A.domain
  right_inverse : ∀ f, A ⟨inverse f, mem_domain f⟩ + (a : ℂ) • inverse f = f
  left_inverse : ∀ x : A.domain, inverse (A x + (a : ℂ) • (x : H)) = (x : H)
  selfAdjoint : ∀ f g, inner ℂ (inverse f) g = inner ℂ f (inverse g)
  nonnegative : ∀ f, 0 ≤ (inner ℂ f (inverse f)).re

/-- Quadratic-form order for bounded operators. -/
def FormLE (A B : H →L[ℂ] H) : Prop :=
  ∀ f, (inner ℂ f (A f)).re ≤ (inner ℂ f (B f)).re

/-- Compression to the isometrically included original Hilbert space. -/
def compression {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace H] [CompleteSpace G] (i : H →ₗᵢ[ℂ] G) (B : G →L[ℂ] G) : H →L[ℂ] H :=
  i.toContinuousLinearMap.adjoint ∘L B ∘L i.toContinuousLinearMap

/-- Extension includes the original domain as well as its action. -/
def ExtendsAlong {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (i : H →ₗᵢ[ℂ] G) (S : Operator ℂ H H) (T : Operator ℂ G G) : Prop :=
  ∀ y : S.domain, ∃ hy : i (y : H) ∈ T.domain,
    T ⟨i (y : H), hy⟩ = i (S y)

namespace Spec
/-- Both extremal extensions exist for S≥0, with no positive lower bound.
The bounds apply to every enlargement, inclusion, and nonnegative self-adjoint
extension, simultaneously for every a>0. F is the actual form closure and K
is the unshifted energy construction specified upstream. -/
def ResolventBounds : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H) (h : SemiboundedSymmetric S 0), S.IsClosed →
    ∃ F : FormClosure (operatorForm S 0 h), ∃ K : Construction S h,
    ∃ SF : Operator ℂ H H, F.closedForm.Associated SF ∧
      S ≤ SF ∧
      Dense (SF.domain : Set H) ∧
      SF = HilbertAdjointSpec.adjointValue SF ∧
      (∀ x : SF.domain,
        0 ≤ (inner ℂ (x : H) (SF x)).re) ∧
      ∀ a : ℝ, 0 < a →
        ∃ RF : PositiveResolvent SF a,
        ∃ RK : PositiveResolvent K.extension a,
        ∀ {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
          (i : H →ₗᵢ[ℂ] G) (T : Operator ℂ G G) (_hT : SemiboundedSymmetric T 0),
          T = HilbertAdjointSpec.adjointValue T → ExtendsAlong i S T →
          ∃ RT : PositiveResolvent T a,
            (∀ f g, inner ℂ (compression i RT.inverse f) g =
              inner ℂ f (compression i RT.inverse g)) ∧
            FormLE RF.inverse (compression i RT.inverse) ∧
            FormLE (compression i RT.inverse) RK.inverse
end Spec
end ExpandedFA.Moments.FriedrichsKreinResolventBounds
