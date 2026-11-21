import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LocalNullVariant
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LocalNullEndpointRepresentative

/-! The final local-null endpoint theorem, on precisely the full Carathéodory
space specified in paper.tex:5770–5789. Native L¹ is the shared ordinary a.e.
quotient; the source of the equivalence is the separate local-null quotient.
The formulas explicitly require product integrability and use no conjugation. -/
open Set MeasureTheory
open scoped ENNReal
universe u
namespace Specs.D11.Ch20.LocalNullEndpointSpecialization
open _root_.D11.Ch20.LocalNullVariant

/-- Local-null changes are invisible to every ordinary L¹ function, on any
positive measure space. -/
def local_null_pairing_invariant : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (ν : Measure X) (g h : BoundedMeasurable X 𝕜),
    LocallyNull ν {x | g.val x ≠ h.val x} →
    ∀ f : Lp 𝕜 1 ν,
      Integrable (fun x => f x * g.val x) ν ∧
      Integrable (fun x => f x * h.val x) ν ∧
      (∫ x, f x * g.val x ∂ν) = ∫ x, f x * h.val x ∂ν

/-- The local quotient embeds scalar-linearly and isometrically into the dual.
The norm here is exactly the literal local-essential-supremum infimum. -/
def local_pairing_isometry : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (ν : Measure X),
    ∃ J : LocalLInfinity 𝕜 ν →ₗᵢ[𝕜] (Lp 𝕜 1 ν →L[𝕜] 𝕜),
      (∀ (g : BoundedMeasurable X 𝕜) (f : Lp 𝕜 1 ν),
        Integrable (fun x => f x * g.val x) ν ∧
        J (ClassOf ν g) f = ∫ x, f x * g.val x ∂ν) ∧
      (∀ g : BoundedMeasurable X 𝕜, ‖J (ClassOf ν g)‖ = LocalNorm ν g)

/-- Surjectivity is asserted only in the exact Radon-derived Carathéodory
framework, with no sigma-finiteness assumption. The bundled equivalence gives
linearity, bijectivity, norm equality and uniqueness of the local-null class. -/
def endpoint_specialization : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure X (borel X)), RadonCaratheodoryLocalization.Radon μ →
    letI : MeasurableSpace X := RadonDisjointCompactLocalization.M μ
    ∃ J : LocalLInfinity 𝕜 (RadonDisjointCompactLocalization.m μ) ≃ₗᵢ[𝕜]
        (Lp 𝕜 1 (RadonDisjointCompactLocalization.m μ) →L[𝕜] 𝕜),
      (∀ (g : BoundedMeasurable X 𝕜)
          (f : Lp 𝕜 1 (RadonDisjointCompactLocalization.m μ)),
        Integrable (fun x => f x * g.val x) (RadonDisjointCompactLocalization.m μ) ∧
        J (ClassOf (RadonDisjointCompactLocalization.m μ) g) f =
          ∫ x, f x * g.val x ∂(RadonDisjointCompactLocalization.m μ)) ∧
      (∀ g : BoundedMeasurable X 𝕜,
        ‖J (ClassOf (RadonDisjointCompactLocalization.m μ) g)‖ =
          LocalNorm (RadonDisjointCompactLocalization.m μ) g)

end Specs.D11.Ch20.LocalNullEndpointSpecialization
