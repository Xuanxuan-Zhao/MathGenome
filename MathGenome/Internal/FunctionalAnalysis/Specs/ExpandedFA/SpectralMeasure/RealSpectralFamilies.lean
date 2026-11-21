import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealSelfAdjointSpectral
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.SpectralFamilies

/-! Real spectral families and ordinary tagged Stieltjes integration for the
adopted `fa2:p2:spectral-corollaries`. All resolving radii are allowed, and the
partition is exactly the existing scalar-independent finite tagged partition. -/
noncomputable section
open Set Filter MeasureTheory
open scoped InnerProductSpace Topology
namespace ExpandedFA.SpectralMeasure.RealSpectralFamilies
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev TaggedPartition := SpectralFamilies.Spec.TaggedPartition

def realFamily (E : RealProjectionValuedMeasure ℝ H) (t : ℝ) : H →L[ℝ] H := E (Iic t)

def realOperatorSum {m M : ℝ} (P : TaggedPartition m M)
    (E : RealProjectionValuedMeasure ℝ H) : H →L[ℝ] H :=
  P.lowerTag • realFamily E m + ∑ i : Fin P.n,
    P.tag i • (realFamily E (P.point i.succ) - realFamily E (P.point i.castSucc))

def realScalarSum {m M : ℝ} (P : TaggedPartition m M)
    (F : ℝ → ℝ) (lowerAtom : ℝ) : ℝ :=
  P.lowerTag * lowerAtom + ∑ i : Fin P.n,
    P.tag i * (F (P.point i.succ) - F (P.point i.castSucc))

/-- Ordinary epsilon/mesh definition, with a separately retained lower atom. -/
def HasRealStieltjesIntegral (m M : ℝ) (F : ℝ → ℝ) (lowerAtom value : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ P : TaggedPartition m M,
    P.mesh < δ → ‖realScalarSum P F lowerAtom - value‖ < ε

namespace Spec

def FamilyConclusion (E : RealProjectionValuedMeasure ℝ H) : Prop :=
  (∀ t, IsSelfAdjoint (realFamily E t) ∧ realFamily E t * realFamily E t = realFamily E t ∧
    IsClosed (LinearMap.range (realFamily E t).toLinearMap : Set H)) ∧
  (∀ s t, s ≤ t → LinearMap.range (realFamily E s).toLinearMap ≤
    LinearMap.range (realFamily E t).toLinearMap) ∧
  (∀ t x, Tendsto (fun r => realFamily E r x) (nhdsWithin t (Ici t))
    (𝓝 (realFamily E t x))) ∧
  (∀ x, Tendsto (fun t => realFamily E t x) atBot (𝓝 0)) ∧
  (∀ x, Tendsto (fun t => realFamily E t x) atTop (𝓝 x))

def StieltjesConclusion (A : H →L[ℝ] H) (E : RealProjectionValuedMeasure ℝ H)
    (C : RealBoundedRealization E) : Prop :=
  ∀ m M : ℝ, (spectrum ℝ A ⊆ Icc m M) →
    (∀ P : TaggedPartition m M, ‖realOperatorSum P E - A‖ ≤ P.mesh) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ P : TaggedPartition m M,
      P.mesh < δ → ‖realOperatorSum P E - A‖ < ε) ∧
    (∀ x y : H, HasRealStieltjesIntegral m M (fun t => ⟪x, realFamily E t y⟫_ℝ)
      ⟪x, E {m} y⟫_ℝ ⟪x, A y⟫_ℝ ∧
      Integrable (fun t : ℝ => t) (C.coefficient x y).variation ∧
      ⟪x, A y⟫_ℝ = (C.coefficient x y).integral (fun t : ℝ => t)
        (ContinuousLinearMap.lsmul ℝ ℝ)) ∧
    (m = M → A = m • (1 : H →L[ℝ] H)) ∧
    (∀ P : TaggedPartition m M, P.n = 0 → realOperatorSum P E = m • (1 : H →L[ℝ] H))

def FamilyProperties : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H), IsSelfAdjoint A →
    ∀ (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
      (R : ℝ) (hR : 0 ≤ R), RealSelfAdjointSpectral.Resolves A E C R hR → FamilyConclusion E

def StieltjesApproximation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H), IsSelfAdjoint A →
    ∀ (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E)
      (R : ℝ) (hR : 0 ≤ R), RealSelfAdjointSpectral.Resolves A E C R hR → StieltjesConclusion A E C

/-- Existence is a conclusion, obtained from the actual real spectral theorem. -/
def SpectralFamilyExists : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H), IsSelfAdjoint A →
    ∃ (E : RealProjectionValuedMeasure ℝ H) (C : RealBoundedRealization E),
      RealSelfAdjointSpectral.Resolves A E C ‖A‖ (norm_nonneg A) ∧
      FamilyConclusion E ∧ StieltjesConclusion A E C

/-- Both scalar versions, using the unchanged complex targets. -/
def RealOrComplexConclusion : Prop :=
  SpectralFamilyExists.{u} ∧ FamilyProperties.{u} ∧ StieltjesApproximation.{u} ∧
    SpectralFamilies.Spec.FamilyProperties.{u} ∧ SpectralFamilies.Spec.StieltjesApproximation.{u}

end Spec
end ExpandedFA.SpectralMeasure.RealSpectralFamilies
