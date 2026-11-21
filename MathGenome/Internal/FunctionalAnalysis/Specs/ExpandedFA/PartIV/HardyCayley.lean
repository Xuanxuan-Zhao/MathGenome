import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyDisk
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyHalfPlaneRepresentation

/-! Cayley correspondence in paper.tex, fa2:p4:hardy-halfplane,
lines 18903–18905 and 18927–18942. The disk uses normalized circle measure;
the half-plane uses unscaled Lebesgue measure. Ambient functions are identified
only on their analytic domains. No boundary value is assumed. -/
noncomputable section
open MeasureTheory Set
open scoped Real ENNReal
namespace ExpandedFA.PartIV.HardyCayleySpec
open HardyHalfPlaneRepresentationSpec

/-- Disk-to-half-plane coordinate. -/
def cayley (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)
/-- Half-plane-to-disk coordinate. -/
def uncayley (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)
/-- The normalization for circle Haar measure of mass one. -/
def normalization : ℂ := 2 * (Real.sqrt Real.pi : ℂ)
def transform (F : ℂ → ℂ) (w : ℂ) : ℂ := normalization * F (cayley w) / (1 - w)
def inverseTransform (g : HardyDiskSpec.H2) (z : ℂ) : ℂ :=
  (1 - uncayley z) * HardyDiskSpec.eval g (uncayley z) / normalization

/-- Both directions of membership, including uniqueness in the canonical
coefficient model. In particular, transformed analytic functions really belong
to disk H², not just to the ambient boundary L² space. -/
def Correspondence : Prop := ∀ F : ℂ → ℂ,
  IsH2 F ↔ ∃! g : HardyDiskSpec.H2,
    EqOn (HardyDiskSpec.eval g) (transform F) HardyDiskSpec.disk

/-- Every disk vector is attained by the explicit inverse formula. -/
def Onto : Prop := ∀ g : HardyDiskSpec.H2,
  IsH2 (inverseTransform g) ∧
    EqOn (transform (inverseTransform g)) (HardyDiskSpec.eval g) HardyDiskSpec.disk

/-- Norm preservation for the actual strong L² boundary values supplied by
the half-plane theorem. -/
def BoundaryNorm : Prop := ∀ (F : ℂ → ℂ) (g : HardyDiskSpec.H2),
  IsH2 F → EqOn (HardyDiskSpec.eval g) (transform F) HardyDiskSpec.disk →
    ∀ b : BoundaryL2, HasBoundary F b → ‖g‖ = ‖b‖

/-- The same norm is the supremum of genuine horizontal square integrals;
`IsLUB` avoids any convention for the supremum of an unbounded set. -/
def SliceNorm : Prop := ∀ (F : ℂ → ℂ) (g : HardyDiskSpec.H2),
  IsH2 F → EqOn (HardyDiskSpec.eval g) (transform F) HardyDiskSpec.disk →
    IsLUB {r : ℝ | ∃ y : ℝ, 0 < y ∧ r = ∫ x : ℝ, ‖slice F y x‖ ^ 2} (‖g‖ ^ 2)

/-- The function correspondence is complex linear, including zero vectors. -/
def LinearCorrespondence : Prop := ∀ (F G : ℂ → ℂ) (g h : HardyDiskSpec.H2),
  IsH2 F → IsH2 G →
    EqOn (HardyDiskSpec.eval g) (transform F) HardyDiskSpec.disk →
    EqOn (HardyDiskSpec.eval h) (transform G) HardyDiskSpec.disk →
    ∀ a b : ℂ, IsH2 (a • F + b • G) ∧
      EqOn (HardyDiskSpec.eval (a • g + b • h))
        (transform (a • F + b • G)) HardyDiskSpec.disk

/-- A bundled unitary realizing the same weighted analytic formula in the
accepted causal spectral model. The preceding norm conclusions identify this
model's norm with both the horizontal and boundary norms. -/
def Unitary : Prop := ∃ U : HardyDiskSpec.H2 ≃ₗᵢ[ℂ] Lp ℂ 2 positiveMeasure,
  ∀ (g : HardyDiskSpec.H2) (w : ℂ), w ∈ HardyDiskSpec.disk →
    HardyDiskSpec.eval g w = transform (laplace (U g)) w

def CayleyType := ℂ → ℂ
def CayleyValue : CayleyType := cayley
def UncayleyType := ℂ → ℂ
def UncayleyValue : UncayleyType := uncayley
def TransformType := (ℂ → ℂ) → ℂ → ℂ
def TransformValue : TransformType := transform
def InverseTransformType := HardyDiskSpec.H2 → ℂ → ℂ
def InverseTransformValue : InverseTransformType := inverseTransform
end ExpandedFA.PartIV.HardyCayleySpec
