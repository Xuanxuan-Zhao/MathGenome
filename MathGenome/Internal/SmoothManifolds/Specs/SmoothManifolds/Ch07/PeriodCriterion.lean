import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.PathIntegration
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.SpheresAndTori
import Mathlib.Topology.LocallyConstant.Basic

/-! Independent statements for M07.05, paper.tex 1574–1596.
The integral and smoothness conventions are exactly the upstream ones. There is
no connectedness, closedness, positive dimension, or nonemptiness hypothesis.
The circle form is written using the differentials of the restrictions of the
two ambient coordinates. By the upstream pullback-differential identity this is
the restriction of x dy - y dx by the unit-circle inclusion.
-/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.PeriodData
open ModelData AtlasData PartitionData CovectorData PathIntegrationData
  TangentData BundleOperationsData SphereTorusData
universe u

variable {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]

def Exact (S : SmoothManifold n k M) (α : CovectorField S) : Prop :=
  ∃ (f : M → ℝ) (hf : ScalarSmooth S.smoothStructure.val f), dFunction S f hf = α

def ZeroPeriods (S : SmoothManifold n k M) (α : CovectorField S) : Prop :=
  ∀ (γ : ℝ → M) (a b : ℝ), PiecewiseSmoothOn S γ a b → γ a = γ b →
    pathIntegral S α γ a b = 0

/-- Both parameter intervals are arbitrary, and may be degenerate. -/
def PathIndependent (S : SmoothManifold n k M) (α : CovectorField S) : Prop :=
  ∀ (γ η : ℝ → M) (a b c d : ℝ),
    PiecewiseSmoothOn S γ a b → PiecewiseSmoothOn S η c d →
    γ a = η c → γ b = η d → pathIntegral S α γ a b = pathIntegral S α η c d

def circleX (p : Sphere 1) : ℝ := p.val 0
def circleY (p : Sphere 1) : ℝ := p.val 1

/-- One positive turn, with the source's radian parameter on [0,2π]. -/
def circleLoop (t : ℝ) : Sphere 1 :=
  ⟨![Real.cos t, Real.sin t], by
    simpa [squareSum, Fin.sum_univ_two] using Real.cos_sq_add_sin_sq t⟩

def circleForm (S : SmoothManifold 1 .euclidean (Sphere 1))
    (hx : ScalarSmooth S.smoothStructure.val circleX)
    (hy : ScalarSmooth S.smoothStructure.val circleY) : CovectorField S :=
  fun p => circleX p • dFunction S circleY hy p - circleY p • dFunction S circleX hx p

/-- The canonical degree-one exterior field of a covector field. -/
def oneField (S : SmoothManifold n k M) (α : CovectorField S) : ExteriorData.Field S 1 :=
  fun p => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm (α p)

end SmoothManifolds.PeriodData

namespace Specs.SmoothManifolds.Ch07.PeriodCriterion
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.PartitionData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.PathIntegrationData _root_.SmoothManifolds.PeriodData
  _root_.SmoothManifolds.SphereTorusData _root_.SmoothManifolds.ExteriorDerivativeData
  Set
universe u

def exact_zero_periodsType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C),
    Exact S α.field → ZeroPeriods S α.field

def zero_periods_exactType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C),
    ZeroPeriods S α.field → Exact S α.field

def zero_periods_iff_path_independentType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (C : CotangentBundle S) (α : OneForm C),
    ZeroPeriods S α.field ↔ PathIndependent S α.field

/-- Equality of differentials is precisely the ambiguity of a primitive.
The reverse implication also permits every independently chosen component constant. -/
def primitive_differenceType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (f g : M → ℝ)
    (hf : ScalarSmooth S.smoothStructure.val f) (hg : ScalarSmooth S.smoothStructure.val g),
    dFunction S f hf = dFunction S g hg ↔ IsLocallyConstant (fun p => f p - g p)

/-- Locally constant functions are smooth and are exactly arbitrary constants on
the actual nonempty connected components. No basepoint is selected on an empty base. -/
def locally_constant_componentsType : Prop :=
  ∀ {n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n k M) (f : M → ℝ),
    IsLocallyConstant f ↔
      ScalarSmooth S.smoothStructure.val f ∧
        ∀ p q, q ∈ connectedComponent p → f q = f p

/-- The substantive circle example includes actual smoothness, a closed path,
the numerical period, closedness as a degree-one exterior field, and nonexactness.
The only atlas hypothesis identifies the already constructed standard sphere. -/
def circle_exampleType : Prop :=
  ∀ (S : SmoothManifold 1 .euclidean (Sphere 1)),
    S.smoothStructure.val = AtlasData.maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 1) →
    ∀ C : CotangentBundle S,
    ∃ (hx : ScalarSmooth S.smoothStructure.val circleX)
      (hy : ScalarSmooth S.smoothStructure.val circleY),
      IsOneForm C (circleForm S hx hy) ∧
      HasExteriorDerivative C (oneField S (circleForm S hx hy)) 0 ∧
      PiecewiseSmoothOn S circleLoop 0 (2 * Real.pi) ∧
      circleLoop 0 = circleLoop (2 * Real.pi) ∧
      pathIntegral S (circleForm S hx hy) circleLoop 0 (2 * Real.pi) = 2 * Real.pi ∧
      ¬ Exact S (circleForm S hx hy)

end Specs.SmoothManifolds.Ch07.PeriodCriterion
