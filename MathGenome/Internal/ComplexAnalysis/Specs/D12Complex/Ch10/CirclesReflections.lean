import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.TriplesCrossRatio
import Mathlib.Analysis.Complex.Norm

/-! Generalized circles and their reflections, paper.tex:2344–2351.
The discriminant is strictly positive: points and empty loci are excluded.
Infinity belongs to the equation exactly when its quadratic coefficient is zero. -/
noncomputable section
namespace D12Complex.CirclesReflections
open Mobius

def sphereConj (p : RiemannSphere) : RiemannSphere :=
  OnePoint.elim p sphereInfty (fun z => sphereFinite (star z))

def extendedRealLine : Set RiemannSphere :=
  {p | OnePoint.elim p True (fun z => z.im = 0)}

def circleEquation (α : ℝ) (β : ℂ) (γ : ℝ) : Set RiemannSphere :=
  {p | OnePoint.elim p (α = 0)
    (fun z => α * Complex.normSq z + 2 * (β * z).re + γ = 0)}

def IsGeneralizedCircle (C : Set RiemannSphere) : Prop :=
  ∃ (α : ℝ) (β : ℂ) (γ : ℝ),
    0 < Complex.normSq β - α * γ ∧ C = circleEquation α β γ

def euclideanCircle (c : ℂ) (r : ℝ) : Set RiemannSphere :=
  sphereFinite '' {z | ‖z - c‖ = r}

def extendedLine (c v : ℂ) : Set RiemannSphere :=
  {sphereInfty} ∪ sphereFinite '' {z | ∃ t : ℝ, z = c + t * v}

/-- Coefficients are real after multiplication by a single nonzero complex scalar. -/
def RealCoefficientsUpToScalar (M : Coefficients) : Prop :=
  ∃ k : ℂ, k ≠ 0 ∧ ∀ i j, (k * M i j).im = 0

def reflectionVia (M : Coefficients) : RiemannSphere → RiemannSphere :=
  mobiusMap (inverseCoefficients M) ∘ sphereConj ∘ mobiusMap M

end D12Complex.CirclesReflections
namespace Specs.D12Complex.Ch10.CirclesReflections
open _root_.D12Complex _root_.D12Complex.Mobius _root_.D12Complex.CirclesReflections

def sphereConj_type := RiemannSphere → RiemannSphere
def sphereConj_value : sphereConj_type :=
  fun p => OnePoint.elim p sphereInfty (fun z => sphereFinite (star z))
def extendedRealLine_type := Set RiemannSphere
def extendedRealLine_value : extendedRealLine_type :=
  {p | OnePoint.elim p True (fun z => z.im = 0)}
def circleEquation_type := ℝ → ℂ → ℝ → Set RiemannSphere
def circleEquation_value : circleEquation_type := fun α β γ =>
  {p | OnePoint.elim p (α = 0)
    (fun z => α * Complex.normSq z + 2 * (β * z).re + γ = 0)}
def IsGeneralizedCircle_type := Set RiemannSphere → Prop
def IsGeneralizedCircle_value : IsGeneralizedCircle_type := fun C =>
  ∃ (α : ℝ) (β : ℂ) (γ : ℝ),
    0 < Complex.normSq β - α * γ ∧ C = circleEquation α β γ

def euclideanCircle_type := ℂ → ℝ → Set RiemannSphere
def euclideanCircle_value : euclideanCircle_type :=
  fun c r => sphereFinite '' {z | ‖z - c‖ = r}
def extendedLine_type := ℂ → ℂ → Set RiemannSphere
def extendedLine_value : extendedLine_type :=
  fun c v => {sphereInfty} ∪ sphereFinite '' {z | ∃ t : ℝ, z = c + t * v}
def RealCoefficientsUpToScalar_type := Coefficients → Prop
def RealCoefficientsUpToScalar_value : RealCoefficientsUpToScalar_type := fun M =>
  ∃ k : ℂ, k ≠ 0 ∧ ∀ i j, (k * M i j).im = 0
def reflectionVia_type := Coefficients → RiemannSphere → RiemannSphere
def reflectionVia_value : reflectionVia_type := fun M =>
  mobiusMap (inverseCoefficients M) ∘ sphereConj ∘ mobiusMap M

def generalizedCircle_iff_geometric_type : Prop :=
  ∀ C : Set RiemannSphere, IsGeneralizedCircle C ↔
    (∃ (c : ℂ) (r : ℝ), 0 < r ∧ C = euclideanCircle c r) ∨
    (∃ c v : ℂ, v ≠ 0 ∧ C = extendedLine c v)

def mobius_image_generalizedCircle_type : Prop :=
  ∀ (M : Coefficients) (C : Set RiemannSphere), Regular M →
    IsGeneralizedCircle C → IsGeneralizedCircle (mobiusMap M '' C)

def generalizedCircle_to_realLine_type : Prop :=
  ∀ C : Set RiemannSphere, IsGeneralizedCircle C →
    ∃ M : Coefficients, Regular M ∧ mobiusMap M '' C = extendedRealLine

def preserves_realLine_iff_realCoefficients_type : Prop :=
  ∀ M : Coefficients, Regular M →
    (mobiusMap M '' extendedRealLine = extendedRealLine ↔ RealCoefficientsUpToScalar M)

def reflection_independent_type : Prop :=
  ∀ (C : Set RiemannSphere) (M N : Coefficients), IsGeneralizedCircle C →
    Regular M → Regular N →
    mobiusMap M '' C = extendedRealLine → mobiusMap N '' C = extendedRealLine →
    reflectionVia M = reflectionVia N

end Specs.D12Complex.Ch10.CirclesReflections
