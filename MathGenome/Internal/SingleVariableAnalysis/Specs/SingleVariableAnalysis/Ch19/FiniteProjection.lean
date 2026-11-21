import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Representation

/-! K03.19.finite_projection (paper.tex:4706–4725). All values are proper
Darboux integrals on actual functions. Integrability witnesses are explicit;
the existence statements ensure that they add no regularity assumptions.
The complex formulation includes real functions by the proved real embedding.
No completeness or definiteness of an integral seminorm is assumed. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.FiniteProjection
open Ch08.Integral PeriodicSetup Representation
open scoped BigOperators

abbrev polynomialType := Finset ℤ → (ℤ → ℂ) → ℝ → ℂ
def polynomialValue : polynomialType := fun E d x => ∑ n ∈ E, d n * modeValue n x

abbrev projectionType := (f : ℝ → ℂ) → ComplexWeights f → Finset ℤ → ℝ → ℂ
def projectionValue : projectionType := fun f h E =>
  polynomialValue E (fun n => coefficientValue f n (h n))

abbrev normSquaredType := (f : ℝ → ℂ) →
  realIntegrableValue (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi → ℝ
def normSquaredValue : normSquaredType := fun f h =>
  (1 / (2 * Real.pi)) * realIntegralValue (fun x => ‖f x‖ ^ 2) h

def polynomialIntegrability : Prop := ∀ E d,
  complexIntegrableValue (polynomialValue E d) (-Real.pi) Real.pi

def squaredNormIntegrability : Prop := ∀ (f : ℝ → ℂ),
  complexIntegrableValue f (-Real.pi) Real.pi →
  realIntegrableValue (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi

def residualIntegrability : Prop := ∀ (f : ℝ → ℂ),
  complexIntegrableValue f (-Real.pi) Real.pi → ∀ E d,
  realIntegrableValue (fun x => ‖f x - polynomialValue E d x‖ ^ 2) (-Real.pi) Real.pi

/-- The finite Pythagorean identity; valid even without periodicity, since all
integrals and coefficients use the fixed reference period. -/
def projectionIdentity : Prop := ∀ (f : ℝ → ℂ)
  (_hf : complexIntegrableValue f (-Real.pi) Real.pi) (h : ComplexWeights f)
  (E : Finset ℤ) (d : ℤ → ℂ)
  (hd : realIntegrableValue (fun x => ‖f x - polynomialValue E d x‖ ^ 2)
    (-Real.pi) Real.pi)
  (hP : realIntegrableValue (fun x => ‖f x - projectionValue f h E x‖ ^ 2)
    (-Real.pi) Real.pi),
  normSquaredValue (fun x => f x - polynomialValue E d x) hd =
    normSquaredValue (fun x => f x - projectionValue f h E x) hP +
      ∑ n ∈ E, ‖coefficientValue f n (h n) - d n‖ ^ 2

def bestApproximation : Prop := ∀ (f : ℝ → ℂ)
  (_hf : complexIntegrableValue f (-Real.pi) Real.pi) (h : ComplexWeights f)
  (E : Finset ℤ) (d : ℤ → ℂ)
  (hd : realIntegrableValue (fun x => ‖f x - polynomialValue E d x‖ ^ 2)
    (-Real.pi) Real.pi)
  (hP : realIntegrableValue (fun x => ‖f x - projectionValue f h E x‖ ^ 2)
    (-Real.pi) Real.pi),
  normSquaredValue (fun x => f x - projectionValue f h E x) hP ≤
    normSquaredValue (fun x => f x - polynomialValue E d x) hd

def realEmbedding : Prop := ∀ (f : ℝ → ℝ), periodicRealValue f →
  periodicComplexValue (fun x => (f x : ℂ)) ∧
    ∀ x, ‖(f x : ℂ)‖ ^ 2 = |f x| ^ 2

def emptyProjection : Prop := ∀ (f : ℝ → ℂ) (h : ComplexWeights f),
  projectionValue f h ∅ = (fun _ => 0)

end Specs.SingleVariableAnalysis.Ch19.FiniteProjection
