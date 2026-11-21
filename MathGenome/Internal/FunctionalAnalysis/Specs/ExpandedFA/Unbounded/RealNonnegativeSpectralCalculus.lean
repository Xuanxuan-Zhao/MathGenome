import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Real Hilbert spectral calculus used by `fa2:p3:kooper-wave` and
`fa2:p3:homogeneous-wave-group`, with the scalar convention of paper.tex 67–73.
The spectral base ℝ≥0 includes zero. No gap, injectivity, nonzero-space or
separability assumption occurs. Operators are the shared domain-carrying maps.

`Calculus` describes the result to be constructed, not an input certificate.
`SpectralExistence` quantifies over every densely defined nonnegative real
self-adjoint operator. The final theorem asserts existence of this data and all
wave laws; it does not assume a spectral representation of the input operator.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
universe u

/-- Borel real functions with a pointwise finite uniform bound. -/
def IsBoundedMeasurable (f : ℝ≥0 → ℝ) : Prop :=
  Measurable f ∧ ∃ M : ℝ, ∀ s, |f s| ≤ M

/-- Coordinate on the closed half-line. -/
def coordinate (s : ℝ≥0) : ℝ := s

/-- The nonnegative square-root coordinate. -/
def root (s : ℝ≥0) : ℝ := Real.sqrt s

def cosine (t : ℝ) (s : ℝ≥0) : ℝ := Real.cos (t * root s)
def sine (t : ℝ) (s : ℝ≥0) : ℝ := Real.sin (t * root s)

/-- The continuous zero-mode extension of sin(t√λ)/√λ. -/
def quotientSine (t : ℝ) (s : ℝ≥0) : ℝ :=
  if s = 0 then t else Real.sin (t * root s) / root s

/-- Exact square integrability, using a nonnegative, non-totalized integral. -/
def SquareIntegrable (μ : Measure ℝ≥0) (f : ℝ≥0 → ℝ) : Prop :=
  (∫⁻ s, ENNReal.ofReal (|f s| ^ 2) ∂μ) < ⊤

/-- Truncation including its boundary, as in the manuscript. -/
def truncation (f : ℝ≥0 → ℝ) (n : ℕ) : ℝ≥0 → ℝ :=
  {s | |f s| ≤ (n : ℝ)}.indicator f

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Real orthogonal-projection-valued Borel measure. Countable additivity is
strong (Hilbert norm), and only Borel values matter. -/
structure ProjectionValuedMeasure where
  toFun : Set ℝ≥0 → H →L[ℝ] H
  univ : toFun Set.univ = 1
  selfAdjoint : ∀ B, MeasurableSet B → IsSelfAdjoint (toFun B)
  inter : ∀ B D, MeasurableSet B → MeasurableSet D →
    toFun B * toFun D = toFun (B ∩ D)
  iUnion : ∀ (B : ℕ → Set ℝ≥0), (∀ n, MeasurableSet (B n)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) →
    ∀ x, HasSum (fun n => toFun (B n) x) (toFun (⋃ n, B n) x)

instance : CoeFun (ProjectionValuedMeasure H) (fun _ => Set ℝ≥0 → H →L[ℝ] H) :=
  ⟨ProjectionValuedMeasure.toFun⟩

variable {H}

/-- Full real calculus, including coefficient integrals. All these data and
laws are existential conclusions of `SpectralExistence`.
The signed coefficient integral is required to be integrable against total
variation; this prevents a vacuous identity from integral totalization.
The general product domain law includes its normally essential D(g) factor. -/
structure Calculus where
  E : ProjectionValuedMeasure H
  measure : H → Measure ℝ≥0
  coefficient : H → H → SignedMeasure ℝ≥0
  finite : ∀ x, IsFiniteMeasure (measure x)
  measure_apply : ∀ x B, MeasurableSet B →
    measure x B = ENNReal.ofReal (inner ℝ x (E B x))
  coefficient_apply : ∀ x y B, MeasurableSet B →
    coefficient x y B = inner ℝ x (E B y)
  bounded : (ℝ≥0 → ℝ) → H →L[ℝ] H
  integral : (ℝ≥0 → ℝ) → Operator ℝ H H
  bounded_one : bounded (fun _ => 1) = 1
  bounded_add : ∀ f g, IsBoundedMeasurable f → IsBoundedMeasurable g →
    bounded (f + g) = bounded f + bounded g
  bounded_smul : ∀ (a : ℝ) f, IsBoundedMeasurable f →
    bounded (a • f) = a • bounded f
  bounded_mul : ∀ f g, IsBoundedMeasurable f → IsBoundedMeasurable g →
    bounded (f * g) = bounded f * bounded g
  bounded_adjoint : ∀ f, IsBoundedMeasurable f →
    ContinuousLinearMap.adjoint (bounded f) = bounded f
  bounded_indicator : ∀ B, MeasurableSet B →
    bounded (B.indicator (fun _ => 1)) = E B
  bounded_bound : ∀ f M, IsBoundedMeasurable f → 0 ≤ M →
    (∀ s, |f s| ≤ M) → ‖bounded f‖ ≤ M
  bounded_agrees : ∀ f, IsBoundedMeasurable f →
    integral f = (bounded f).toLinearMap.toPMap ⊤
  strong_convergence : ∀ f (a : ℕ → ℝ≥0 → ℝ), IsBoundedMeasurable f →
    (∀ n, IsBoundedMeasurable (a n)) →
    (∃ M : ℝ, ∀ n s, |a n s| ≤ M) →
    (∀ x, ∀ᵐ s ∂measure x, Tendsto (fun n => a n s) atTop (𝓝 (f s))) →
    ∀ x, Tendsto (fun n => bounded (a n) x) atTop (𝓝 (bounded f x))
  domain : ∀ f, Measurable f → ∀ x,
    x ∈ (integral f).domain ↔ SquareIntegrable (measure x) f
  dense : ∀ f, Measurable f → Dense ((integral f).domain : Set H)
  closed : ∀ f, Measurable f → (integral f).IsClosed
  selfAdjoint : ∀ f, Measurable f → (integral f).adjoint = integral f
  truncation_limit : ∀ f, Measurable f → ∀ x : (integral f).domain,
    Tendsto (fun n => bounded (truncation f n) x) atTop (𝓝 (integral f x))
  norm_sq : ∀ f, Measurable f → ∀ x : (integral f).domain,
    ‖integral f x‖ ^ 2 = ∫ s, |f s| ^ 2 ∂measure x
  inner_integrable : ∀ f, Measurable f → ∀ x (y : (integral f).domain),
    (coefficient x y).Integrable f
  inner_integral : ∀ f, Measurable f → ∀ x (y : (integral f).domain),
    inner ℝ x (integral f y) =
      (coefficient x y).integral f (ContinuousLinearMap.mul ℝ ℝ)
  nonnegative : ∀ f, Measurable f → (∀ s, 0 ≤ f s) →
    ∀ x : (integral f).domain, 0 ≤ inner ℝ (x : H) (integral f x)
  product_domain : ∀ f g, Measurable f → Measurable g →
    (OperatorDomainsSpec.productValue (integral f) (integral g)).domain =
      (integral g).domain ⊓ (integral (f * g)).domain
  product_le : ∀ f g, Measurable f → Measurable g →
    OperatorDomainsSpec.productValue (integral f) (integral g) ≤ integral (f * g)
  /-- The elementary L² growth implication, convenient for exact root domains. -/
  domain_bound : ∀ f g, Measurable f → Measurable g →
    (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ s, |f s| ^ 2 ≤ a + b * |g s| ^ 2) →
    (integral g).domain ≤ (integral f).domain
  bounded_commutes : ∀ f g, Measurable f → IsBoundedMeasurable g →
    ∀ x : (integral f).domain,
      (bounded g x, bounded g (integral f x)) ∈ (integral f).graph

/-- No extra closedness premise: dense self-adjointness implies it. -/
def NonnegativeSelfAdjoint (L : Operator ℝ H H) : Prop :=
  Dense (L.domain : Set H) ∧ L.adjoint = L ∧
    ∀ x : L.domain, 0 ≤ inner ℝ (x : H) (L x)

def squareRoot (C : Calculus (H := H)) : Operator ℝ H H := C.integral root

def cosOperator (C : Calculus (H := H)) (t : ℝ) : H →L[ℝ] H := C.bounded (cosine t)
def sinOperator (C : Calculus (H := H)) (t : ℝ) : H →L[ℝ] H := C.bounded (sine t)
def quotientOperator (C : Calculus (H := H)) (t : ℝ) : H →L[ℝ] H :=
  C.bounded (quotientSine t)

/-- Exact root square and kernel, q(H) ⊂ D(√L), and commutation on D(√L).
Graph membership states both the domain assertion and the evaluation identity. -/
def WaveLaws (C : Calculus (H := H)) (L : Operator ℝ H H) : Prop :=
  OperatorDomainsSpec.productValue (squareRoot C) (squareRoot C) = L ∧
  (squareRoot C).ker = L.ker ∧
  (∀ x : (squareRoot C).domain, 0 ≤ inner ℝ (x : H) (squareRoot C x)) ∧
  (∀ t, ‖cosOperator C t‖ ≤ 1 ∧ ‖sinOperator C t‖ ≤ 1 ∧
    ‖quotientOperator C t‖ ≤ |t|) ∧
  (∀ t x, (quotientOperator C t x, sinOperator C t x) ∈ (squareRoot C).graph) ∧
  (∀ t (x : (squareRoot C).domain),
    (cosOperator C t x, cosOperator C t (squareRoot C x)) ∈ (squareRoot C).graph ∧
    (sinOperator C t x, sinOperator C t (squareRoot C x)) ∈ (squareRoot C).graph)

namespace Spec

def SpectralExistence : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (L : Operator ℝ H H), NonnegativeSelfAdjoint L →
    ∃ C : Calculus (H := H), C.integral coordinate = L

/-- The wave laws can be proved independently of the real existence construction. -/
def WaveConsequences : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Calculus (H := H)) (L : Operator ℝ H H),
    C.integral coordinate = L → WaveLaws C L

def FullTheorem : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (L : Operator ℝ H H), NonnegativeSelfAdjoint L →
    ∃ C : Calculus (H := H), C.integral coordinate = L ∧ WaveLaws C L

end Spec
end ExpandedFA.Unbounded.RealNonnegativeSpectralCalculus
