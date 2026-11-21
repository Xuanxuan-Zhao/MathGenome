import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.DarbouxSums

/-!
Independent specification for K03.08.integral, paper.tex:1930–1940.
The ordinary interval is ordered (`a ≤ b`), including singleton intervals.
Bounds are real suprema/infima of all finite strict-partition sums. Integral
values require a proof of Darboux integrability; there is no default integral
of a nonintegrable function. Complex values are defined by their two real
components. `scalarIntegrableValue` / `scalarIntegralValue` provide one interface
for exactly the two scalar choices of the manuscript.
The step-function comparison at paper.tex:1941–1953 is allocated separately to
`d03_08_step_comparison`.
-/
namespace Specs.SingleVariableAnalysis.Ch08.Integral
open _root_.SingleVariableAnalysis _root_.SingleVariableAnalysis.Riemann
open DarbouxSums
open Specs.SingleVariableAnalysis.Ch01

abbrev boundType := (f : ℝ → ℝ) → {a b : ℝ} → a ≤ b →
  boundedOnIntervalValue f a b → ℝ

noncomputable def lowerIntegralValue : boundType := fun f {_ _} _ hf =>
  sSup (Set.range (fun P => lowerSumValue f P hf))

noncomputable def upperIntegralValue : boundType := fun f {_ _} _ hf =>
  sInf (Set.range (fun P => upperSumValue f P hf))

abbrev realIntegrableType := (ℝ → ℝ) → ℝ → ℝ → Prop

def realIntegrableValue : realIntegrableType := fun f a b =>
  ∃ (hab : a ≤ b) (hf : boundedOnIntervalValue f a b),
    lowerIntegralValue f hab hf = upperIntegralValue f hab hf

abbrev realIntegralType := (f : ℝ → ℝ) → {a b : ℝ} →
  realIntegrableValue f a b → ℝ

noncomputable def realIntegralValue : realIntegralType := fun f {_ _} h =>
  lowerIntegralValue f h.choose h.choose_spec.choose

abbrev complexIntegrableType := (ℝ → ℂ) → ℝ → ℝ → Prop

def complexIntegrableValue : complexIntegrableType := fun f a b =>
  realIntegrableValue (fun x => (f x).re) a b ∧
  realIntegrableValue (fun x => (f x).im) a b

abbrev complexIntegralType := (f : ℝ → ℂ) → {a b : ℝ} →
  complexIntegrableValue f a b → ℂ

noncomputable def complexIntegralValue : complexIntegralType := fun f {_ _} h =>
  (realIntegralValue (fun x => (f x).re) h.1 : ℂ) +
  (realIntegralValue (fun x => (f x).im) h.2 : ℂ) * Complex.I

abbrev scalarIntegrableType := (k : ScalarKind) →
  (ℝ → Scalar.scalarValue k) → ℝ → ℝ → Prop

def scalarIntegrableValue : scalarIntegrableType
  | .real => realIntegrableValue
  | .complex => complexIntegrableValue

abbrev scalarIntegralType := (k : ScalarKind) → (f : ℝ → Scalar.scalarValue k) →
  {a b : ℝ} → scalarIntegrableValue k f a b → Scalar.scalarValue k

noncomputable def scalarIntegralValue : scalarIntegralType
  | .real => realIntegralValue
  | .complex => complexIntegralValue

def partitionExists : Prop := ∀ {a b : ℝ}, a ≤ b → Nonempty (PartitionData a b)

/-- Nonempty, bounded families ensure the real bounds are finite mathematical
suprema/infima, rather than the library's defaults at empty/unbounded sets. -/
def sumRangesFinite : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (_hab : a ≤ b)
  (hf : boundedOnIntervalValue f a b),
  (Set.range (fun P => lowerSumValue f P hf)).Nonempty ∧
  (Set.range (fun P => upperSumValue f P hf)).Nonempty ∧
  BddAbove (Set.range (fun P => lowerSumValue f P hf)) ∧
  BddBelow (Set.range (fun P => upperSumValue f P hf))

def lowerIsLUB : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hf : boundedOnIntervalValue f a b),
  IsLUB (Set.range (fun P => lowerSumValue f P hf)) (lowerIntegralValue f hab hf)

def upperIsGLB : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hf : boundedOnIntervalValue f a b),
  IsGLB (Set.range (fun P => upperSumValue f P hf)) (upperIntegralValue f hab hf)

def lowerLeUpper : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
  (hf : boundedOnIntervalValue f a b),
  lowerIntegralValue f hab hf ≤ upperIntegralValue f hab hf

def realIntegralCommonValue : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}
  (h : realIntegrableValue f a b) (hab : a ≤ b) (hf : boundedOnIntervalValue f a b),
  realIntegralValue f h = lowerIntegralValue f hab hf ∧
  realIntegralValue f h = upperIntegralValue f hab hf

def realIntegralBounds : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}
  (h : realIntegrableValue f a b) (P : PartitionData a b),
  lowerSumValue f P h.choose_spec.choose ≤ realIntegralValue f h ∧
  realIntegralValue f h ≤ upperSumValue f P h.choose_spec.choose

def complexIntegralComponents : Prop := ∀ (f : ℝ → ℂ) {a b : ℝ}
  (h : complexIntegrableValue f a b),
  (complexIntegralValue f h).re = realIntegralValue (fun x => (f x).re) h.1 ∧
  (complexIntegralValue f h).im = realIntegralValue (fun x => (f x).im) h.2

def degenerateBounds : Prop := ∀ (f : ℝ → ℝ) (a : ℝ)
  (hf : boundedOnIntervalValue f a a),
  lowerIntegralValue f le_rfl hf = 0 ∧ upperIntegralValue f le_rfl hf = 0

def degenerateIntegrable : Prop := ∀ (k : ScalarKind)
  (f : ℝ → Scalar.scalarValue k) (a : ℝ), scalarIntegrableValue k f a a

def degenerateIntegral : Prop := ∀ (k : ScalarKind)
  (f : ℝ → Scalar.scalarValue k) (a : ℝ) (h : scalarIntegrableValue k f a a),
  scalarIntegralValue k f h = (match k with
    | .real => (0 : ℝ)
    | .complex => (0 : ℂ))

end Specs.SingleVariableAnalysis.Ch08.Integral
