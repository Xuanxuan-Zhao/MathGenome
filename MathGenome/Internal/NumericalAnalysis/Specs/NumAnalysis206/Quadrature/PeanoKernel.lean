import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Order.ProjIcc

/-! Independent statement of paper.tex, W55 and the finite weighted-point example.
The functional acts on the full Banach space of real continuous functions. -/
namespace NumAnalysis206.Quadrature.PeanoKernelSpec
open Set
open scoped BigOperators

abbrev IntervalSpace (a b : ℝ) := C(Icc a b, ℝ)

noncomputable def polynomialValue {a b : ℝ} (p : Polynomial ℝ) : IntervalSpace a b :=
  ⟨fun x => p.eval x, p.continuous.comp continuous_subtype_val⟩

def annihilatesValue {a b : ℝ} (E : IntervalSpace a b →L[ℝ] ℝ) (r : ℕ) : Prop :=
  ∀ p : Polynomial ℝ, p.degree < (r : WithBot ℕ) → E (polynomialValue p) = 0

noncomputable def sliceValue {a b : ℝ} (r : ℕ) (t : ℝ) : IntervalSpace a b :=
  ⟨fun x => max ((x : ℝ) - t) 0 ^ (r - 1) / ((r - 1).factorial : ℝ),
    (((continuous_subtype_val.sub continuous_const).max continuous_const).pow _).div_const _⟩

noncomputable def kernelValue {a b : ℝ} (E : IntervalSpace a b →L[ℝ] ℝ)
    (r : ℕ) (t : ℝ) : ℝ := E (sliceValue r t)

noncomputable def functionValue {a b : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (hD : NumAnalysis206.Approximation.IntervalCalculusSpec.jetValue a b r f D) :
    IntervalSpace a b :=
  ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp
    ((hD.2.1 0 (Nat.zero_le _)).congr hD.1.symm)⟩

noncomputable def derivativeValue {a b : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (hD : NumAnalysis206.Approximation.IntervalCalculusSpec.jetValue a b r f D) :
    IntervalSpace a b :=
  ⟨fun x => D r x, continuousOn_iff_continuous_domRestrict.mp (hD.2.1 r le_rfl)⟩

def polynomialType := ∀ {a b : ℝ}, Polynomial ℝ → IntervalSpace a b
def annihilatesType := ∀ {a b : ℝ}, (IntervalSpace a b →L[ℝ] ℝ) → ℕ → Prop
def sliceType := ∀ {a b : ℝ}, ℕ → ℝ → IntervalSpace a b
def kernelType := ∀ {a b : ℝ}, (IntervalSpace a b →L[ℝ] ℝ) → ℕ → ℝ → ℝ

def continuous_type : Prop :=
  ∀ {a b : ℝ} (E : IntervalSpace a b →L[ℝ] ℝ) (r : ℕ), Continuous (kernelValue E r)

def representation_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (E : IntervalSpace a b →L[ℝ] ℝ), a < b → 2 ≤ r → annihilatesValue E r →
    ∀ hD : NumAnalysis206.Approximation.IntervalCalculusSpec.jetValue a b r f D,
      E (functionValue hD) = ∫ t in a..b, D r t * kernelValue E r t

def bound_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}
    (E : IntervalSpace a b →L[ℝ] ℝ), a < b → 2 ≤ r → annihilatesValue E r →
    ∀ hD : NumAnalysis206.Approximation.IntervalCalculusSpec.jetValue a b r f D,
      |E (functionValue hD)| ≤ ‖derivativeValue hD‖ * ∫ t in a..b, |kernelValue E r t|

def mass_type : Prop :=
  ∀ {a b : ℝ} {r : ℕ} (E : IntervalSpace a b →L[ℝ] ℝ),
    a < b → 2 ≤ r → annihilatesValue E r →
    ((∀ t ∈ Icc a b, 0 ≤ kernelValue E r t) ∨
      (∀ t ∈ Icc a b, kernelValue E r t ≤ 0)) →
    (∫ t in a..b, |kernelValue E r t|) =
      |E (polynomialValue ((Polynomial.C ((r.factorial : ℝ)⁻¹)) * Polynomial.X ^ r))|

/-- The projection gives an explicit extension, irrelevant to the interval integral. -/
noncomputable def quadratureValue {a b : ℝ} (hab : a ≤ b) {ι : Type*}
    (s : Finset ι) (nodes : ι → Icc a b) (weights : ι → ℝ)
    (F : IntervalSpace a b) : ℝ :=
  (∫ t in a..b, F (projIcc a b hab t)) - ∑ i ∈ s, weights i * F (nodes i)

def quadrature_type : Prop :=
  ∀ {a b : ℝ} (hab : a ≤ b) {ι : Type*} (s : Finset ι)
    (nodes : ι → Icc a b) (weights : ι → ℝ),
    ∃ E : IntervalSpace a b →L[ℝ] ℝ,
      (∀ F, E F = quadratureValue hab s nodes weights F) ∧
      ‖E‖ ≤ (b - a) + ∑ i ∈ s, |weights i|

end NumAnalysis206.Quadrature.PeanoKernelSpec
