import Mathlib.MeasureTheory.Integral.Bochner.L1

/-!
Independent specification of paper.tex:17017–17024 and the Lᵖ-space definitions
used at 17036–17040. Measures are arbitrary positive measures: no finiteness,
sigma-finiteness, completeness of the measure, or separability is imposed.

The definitions make sense for normed groups, hence in particular for every
real or complex Banach space in the paper. Completeness is not needed to
form the definitions. Scalar multiplication in simple integration is real
scalar multiplication, also for a complex Banach space.
-/

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.FunctionSpaces.BochnerDefinitionsSpec

def StrongMeasurableType :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E],
    Measure X → (X → E) → Prop

/-- The paper's convention is an *a.e.* pointwise norm limit. -/
def StrongMeasurableValue : StrongMeasurableType.{u,v} :=
  fun μ f => ∃ s : ℕ → SimpleFunc _ _,
    ∀ᵐ x ∂μ, Tendsto (fun n => ‖s n x - f x‖) atTop (𝓝 0)

def IntegrableSimpleType :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E],
    Measure X → SimpleFunc X E → Prop

/-- Nonzero level sets have finite measure; the zero level may be infinite. -/
def IntegrableSimpleValue : IntegrableSimpleType.{u,v} :=
  fun μ s => ∀ y, y ≠ 0 → μ (s ⁻¹' {y}) < ∞

def BochnerIntegrableType := StrongMeasurableType.{u,v}

/-- L¹ approximation by integrable finite-valued measurable simple functions.
The extended L¹ norm is used before finiteness has been established; unlike
`ENNReal.toReal`, it does not turn an infinite error into zero. -/
def BochnerIntegrableValue : BochnerIntegrableType.{u,v} :=
  fun μ f => ∃ s : ℕ → SimpleFunc _ _,
    (∀ n, IntegrableSimpleValue μ (s n)) ∧
      Tendsto (fun n => eLpNorm (f - ⇑(s n)) 1 μ) atTop (𝓝 0)

def SimpleIntegralType :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E], Measure X → SimpleFunc X E → E

/-- Canonical disjoint level-set partition; the zero-level term is zero.
On integrable simple functions all nonzero level sets have finite measure. -/
def SimpleIntegralValue : SimpleIntegralType.{u,v} :=
  fun μ s => ∑ y ∈ s.range, μ.real (s ⁻¹' {y}) • y

def BochnerLpType :=
  ∀ {X : Type u} (E : Type v) [MeasurableSpace X] [NormedAddCommGroup E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], Measure X → Type (max u v)

/-- `Lp` is the subtype with finite extended p-norm of `AEEqFun`, the
quotient of a.e. strongly measurable functions by a.e. equality. -/
abbrev BochnerLpValue : BochnerLpType.{u,v} := fun E _ _ p _ μ => Lp E p μ

def LpNormType :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X), BochnerLpValue E p μ → ℝ

/-- Usual p-norm, with the essential-supremum definition at p = ∞. -/
def LpNormValue : LpNormType.{u,v} :=
  fun p _ μ f => (eLpNorm f p μ).toReal

/-- Bridge checking that the canonical quotient uses the paper's definition. -/
def StrongMeasurableIdentification : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : X → E),
    StrongMeasurableValue μ f ↔ AEStronglyMeasurable f μ

def IntegrableSimpleIdentification : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (s : SimpleFunc X E),
    IntegrableSimpleValue μ s ↔ Integrable s μ

/-- The canonical simple integral obeys the stated rule for *any* finite
measurable disjoint partition, allowing repeated values and zero values. -/
def SimpleIntegralPartition : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (n : ℕ) (A : Fin n → Set X)
    (hA : ∀ j, MeasurableSet (A j))
    (_hfin : ∀ j, μ (A j) < ∞)
    (_hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (x : Fin n → E),
    SimpleIntegralValue μ
      (∑ j, SimpleFunc.piecewise (A j) (hA j) (SimpleFunc.const X (x j)) 0) =
        ∑ j, μ.real (A j) • x j

/-- Membership consists exactly of the source's strongly measurable functions
with finite p-norm. -/
def LpMembership : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X) (f : X → E),
    MemLp f p μ ↔ StrongMeasurableValue μ f ∧ eLpNorm f p μ < ∞

/-- Equality in the canonical quotient is precisely a.e. equality. -/
def LpEquality : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X)
    (f g : BochnerLpValue E p μ), f = g ↔ f =ᵐ[μ] g

/-- Explicit finite-p power-integral norm formula, including p = 1. -/
def LpNormFinite : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure X) (hp : p ≠ ∞)
    (f : BochnerLpValue E p μ),
    LpNormValue p μ f = ((∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)).toReal

/-- Explicit essential-supremum norm formula at the endpoint. -/
def LpNormInfinity : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : BochnerLpValue E ∞ μ),
    LpNormValue ∞ μ f = (essSup (fun x => ‖f x‖ₑ) μ).toReal

end ExpandedFA.FunctionSpaces.BochnerDefinitionsSpec
