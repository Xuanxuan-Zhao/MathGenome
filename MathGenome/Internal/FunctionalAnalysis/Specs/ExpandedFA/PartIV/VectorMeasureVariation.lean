import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerIntegral
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
Independent statements for paper.tex:20814–20827, 20910–20923 and 20930–20935.
`VectorMeasure` means countable additivity with convergence in the codomain's
norm topology. Values on nonmeasurable sets are canonically zero; all measure
identities below are asserted on the original sigma algebra. No reflexivity,
separability, sigma-finiteness or completeness of the measure is assumed.
Real normed spaces include the underlying real spaces of complex Banach spaces.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.PartIV.VectorMeasureVariationSpec
open ExpandedFA.FunctionSpaces.BochnerDefinitionsSpec
open ExpandedFA.FunctionSpaces.BochnerIntegralSpec

def VariationType :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E],
    VectorMeasure X E → Measure X

def VariationValue : VariationType.{u,v} := fun m => m.variation

/-- The exact supremum over finite measurable disjoint partitions of A.
The extended nonnegative norm retains infinite variation. `Finpartition`
excludes empty parts, which contribute zero and can always be removed. -/
def VariationPartition : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (m : VectorMeasure X E) (A : Set X) (hA : MeasurableSet A),
    VariationValue m A =
      ⨆ (P : Finpartition (⟨A, hA⟩ : Subtype MeasurableSet)),
        ∑ B ∈ P.parts, ‖m B.val‖ₑ

def VariationFinite : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (m : VectorMeasure X E), VariationValue m univ < ∞ →
      IsFiniteMeasure (VariationValue m)

/-- In fact variation is countably additive even when its total mass is infinite. -/
def VariationCountable : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (m : VectorMeasure X E) (A : ℕ → Set X),
    (∀ n, MeasurableSet (A n)) → Pairwise (fun i j => Disjoint (A i) (A j)) →
      VariationValue m (⋃ n, A n) = ∑' n, VariationValue m (A n)

/-- Vector absolute continuity is vanishing on every measurable null set. -/
def VariationAbsolutelyContinuous : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (m : VectorMeasure X E) (μ : Measure X),
    (∀ A, MeasurableSet A → μ A = 0 → m A = 0) → VariationValue m ≪ μ

def DensityMeasureType :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E], Measure X → (X → E) → VectorMeasure X E

/-- Totalized by zero for nonintegrable densities; the intended domain is L¹. -/
def DensityMeasureValue : DensityMeasureType.{u,v} := fun μ f => μ.withDensityᵥ f

def DensityMeasureApply : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E),
    BochnerIntegrableValue μ f → ∀ A, MeasurableSet A →
      DensityMeasureValue μ f A = IntegralValue (μ.restrict A) f

/-- The construction is norm-countably-additive, not merely weakly additive. -/
def DensityMeasureCountable : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E)
    (A : ℕ → Set X), BochnerIntegrableValue μ f →
    (∀ n, MeasurableSet (A n)) → Pairwise (fun i j => Disjoint (A i) (A j)) →
      HasSum (fun n => DensityMeasureValue μ f (A n))
        (DensityMeasureValue μ f (⋃ n, A n))

def DensityMeasureAbsolutelyContinuous : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E),
    BochnerIntegrableValue μ f →
      ∀ A, MeasurableSet A → μ A = 0 → DensityMeasureValue μ f A = 0

/-- Equality of positive measures gives the variation formula on every measurable A. -/
def DensityVariation : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E),
    BochnerIntegrableValue μ f →
      VariationValue (DensityMeasureValue μ f) = μ.withDensity (fun x => ‖f x‖ₑ)

/-- Both extended and real forms of the formula, without discarding infinity
before the finiteness of the variation has been proved. -/
def DensityVariationApply : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E),
    BochnerIntegrableValue μ f → ∀ A, MeasurableSet A →
      VariationValue (DensityMeasureValue μ f) A = ∫⁻ x in A, ‖f x‖ₑ ∂μ ∧
      (VariationValue (DensityMeasureValue μ f)).real A = ∫ x in A, ‖f x‖ ∂μ

def DensityVariationFinite : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E),
    BochnerIntegrableValue μ f → IsFiniteMeasure (VariationValue (DensityMeasureValue μ f))

def DensityUnique : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f g : X → E),
    BochnerIntegrableValue μ f → BochnerIntegrableValue μ g →
    (∀ A, MeasurableSet A → IntegralValue (μ.restrict A) f = IntegralValue (μ.restrict A) g) →
      f =ᵐ[μ] g

/-- Relative compactness in norm, with no reflexivity assumption on E. -/
def DensityCompactRange : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure X) (f : X → E),
    BochnerIntegrableValue μ f → IsCompact (closure (range (DensityMeasureValue μ f)))

end ExpandedFA.PartIV.VectorMeasureVariationSpec
