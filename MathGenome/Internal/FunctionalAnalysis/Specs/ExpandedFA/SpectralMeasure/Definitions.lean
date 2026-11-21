import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Order
import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
Independent interface for paper.tex 12374–12400 (`fa2:p2:pvm-definition`).
The space S has only a measurable structure; H is an arbitrary complex Hilbert
space, including the zero space. Inner products are conjugate linear first.
A PVM carries only the source's normalization, orthogonal projection,
intersection, and strong countable additivity axioms. In particular, scalar
measures and functional calculus are conclusions, not fields of a PVM.
Values on nonmeasurable sets are irrelevant and are not constrained.
-/
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Filter

namespace ExpandedFA.SpectralMeasure
universe u v

/-- A normalized orthogonal PVM, extended arbitrarily off measurable sets.
`HasSum` is convergence in the Hilbert norm, not convergence in operator norm. -/
structure ProjectionValuedMeasure (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  toFun : Set S → H →L[ℂ] H
  univ : toFun Set.univ = 1
  selfAdjoint : ∀ B, MeasurableSet B → IsSelfAdjoint (toFun B)
  inter : ∀ B C, MeasurableSet B → MeasurableSet C →
    (toFun B) * (toFun C) = toFun (B ∩ C)
  iUnion : ∀ (B : ℕ → Set S), (∀ n, MeasurableSet (B n)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) →
    ∀ x, HasSum (fun n => toFun (B n) x) (toFun (⋃ n, B n) x)

instance {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    CoeFun (ProjectionValuedMeasure S H) (fun _ => Set S → H →L[ℂ] H) := ⟨fun E => E.toFun⟩

namespace Spec

def PVMType := ∀ (S : Type u) (H : Type v) [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H], Type (max u v)
abbrev PVMValue : PVMType.{u, v} := fun S H _ _ _ _ => ProjectionValuedMeasure S H

variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def CoefficientType := ProjectionValuedMeasure S H → H → H → Set S → ℂ
def CoefficientValue : CoefficientType (S := S) (H := H) :=
  fun E x y B => ⟪x, E B y⟫_ℂ

/-- The printed definition with ordered partial sums converging in norm.
This is compared with unconditional `HasSum`, rather than silently assuming
unconditional convergence as an additional hypothesis. -/
def SourceAxioms (F : Set S → H →L[ℂ] H) : Prop :=
  F Set.univ = 1 ∧
  (∀ B, MeasurableSet B → IsSelfAdjoint (F B)) ∧
  (∀ B C, MeasurableSet B → MeasurableSet C → F B * F C = F (B ∩ C)) ∧
  (∀ (B : ℕ → Set S), (∀ n, MeasurableSet (B n)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) → ∀ x,
      Tendsto (fun N => ∑ n ∈ Finset.range N, F (B n) x) atTop (nhds (F (⋃ n, B n) x)))

def SourceRealization : Prop := ∀ F : Set S → H →L[ℂ] H,
  SourceAxioms F ↔ ∃ E : ProjectionValuedMeasure S H, E.toFun = F

def Empty : Prop := ∀ E : ProjectionValuedMeasure S H, E ∅ = 0

def ProjectionLaws : Prop := ∀ (E : ProjectionValuedMeasure S H) (B : Set S),
  MeasurableSet B → IsSelfAdjoint (E B) ∧ E B * E B = E B ∧
    ‖E B‖ ≤ 1 ∧ (∀ x, ‖E B x‖ ≤ ‖x‖)

def CoefficientProjection : Prop :=
  ∀ (E : ProjectionValuedMeasure S H) (B : Set S), MeasurableSet B →
    ∀ x y : H, CoefficientValue E x y B = ⟪E B x, E B y⟫_ℂ

def Orthogonality : Prop :=
  ∀ (E : ProjectionValuedMeasure S H) (B C : Set S),
    MeasurableSet B → MeasurableSet C → Disjoint B C →
      ∀ x y : H, ⟪E B x, E C y⟫_ℂ = 0

/-- The scalar complex measures and positive finite diagonal measures are
constructed from E, with precisely the original values on measurable sets. -/
def ScalarMeasures : Prop :=
  ∀ E : ProjectionValuedMeasure S H,
    ∃ (μ : H → H → ComplexMeasure S) (ν : H → Measure S),
      (∀ x y B, MeasurableSet B → μ x y B = CoefficientValue E x y B) ∧
      (∀ x, IsFiniteMeasure (ν x)) ∧
      (∀ x B, MeasurableSet B → ν x B = ENNReal.ofReal (‖E B x‖ ^ 2)) ∧
      (∀ x B, MeasurableSet B → μ x x B = ((ν x).real B : ℂ)) ∧
      (∀ x, ν x Set.univ = ENNReal.ofReal (‖x‖ ^ 2)) ∧
      (∀ x y, (μ x y).variation Set.univ ≤ ENNReal.ofReal (‖x‖ * ‖y‖))

/-- All bounded measurable functions, with a pointwise bound, not an a.e.
quotient with respect to an assumed scalar control measure. -/
def IsBoundedMeasurable (f : S → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ s, ‖f s‖ ≤ C

/-- The simple spectral integral uses every fibre, including the zero fibre.
Its coefficient on the zero fibre is zero; S may be empty. -/
def SimpleIntegralValue (E : ProjectionValuedMeasure S H) (f : SimpleFunc S ℂ) : H →L[ℂ] H :=
  ∑ c ∈ f.range, c • E (f ⁻¹' {c})

/-- Full remaining construction and identities. Uniform approximation is
stated for every sequence of measurable simple functions converging uniformly.
The algebra laws are stated on actual bounded measurable functions; no
separability, sigma-finiteness, or extra scalar control measure is assumed. -/
def FunctionalCalculus : Prop :=
  ∀ E : ProjectionValuedMeasure S H,
    ∃ (μ : H → H → ComplexMeasure S) (ν : H → Measure S)
      (Φ : (S → ℂ) → H →L[ℂ] H),
      (∀ x y B, MeasurableSet B → μ x y B = CoefficientValue E x y B) ∧
      (∀ x, IsFiniteMeasure (ν x)) ∧
      (∀ x B, MeasurableSet B → ν x B = ENNReal.ofReal (‖E B x‖ ^ 2)) ∧
      (∀ x B, MeasurableSet B → μ x x B = ((ν x).real B : ℂ)) ∧
      (∀ x, ν x Set.univ = ENNReal.ofReal (‖x‖ ^ 2)) ∧
      (∀ x y, (μ x y).variation Set.univ ≤ ENNReal.ofReal (‖x‖ * ‖y‖)) ∧
      (∀ f : SimpleFunc S ℂ, Φ f = SimpleIntegralValue E f) ∧
      (∀ f, IsBoundedMeasurable f →
        ∃ a : ℕ → SimpleFunc S ℂ, TendstoUniformly (fun n => a n) f atTop) ∧
      (∀ f, IsBoundedMeasurable f → ∀ a : ℕ → SimpleFunc S ℂ,
        TendstoUniformly (fun n => a n) f atTop →
          Tendsto (fun n => SimpleIntegralValue E (a n)) atTop (nhds (Φ f))) ∧
      Φ (fun _ => 1) = 1 ∧
      (∀ f g, IsBoundedMeasurable f → IsBoundedMeasurable g →
        Φ (f + g) = Φ f + Φ g) ∧
      (∀ (c : ℂ) f, IsBoundedMeasurable f → Φ (c • f) = c • Φ f) ∧
      (∀ f g, IsBoundedMeasurable f → IsBoundedMeasurable g →
        Φ (f * g) = Φ f * Φ g) ∧
      (∀ f, IsBoundedMeasurable f → Φ (star f) = star (Φ f)) ∧
      (∀ f C, IsBoundedMeasurable f → 0 ≤ C → (∀ s, ‖f s‖ ≤ C) → ‖Φ f‖ ≤ C) ∧
      (∀ f, IsBoundedMeasurable f → ∀ x y,
        ⟪x, Φ f y⟫_ℂ = (μ x y).integral f (ContinuousLinearMap.mul ℝ ℂ)) ∧
      (∀ f, IsBoundedMeasurable f → ∀ x,
        ‖Φ f x‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 ∂ν x)


/-! Closed interface types for binding checks. The mathematical predicates
above remain parameterized for convenient use within proofs. -/
def CoefficientInterfaceType :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    CoefficientType (S := S) (H := H)

def CoefficientInterfaceValue : CoefficientInterfaceType.{u, v} :=
  fun {_ _} _ _ _ _ => CoefficientValue

def SimpleIntegralInterfaceType :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ProjectionValuedMeasure S H → SimpleFunc S ℂ → H →L[ℂ] H

def SimpleIntegralInterfaceValue : SimpleIntegralInterfaceType.{u, v} :=
  fun {_ _} _ _ _ _ => SimpleIntegralValue

def EmptyInterface : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    Empty (S := S) (H := H)

def ProjectionLawsInterface : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ProjectionLaws (S := S) (H := H)

def CoefficientProjectionInterface : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    CoefficientProjection (S := S) (H := H)

def OrthogonalityInterface : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    Orthogonality (S := S) (H := H)

def ScalarMeasuresInterface : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    ScalarMeasures (S := S) (H := H)

def SourceRealizationInterface : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    SourceRealization (S := S) (H := H)

def FunctionalCalculusInterface : Prop :=
  ∀ {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    FunctionalCalculus (S := S) (H := H)

end Spec
end ExpandedFA.SpectralMeasure
