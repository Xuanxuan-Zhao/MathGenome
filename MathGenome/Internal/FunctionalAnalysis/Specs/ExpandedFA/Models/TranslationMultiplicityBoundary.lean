import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.FullTranslationModel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.CoordinateMultiplicationModel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityUniqueness

noncomputable section
open MeasureTheory Set

namespace ExpandedFA.Models.TranslationMultiplicityBoundary
open FullTranslationModel

/-- Both spectral regions occur with positive Lebesgue measure locally. -/
def LocallySplit (E : Set ℝ) : Prop :=
  MeasurableSet E ∧ ∀ a b : ℝ, a < b →
    0 < volume (E ∩ Ioo a b) ∧ 0 < volume (Eᶜ ∩ Ioo a b)

/-- The multiplicity over the ambient Lebesgue parameter, allowing zero fibers. -/
def scalarMultiplicity (E : Set ℝ) (r : ℝ) : ℕ∞ := by
  classical
  exact if r ∈ E then 1 else 0

/-- A scalar fiber is the scalar line on E and the zero space off E. -/
def scalarFiber (E : Set ℝ) (r : ℝ) : Submodule ℂ ℂ := by
  classical
  exact if r ∈ E then ⊤ else ⊥

/-- The direct integral of the scalar fibers, written in a fixed ambient
scalar L² space: the sections vanish on Eᶜ. -/
def scalarSections (E : Set ℝ) : Submodule ℂ (L2 ℂ) where
  carrier := {f | ∀ᵐ r ∂volume, r ∉ E → f r = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 volume] with r hr
    exact fun _ => hr
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with r hf hg hr
    intro he
    change (f + g : L2 ℂ) r = 0
    rw [hr]
    simp only [Pi.add_apply, hf he, hg he, add_zero]
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, Lp.coeFn_smul c f] with r hf hr
    intro he
    simp [hr, hf he]

/-- Finite control measure of the bounded spectral window [-1,1], on the
same complex spectral parameter as the separable multiplicity theorem. -/
def cutMeasure (E : Set ℝ) : Measure ℂ :=
  Measure.map (fun r : ℝ => (r : ℂ)) (volume.restrict (E ∩ Icc (-1) 1))

/-- Constant scalar multiplicity on a control measure's support. -/
def unitMultiplicity (μ : Measure ℂ) : VonNeumann.MultiplicityModel.Spec.Multiplicity μ where
  toFun := fun _ => 1
  measurable_toFun := measurable_const
  positive := Filter.Eventually.of_forall fun _ => zero_lt_one

namespace Spec
universe u

/-- Actual bounded-coordinate inequivalence of the scalar window model and
every positive-multiplicity model on the full window control measure. This uses spectral classification,
including its measure-class invariant, rather than topological support. -/
def BoundedMultiplicityObstruction (E : Set ℝ) : Prop :=
  ∃ (hE : VonNeumann.MultiplicityModel.Spec.BoundedCoordinate (cutMeasure E))
    (hR : VonNeumann.MultiplicityModel.Spec.BoundedCoordinate (cutMeasure univ)),
    ∀ n : VonNeumann.MultiplicityModel.Spec.Multiplicity (cutMeasure univ),
    ¬ VonNeumann.MultiplicityUniqueness.Spec.CoordinateEquivalent
      (cutMeasure E) (cutMeasure univ) (unitMultiplicity (cutMeasure E)) n hE hR

def BoundedClassificationObstruction : Prop :=
  ∀ E : Set ℝ, LocallySplit E → BoundedMultiplicityObstruction E

/-- An actual unitary to the direct integral, with its pointwise formula and
entire maximal coordinate graph, and the dimensions of its fibers. -/
def ScalarFiberRealization (E : Set ℝ) : Prop :=
    Measurable (scalarMultiplicity E) ∧
    (∀ r, (Module.finrank ℂ (scalarFiber E r) : ℕ∞) = scalarMultiplicity E r) ∧
    (∀ f : L2 ℂ, f ∈ scalarSections E ↔ ∀ᵐ r ∂volume, f r ∈ scalarFiber E r) ∧
    ∃ W : RestrictedL2 E ≃ₗᵢ[ℂ] scalarSections E,
      (∀ f, ((W f).val : ℝ → ℂ) =ᵐ[volume] E.indicator (fun r => f r)) ∧
      ∀ f g, RestrictedCoordinateGraph E f g ↔
        ((W g).val : ℝ → ℂ) =ᵐ[volume] fun r => (r : ℂ) * (W f).val r

def ScalarMultiplicityRealization : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → ScalarFiberRealization E

def LocallySplitExists : Prop := ∃ E : Set ℝ, LocallySplit E

def NonconstantScalarMultiplicity : Prop :=
  ∀ E : Set ℝ, LocallySplit E → ∀ c : ℕ∞,
    ¬ ∀ᵐ r ∂volume, scalarMultiplicity E r = c

/-- The concrete operator, its actual PVM and scalar measures, full support,
and failure of every nonzero full translation representation. -/
def SelfAdjointBoundary (E : Set ℝ) : Prop :=
  ∃ (P : SpectralMeasure.ProjectionValuedMeasure ℝ (RestrictedL2 E))
    (C : Unbounded.MeasurableSpectralCalculus.BoundedRealization P)
    (A : Unbounded.Operator ℂ (RestrictedL2 E) (RestrictedL2 E)),
    (∀ B : Set ℝ, MeasurableSet B → ∀ f : RestrictedL2 E,
      (P B f : ℝ → ℂ) =ᵐ[volume.restrict E] B.indicator (fun r => f r)) ∧
    (∀ m : ℝ → ℂ, SpectralMeasure.Spec.IsBoundedMeasurable m →
      ∀ f : RestrictedL2 E,
        (C.integral m f : ℝ → ℂ) =ᵐ[volume.restrict E] (fun r => m r * f r)) ∧
    Unbounded.MeasurableSpectralCalculus.measurableIntegral C
      (fun r : ℝ => (r : ℂ)) = A ∧
    Unbounded.SymmetryAndDeficienciesSpec.selfAdjointValue A ∧
    (∀ f g : RestrictedL2 E, (f, g) ∈ A.graph ↔ RestrictedCoordinateGraph E f g) ∧
    (∀ f : RestrictedL2 E, C.measure f ≪ (volume : Measure ℝ)) ∧
    (∀ a b : ℝ, a < b → P (Ioo a b) ≠ 0) ∧
    (∃ f : RestrictedL2 E,
      Measure.map (fun r : ℝ => (r : ℂ)) (C.measure f) = cutMeasure E) ∧
    ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
      [CompleteSpace M] [Nontrivial M], ¬ OperatorTranslationModel M A

/-- One witness carries all the conclusions, including its exact multiplicity
field, the bounded spectral-classification obstruction, and the operator. -/
def BoundaryCounterexample : Prop :=
  ∃ E : Set ℝ, LocallySplit E ∧ ScalarFiberRealization E ∧
    (∀ c : ℕ∞, ¬ ∀ᵐ r ∂volume, scalarMultiplicity E r = c) ∧
    BoundedMultiplicityObstruction E ∧ SelfAdjointBoundary.{u} E

end Spec
end ExpandedFA.Models.TranslationMultiplicityBoundary
