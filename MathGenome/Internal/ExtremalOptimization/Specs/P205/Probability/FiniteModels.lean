import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic

/-! Finite weighted experiments, paper.tex 746–757 and 1291–1306.
The canonical objects live here so that all clients use the same weights,
events, expectation, and product. No strict positivity assumption is imposed.
A finite type equipped with measurable singletons has all subsets measurable;
in particular one may always choose `MeasurableSpace Ω := ⊤`. -/

open MeasureTheory
open scoped BigOperators Classical

namespace P205.Probability

structure FiniteModel (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : ∑ ω, weight ω = 1

namespace FiniteModel

variable {Ω : Type*} [Fintype Ω]

noncomputable def eventMass (M : FiniteModel Ω) (A : Set Ω) : ℝ :=
  ∑ ω, A.indicator M.weight ω

def positiveSupport (M : FiniteModel Ω) : Set Ω := {ω | 0 < M.weight ω}

noncomputable def expectation (M : FiniteModel Ω) (Z : Ω → ℝ) : ℝ :=
  ∑ ω, M.weight ω * Z ω

noncomputable def pmf (M : FiniteModel Ω) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (M.weight ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => M.weight_nonneg ω),
      M.weight_sum, ENNReal.ofReal_one])

noncomputable def measure [MeasurableSpace Ω] (M : FiniteModel Ω) : Measure Ω :=
  M.pmf.toMeasure

/-- The probability measure on the full powerset sigma-algebra. -/
noncomputable def discreteMeasure (M : FiniteModel Ω) : @Measure Ω ⊤ :=
  @measure Ω _ ⊤ M

noncomputable def pi {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (M : ∀ i, FiniteModel (X i)) : FiniteModel (∀ i, X i) where
  weight ω := ∏ i, (M i).weight (ω i)
  weight_nonneg ω := Finset.prod_nonneg (fun i _ => (M i).weight_nonneg (ω i))
  weight_sum := by
    classical
    rw [← Fintype.prod_sum]
    simp only [weight_sum, Finset.prod_const_one]

end FiniteModel

namespace FiniteModelsSpec

-- Each expected statement is a closed, universally quantified type.
-- These declarations specify propositions, and do not assume their proofs.

def fromWeightsType := ∀ {Ω : Type*} [Fintype Ω],
  (p : Ω → ℝ) → (∀ ω, 0 ≤ p ω) → (∑ ω, p ω = 1) → FiniteModel Ω

def fromWeightsValue : fromWeightsType := fun p hp hs => ⟨p, hp, hs⟩

noncomputable def productType := ∀ {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)], (∀ i, FiniteModel (X i)) → FiniteModel (∀ i, X i)

noncomputable def productValue : productType := FiniteModel.pi

def discreteRealization : Prop := ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω),
  (∀ A : Set Ω, @MeasurableSet Ω ⊤ A) ∧
  @IsProbabilityMeasure Ω ⊤ M.discreteMeasure ∧
  (∀ A : Set Ω, M.discreteMeasure A = ENNReal.ofReal (M.eventMass A)) ∧
  (∀ Z : Ω → ℝ, (∫ ω, Z ω ∂M.discreteMeasure) = M.expectation Z)

def supportNonempty : Prop := ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω),
  M.positiveSupport.Nonempty

def massFormula : Prop := ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω) (A : Set Ω),
  M.eventMass A = ∑ ω ∈ A.toFinset, M.weight ω

def massNonnegative : Prop := ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω) (A : Set Ω),
  0 ≤ M.eventMass A

def expectationIndicator : Prop := ∀ {Ω : Type*} [Fintype Ω] (M : FiniteModel Ω) (A : Set Ω),
  M.expectation (A.indicator (fun _ => (1 : ℝ))) = M.eventMass A

def expectationLinear : Prop := ∀ {Ω : Type*} [Fintype Ω]
    (M : FiniteModel Ω) (a b : ℝ) (Z W : Ω → ℝ),
  M.expectation (fun ω => a * Z ω + b * W ω) =
    a * M.expectation Z + b * M.expectation W

def expectationFiniteSum : Prop := ∀ {Ω : Type*} [Fintype Ω] {ι : Type*} (s : Finset ι)
    (M : FiniteModel Ω) (Z : ι → Ω → ℝ),
  M.expectation (fun ω => ∑ i ∈ s, Z i ω) = ∑ i ∈ s, M.expectation (Z i)

def allMeasurable : Prop := ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (A : Set Ω), MeasurableSet A

def probabilityMeasure : Prop := ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (M : FiniteModel Ω), IsProbabilityMeasure M.measure

def measureFormula : Prop := ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (M : FiniteModel Ω) (A : Set Ω),
  M.measure A = ENNReal.ofReal (M.eventMass A)

def realMeasureFormula : Prop := ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (M : FiniteModel Ω) (A : Set Ω),
  (M.measure A).toReal = M.eventMass A

def integralFormula : Prop := ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (M : FiniteModel Ω) (Z : Ω → ℝ),
  (∫ ω, Z ω ∂M.measure) = M.expectation Z

def integrableAll : Prop := ∀ {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (M : FiniteModel Ω) (Z : Ω → ℝ), Integrable Z M.measure

noncomputable def productWeights : Prop := ∀ {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (M : ∀ i, FiniteModel (X i)) (ω : ∀ i, X i),
  (FiniteModel.pi M).weight ω = ∏ i, (M i).weight (ω i)

def productMeasure : Prop := ∀ {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (M : ∀ i, FiniteModel (X i)),
  (FiniteModel.pi M).measure = Measure.pi (fun i => (M i).measure)

def independentCoordinates : Prop := ∀ {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (M : ∀ i, FiniteModel (X i)),
  ProbabilityTheory.iIndepFun (fun i (ω : ∀ i, X i) => ω i) (FiniteModel.pi M).measure

def coordinateMarginal : Prop := ∀ {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (M : ∀ i, FiniteModel (X i)) (i : ι),
  (FiniteModel.pi M).measure.map (fun ω => ω i) = (M i).measure

def coordinateEventMass : Prop := ∀ {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (M : ∀ i, FiniteModel (X i)) (i : ι) (A : Set (X i)),
  (FiniteModel.pi M).eventMass {ω | ω i ∈ A} = (M i).eventMass A

end FiniteModelsSpec
end P205.Probability
