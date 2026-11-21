import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ShiftSpaces
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Independent objects and statements for paper.tex, Lemma
`d13:19:bernoulli-measure`. The measurable structures are the native product
structures on the exact upstream symbolic spaces. For the countable index sets
ℕ and ℤ, `borel_compatibilityStatement` identifies these with their Borel
structures. No dynamical invariance or mixing is assumed. -/
namespace Specs.D13Unified.Ch19.BernoulliMeasure

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
open Specs.D13Unified.Ch17.ShiftSpaces
noncomputable section

/-- A fair binary coordinate: half the mass at each of the two symbols. -/
def fair : Measure Binary := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 0 + Measure.dirac 1)

/-- The product construction, also used for finite-coordinate marginals. -/
def bernoulliMeasure (I : Type) : Measure (I → Binary) :=
  Measure.infinitePi (fun _ : I => fair)

def bernoulliPlus : Measure OneSided := bernoulliMeasure ℕ
def bernoulliTwoSided : Measure TwoSided := bernoulliMeasure ℤ

def fairType := Measure Binary
def bernoulliMeasureType := (I : Type) → Measure (I → Binary)
def bernoulliPlusType := Measure OneSided
def bernoulliTwoSidedType := Measure TwoSided

/-- All finite coordinate assignments, including the empty assignment. -/
def HasFairCylinderMasses {I : Type} (μ : Measure (I → Binary)) : Prop :=
  ∀ (s : I → Binary) (F : Finset I),
    μ (cylinder s F) = (2 : ℝ≥0∞) ^ (-(F.card : ℤ))

def probabilityStatement : Prop :=
  ∀ I : Type, IsProbabilityMeasure (bernoulliMeasure I)

def cylinder_massStatement : Prop :=
  ∀ I : Type, HasFairCylinderMasses (bernoulliMeasure I)

def borel_compatibilityStatement : Prop :=
  ∀ (I : Type) [Countable I],
    (inferInstance : MeasurableSpace (I → Binary)) = borel (I → Binary)

def uniquenessStatement : Prop :=
  ∀ (I : Type) (μ : Measure (I → Binary)),
    IsProbabilityMeasure μ → HasFairCylinderMasses μ → μ = bernoulliMeasure I

def exists_uniquePlusStatement : Prop :=
  ∃! μ : Measure OneSided, IsProbabilityMeasure μ ∧ HasFairCylinderMasses μ

def exists_uniqueTwoSidedStatement : Prop :=
  ∃! μ : Measure TwoSided, IsProbabilityMeasure μ ∧ HasFairCylinderMasses μ

/-- Independence of the entire finite coordinate vectors entails independence
of all coordinate conditions, including finite unions of assignments. -/
def independent_blocksStatement : Prop :=
  ∀ (I : Type) (S T : Finset I), Disjoint S T →
    IndepFun (fun s : I → Binary => fun j : S => s j)
      (fun s : I → Binary => fun j : T => s j) (bernoulliMeasure I)

/-- Explicit event formulation of independence for arbitrary finite conditions. -/
def independent_eventsStatement : Prop :=
  ∀ (I : Type) (S T : Finset I), Disjoint S T →
    ∀ (A : Set (S → Binary)) (B : Set (T → Binary)),
      bernoulliMeasure I
          ((S.restrict ⁻¹' A) ∩ (T.restrict ⁻¹' B)) =
        bernoulliMeasure I (S.restrict ⁻¹' A) *
          bernoulliMeasure I (T.restrict ⁻¹' B)

end
end Specs.D13Unified.Ch19.BernoulliMeasure
