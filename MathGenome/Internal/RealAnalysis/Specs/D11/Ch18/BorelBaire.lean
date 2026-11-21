import MathGenome.Internal.RealAnalysis.D11.Ch01.SetSystems
import MathGenome.Internal.RealAnalysis.D11.Ch19.CcCzero
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Independent specifications for paper.tex:5318–5322, `d11:18:borel-baire`.

Borel means generation by all opens. Baire means generation by inverse images
of Borel subsets of ℝ under the shared native Cc functions. All measurable-space
arguments are explicit: an unrelated ambient measurable space cannot enter the
definitions. These constructions and inclusion make sense on any topological
space, so the statements include every locally compact Hausdorff space without
any countability or nonemptiness assumption.
-/

namespace Specs.D11.Ch18.BorelBaire

open scoped MeasureTheory

universe u

def measurableSpaceType :=
  ∀ (X : Type u) [TopologicalSpace X], MeasurableSpace X

def borelSpaceValue : measurableSpaceType.{u} :=
  fun X _ => MeasurableSpace.generateFrom {s : Set X | IsOpen s}

def generatorFamilyType :=
  ∀ (X : Type u) [TopologicalSpace X], Set (Set X)

def baireGeneratorsValue : generatorFamilyType.{u} :=
  fun X _ => {s | ∃ f : D11.Ch19.Cc X ℝ, ∃ A : Set ℝ,
    MeasurableSet[borel ℝ] A ∧ (f : X → ℝ) ⁻¹' A = s}

def baireSpaceValue : measurableSpaceType.{u} :=
  fun X _ => MeasurableSpace.generateFrom (baireGeneratorsValue X)

def borelSpace_eq_generateFrom : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    borelSpaceValue X = MeasurableSpace.generateFrom {s : Set X | IsOpen s}

/-- Every continuous real function is Borel measurable, with both structures fixed. -/
def continuous_borel_measurable : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (f : X → ℝ), Continuous f →
    @Measurable X ℝ (borelSpaceValue X) (borel ℝ) f

/-- The generating Cc functions really are measurable for the Baire structure. -/
def cc_baire_measurable : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (f : D11.Ch19.Cc X ℝ),
    @Measurable X ℝ (baireSpaceValue X) (borel ℝ) f

/-- Minimality characterizes exactly the source's Cc-real-generated sigma-algebra. -/
def baireSpace_le_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (m : MeasurableSpace X),
    baireSpaceValue X ≤ m ↔
      ∀ f : D11.Ch19.Cc X ℝ, @Measurable X ℝ m (borel ℝ) f

def baireSpace_le_borelSpace : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], baireSpaceValue X ≤ borelSpaceValue X

def baire_measurableSet_borel : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (s : Set X),
    MeasurableSet[baireSpaceValue X] s → MeasurableSet[borelSpaceValue X] s

end Specs.D11.Ch18.BorelBaire
