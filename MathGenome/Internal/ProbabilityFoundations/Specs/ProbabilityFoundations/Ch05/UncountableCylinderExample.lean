import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.CylinderFramework
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The two-point discrete space is represented by `Bool`, with `false` representing
0 and `true` representing 1. Its canonical topology is discrete and its canonical
measurable space is the full power set. The function space has the product topology;
its cylinder sigma-algebra is the shared finite-projection construction. -/
open scoped MeasureTheory

namespace ProbabilityFoundations.Ch05.UncountableCylinderExample

open CylinderFramework
universe u v

/-- Membership in `A` depends only on the coordinates in `J`. -/
def Determines {I : Type u} {S : I → Type v}
    (J : Set I) (A : Set (ProductSpace S)) : Prop :=
  ∀ x y, (∀ i ∈ J, x i = y i) → (x ∈ A ↔ y ∈ A)

/-- The all-zero point in the discrete two-point product. -/
def zeroPoint (I : Type u) : ProductSpace (fun _ : I => Bool) := fun _ => false

end ProbabilityFoundations.Ch05.UncountableCylinderExample

namespace Specs.ProbabilityFoundations.Ch05.UncountableCylinderExample

open _root_.ProbabilityFoundations.Ch05.CylinderFramework
open _root_.ProbabilityFoundations.Ch05.UncountableCylinderExample
universe u v

/-- Countable dependence holds in particular for the binary product in the example. -/
def CountableDependence : Prop :=
  ∀ {I : Type u} (S : I → Type v) [∀ i, MeasurableSpace (S i)]
    (A : Set (ProductSpace S)), MeasurableSet[cylinderSigma S] A →
      ∃ J : Set I, J.Countable ∧ Determines J A

/-- No countable coordinate set determines membership in the zero singleton. -/
def ZeroSingletonNotDetermined : Prop :=
  ∀ (I : Type u) [Uncountable I] (J : Set I), J.Countable →
    ¬ Determines J ({zeroPoint I} : Set (ProductSpace (fun _ : I => Bool)))

def ZeroSingletonClosed : Prop :=
  ∀ (I : Type u), IsClosed ({zeroPoint I} : Set (ProductSpace (fun _ : I => Bool)))

def ZeroSingletonNotMeasurable : Prop :=
  ∀ (I : Type u) [Uncountable I],
    ¬ MeasurableSet[cylinderSigma (fun _ : I => Bool)] {zeroPoint I}

def CylinderLtBorel : Prop :=
  ∀ (I : Type u) [Uncountable I],
    cylinderSigma (fun _ : I => Bool) < borel (ProductSpace (fun _ : I => Bool))

end Specs.ProbabilityFoundations.Ch05.UncountableCylinderExample
