import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace ProbabilityFoundations.Ch07

/-- Coordinate directions for a multi-index: coordinate j occurs α j times.
The sigma type has cardinality ∑ j, α j; `equivFin` fixes an enumeration. -/
noncomputable def multiIndexDirections {d : ℕ} (α : Fin d → ℕ) :
    Fin (Fintype.card (Σ j, Fin (α j))) → Euclidean d :=
  fun i => EuclideanSpace.basisFun (Fin d) ℝ ((Fintype.equivFin (Σ j, Fin (α j))).symm i).1

/-- The coordinate specialization of the total Fréchet derivative of order |α|.
For a C^m function these are its mixed coordinate partial derivatives. -/
noncomputable def multiIndexPartial {d : ℕ} (α : Fin d → ℕ)
    (f : Euclidean d → ℂ) (t : Euclidean d) : ℂ :=
  iteratedFDeriv ℝ (Fintype.card (Σ j, Fin (α j))) f t (multiIndexDirections α)

end ProbabilityFoundations.Ch07

namespace Specs.ProbabilityFoundations.Ch07.CharacteristicMoments
open _root_.ProbabilityFoundations.Ch07

universe u

def Smoothness : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d), Measurable X →
    ∀ (m : ℕ), 1 ≤ m → Integrable (fun ω => ‖X ω‖ ^ m) P →
    ContDiff ℝ m (charFun (P.map X))

def FrechetFormula : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d), Measurable X →
    ∀ (m : ℕ), 1 ≤ m → Integrable (fun ω => ‖X ω‖ ^ m) P →
    ∀ (n : ℕ), n ≤ m → ∀ (t : Euclidean d) (v : Fin n → Euclidean d),
      iteratedFDeriv ℝ n (charFun (P.map X)) t v =
        ∫ ω, (∏ k, Complex.I * (inner ℝ (v k) (X ω) : ℂ)) *
          Complex.exp (Complex.I * (inner ℝ t (X ω) : ℂ)) ∂P

def MultiIndexFormula : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d), Measurable X →
    ∀ (m : ℕ), 1 ≤ m → Integrable (fun ω => ‖X ω‖ ^ m) P →
    ∀ (α : Fin d → ℕ), (∑ j, α j) ≤ m →
      Continuous (multiIndexPartial α (charFun (P.map X))) ∧
      ∀ t, multiIndexPartial α (charFun (P.map X)) t =
        ∫ ω, (∏ j, (Complex.I * (X ω j : ℂ)) ^ (α j)) *
          Complex.exp (Complex.I * (inner ℝ t (X ω) : ℂ)) ∂P

/-- The limit is in all Euclidean directions, with complex-norm little-o.
Only the second absolute moment is needed. -/
def SecondOrder : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d), Measurable X →
    Integrable (fun ω => ‖X ω‖ ^ 2) P →
    (fun t => charFun (P.map X) t -
      (1 + Complex.I * (inner ℝ t (∫ ω, X ω ∂P) : ℂ) -
        (1 / 2 : ℂ) * ∫ ω, ((inner ℝ t (X ω) : ℂ) ^ 2) ∂P))
      =o[𝓝 (0 : Euclidean d)] (fun t => ‖t‖ ^ 2)

/-- The second-order conclusion under the original m-th moment hypothesis, m ≥ 2. -/
def SecondOrderOfMoment : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d), Measurable X →
    ∀ (m : ℕ), 2 ≤ m → Integrable (fun ω => ‖X ω‖ ^ m) P →
    (fun t => charFun (P.map X) t -
      (1 + Complex.I * (inner ℝ t (∫ ω, X ω ∂P) : ℂ) -
        (1 / 2 : ℂ) * ∫ ω, ((inner ℝ t (X ω) : ℂ) ^ 2) ∂P))
      =o[𝓝 (0 : Euclidean d)] (fun t => ‖t‖ ^ 2)

end Specs.ProbabilityFoundations.Ch07.CharacteristicMoments
