import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcStieltjesEquivalence
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.LebesgueDecompositionFiniteTarget
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Independent scope for paper.tex:4179–4215. All scalar measures below are
on the Borel sigma-algebra of ℝ. The two final statements impose no additional
finiteness assumption on real or complex measures. Series use the actual nonzero
atoms, and convergence is expressed independently of a choice of enumeration. -/
noncomputable section
open scoped Classical
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Specs.D11.Ch12.StieltjesThreeParts
open ScalarStieltjesCorrespondence
open Specs.D11.Ch14.ScalarInterfaces

variable {K : Type*} [RCLike K]

def atoms (ν : VectorMeasure ℝ K) : Set ℝ := {x | ν {x} ≠ 0}

def IsDiscrete (d : VectorMeasure ℝ K) : Prop :=
  ∃ D : Set ℝ, D.Countable ∧ d.variation Dᶜ = 0

def IsAtomless (s : VectorMeasure ℝ K) : Prop := ∀ x : ℝ, s {x} = 0

/-- The source classes and all three singularity relations. -/
def IsDecomposition (ν d a s : VectorMeasure ℝ K) : Prop :=
  IsFiniteMeasure d.variation ∧ IsFiniteMeasure a.variation ∧
  IsFiniteMeasure s.variation ∧ ν = d + a + s ∧
  IsDiscrete d ∧ a.variation ≪ volume ∧
  scalarPositiveSingular_value s volume ∧ IsAtomless s ∧
  scalarSingular_value d a ∧ scalarSingular_value d s ∧ scalarSingular_value a s

/-- Absolute summability, the Dirac series on every Borel set, and uniform convergence of the cumulative jump series. -/
def AtomicData (ν d : VectorMeasure ℝ K) : Prop :=
  (atoms ν).Countable ∧
  Summable (fun p : atoms ν => ‖ν {p.val}‖) ∧
  (∀ E : Set ℝ, MeasurableSet E →
    HasSum (fun p : atoms ν => VectorMeasure.dirac p.val (ν {p.val}) E) (d E)) ∧
  (∀ x, cumulative_value d x = ∑' p : atoms ν, if p.val ≤ x then ν {p.val} else 0) ∧
  TendstoUniformly
    (fun t : Finset (atoms ν) => fun x : ℝ =>
      ∑ p ∈ t, if p.val ≤ x then ν {p.val} else 0)
    (cumulative_value d) atTop


/-- Function conclusions refer to the canonical every-point cumulative values.
`HasDerivAt`, rather than just a zero totalized `deriv`, asserts existence. -/
def FunctionData (ν d a s : VectorMeasure ℝ K) : Prop :=
  NBV_value (cumulative_value d) ∧ NBV_value (cumulative_value a) ∧
  NBV_value (cumulative_value s) ∧
  (∀ x, cumulative_value ν x =
    cumulative_value d x + cumulative_value a x + cumulative_value s x) ∧
  absolutelyContinuousValue (cumulative_value a) ∧ Continuous (cumulative_value s) ∧
  (∀ᵐ x ∂volume, HasDerivAt (cumulative_value d) 0 x) ∧
  (∀ᵐ x ∂volume, HasDerivAt (cumulative_value s) 0 x)

def CompleteResult (ν : VectorMeasure ℝ K) : Prop :=
  ∃ d a s, IsDecomposition ν d a s ∧ AtomicData ν d ∧ FunctionData ν d a s ∧
    ∀ d' a' s', IsDecomposition ν d' a' s' → d' = d ∧ a' = a ∧ s' = s

def real_three_parts : Prop := ∀ ν : SignedMeasure ℝ, CompleteResult ν

def complex_three_parts : Prop := ∀ ν : ComplexMeasure ℝ, CompleteResult ν

/-- The NBV version uses the same shared Stieltjes measure and normalized values.
It retains the original function at every point. -/
def nbv_real_three_parts : Prop :=
  ∀ F : ℝ → ℝ, NBV_value F →
    CompleteResult (stieltjesMeasure_value F) ∧
    cumulative_value (stieltjesMeasure_value F) = F

def nbv_complex_three_parts : Prop :=
  ∀ F : ℝ → ℂ, NBV_value F →
    CompleteResult (stieltjesMeasure_value F) ∧
    cumulative_value (stieltjesMeasure_value F) = F

end Specs.D11.Ch12.StieltjesThreeParts
