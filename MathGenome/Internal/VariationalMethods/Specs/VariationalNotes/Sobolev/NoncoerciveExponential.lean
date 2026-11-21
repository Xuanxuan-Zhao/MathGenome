import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The second example in paper.tex:3985–3989. The admissible space is the
accepted closure-defined scalar H¹₀ on the open unit interval, with its full
Euclidean H¹ norm. The real coordinate is an isometric coordinate on Domain 1.
No boundary condition is replaced by a one-endpoint normalization. -/
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace VariationalNotes.Sobolev.NoncoerciveExponential

def unitInterval : Opens (Domain 1) :=
  ⟨{x | x 0 ∈ Ioo (0 : ℝ) 1}, isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 0)⟩

abbrev Admissible := H1Zero unitInterval 1

def linePoint (t : ℝ) : Domain 1 := WithLp.toLp 2 (fun _ => t)

/-- A measurable scalar representative of the underlying L² equivalence class.
The integral below is independent of changes on null sets. -/
def scalarField (u : Admissible) (t : ℝ) : ℝ :=
  coordinateLp unitInterval Exponent.two 0
    (value unitInterval 1 Exponent.two u.val) (linePoint t)

def functional (u : Admissible) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, Real.exp (-scalarField u t)

def profile (n : ℕ) (t : ℝ) : ℝ := (n : ℝ) * t * (1 - t)

namespace Expected

def Finite : Prop := ∀ u : Admissible,
  IntegrableOn (fun t => Real.exp (-scalarField u t)) (Ioo (0 : ℝ) 1)

def Continuity : Prop := Continuous functional

def Convexity : Prop := ConvexOn ℝ Set.univ functional

def Positive : Prop := ∀ u : Admissible, 0 < functional u

def Infimum : Prop := IsGLB (Set.range functional) 0

def NoMinimizer : Prop := ¬ ∃ u : Admissible, ∀ v : Admissible, functional u ≤ functional v

/-- The source's explicit sequence, with divergence of the full H¹ norms.
Divergence implies unboundedness, so this also witnesses the failure of norm
bounds for minimizing sequences. -/
def MinimizingSequence : Prop := ∃ w : ℕ → Admissible,
  (∀ n, scalarField (w n) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] profile n) ∧
  Tendsto (fun n => functional (w n)) atTop (𝓝 0) ∧
  Tendsto (fun n => ‖w n‖) atTop atTop

end Expected
end VariationalNotes.Sobolev.NoncoerciveExponential
