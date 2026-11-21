import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuousPathModulus
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.Tightness

/-! The continuous-path tightness criterion, paper.tex §6.11.
The positive-radius quantified modulus condition expresses the right-hand limit
uniformly over the family, including the empty family. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityFoundations.Ch06.Specs

noncomputable section

local instance (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d)) := borel _
local instance (d : ℕ) : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

local instance (T : ℝ) (d : ℕ) : MeasurableSpace (Path T d) := borel _
local instance (T : ℝ) (d : ℕ) : BorelSpace (Path T d) := ⟨rfl⟩

def initialEval {T : ℝ} (hT : 0 < T) {d : ℕ} (x : Path T d) :
    EuclideanSpace ℝ (Fin d) := x ⟨0, le_rfl, hT.le⟩

noncomputable def initialLaw {T : ℝ} (hT : 0 < T) {d : ℕ}
    (μ : ProbabilityMeasure (Path T d)) : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
  _root_.Specs.ProbabilityFoundations.Ch06.WeakFramework.probabilityLawValue
    (μ : Measure (Path T d)) (initialEval hT) (continuous_eval_const _).measurable

/-- All positive tolerances, uniformly in the law. Monotonicity of the modulus
makes this equivalent to the right-hand limit of the extended nonnegative
supremum being zero. -/
def UniformModulus {T : ℝ} {d : ℕ} (A : Set (ProbabilityMeasure (Path T d))) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ A,
      (μ : Measure (Path T d)) {x | η < modulus x δ} < ENNReal.ofReal ε

/-- The literal right-hand limit of the supremum of bad-modulus probabilities.
The extended nonnegative supremum of an empty family is zero. -/
def ModulusLimit {T : ℝ} {d : ℕ} (A : Set (ProbabilityMeasure (Path T d))) : Prop :=
  ∀ η : ℝ, 0 < η → Tendsto
    (fun δ : ℝ => ⨆ μ ∈ A, (μ : Measure (Path T d)) {x | η < modulus x δ})
    (𝓝[>] (0 : ℝ)) (𝓝 0)

def UniformModulusIffLimit : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (d : ℕ) (A : Set (ProbabilityMeasure (Path T d))),
    UniformModulus A ↔ ModulusLimit A

def ContinuousPathTightnessQuantified : Prop :=
  ∀ (T : ℝ) (hT : 0 < T) (d : ℕ) (A : Set (ProbabilityMeasure (Path T d))),
    _root_.Specs.ProbabilityFoundations.Ch06.Tightness.uniformlyTightValue A ↔
      _root_.Specs.ProbabilityFoundations.Ch06.Tightness.uniformlyTightValue
        (initialLaw hT '' A) ∧ UniformModulus A

def ContinuousPathTightness : Prop :=
  ∀ (T : ℝ) (hT : 0 < T) (d : ℕ) (A : Set (ProbabilityMeasure (Path T d))),
    _root_.Specs.ProbabilityFoundations.Ch06.Tightness.uniformlyTightValue A ↔
      _root_.Specs.ProbabilityFoundations.Ch06.Tightness.uniformlyTightValue
        (initialLaw hT '' A) ∧ ModulusLimit A

end
end ProbabilityFoundations.Ch06.Specs
