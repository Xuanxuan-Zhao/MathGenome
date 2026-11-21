import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
Canonical interfaces for paper.tex, W16 and the generator paragraph (lines 545–585).
Time is represented by a real variable. Values of `T` at negative times and of `C`
at nonpositive steps are arbitrary extensions; none of the definitions' limits or
semigroup laws imposes conditions on these values. All limits use h ↓ 0.
-/

open Filter Topology

noncomputable section

namespace NumAnalysis206.Evolution

universe u v

/-- A strongly continuous semigroup on the same real or complex Banach space
as the discrete operators. Continuity is strong, rather than operator-norm continuity. -/
structure StronglyContinuousSemigroup (𝕜 : Type u) [RCLike 𝕜]
    (X : Type v) [NormedAddCommGroup X] [NormedSpace 𝕜 X] where
  toFun : ℝ → X →L[𝕜] X
  map_zero : toFun 0 = 1
  map_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → toFun (s + t) = toFun s * toFun t
  strong_continuous : ∀ x : X, ContinuousOn (fun t => toFun t x) (Set.Ici 0)

instance {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] : CoeFun (StronglyContinuousSemigroup 𝕜 X)
      (fun _ => ℝ → X →L[𝕜] X) := ⟨StronglyContinuousSemigroup.toFun⟩

/-- The finite set of all mesh times in the horizon, including n = 0 when T₀ ≥ 0.
The filter makes the total extension to negative horizons harmless. -/
noncomputable def meshIndices (T₀ h : ℝ) : Finset ℕ :=
  (Finset.range (⌊T₀ / h⌋₊ + 1)).filter (fun n => (n : ℝ) * h ≤ T₀)

/-- Only steps whose *endpoint* is in the horizon enter the orbit defect. -/
noncomputable def orbitIndices (T₀ h : ℝ) : Finset ℕ :=
  (meshIndices T₀ h).filter (fun j => ((j : ℝ) + 1) * h ≤ T₀)

variable {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
  [NormedSpace 𝕜 X]

/-- A real finite bound, uniform over all sufficiently small positive steps and
all mesh powers on this fixed horizon. Thus constants may depend on the horizon. -/
def SmallStepStable (C : ℝ → X →L[𝕜] X) (T₀ : ℝ) : Prop :=
  ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ M : ℝ, 0 ≤ M ∧
    ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ n : ℕ, (n : ℝ) * h ≤ T₀ → ‖C h ^ n‖ ≤ M

/-- The pointwise norm of the one-step local defect divided by h. -/
def localDefect (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    (h : ℝ) (x : X) : ℝ := h⁻¹ * ‖(C h - T h) x‖

def PointwiseConsistent (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (x : X) : Prop :=
  Tendsto (fun h => localDefect C T h x) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Finite maximum of the orbit defects, with the empty maximum equal to zero.
The common positive factor 1/h is placed outside the maximum. `Finset.sup` on
nonnegative reals has bottom zero, so it implements exactly the empty convention. -/
noncomputable def orbitDefect (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (T₀ h : ℝ) (x : X) : ℝ :=
  h⁻¹ * (((orbitIndices T₀ h).sup (fun j => ‖(C h - T h) (T ((j : ℝ) * h) x)‖₊) : NNReal) : ℝ)

def UniformOrbitConsistent (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (T₀ : ℝ) (x : X) : Prop :=
  Tendsto (fun h => orbitDefect C T T₀ h x) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Maximum error over all mesh times, with n = 0 included. -/
noncomputable def meshError (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (T₀ h : ℝ) (x : X) : ℝ :=
  (((meshIndices T₀ h).sup (fun n => ‖(C h ^ n) x - T ((n : ℝ) * h) x‖₊) : NNReal) : ℝ)

def StronglyConvergent (C : ℝ → X →L[𝕜] X)
    (T : StronglyContinuousSemigroup 𝕜 X) (T₀ : ℝ) : Prop :=
  ∀ x : X, Tendsto (fun h => meshError C T T₀ h x) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- The real-time difference quotient, valid over both ℝ and ℂ. -/
def differenceQuotient (C : ℝ → X →L[𝕜] X) (h : ℝ) (x : X) : X :=
  (h⁻¹ : 𝕜) • ((C h - 1) x)

/-- A is the right derivative at time zero on the vector x. -/
def HasGeneratorValue (T : StronglyContinuousSemigroup 𝕜 X) (x A : X) : Prop :=
  Tendsto (fun h => differenceQuotient T.toFun h x) (𝓝[>] (0 : ℝ)) (𝓝 A)

def generatorDomain (T : StronglyContinuousSemigroup 𝕜 X) : Set X :=
  {x | ∃ A : X, HasGeneratorValue T x A}

/-- The generator is defined only on its domain, by its (unique) right derivative. -/
noncomputable def generator (T : StronglyContinuousSemigroup 𝕜 X)
    (x : generatorDomain T) : X := Classical.choose x.property

end NumAnalysis206.Evolution

namespace Specs.NumAnalysis206.Evolution

open _root_.NumAnalysis206.Evolution

universe u v

/-- Closed type of the public stability definition, for value-level comparison. -/
def smallStepStabilityType :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X], (ℝ → X →L[𝕜] X) → ℝ → Prop

/-- The expected value is the canonical quantified small-step stability predicate. -/
def smallStepStabilityValue : smallStepStabilityType := @SmallStepStable

/-- Full pointwise generator bridge; no orbit consistency is in its conclusion. -/
def generatorConsistencyEquivalence : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    (C : ℝ → X →L[𝕜] X) (T : StronglyContinuousSemigroup 𝕜 X)
    (x : generatorDomain T),
    PointwiseConsistent C T x ↔
      Tendsto (fun h => differenceQuotient C h x) (𝓝[>] (0 : ℝ)) (𝓝 (generator T x))

end Specs.NumAnalysis206.Evolution
