import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.CanonicalPathLaw
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Probability.Independence.InfinitePi

/-! Shared objects for paper.tex §4.3, and independent propositions for the
Fourier and parity assertions of Lemma `p207:lem:lattice-fourier`.
`[NeZero d]` expresses the source hypothesis `d ≥ 1`. The circle is literally
`ℝ / (2πℤ)`, and its Haar measure is normalized to mass one. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory BigOperators

namespace P207.Walk

abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Torus (d : ℕ) := Fin d → AddCircle (2 * Real.pi)
abbrev StepChoice (d : ℕ) := Fin d × Bool

noncomputable section

/-- A choice of axis and sign, with `true` meaning the positive direction. -/
def step {d : ℕ} (a : StepChoice d) : Lattice d :=
  if a.2 then Pi.single a.1 1 else -Pi.single a.1 1

/-- Uniform probability on the `2d` labelled directions. -/
def choiceLaw (d : ℕ) [NeZero d] : PMF (StepChoice d) :=
  PMF.ofFintype (fun _ => (Fintype.card (StepChoice d) : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp [Fintype.card_prod, NeZero.ne d]) (ENNReal.natCast_ne_top _))

/-- The actual nearest-neighbor increment law on `ℤ^d`. -/
def stepLaw (d : ℕ) [NeZero d] : PMF (Lattice d) :=
  (choiceLaw d).map step

/-- Translation of the same increment law at every state. -/
def latticeKernel (d : ℕ) [NeZero d] : Markov.StochasticMatrix (Lattice d) :=
  fun x => (stepLaw d).map (fun z => x + z)

/-- The product law of independent lattice-valued increments, indexed from zero.
Increment `ω k` makes the move from time `k` to time `k+1`. -/
def incrementMeasure (d : ℕ) [NeZero d] : Measure (ℕ → Lattice d) :=
  Measure.infinitePi (fun _ : ℕ => (stepLaw d).toMeasure)

instance incrementMeasure_probability (d : ℕ) [NeZero d] :
    IsProbabilityMeasure (incrementMeasure d) := by
  unfold incrementMeasure
  infer_instance

/-- Walk with independent increments; the sum is empty at time zero. -/
def iidWalk {d : ℕ} (x : Lattice d) (ω : ℕ → Lattice d) (n : ℕ) : Lattice d :=
  x + ∑ k ∈ Finset.range n, ω k

/-- The canonical Markov law of the same walk started at `x`. -/
abbrev latticePathLaw (d : ℕ) [NeZero d] (x : Lattice d) :
    Measure (ℕ → Lattice d) := Markov.statePathLaw (latticeKernel d) x

instance latticePathLaw_probability (d : ℕ) [NeZero d] (x : Lattice d) :
    IsProbabilityMeasure (latticePathLaw d x) := by
  change IsProbabilityMeasure (Markov.pathLaw (latticeKernel d) (PMF.pure x))
  infer_instance

/-- Product of the normalized one-dimensional Haar measures. -/
def torusMeasure (d : ℕ) : Measure (Torus d) :=
  Measure.pi (fun _ : Fin d =>
    @AddCircle.haarAddCircle (2 * Real.pi) ⟨by positivity⟩)

instance torusMeasure_probability (d : ℕ) : IsProbabilityMeasure (torusMeasure d) := by
  unfold torusMeasure
  infer_instance

/-- The cosine average on the actual angular torus. -/
def phi {d : ℕ} (t : Torus d) : ℝ :=
  (d : ℝ)⁻¹ * ∑ j : Fin d, Real.Angle.cos (t j)

/-- Return mass of the canonical transition powers, not defined by an integral. -/
def returnProbability (d : ℕ) [NeZero d] (n : ℕ) : ℝ≥0∞ :=
  Markov.power (latticeKernel d) n 0 0

namespace LatticeFourierSpec

-- The expected values expose the concrete objects, independently of any proof.
def LatticeType := ℕ → Type
def LatticeValue : LatticeType := fun d => Fin d → ℤ
def TorusType := ℕ → Type
def TorusValue : TorusType := fun d => Fin d → AddCircle (2 * Real.pi)
def StepChoiceType := ℕ → Type
def StepChoiceValue : StepChoiceType := fun d => Fin d × Bool

def stepType := {d : ℕ} → StepChoice d → Lattice d
def stepValue : stepType := fun a => if a.2 then Pi.single a.1 1 else -Pi.single a.1 1

def choiceLawType := (d : ℕ) → [NeZero d] → PMF (StepChoice d)
def choiceLawValue : choiceLawType := choiceLaw

def stepLawType := (d : ℕ) → [NeZero d] → PMF (Lattice d)
def stepLawValue : stepLawType := fun d _ => (choiceLaw d).map step

def latticeKernelType := (d : ℕ) → [NeZero d] → Markov.StochasticMatrix (Lattice d)
def latticeKernelValue : latticeKernelType := fun d _ x => (stepLaw d).map (fun z => x + z)

def incrementMeasureType := (d : ℕ) → [NeZero d] → Measure (ℕ → Lattice d)
def incrementMeasureValue : incrementMeasureType :=
  fun d _ => Measure.infinitePi (fun _ : ℕ => (stepLaw d).toMeasure)

def iidWalkType := {d : ℕ} → Lattice d → (ℕ → Lattice d) → ℕ → Lattice d
def iidWalkValue : iidWalkType := fun x ω n => x + ∑ k ∈ Finset.range n, ω k

def latticePathLawType := (d : ℕ) → [NeZero d] → Lattice d → Measure (ℕ → Lattice d)
def latticePathLawValue : latticePathLawType :=
  fun d _ x => Markov.statePathLaw (latticeKernel d) x

def torusMeasureType := (d : ℕ) → Measure (Torus d)
def torusMeasureValue : torusMeasureType := fun d =>
  Measure.pi (fun _ : Fin d => @AddCircle.haarAddCircle (2 * Real.pi) ⟨by positivity⟩)

def phiType := {d : ℕ} → Torus d → ℝ
def phiValue : phiType := fun {d} t => (d : ℝ)⁻¹ * ∑ j : Fin d, Real.Angle.cos (t j)

def returnProbabilityType := (d : ℕ) → [NeZero d] → ℕ → ℝ≥0∞
def returnProbabilityValue : returnProbabilityType :=
  fun d _ n => Markov.power (latticeKernel d) n 0 0

/-- Distinct labelled directions give the `2d` distinct prescribed increments. -/
def step_injective : Prop := ∀ d : ℕ, Function.Injective (step (d := d))

def stepLaw_step : Prop := ∀ (d : ℕ) [NeZero d] (a : StepChoice d),
  stepLaw d (step a) = ((2 * d : ℕ) : ℝ≥0∞)⁻¹

def stepLaw_elsewhere : Prop := ∀ (d : ℕ) [NeZero d] (z : Lattice d),
  z ∉ Set.range (step (d := d)) → stepLaw d z = 0

/-- The literal probability Haar measure on the torus is normalized. -/
def torus_probability : Prop := ∀ d : ℕ, IsProbabilityMeasure (torusMeasure d)

/-- Representative formula fixes the angular (rather than unit-circle) scaling. -/
def phi_representative : Prop := ∀ (d : ℕ) (t : Fin d → ℝ),
  phi (fun j => (t j : Real.Angle)) = (d : ℝ)⁻¹ * ∑ j : Fin d, Real.cos (t j)

/-- Independence and identical increment laws of the explicit product construction. -/
def independent_increments : Prop := ∀ (d : ℕ) [NeZero d],
  iIndepFun (fun k (ω : ℕ → Lattice d) => ω k) (incrementMeasure d)

def increment_law : Prop := ∀ (d : ℕ) [NeZero d] (k : ℕ),
  (incrementMeasure d).map (fun ω => ω k) = (stepLaw d).toMeasure

/-- Essential bridge between the independent-increment construction and the
canonical path law of the fixed lattice kernel, for every starting state. -/
def iidWalk_pathLaw : Prop := ∀ (d : ℕ) [NeZero d] (x : Lattice d),
  (incrementMeasure d).map (iidWalk x) = latticePathLaw d x

/-- Actual time marginals of the canonical process and its matrix powers. -/
def canonical_marginal : Prop := ∀ (d : ℕ) [NeZero d] (x : Lattice d) (n : ℕ),
  (latticePathLaw d x).map (fun ω => ω n) =
    (Markov.power (latticeKernel d) n x).toMeasure

def fourier_return : Prop := ∀ (d : ℕ) [NeZero d] (n : ℕ),
  (returnProbability d n).toReal = ∫ t : Torus d, phi t ^ n ∂torusMeasure d

def odd_return : Prop := ∀ (d : ℕ) [NeZero d] (n : ℕ),
  Odd n → returnProbability d n = 0

/-- The same parity conclusion as an event under the canonical path law. -/
def odd_path_return : Prop := ∀ (d : ℕ) [NeZero d] (n : ℕ),
  Odd n → latticePathLaw d 0 {ω | ω n = 0} = 0

end LatticeFourierSpec
end
end P207.Walk
