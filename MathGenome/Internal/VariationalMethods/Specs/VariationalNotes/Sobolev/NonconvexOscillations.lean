import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Spaces
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The third example in paper.tex, `ex:direct-limitations`.
The natural index `n` is the number of cells. Statements about a single tent
assume `0 < n`; sequential statements use `n + 1` to enumerate all positive
indices. Values at the finitely many corners do not affect Lp classes. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal Topology

namespace VariationalNotes.Sobolev.NonconvexOscillations

def four : Exponent := ⟨4, by norm_num⟩

def interval : Opens (Domain 1) :=
  ⟨{x | x 0 ∈ Ioo (0 : ℝ) 1},
    isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous⟩

/-- On every cell, the fractional part rises from 0 to 1 and is folded at 1/2.
Dividing by n gives precisely slopes +1 and -1, and height 1/(2n). -/
def tent (n : ℕ) (x : ℝ) : ℝ :=
  min (Int.fract ((n : ℝ) * x)) (1 - Int.fract ((n : ℝ) * x)) / n

/-- The a.e. derivative, with arbitrary choices at the corners. -/
def tentSlope (n : ℕ) (x : ℝ) : ℝ :=
  if Int.fract ((n : ℝ) * x) < (1 / 2 : ℝ) then 1 else -1

def tentField (n : ℕ) (x : Domain 1) : Vector 1 :=
  EuclideanSpace.single 0 (tent n (x 0))

def slopeField (n : ℕ) (x : Domain 1) : Gradient 1 1 :=
  EuclideanSpace.single (0, 0) (tentSlope n (x 0))

/-- The original quartic double-well integrand; it is independent of x and s. -/
def integrand (_x : Domain 1) (_s : Vector 1) (Z : Gradient 1 1) : ℝ :=
  ((Z (0, 0)) ^ 2 - 1) ^ 2

/-- An actual graph-space Sobolev class, with the prescribed value and gradient. -/
def RepresentsTent (n : ℕ) (u : W1p interval 1 four) : Prop :=
  (value interval 1 four u : Domain 1 → Vector 1) =ᵐ[domainMeasure interval] tentField n ∧
  (gradient interval 1 four u : Domain 1 → Gradient 1 1) =ᵐ[domainMeasure interval] slopeField n

/-- Weak convergence in the full continuous dual of the gradient L4 space. -/
def GradientWeaklyConverges (u : ℕ → W1p interval 1 four) : Prop :=
  ∀ ℓ : GradientLp interval 1 four →L[ℝ] ℝ,
    Tendsto (fun n => ℓ (gradient interval 1 four (u n))) atTop (𝓝 0)

/-- The weak sequential lower-semicontinuity property on the zero-boundary class. -/
def WeakSequentialLowerSemicontinuity : Prop :=
  ∀ (u : ℕ → W1p interval 1 four) (v : W1p interval 1 four),
    (∀ n, u n ∈ zeroSubmodule interval 1 four) →
    v ∈ zeroSubmodule interval 1 four → WeaklyConverges u v →
    energy interval 1 four integrand v ≤
      Filter.liminf (fun n => energy interval 1 four integrand (u n)) atTop

/-- The strong-value/weak-gradient sequential inequality from §8.2,
specialized to L4 in both fields. -/
def StrongWeakSequentialLowerSemicontinuity : Prop :=
  ∀ (u : ℕ → W1p interval 1 four) (v : W1p interval 1 four),
    (∀ n, u n ∈ zeroSubmodule interval 1 four) →
    v ∈ zeroSubmodule interval 1 four →
    Tendsto (fun n => value interval 1 four (u n)) atTop (𝓝 (value interval 1 four v)) →
    (∀ ℓ : GradientLp interval 1 four →L[ℝ] ℝ,
      Tendsto (fun n => ℓ (gradient interval 1 four (u n))) atTop
        (𝓝 (ℓ (gradient interval 1 four v)))) →
    energy interval 1 four integrand v ≤
      Filter.liminf (fun n => energy interval 1 four integrand (u n)) atTop

namespace Expected

def Geometry : Prop :=
  ∀ n : ℕ, 0 < n → Continuous (tent n) ∧
    (∀ k : ℕ, k ≤ n → tent n ((k : ℝ) / n) = 0) ∧
    (∀ k : ℕ, k < n →
      (∀ x ∈ Icc ((k : ℝ) / n) (((k : ℝ) + 1 / 2) / n),
        tent n x = x - (k : ℝ) / n) ∧
      (∀ x ∈ Icc (((k : ℝ) + 1 / 2) / n) (((k : ℝ) + 1) / n),
        tent n x = ((k : ℝ) + 1) / n - x))

def UniformConvergence : Prop :=
  (∀ n : ℕ, 0 < n → ∀ x : ℝ, 0 ≤ tent n x ∧ tent n x ≤ 1 / (2 * (n : ℝ))) ∧
    TendstoUniformlyOn (fun n => tent (n + 1)) (fun _ => 0) atTop (Icc 0 1)

def Realization : Prop :=
  ∀ n : ℕ, 0 < n → ∃ u : W1p interval 1 four,
    RepresentsTent n u ∧ u ∈ zeroSubmodule interval 1 four

def GradientConvergence : Prop :=
  ∀ u : ℕ → W1p interval 1 four,
    (∀ n, RepresentsTent (n + 1) (u n)) → GradientWeaklyConverges u

def ValueConvergence : Prop :=
  ∀ u : ℕ → W1p interval 1 four,
    (∀ n, RepresentsTent (n + 1) (u n)) →
    Tendsto (fun n => value interval 1 four (u n)) atTop (𝓝 0)

def EnergyOnTent : Prop :=
  ∀ (n : ℕ) (u : W1p interval 1 four), RepresentsTent n u →
    energy interval 1 four integrand u = 0

def EnergyAtZero : Prop := energy interval 1 four integrand 0 = 1

def Nonconvexity : Prop :=
  ∀ (x : Domain 1) (s : Vector 1), ¬ConvexOn ℝ Set.univ (integrand x s)

/-- All parts refer to the same exact sequence, in the accepted Euclidean model. -/
def Counterexample : Prop :=
  ∃ u : ℕ → W1p interval 1 four,
    (∀ n, RepresentsTent (n + 1) (u n)) ∧
    (∀ n, u n ∈ zeroSubmodule interval 1 four) ∧
    Tendsto (fun n => value interval 1 four (u n)) atTop (𝓝 0) ∧
    GradientWeaklyConverges u ∧ WeaklyConverges u 0 ∧
    (∀ n, energy interval 1 four integrand (u n) = 0) ∧
    energy interval 1 four integrand 0 = 1 ∧
    ¬WeakSequentialLowerSemicontinuity ∧
    ¬StrongWeakSequentialLowerSemicontinuity

end Expected
end VariationalNotes.Sobolev.NonconvexOscillations
