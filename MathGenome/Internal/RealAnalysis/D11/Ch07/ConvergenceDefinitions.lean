import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch04.EssentialBounds
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral

/-!
Representative convergence modes (paper.tex:2100–2125, 2395–2403).

The raw analytic predicates also make sense beyond measurable scalar functions;
source theorems use measurable real or complex representatives. No everywhere
quantifier is replaced by an a.e. one. Lp convergence includes measurable
membership of both the sequence and its limit and uses p-power integrals.
The infinity endpoint uses the upstream ordinary a.e. essential supremum.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
universe u v
noncomputable section
namespace D11.Ch07.ConvergenceDefinitions

open D11.Ch04.AeCommonException
open D11.Ch04.EssentialBounds
open D11.Ch05.NonnegativeIntegral

variable {X : Type u} {E : Type v} [NormedAddCommGroup E]

/-- Convergence at every point of the domain. -/
def pointwiseConverges (f : ℕ → X → E) (g : X → E) : Prop :=
  ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))

/-- Convergence outside a measurable null envelope in the given space. -/
def aeConverges [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → E) (g : X → E) : Prop :=
  almostEverywhere μ (fun x => Tendsto (fun n => f n x) atTop (𝓝 (g x)))

/-- Uniform convergence on the specified retained set. -/
def uniformConvergesOn (f : ℕ → X → E) (g : X → E) (A : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ A, ‖f n x - g x‖ < ε

/-- Uniform convergence with the original everywhere quantifier. -/
def uniformConverges (f : ℕ → X → E) (g : X → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖f n x - g x‖ < ε

def almostUniformConverges [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ A : Set X, MeasurableSet A ∧ μ A < ENNReal.ofReal δ ∧
    uniformConvergesOn f g Aᶜ

/-- Strict deviation threshold, as in the source's global definition. -/
def deviationSet (f g : X → E) (ε : ℝ) : Set X := {x | ε < ‖f x - g x‖}

def inMeasureConverges [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n => μ (deviationSet (f n) g ε)) atTop (𝓝 0)

def cauchyInMeasure [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, μ (deviationSet (f n) (f m) ε) < ENNReal.ofReal δ

def locallyInMeasureConverges [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E) : Prop :=
  ∀ A : Set X, MeasurableSet A → μ A < ∞ → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ (A ∩ deviationSet (f n) g ε)) atTop (𝓝 0)

/-- Nonnegative p-power integral on representatives, without a quotient norm. -/
def powerIntegral [MeasurableSpace X] (μ : Measure X) (p : ℝ) (f : X → E) : ℝ≥0∞ :=
  nonnegativeIntegral μ (fun x => ENNReal.ofReal (‖f x‖ ^ p))

/-- Measurability is on the original sigma-algebra, not its completion. -/
def finitePowerIntegral [MeasurableSpace X] [MeasurableSpace E]
    (μ : Measure X) (p : ℝ) (f : X → E) : Prop :=
  Measurable f ∧ powerIntegral μ p f < ∞

/-- Finite p, including p=1, with membership for every representative. -/
def lpConverges [MeasurableSpace X] [MeasurableSpace E]
    (μ : Measure X) (p : ℝ) (f : ℕ → X → E) (g : X → E) : Prop :=
  1 ≤ p ∧ finitePowerIntegral μ p g ∧ (∀ n, finitePowerIntegral μ p (f n)) ∧
    Tendsto (fun n => powerIntegral μ p (fun x => f n x - g x)) atTop (𝓝 0)

/-- The infinity endpoint requires all functions to be essentially bounded. -/
def linftyConverges [MeasurableSpace X] [MeasurableSpace E]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E) : Prop :=
  (Measurable g ∧ essentiallyBounded μ g) ∧
    (∀ n, Measurable (f n) ∧ essentiallyBounded μ (f n)) ∧
    Tendsto (fun n => essentialSupNorm μ (fun x => f n x - g x)) atTop (𝓝 0)

/-- Each intersected deviation measure is squeezed between zero and the
corresponding global deviation measure. Even finiteness of A is unused. -/
theorem global_implies_local [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → E) (g : X → E)
    (h : inMeasureConverges μ f g) : locallyInMeasureConverges μ f g := by
  intro A _ _ ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ => bot_le) (fun _ => measure_mono inter_subset_right)

theorem measurable_deviationSet {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f g : X → 𝕜) (ε : ℝ)
    (hf : Measurable f) (hg : Measurable g) : MeasurableSet (deviationSet f g ε) := by
  exact measurableSet_lt measurable_const (hf.sub hg).norm

theorem powerIntegral_eq_lintegral [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (f : X → E) :
    powerIntegral μ p f = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p) ∂μ :=
  integral_eq_lintegral μ _

end D11.Ch07.ConvergenceDefinitions
