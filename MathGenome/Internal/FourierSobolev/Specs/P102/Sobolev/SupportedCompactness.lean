import MathGenome.Internal.FourierSobolev.Specs.P102.U4.WholeSpaceDensity
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statements for the common bounded-support compactness argument,
paper.tex:1893–1914 and 2082–2102. The gradient norm here is the Lp norm of
its Euclidean pointwise length, as stipulated at paper.tex:1708–1712.
All exponents include 1 and exclude infinity; all dimensions are positive. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions ENNReal Topology
namespace P102.Sobolev
open U4

abbrev WholeSobolev (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞)
    [Fact (1 ≤ p)] := U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p

/-- Removing the restriction to the whole space changes no Lp class. -/
def wholeLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (u : DomainLp 𝕜 (⊤ : Opens (Space d)) p) : Lp 𝕜 p (volume : Measure (Space d)) :=
  (show MemLp (u : Space d → 𝕜) p volume by
    simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp u).toLp u

def supportedFirstIndex {d : ℕ} (i : Fin d) : SobolevIndex d 1 := ⟨{i}, by simp⟩

def gradientFunction {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : WholeSobolev d 𝕜 p) : Space d → EuclideanSpace 𝕜 (Fin d) :=
  fun x => WithLp.toLp 2 (fun i => wholeLp (sobolevDerivative u (supportedFirstIndex i)) x)

theorem gradientFunction_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : WholeSobolev d 𝕜 p) : MemLp (gradientFunction u) p volume := by
  apply MemLp.of_eval_piLp
  intro i
  exact Lp.memLp (wholeLp (sobolevDerivative u (supportedFirstIndex i)))

def gradientLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : WholeSobolev d 𝕜 p) :
    Lp (EuclideanSpace 𝕜 (Fin d)) p (volume : Measure (Space d)) :=
  (gradientFunction_memLp u).toLp (gradientFunction u)

def gradientNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : WholeSobolev d 𝕜 p) : ℝ := ‖gradientLp u‖

/-- Translation by +h, acting on equivalence classes. -/
def translateLp {d : ℕ} {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (h : Space d) (f : Lp E p (volume : Measure (Space d))) : Lp E p (volume : Measure (Space d)) :=
  Lp.compMeasurePreserving (fun x => x + h) (measurePreserving_add_right (volume : Measure (Space d)) h) f

def IsProbabilityKernel {d : ℕ} (η : WholeTests d ℝ) : Prop :=
  (∀ x, 0 ≤ η x) ∧ (∫ x, η x) = 1

/-- The actual pointwise regularization in the source's convolution order. -/
def smoothFunction {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (η : WholeTests d ℝ) (u : WholeSobolev d 𝕜 p) : Space d → 𝕜 :=
  fun x => ∫ y, η (x - y) • wholeLp (sobolevUnderlying u) y

/-- Its Lp-valued weighted-translation construction. The agreement with the
pointwise integral is a conclusion of `Smoothing`, not an assumed certificate. -/
def smoothLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (η : WholeTests d ℝ) (u : WholeSobolev d 𝕜 p) : Lp 𝕜 p (volume : Measure (Space d)) :=
  ∫ y, η y • translateLp (-y) (wholeLp (sobolevUnderlying u))

namespace SupportedCompactnessExpected

def Translation : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ⊤ → ∀ (u : WholeSobolev d 𝕜 p) (h : Space d),
    ‖translateLp h (wholeLp (sobolevUnderlying u)) - wholeLp (sobolevUnderlying u)‖ ≤
      ‖h‖ * gradientNorm u

def ProbabilityKernels : Prop :=
  ∀ d : ℕ, 0 < d → ∃ η : ℝ → WholeTests d ℝ,
    ∀ ε > 0, IsProbabilityKernel (η ε) ∧ tsupport (η ε) ⊆ Metric.closedBall 0 ε

/-- Constant one is valid for every nonnegative mass-one kernel supported in
B(0, ε). In particular the estimate is uniform over every gradient-bounded family.
Compact essential support is used only for compact support of the output. -/
def Smoothing : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ⊤ → ∀ (ε : ℝ), 0 < ε → ∀ (η : WholeTests d ℝ),
    IsProbabilityKernel η → tsupport η ⊆ Metric.closedBall 0 ε →
    ∀ u : WholeSobolev d 𝕜 p,
      ((smoothLp η u : Space d → 𝕜) =ᵐ[volume] smoothFunction η u) ∧
      MemLp (smoothFunction η u) p volume ∧
      ContDiff ℝ (⊤ : ℕ∞) (smoothFunction η u) ∧
      ‖smoothLp η u - wholeLp (sobolevUnderlying u)‖ ≤ ε * gradientNorm u ∧
      (∀ B : Set (Space d), Bornology.IsBounded B →
        (∀ᵐ x ∂volume, x ∉ B → wholeLp (sobolevUnderlying u) x = 0) →
        HasCompactSupport (smoothFunction η u))

/-- At any chosen family of the probability kernels, the approximation is
uniform over every Sobolev-bounded family, not just over each individual class. -/
def UniformApproximation : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ⊤ → ∀ (A : Set (WholeSobolev d 𝕜 p)), Bornology.IsBounded A →
    ∀ η : ℝ → WholeTests d ℝ,
    (∀ ε > 0, IsProbabilityKernel (η ε) ∧ tsupport (η ε) ⊆ Metric.closedBall 0 ε) →
    TendstoUniformlyOn (fun ε u => smoothLp (η ε) u)
      (fun u => wholeLp (sobolevUnderlying u)) (𝓝[>] 0) A

/-- No compactness is assumed of the input family. Relative compactness is
compactness of its Lp closure. The support set need not be open or measurable. -/
def Compactness : Prop :=
  ∀ {d : ℕ}, 0 < d → ∀ {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ⊤ → ∀ (A : Set (WholeSobolev d 𝕜 p)), Bornology.IsBounded A →
    ∀ B : Set (Space d), Bornology.IsBounded B →
    (∀ u ∈ A, ∀ᵐ x ∂volume, x ∉ B → wholeLp (sobolevUnderlying u) x = 0) →
    IsCompact (closure ((fun u => wholeLp (sobolevUnderlying u)) '' A))

end SupportedCompactnessExpected
end P102.Sobolev
