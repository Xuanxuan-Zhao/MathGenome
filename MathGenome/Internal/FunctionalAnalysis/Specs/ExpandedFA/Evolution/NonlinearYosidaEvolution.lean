import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.MonotoneGraphResolvents
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent statements for the Yosida evolution and graph-limit stage of
`paper.tex:15944–15971`. No finite dimensionality or separability is assumed.
The semigroup extension and exponential formula belong to subsequent goals. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace ExpandedFA.Evolution.NonlinearYosidaEvolution.Spec
universe u v
namespace R
abbrev onto := MonotoneGraphResolvents.Spec.ShiftOntoValue
abbrev J := MonotoneGraphResolvents.Spec.ResolventValue
abbrev Y := MonotoneGraphResolvents.Spec.YosidaValue
end R

/-- A classical solution for the everywhere Lipschitz regularized equation.
It is harmless, and stronger than forward existence, to solve on all of ℝ. -/
def GlobalApproximation {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)) (lam : ℝ) (honto : R.onto H A lam) (x : H) (u : ℝ → H) : Prop :=
  u 0 = x ∧ ∀ t, HasDerivAt u (-R.Y H A lam honto (u t)) t

/-- Construction of the entire family of global regularized flows. -/
def ApproximationFamily : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (honto : ∀ lam : ℝ, 0 < lam → R.onto H A lam),
    ∃ F : ℝ → H → ℝ → H,
      ∀ (lam : ℝ) (hlam : 0 < lam) (x : H),
        GlobalApproximation A lam (honto lam hlam) x (F lam x)

def InitialYosidaBound : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (lam : ℝ), 0 < lam → ∀ (honto : R.onto H A lam) (x a₀ : H),
      (x, a₀) ∈ A → ‖R.Y H A lam honto x‖ ≤ ‖a₀‖

def ApproximateContraction : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (lam : ℝ), 0 < lam → ∀ (honto : R.onto H A lam) (x y : H) (u v : ℝ → H),
      GlobalApproximation A lam honto x u → GlobalApproximation A lam honto y v →
      ∀ t : ℝ, 0 ≤ t → ‖u t - v t‖ ≤ ‖x - y‖

def ApproximateSpeedBound : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (lam : ℝ), 0 < lam → ∀ (honto : R.onto H A lam) (x a₀ : H) (u : ℝ → H),
      (x, a₀) ∈ A → GlobalApproximation A lam honto x u →
      ∀ t : ℝ, 0 ≤ t → ‖R.Y H A lam honto (u t)‖ ≤ ‖a₀‖

def ApproximateLipschitz : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (lam : ℝ), 0 < lam → ∀ (honto : R.onto H A lam) (x a₀ : H) (u : ℝ → H),
      (x, a₀) ∈ A → GlobalApproximation A lam honto x u →
      LipschitzOnWith ‖a₀‖₊ u (Ici 0)

def ParameterComparison : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (lam μ : ℝ), 0 < lam → 0 < μ →
    ∀ (hlam : R.onto H A lam) (hμ : R.onto H A μ) (x y : H) (C : ℝ),
      ‖R.Y H A lam hlam x‖ ≤ C → ‖R.Y H A μ hμ y‖ ≤ C →
      -inner ℝ (R.Y H A lam hlam x - R.Y H A μ hμ y) (x - y) ≤
        2 * (lam + μ) * C ^ 2

def ApproximateCauchyEstimate : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (lam μ : ℝ), 0 < lam → 0 < μ →
    ∀ (hlam : R.onto H A lam) (hμ : R.onto H A μ) (x a₀ : H) (u v : ℝ → H),
      (x, a₀) ∈ A → GlobalApproximation A lam hlam x u →
      GlobalApproximation A μ hμ x v →
      ∀ t : ℝ, 0 ≤ t → ‖u t - v t‖ ^ 2 ≤ 4 * (lam + μ) * ‖a₀‖ ^ 2 * t

/-- The convergence part is factored from existence of the regularized flows.
This statement is not a replacement for `YosidaEvolution`, which also constructs
the flows and establishes the limiting differential inclusion. -/
def ApproximateUniformLimit : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (honto : ∀ lam : ℝ, 0 < lam → R.onto H A lam)
      (F : ℝ → H → ℝ → H),
      (∀ (lam : ℝ) (hlam : 0 < lam) (x : H),
        GlobalApproximation A lam (honto lam hlam) x (F lam x)) →
    ∀ (x a₀ : H), (x, a₀) ∈ A →
      ∃ u : ℝ → H, u 0 = x ∧ LipschitzOnWith ‖a₀‖₊ u (Ici 0) ∧
        ∀ T : ℝ, 0 < T →
          TendstoUniformlyOn (fun lam => F lam x) u (𝓝[>] (0 : ℝ)) (Icc 0 T)

/-- The integrated Minty test uses one measurable test pair, rather than an
intersection of exceptional sets indexed by all graph elements. Integrability
is explicit: the total Bochner integral must not hide a divergent square. -/
def IntegratedMinty : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Type v) [MeasurableSpace X] (m : Measure X)
    (A : Set (H × H)) (honto : R.onto H A 1) (u a : X → H),
    let v := fun t => R.J H A 1 honto (u t + a t)
    let b := fun t => u t + a t - v t
    Integrable (fun t => ‖a t - b t‖ ^ 2) m →
    0 ≤ ∫ t, inner ℝ (a t - b t) (u t - v t) ∂m →
      ∀ᵐ t ∂m, (u t, a t) ∈ A

/-- Full original obligation. The approximation family is required to exist,
not supplied as a hypothesis. All positive parameters converge, not merely a
chosen sequence. The derivative is a strong derivative in the Hilbert space. -/
def YosidaEvolution : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (honto : ∀ lam : ℝ, 0 < lam → R.onto H A lam),
    ∃ F : ℝ → H → ℝ → H,
      (∀ (lam : ℝ) (hlam : 0 < lam) (x : H),
        GlobalApproximation A lam (honto lam hlam) x (F lam x)) ∧
      (∀ (lam : ℝ), 0 < lam → ∀ (x y : H) (t : ℝ), 0 ≤ t →
        ‖F lam x t - F lam y t‖ ≤ ‖x - y‖) ∧
      ∀ (x a₀ : H), (x, a₀) ∈ A →
        (∀ (lam : ℝ) (hlam : 0 < lam) (t : ℝ), 0 ≤ t →
          ‖R.Y H A lam (honto lam hlam) (F lam x t)‖ ≤ ‖a₀‖) ∧
        ∃ u : ℝ → H, u 0 = x ∧ LipschitzOnWith ‖a₀‖₊ u (Ici 0) ∧
          (∀ T : ℝ, 0 < T →
            TendstoUniformlyOn (fun lam => F lam x) u (𝓝[>] (0 : ℝ)) (Icc 0 T)) ∧
          (∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
            ∃ a : H, (u t, a) ∈ A ∧ HasDerivAt u (-a) t)

end ExpandedFA.Evolution.NonlinearYosidaEvolution.Spec
