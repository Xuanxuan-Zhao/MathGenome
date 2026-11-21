import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Independent statements of `fa2:p4:sobolev-translations`, including the
p=1 obstruction in its proof. No positive-dimension restriction is imposed
on either affirmative assertion. All gradients use the Euclidean pointwise
norm, rather than the sum of the norms of their Lp components. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace ExpandedFA.Sobolev.Translation
open ExpandedFA.Distributions

/-- The multi-index for the j-th first derivative. -/
def firstIndex {d : ℕ} (j : Fin d) : DerivativeIndex d 1 :=
  ⟨fun i => ⟨if i = j then 1 else 0, by split_ifs <;> omega⟩, by simp⟩

/-- Euclidean length on the coordinate model, whose ambient Lean norm is the
supremum norm. This explicit conversion prevents a dimension-dependent loss. -/
def euclideanLength {d : ℕ} (h : Domain d) : ℝ :=
  ‖WithLp.toLp 2 h‖

/-- The weak gradient, as an a.e. defined Euclidean vector of scalar values. -/
def gradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue
      𝕜 d (⊤ : Opens (Domain d)) 1 p) (x : Domain d) : EuclideanSpace 𝕜 (Fin d) :=
  WithLp.toLp 2 (fun j => u.val (firstIndex j) x)

/-- The concrete real interval indicator used for the endpoint obstruction. -/
def intervalIndicator : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (fun _ => 1)

/-- The ordinary scalar weak first derivative on the real line, tested against
all smooth compactly supported real functions. -/
def HasRealWeakDerivative (f g : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (∫ x, φ x * g x) = -(∫ x, deriv φ x * f x)

end ExpandedFA.Sobolev.Translation

namespace Specs.ExpandedFA.Sobolev.SobolevTranslationCharacterization
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Sobolev.Translation
open _root_.ExpandedFA.Distributions WeakDerivativeSpaces

/-- The Euclidean gradient is in the same Lp space, at infinity as well. -/
def GradientMemLp : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SpaceValue 𝕜 d (⊤ : Opens (Domain d)) 1 p),
  MemLp (gradient u) p volume

/-- The sharp translation estimate, including p=1 and p=infinity. -/
def ForwardEstimate : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : SpaceValue 𝕜 d (⊤ : Opens (Domain d)) 1 p) (h : Domain d),
  eLpNorm (fun x => u.val (zeroIndex d 1) (x + h) - u.val (zeroIndex d 1) x)
      p volume ≤ ENNReal.ofReal (euclideanLength h) * eLpNorm (gradient u) p volume

/-- Interior converse, with a separate sharp bound for every coordinate.
The conclusion is membership in the accepted derivative graph, with its
underlying Lp class equal to the given one. -/
def Converse : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p) (C : ℝ),
    (∀ h : Domain d,
      (eLpNorm (fun x => u (x + h) - u x) p volume).toReal ≤
        C * euclideanLength h) →
    ∃ v : SpaceValue 𝕜 d (⊤ : Opens (Domain d)) 1 p,
      v.val (zeroIndex d 1) = u ∧ ∀ j : Fin d, ‖v.val (firstIndex j)‖ ≤ C

/-- Nonmembership in the actual accepted derivative graph, using the standard
measure-preserving coordinate identification ℝ¹ ≃ ℝ. -/
def GraphEndpointObstruction : Prop :=
  ¬ ∃ u : SpaceValue ℝ 1 (⊤ : Opens (Domain 1)) 1 1,
    u.val (zeroIndex 1 1) =ᵐ[volume] (fun x : Domain 1 => intervalIndicator (x 0))

/-- Bounded L1 difference quotients do not imply an L1 weak derivative.
The example is explicitly the interval indicator, with constant 2. -/
def EndpointObstruction : Prop :=
  MemLp intervalIndicator 1 volume ∧
  (∀ h : ℝ, eLpNorm (fun x => intervalIndicator (x + h) - intervalIndicator x)
      1 volume ≤ ENNReal.ofReal (2 * |h|)) ∧
  ¬ ∃ g : ℝ → ℝ, Integrable g volume ∧ HasRealWeakDerivative intervalIndicator g

end Specs.ExpandedFA.Sobolev.SobolevTranslationCharacterization
