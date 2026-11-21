import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.NonlinearYosidaEvolution
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Independent statements for `fa2:p3:nonlinear-monotone`, paper.tex:15933–15995.
Time zero and zero Euler steps have their identity values. The graph is allowed
to be multivalued, and the real Hilbert space need not be separable. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology NNReal
namespace ExpandedFA.Evolution.NonlinearMonotoneEvolution.Spec
universe u
namespace R
abbrev onto := MonotoneGraphResolvents.Spec.ShiftOntoValue
abbrev J := MonotoneGraphResolvents.Spec.ResolventValue
end R
abbrev GlobalApproximation := @NonlinearYosidaEvolution.Spec.GlobalApproximation

def domain {H : Type u} (A : Set (H × H)) : Set H := {x | ∃ a, (x, a) ∈ A}

/-- The canonical implicit product, with the identity convention at t = 0. -/
def implicitProduct {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)) (honto : ∀ h : ℝ, 0 < h → R.onto H A h)
    (n : ℕ) (t : ℝ) (x : H) : H :=
  if ht : 0 < t / (n : ℝ) then (R.J H A (t / n) (honto _ ht))^[n] x else x

/-- Strong forward solutions in the Lipschitz class specified in the source. -/
def StrongSolution {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)) (x : H) (v : ℝ → H) : Prop :=
  v 0 = x ∧ (∃ C : ℝ≥0, LipschitzOnWith C v (Ici 0)) ∧
    ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∃ a : H, (v t, a) ∈ A ∧ HasDerivAt v (-a) t

/-- All semigroup and regularized-limit conclusions, before the Euler formula. -/
def SemigroupData {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)) (honto : ∀ h : ℝ, 0 < h → R.onto H A h)
    (F : ℝ → H → ℝ → H) (S : ℝ → H → H) : Prop :=
  (∀ lam : ℝ, ∀ hlam : 0 < lam, ∀ x : H,
    GlobalApproximation A lam (honto lam hlam) x (F lam x)) ∧
  (∀ x ∈ closure (domain A), S 0 x = x) ∧
  (∀ x ∈ closure (domain A), ∀ t ∈ Ici (0 : ℝ), S t x ∈ closure (domain A)) ∧
  (∀ t ∈ Ici (0 : ℝ), ∀ x ∈ closure (domain A), ∀ y ∈ closure (domain A),
    ‖S t x - S t y‖ ≤ ‖x - y‖) ∧
  (∀ s ∈ Ici (0 : ℝ), ∀ t ∈ Ici (0 : ℝ), ∀ x ∈ closure (domain A),
    S (s + t) x = S t (S s x)) ∧
  (∀ x ∈ closure (domain A), ContinuousOn (fun t => S t x) (Ici 0)) ∧
  (∀ x ∈ closure (domain A), ∀ T : ℝ, 0 < T →
    TendstoUniformlyOn (fun lam => F lam x) (fun t => S t x)
      (𝓝[>] (0 : ℝ)) (Icc 0 T)) ∧
  (∀ x a₀ : H, (x, a₀) ∈ A →
    LipschitzOnWith ‖a₀‖₊ (fun t => S t x) (Ici 0) ∧
    ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∃ a : H, (S t x, a) ∈ A ∧ HasDerivAt (fun t => S t x) (-a) t)

def SemigroupExistence : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (honto : ∀ h : ℝ, 0 < h → R.onto H A h),
      ∃ F S, SemigroupData A honto F S

/-- The full assigned result, retaining the quantitative implicit-step estimate. -/
def NonlinearEvolution : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : Set (H × H)),
    ExpandedFA.Monotone.Spec.MonotoneValue H
      (ExpandedFA.Monotone.Spec.HilbertGraphValue H A) →
    ∀ (honto : ∀ h : ℝ, 0 < h → R.onto H A h),
    ∃ F S, SemigroupData A honto F S ∧
      (∀ x ∈ domain A, ∀ v : ℝ → H, StrongSolution A x v →
        ∀ t ∈ Ici (0 : ℝ), v t = S t x) ∧
      (∀ x ∈ closure (domain A), ∀ T : ℝ, 0 < T →
        TendstoUniformlyOn (fun n : ℕ => fun t => implicitProduct A honto n t x)
          (fun t => S t x) atTop (Icc 0 T)) ∧
      (∀ x a₀ : H, (x, a₀) ∈ A → ∀ h : ℝ, ∀ hh : 0 < h, ∀ n : ℕ,
        ‖(R.J H A h (honto h hh))^[n] x - S ((n : ℝ) * h) x‖ ≤
          2 * ‖a₀‖ * Real.sqrt (((n : ℝ) * h) * h))

end ExpandedFA.Evolution.NonlinearMonotoneEvolution.Spec
