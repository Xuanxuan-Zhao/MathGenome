import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Extension
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Independent statements for the supercritical part of paper.tex:2412–2435.
The spaces, Lebesgue measures, and Gagliardo seminorm are the canonical upstream
objects. Positive coordinate dimensions include d = 1. The closure is a subtype,
so uniqueness does not impose any values outside the closed domain.

The domain estimate explicitly bounds the sum of the supremum norm and a
Hölder constant. Thus it controls the full C^{0,s-d/p} norm, including for
disconnected and empty Lipschitz open sets. Compactness at smaller exponents is
a separate allocated obligation, not a premise of either statement below.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology
open BoundedContinuousFunction

namespace P102.Fractional.Morrey
open P102.Fractional

/-- The exact supercritical exponent (as a real number, without truncation). -/
def exponent (d : ℕ) (s : ℝ) (p : ℝ≥0∞) : ℝ := s - (d : ℝ) / p.toReal

/-- The manuscript's sum norm of an a.e. class. -/
def fullNorm {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] {G : Set (Domain d)}
    {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : Space 𝕜 G s p) : ℝ :=
  ‖firstProjection u‖ + (seminorm G s p (firstProjection u)).toReal

/-- A closure function viewed on the ambient space. Only its values on G are
used in the a.e. representative condition; outside the closure it is zero. -/
def closureValue {d : ℕ} {𝕜 : Type*} [Zero 𝕜] {G : Set (Domain d)}
    (f : closure G → 𝕜) (x : Domain d) : 𝕜 := by
  classical
  exact
  if hx : x ∈ closure G then f ⟨x, hx⟩ else 0

/-- The representative condition on the original open set, not on its boundary. -/
def RepresentsOnClosure {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Space 𝕜 G s p) (f : closure G → 𝕜) : Prop :=
  closureValue f =ᵐ[domainMeasure G] firstProjection u

end P102.Fractional.Morrey

namespace Specs.P102.Fractional.Morrey
open _root_.P102.Fractional _root_.P102.Fractional.Morrey
universe u

/-- A unique bounded continuous representative on all of Euclidean space.
The Hölder estimate uses only the seminorm, while the supremum estimate uses
the full norm. The constant is chosen before the input class. -/
def wholeSpace : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → (d : ℝ) < s * p.toReal →
  ∀ (𝕜 : Type u) [RCLike 𝕜], ∃ C : ℝ≥0, 0 < C ∧
    ∀ u : Space 𝕜 (Set.univ : Set (Domain d)) s p,
      ∃! f : Domain d →ᵇ 𝕜,
        ((f : Domain d → 𝕜) =ᵐ[volume] firstProjection u) ∧
        (∀ x y, ‖f x - f y‖ ≤ (C : ℝ) *
          (seminorm Set.univ s p (firstProjection u)).toReal *
          dist x y ^ exponent d s p) ∧
        ‖f‖ ≤ (C : ℝ) * fullNorm u

/-- The representative on closure Ω, with its full Hölder norm bound from
the domain Gagliardo norm. No connectedness, nonemptiness, or C¹ assumption
is imposed. The Hölder constant H is part of the conclusion, and its sum with
the supremum norm is bounded by a single constant chosen before u. -/
def onClosure : Prop :=
  ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
  ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → ((n + 1 : ℕ) : ℝ) < s * p.toReal →
  ∀ (𝕜 : Type u) [RCLike 𝕜], ∃ C : ℝ≥0, 0 < C ∧
    ∀ u : Space 𝕜 G s p, ∃! f : closure G →ᵇ 𝕜,
      RepresentsOnClosure u f ∧
      ∃ H : ℝ≥0, ‖f‖ + (H : ℝ) ≤ (C : ℝ) * fullNorm u ∧
        ∀ x y : closure G, ‖f x - f y‖ ≤ (H : ℝ) *
          dist (x : Domain (n + 1)) (y : Domain (n + 1)) ^ exponent (n + 1) s p

end Specs.P102.Fractional.Morrey
