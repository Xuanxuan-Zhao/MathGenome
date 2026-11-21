import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SharpTraceBound

/-! Independent obligations for the half-space right inverse in
`paper.tex`, `fa2:p4:sharp-trace`, including the fractional density used
in its proof. All dimensions n ≥ 0 and both manuscript scalar fields remain.
No topology inherited from Lp is used for the fractional approximation.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.PartIV.SharpTraceExtension
open ExpandedFA.Distributions ExpandedFA.PartIV.FractionalSobolev

/-- Translation on the canonical Lp quotient, with convention τ_a u(x)=u(x-a). -/
def translation {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : Domain n) : Lp 𝕜 p (volume : Measure (Domain n)) →ₗᵢ[𝕜]
      Lp 𝕜 p (volume : Measure (Domain n)) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (fun x => x - a)
    (measurePreserving_sub_right volume a)

/-- Full fractional error on Lp classes; used only for finite-energy differences. -/
def fractionalError {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (s : ℝ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u v : Lp 𝕜 p (volume : Measure (Domain n))) : ℝ :=
  ‖u - v‖ + (differenceEnergy s p (u - v)).toReal ^ (1 / p.toReal)

end ExpandedFA.PartIV.SharpTraceExtension

namespace Specs.ExpandedFA.PartIV.SharpTraceExtension
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.HalfSpace _root_.ExpandedFA.Sobolev.Lines
open _root_.ExpandedFA.PartIV.FractionalSobolev
open _root_.ExpandedFA.PartIV.SharpTraceBound
open _root_.ExpandedFA.PartIV.SharpTraceExtension
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Translation continuity in the full fractional norm, rather than merely Lp. -/
def FractionalTranslationContinuous : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (n : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ∞ → ∀ u : FractionalSpace 𝕜 n s p,
      Tendsto (fun a => fractionalError s p (translation p a u.val) u.val) (𝓝 0) (𝓝 0)

/-- C_c^∞ density, with the full Lp-plus-difference error and arbitrary input.
The general range includes the needed sharp exponent s=1-1/p. -/
def SmoothDensity : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (n : ℕ) (s : ℝ), 0 < s → s < 1 →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (u : FractionalSpace 𝕜 n s p) (ε : ℝ), 0 < ε →
      ∃ (v : FractionalSpace 𝕜 n s p) (f : Domain n → 𝕜),
        ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧ v.val =ᵐ[volume] f ∧
        fractionalError s p v.val u.val < ε

/-- Bounded scalar-linear right inverse into the actual weak-derivative graph.
The source subtype has no algebraic instances in the independent Specs, so
linearity is expressed using equality of its underlying Lp classes. Existence
of the sums and scalar multiples is supplied by finite-energy closure, already
proved upstream. The target norm is the full first-jet sum norm and therefore
bounds every first weak derivative as well as the undifferentiated Lp norm.
The constant depends only on the dimension and p. The identity is for every
existing coordinate trace, and does not postulate a replacement trace. -/
def BoundedRightInverse : Prop :=
  ∀ (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1)),
      ∃ E : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p →
          SpaceValue 𝕜 (n + 1) (upper i) 1 p,
        (∀ u v w, w.val = u.val + v.val → E w = E u + E v) ∧
        (∀ (c : 𝕜) u v, v.val = c • u.val → E v = c • E u) ∧
        (∀ u, ‖E u‖ ≤ C * fractionalNorm (1 - 1 / p.toReal) p u) ∧
        (∀ (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
            Lp 𝕜 p (volume : Measure (Transverse i))), CoordinateTraceCondition i T →
          ∀ u, reindexedTrace i T (E u) = u.val)

/-- Smooth compactly supported finite-energy data, as a subtype of the
canonical fractional space. Membership is geometric, with no lift assumed. -/
abbrev SmoothData (𝕜 : Type) [RCLike 𝕜] (n : ℕ) (s : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  {u : FractionalSpace 𝕜 n s p // ∃ f : Domain n → 𝕜,
    ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧ u.val =ᵐ[volume] f}

/-- The analytic construction restricted to smooth data. Together with
SmoothDensity, this suffices by extension into the complete first-jet graph.
Linearity and the uniform bound must be proved, not assumed certificates
of the final arbitrary-data extension. -/
def SmoothRightInverse : Prop :=
  ∀ (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1)),
      ∃ E : SmoothData 𝕜 n (1 - 1 / p.toReal) p →
          SpaceValue 𝕜 (n + 1) (upper i) 1 p,
        (∀ u v w, w.val.val = u.val.val + v.val.val → E w = E u + E v) ∧
        (∀ (c : 𝕜) u v, v.val.val = c • u.val.val → E v = c • E u) ∧
        (∀ u, ‖E u‖ ≤ C * fractionalNorm (1 - 1 / p.toReal) p u.val) ∧
        (∀ (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
            Lp 𝕜 p (volume : Measure (Transverse i))), CoordinateTraceCondition i T →
          ∀ u, reindexedTrace i T (E u) = u.val.val)

def Assembly : Prop := SmoothDensity → SmoothRightInverse → BoundedRightInverse

end Specs.ExpandedFA.PartIV.SharpTraceExtension
