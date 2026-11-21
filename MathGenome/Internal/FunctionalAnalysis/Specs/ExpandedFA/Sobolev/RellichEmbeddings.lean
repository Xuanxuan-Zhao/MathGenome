import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.KolmogorovRiesz
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.MorreyEmbedding
import Mathlib.Topology.ContinuousMap.Compact

/-!
Independent statements of the Rellich clauses and the critical concentration
obstruction in paper.tex:17857–17901, using the canonical distributional graph
and its sum norm (paper.tex:17617–17625). Scalars are real or complex. Finite
Lp targets have exponent at least one. The Morrey case includes p = infinity
and dimension zero. W₀ is used only at finite p, exactly as defined upstream.

Compactness means relative compactness of the images of every norm bounded
family under an actual bounded scalar-linear inclusion. The continuous target
is C(closure Ω) with its supremum norm. No nonemptiness is needed for the
positive statements. The negative critical assertion requires a nonempty open
set and 1 ≤ p < d, precisely the range of the finite critical exponent.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.Sobolev.Rellich
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Normalize the whole-space restricted measure to volume, without choosing
new pointwise data. This is needed because `volume.restrict univ` is propositionally,
not definitionally, equal to volume. -/
def wholeUnderlying {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d ⊤ 1 p) :
    Lp 𝕜 p (volume : Measure (Domain d)) :=
  (show MemLp (u.val (zeroIndex d 1)) p volume by
    simpa using Lp.memLp (u.val (zeroIndex d 1))).toLp (u.val (zeroIndex d 1))

/-- A compact inclusion with the prescribed underlying a.e. function. -/
def CompactLpInclusion {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] : Prop :=
  ∃ J : SpaceValue 𝕜 d Ω 1 p →L[𝕜] DomainLp 𝕜 Ω q,
    (∀ u, J u =ᵐ[volume.restrict (Ω : Set (Domain d))] u.val (zeroIndex d 1)) ∧
    ∀ A : Set (SpaceValue 𝕜 d Ω 1 p), Bornology.IsBounded A →
      IsCompact (closure (J '' A))

/-- The same inclusion on the actual norm closure of compact smooth members. -/
def CompactZeroLpInclusion {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] : Prop :=
  ∃ J : (ZeroSpaceValue 𝕜 d Ω 1 p hp) →L[𝕜] DomainLp 𝕜 Ω q,
    (∀ u, J u =ᵐ[volume.restrict (Ω : Set (Domain d))]
      u.val.val (zeroIndex d 1)) ∧
    ∀ A : Set (ZeroSpaceValue 𝕜 d Ω 1 p hp), Bornology.IsBounded A →
      IsCompact (closure (J '' A))

/-- A compact map to the closure, including its boundary values. -/
def CompactContinuousInclusion {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  letI : CompactSpace (closure (Ω : Set (Domain d))) :=
    isCompact_iff_compactSpace.mp hΩ.isCompact_closure
  ∃ J : SpaceValue 𝕜 d Ω 1 p →L[𝕜] C(closure (Ω : Set (Domain d)), 𝕜),
    (∀ u, ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
      ∃ hx : x ∈ closure (Ω : Set (Domain d)),
        J u ⟨x, hx⟩ = u.val (zeroIndex d 1) x) ∧
    ∀ A : Set (SpaceValue 𝕜 d Ω 1 p), Bornology.IsBounded A →
      IsCompact (closure (J '' A))

/-- An explicit rescaling, with concentration scale n+1 and critical amplitude. -/
def concentratingBump {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (p : ℝ≥0) (a : Domain d) (φ : Domain d → 𝕜) (n : ℕ) (x : Domain d) : 𝕜 :=
  ((n + 1 : ℝ) ^ ((d : ℝ) / p - 1)) • φ ((n + 1 : ℝ) • (x - a))

end ExpandedFA.Sobolev.Rellich

namespace Specs.ExpandedFA.Sobolev.RellichEmbeddings
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.Rellich WeakDerivativeSpaces

/-- The base compactness consequence of the accepted translation estimate and
local Kolmogorov–Riesz, with no domain regularity or common support premise. -/
def LocalLpCompactness : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ A : Set (SpaceValue 𝕜 d ⊤ 1 p), Bornology.IsBounded A →
    ∀ s : Set (Domain d), MeasurableSet s → Bornology.IsBounded s →
      IsCompact (closure ((fun u : SpaceValue 𝕜 d ⊤ 1 p =>
        KolmogorovRieszSpec.LpRestrictValue p volume s
          (wholeUnderlying u)) '' A))

/-- Base compactness on any bounded C¹ domain, including p=1. -/
def SameExponent : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    C1Extension.IsC1Domain Ω → Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → CompactLpInclusion (𝕜 := 𝕜) Ω p p

def Subcritical : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    C1Extension.IsC1Domain Ω → Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p q : ℝ≥0), 1 ≤ p → p < d → 1 ≤ q → q < Subcritical.criticalExponent d p →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))],
      CompactLpInclusion (𝕜 := 𝕜) Ω p q

def Critical : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), 1 ≤ d →
    ∀ (Ω : Opens (Domain d)), C1Extension.IsC1Domain Ω →
    Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (q : ℝ≥0), 1 ≤ q →
    ∀ [Fact (1 ≤ (d : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))],
      CompactLpInclusion (𝕜 := 𝕜) Ω d q

def Supercritical : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    C1Extension.IsC1Domain Ω →
    ∀ hΩ : Bornology.IsBounded (Ω : Set (Domain d)),
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], (d : ℝ≥0∞) < p →
      CompactContinuousInclusion (𝕜 := 𝕜) Ω hΩ p

/-- Arbitrary bounded open sets; no C¹ boundary premise. -/
def ZeroSubcritical : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p q : ℝ≥0), 1 ≤ p → p < d → 1 ≤ q → q < Subcritical.criticalExponent d p →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))],
      CompactZeroLpInclusion (𝕜 := 𝕜) Ω p ENNReal.coe_ne_top q

/-- The finite-exponent critical-dimensional case also holds for W₀. -/
def ZeroCritical : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), 1 ≤ d →
    ∀ (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (q : ℝ≥0), 1 ≤ q →
    ∀ [Fact (1 ≤ (d : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))],
      CompactZeroLpInclusion (𝕜 := 𝕜) Ω d (by simp) q

/-- For finite p>d, all finite Lq targets are subcritical as well. -/
def ZeroSupercritical : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p q : ℝ≥0), 1 ≤ p → (d : ℝ≥0) < p → 1 ≤ q →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))],
      CompactZeroLpInclusion (𝕜 := 𝕜) Ω p ENNReal.coe_ne_top q

/-- The usual finite critical-exponent concentration counterexample. It is
already in W₀, hence also obstructs compactness of the full-space inclusion.
The positive critical norm is independent of n, and no strictly increasing
subsequence can converge in that Lp norm. -/
def CriticalNoncompactness : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    (Ω : Set (Domain d)).Nonempty →
    ∀ (p : ℝ≥0), 1 ≤ p → p < d →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))]
      [Fact (1 ≤ (Subcritical.criticalExponent d p : ℝ≥0∞))],
    ∃ (a : Domain d) (φ : Domain d → 𝕜)
      (u : ℕ → ZeroSpaceValue 𝕜 d Ω 1 p ENNReal.coe_ne_top)
      (v : ℕ → DomainLp 𝕜 Ω (Subcritical.criticalExponent d p)),
      a ∈ Ω ∧ ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ φ ≠ 0 ∧
      Bornology.IsBounded (Set.range u) ∧
      (∀ n, HasCompactSupport (concentratingBump p a φ n) ∧
        tsupport (concentratingBump p a φ n) ⊆ Ω) ∧
      (∀ n, (u n).val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        concentratingBump p a φ n) ∧
      (∀ n, v n =ᵐ[volume.restrict (Ω : Set (Domain d))]
        concentratingBump p a φ n) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ n, ‖v n‖ = c) ∧
      ¬ ∃ (σ : ℕ → ℕ) (v₀ : DomainLp 𝕜 Ω (Subcritical.criticalExponent d p)),
        StrictMono σ ∧ Tendsto (v ∘ σ) atTop (𝓝 v₀)

/-- Complete original obligation. Intermediate lemmas are not assumed here. -/
def Embeddings : Prop :=
  Subcritical ∧ Critical ∧ Supercritical ∧ ZeroSubcritical ∧ ZeroCritical ∧
    ZeroSupercritical ∧ CriticalNoncompactness

end Specs.ExpandedFA.Sobolev.RellichEmbeddings
