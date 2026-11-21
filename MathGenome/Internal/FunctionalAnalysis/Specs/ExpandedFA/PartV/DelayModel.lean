import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.OdeIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Independent specification of paper.tex, `fa2:p5:delay-model`, lines 22244–22274.
The coefficients have their actual operator-norm topology, over either manuscript
scalar field. Scalar coefficients act through scalar multiples of the identity.
The history and solution are continuous maps on the displayed finite intervals.
Clamping only defines the integrand outside its domain; on every integration
interval its values are the manuscript's original values. `T = 0` is included.

The higher-derivative interface uses genuine derivative towers on one-sided
intervals. `productJet` is the recursively expanded Leibniz rule (equivalently
the binomial Leibniz sum), with no commutation of operator factors. Its jump
identity describes propagation of the first unmatched history derivative.
-/
noncomputable section
open Set MeasureTheory
namespace ExpandedFA.PartV.DelayModelSpec
open OdeIntegralSpec

abbrev HistoryInterval (τ : ℝ) := Icc (-τ) 0
abbrev SolutionInterval (τ T : ℝ) := Icc (-τ) T

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
local instance delayModelSpecRealNormedSpace : NormedSpace ℝ E :=
  NormedSpace.restrictScalars ℝ 𝕜 E
variable {τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T)

def solutionExtension (u : C(SolutionInterval τ T, E)) : ℝ → E :=
  extendCurve ((neg_nonpos.mpr hτ.le).trans hT) u

def field (A B : C(VolterraInterval 0 T, E →L[𝕜] E))
    (u : C(SolutionInterval τ T, E)) (s : ℝ) : E :=
  extendCurve hT A s (solutionExtension hτ hT u s) +
    extendCurve hT B s (solutionExtension hτ hT u (s - τ))

def IsSolution (η : C(HistoryInterval τ, E))
    (A B : C(VolterraInterval 0 T, E →L[𝕜] E))
    (u : C(SolutionInterval τ T, E)) : Prop :=
  (∀ t : HistoryInterval τ,
    u ⟨t, t.property.1, t.property.2.trans hT⟩ = η t) ∧
  ∀ t : VolterraInterval 0 T,
    u ⟨t, (neg_nonpos.mpr hτ.le).trans t.property.1, t.property.2⟩ =
      η ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩ +
        ∫ s in 0..(t : ℝ), field hτ hT A B u s

end

def UniqueSolvability : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (τ T : ℝ) (hτ : 0 < τ) (hT : 0 ≤ T) (η : C(HistoryInterval τ, E))
  (A B : C(VolterraInterval 0 T, E →L[𝕜] E)),
  ∃! u : C(SolutionInterval τ T, E), IsSolution hτ hT η A B u

/-- The continuous derivative field works at every positive junction, without
any exclusion of integral multiples of τ. At the final endpoint it is a left
within derivative; on the open interval it is an ordinary derivative. -/
def Regularity : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (τ T : ℝ) (hτ : 0 < τ) (hT : 0 ≤ T) (η : C(HistoryInterval τ, E))
  (A B : C(VolterraInterval 0 T, E →L[𝕜] E))
  (u : C(SolutionInterval τ T, E)), IsSolution hτ hT η A B u →
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  Continuous (field hτ hT A B u) ∧
  (∀ t ∈ Icc 0 T, HasDerivWithinAt (solutionExtension hτ hT u)
    (field hτ hT A B u t) (Icc 0 T) t) ∧
  (∀ t ∈ Ioo 0 T, HasDerivAt (solutionExtension hτ hT u)
    (field hτ hT A B u t) t) ∧
  ContDiffOn ℝ 1 (solutionExtension hτ hT u) (Ioo 0 T)

/-- At zero, two-sided differentiability with the history derivative is
exactly the explicit initial compatibility condition. T>0 is necessary for a
right time germ; the zero-interval existence theorem above has no such premise. -/
def InitialCompatibility : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (τ T : ℝ) (hτ : 0 < τ) (hT : 0 < T) (η : C(HistoryInterval τ, E))
  (A B : C(VolterraInterval 0 T, E →L[𝕜] E))
  (u : C(SolutionInterval τ T, E)), IsSolution hτ hT.le η A B u →
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  ∀ d : E, HasDerivWithinAt (extendCurve (neg_nonpos.mpr hτ.le) η)
    d (Icc (-τ) 0) 0 →
  (HasDerivAt (solutionExtension hτ hT.le u) d 0 ↔
    d = A ⟨0, le_rfl, hT.le⟩ (η ⟨0, neg_nonpos.mpr hτ.le, le_rfl⟩) +
      B ⟨0, le_rfl, hT.le⟩ (η ⟨-τ, le_rfl, neg_nonpos.mpr hτ.le⟩))

section Jets
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Recursive Leibniz expansion: shift either the coefficient jet or the
state jet at each differentiation. -/
def productJet : ℕ → (ℕ → E →L[𝕜] E) → (ℕ → E) → E
  | 0, A, U => A 0 (U 0)
  | n + 1, A, U => productJet n (fun k => A (k + 1)) U +
      productJet n A (fun k => U (k + 1))

def equationJet (n : ℕ) (A B : ℕ → E →L[𝕜] E) (U V : ℕ → E) : E :=
  productJet n A U + productJet n B V

end Jets

/-- These are derivatives of actual functions on the chosen one-sided domain,
not formal certificates for the delay solution. -/

def IsDerivativeTower {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : ℕ → ℝ → F) (s : Set ℝ) : Prop :=
  ∀ k < n, ∀ t ∈ s, HasDerivWithinAt (f k) (f (k + 1) t) s t

/-- Differentiating the actual coefficient and state towers differentiates
the recursively expanded RHS. V is the tower for t ↦ u(t-τ). -/
def JetDifferentiation : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (n : ℕ)
  (A B : ℕ → ℝ → E →L[𝕜] E) (U V : ℕ → ℝ → E) (s : Set ℝ),
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  IsDerivativeTower (n + 1)
    (fun k t => (A k t).restrictScalars ℝ) s →
  IsDerivativeTower (n + 1)
    (fun k t => (B k t).restrictScalars ℝ) s →
  IsDerivativeTower (n + 1) U s →
  IsDerivativeTower (n + 1) V s →
  ∀ t ∈ s, HasDerivWithinAt
    (fun r => equationJet n (fun k => A k r) (fun k => B k r)
      (fun k => U k r) (fun k => V k r))
    (equationJet (n + 1) (fun k => A k t) (fun k => B k t)
      (fun k => U k t) (fun k => V k t)) s t

/-- If lower jets already match at a junction, the first possible new jump
is B(c) times the preceding delayed jump. Applying this successively to
one-sided derivative towers records the history-compatibility mechanism. -/
def JumpPropagation : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] (n : ℕ)
  (A B : ℕ → E →L[𝕜] E) (UL UR VL VR : ℕ → E),
  (∀ k ≤ n, UR k = UL k) → (∀ k < n, VR k = VL k) →
  equationJet n A B UR VR - equationJet n A B UL VL = B 0 (VR n - VL n)

/-- Actual one-sided derivative towers of a solution obey every differentiated
version of the delay equation. Taking s to be either adjacent closed step
interval, and then using JumpPropagation, gives the compatibility propagation
at their common endpoint. No differentiability of the history is imposed on
the existence or C¹ theorems. -/
def SolutionJets : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (τ T : ℝ) (hτ : 0 < τ) (hT : 0 ≤ T) (η : C(HistoryInterval τ, E))
  (A B : C(VolterraInterval 0 T, E →L[𝕜] E))
  (u : C(SolutionInterval τ T, E)), IsSolution hτ hT η A B u →
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  ∀ (n : ℕ) (s : Set ℝ), s ⊆ Icc 0 T → UniqueDiffOn ℝ s →
  ∀ (AJ BJ : ℕ → ℝ → E →L[𝕜] E) (U V : ℕ → ℝ → E),
  (∀ t ∈ s, AJ 0 t = extendCurve hT A t) →
  (∀ t ∈ s, BJ 0 t = extendCurve hT B t) →
  (∀ t ∈ s, U 0 t = solutionExtension hτ hT u t) →
  (∀ t ∈ s, V 0 t = solutionExtension hτ hT u (t - τ)) →
  IsDerivativeTower n (fun k t => (AJ k t).restrictScalars ℝ) s →
  IsDerivativeTower n (fun k t => (BJ k t).restrictScalars ℝ) s →
  IsDerivativeTower (n + 1) U s → IsDerivativeTower n V s →
  ∀ k ≤ n, ∀ t ∈ s, U (k + 1) t =
    equationJet k (fun j => AJ j t) (fun j => BJ j t) (fun j => U j t) (fun j => V j t)

section Scalars
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def scalarCoefficient {T : ℝ} (a : C(VolterraInterval 0 T, 𝕜)) :
    C(VolterraInterval 0 T, E →L[𝕜] E) :=
  ⟨fun t => a t • ContinuousLinearMap.id 𝕜 E, a.continuous.smul continuous_const⟩

end Scalars

def ScalarUniqueSolvability : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (τ T : ℝ) (hτ : 0 < τ) (hT : 0 ≤ T) (η : C(HistoryInterval τ, E))
  (a b : C(VolterraInterval 0 T, 𝕜)), ∃! u : C(SolutionInterval τ T, E),
    IsSolution hτ hT η (scalarCoefficient a) (scalarCoefficient b) u

/-- τ=1, η=1, A=0, B=1. At t=1 the one-sided second derivatives
are 0 and 1 although the solution and its first derivative are continuous.
This realizes the failure of the initial compatibility 0 = 1. -/
def FailureExample : Prop :=
  let η : C(HistoryInterval 1, ℝ) := ContinuousMap.const _ 1
  let A : C(VolterraInterval 0 2, ℝ →L[ℝ] ℝ) := ContinuousMap.const _ 0
  let B : C(VolterraInterval 0 2, ℝ →L[ℝ] ℝ) :=
    ContinuousMap.const _ (ContinuousLinearMap.id ℝ ℝ)
  ∃ u : C(SolutionInterval 1 2, ℝ),
    IsSolution zero_lt_one zero_le_two η A B u ∧
    let x := solutionExtension zero_lt_one zero_le_two u
    (∀ t ∈ Icc 0 1, x t = 1 + t) ∧
    HasDerivWithinAt (deriv x) 0 (Icc (1 / 2) 1) 1 ∧
    HasDerivWithinAt (deriv x) 1 (Icc 1 (3 / 2)) 1 ∧
    ¬DifferentiableAt ℝ (deriv x) 1

/-- The method-of-steps smoothness bootstrap: smooth coefficients and the
already known delayed curve give one additional derivative on the current
one-sided step interval. Iterating over translated history intervals supplies
the actual derivative towers used in SolutionJets. -/
def SmoothStep : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (τ T : ℝ) (hτ : 0 < τ) (hT : 0 ≤ T) (η : C(HistoryInterval τ, E))
  (A B : C(VolterraInterval 0 T, E →L[𝕜] E))
  (u : C(SolutionInterval τ T, E)), IsSolution hτ hT η A B u →
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  ∀ (n : ℕ) (s : Set ℝ), s ⊆ Icc 0 T → UniqueDiffOn ℝ s →
  ContDiffOn ℝ n (fun t => (extendCurve hT A t).restrictScalars ℝ) s →
  ContDiffOn ℝ n (fun t => (extendCurve hT B t).restrictScalars ℝ) s →
  ContDiffOn ℝ n (fun t => solutionExtension hτ hT u (t - τ)) s →
  ContDiffOn ℝ (n + 1) (solutionExtension hτ hT u) s

end ExpandedFA.PartV.DelayModelSpec
