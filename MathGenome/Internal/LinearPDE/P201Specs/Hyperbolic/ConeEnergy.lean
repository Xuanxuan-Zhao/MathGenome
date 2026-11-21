import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.WaveEnergy
import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.SmoothCone
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent specification of paper.tex, thm:pde-wave-cone (W04).
The local quantities use restrictions of actual L² classes, including the
canonical distributional spatial gradient. No moving-sphere trace is assumed.
All solution hypotheses are those of W03, with local Bochner L¹ forcing.
-/
noncomputable section
open Set MeasureTheory Metric
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201Specs.Wave.Cone

/-- Restriction is a contraction of actual L² equivalence classes. -/
def restrictL2 {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Set (Space n)) :
    MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n)) →L[ℝ]
      MeasureTheory.Lp E 2 ((domainMeasure (⊤ : Domain n)).restrict B) :=
  LpToLpRestrictCLM (Space n) E ℝ (domainMeasure ⊤) 2 B

/-- The local L² norm is independent of the representative of the L² class. -/
def restrictedNorm {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Set (Space n)) (w : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) : ℝ :=
  ‖restrictL2 B w‖

/-- The shrinking ball B_s = B(a,R-cs), shared with the classical theorem. -/
abbrev coneBall := @P201Specs.SmoothCone.coneBall

/-- Exactly half the local kinetic and weak-gradient energies. -/
def localEnergy {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R : ℝ)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜) (s : ℝ) : ℝ :=
  (restrictedNorm (coneBall c a R s) (v s) ^ 2 +
    c ^ 2 * restrictedNorm (coneBall c a R s) (hGradient (u s)) ^ 2) / 2

/-- The L² norm of 1_{B_s} f(s). -/
def localForcingNorm {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R : ℝ) (f : ℝ → WholeL2 n 𝕜) (s : ℝ) : ℝ :=
  restrictedNorm (coneBall c a R s) (f s)

/-- Equality on a measurable region is equality almost everywhere, not
pointwise equality of arbitrary representatives. -/
def EqualOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (B : Set (Space n)) (w z : WholeL2 n 𝕜) : Prop :=
  (w : Space n → 𝕜) =ᵐ[volume.restrict B] z

def VanishesOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (B : Set (Space n)) (w : WholeL2 n 𝕜) : Prop :=
  ∀ᵐ x ∂volume.restrict B, w x = 0

/-- Essential support in the closed set K. This is an a.e. statement on its
entire complement, rather than pointwise assertions with varying null sets. -/
def SupportedIn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (K : Set (Space n)) (w : WholeL2 n 𝕜) : Prop :=
  VanishesOn Kᶜ w

/-- Full local energy bound, with finiteness of the time integral. -/
def localEnergyEstimateStatement : Prop :=
  ∀ {n : ℕ} (𝕜 : Type) [RCLike 𝕜], 1 ≤ n →
    ∀ (c : ℝ) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
      (f : ℝ → WholeL2 n 𝕜) (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜),
      0 < c → LocallyIntegrableForcing f → IsEnergySolution c g h f u v →
      ∀ (a : Space n) (R t : ℝ), 0 < R → 0 ≤ t → t < R / c →
        IntegrableOn (localForcingNorm c a R f) (Icc 0 t) ∧
        Real.sqrt (2 * localEnergy c a R u v t) ≤
          Real.sqrt (2 * localEnergy c a R u v 0) +
            ∫ s in (0 : ℝ)..t, localForcingNorm c a R f s

/-- Zero displacement AND zero velocity on the initial ball, and source
vanishing for almost every time and almost every point of its cone slice. -/
def vanishingStatement : Prop :=
  ∀ {n : ℕ} (𝕜 : Type) [RCLike 𝕜], 1 ≤ n →
    ∀ (c : ℝ) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
      (f : ℝ → WholeL2 n 𝕜) (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜),
      0 < c → LocallyIntegrableForcing f → IsEnergySolution c g h f u v →
      ∀ (a : Space n) (R : ℝ), 0 < R →
        VanishesOn (coneBall c a R 0) (hUnderlying ⊤ 1 g) →
        VanishesOn (coneBall c a R 0) h →
        (∀ᵐ s ∂volume.restrict (Ico 0 (R / c)),
          VanishesOn (coneBall c a R s) (f s)) →
        ∀ t : ℝ, 0 ≤ t → t < R / c →
          VanishesOn (coneBall c a R t) (hUnderlying ⊤ 1 (u t))

/-- Domain of dependence for two solutions with data and sources equal on
this cone; no assumptions are imposed outside it. -/
def domainOfDependenceStatement : Prop :=
  ∀ {n : ℕ} (𝕜 : Type) [RCLike 𝕜], 1 ≤ n →
    ∀ (c : ℝ) (g₁ g₂ : WholeH1 n 𝕜) (h₁ h₂ : WholeL2 n 𝕜)
      (f₁ f₂ : ℝ → WholeL2 n 𝕜)
      (u₁ u₂ : ℝ → WholeH1 n 𝕜) (v₁ v₂ : ℝ → WholeL2 n 𝕜),
      0 < c → LocallyIntegrableForcing f₁ → LocallyIntegrableForcing f₂ →
      IsEnergySolution c g₁ h₁ f₁ u₁ v₁ → IsEnergySolution c g₂ h₂ f₂ u₂ v₂ →
      ∀ (a : Space n) (R : ℝ), 0 < R →
        EqualOn (coneBall c a R 0) (hUnderlying ⊤ 1 g₁) (hUnderlying ⊤ 1 g₂) →
        EqualOn (coneBall c a R 0) h₁ h₂ →
        (∀ᵐ s ∂volume.restrict (Ico 0 (R / c)),
          EqualOn (coneBall c a R s) (f₁ s) (f₂ s)) →
        ∀ t : ℝ, 0 ≤ t → t < R / c →
          EqualOn (coneBall c a R t) (hUnderlying ⊤ 1 (u₁ t))
            (hUnderlying ⊤ 1 (u₂ t))

/-- Essential finite speed of propagation for both initial data. -/
def finiteSpeedStatement : Prop :=
  ∀ {n : ℕ} (𝕜 : Type) [RCLike 𝕜], 1 ≤ n →
    ∀ (c : ℝ) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
      (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜),
      0 < c → IsEnergySolution c g h 0 u v →
      ∀ (a : Space n) (R₀ : ℝ), 0 ≤ R₀ →
        SupportedIn (closedBall a R₀) (hUnderlying ⊤ 1 g) →
        SupportedIn (closedBall a R₀) h →
        ∀ t : ℝ, 0 ≤ t →
          SupportedIn (closedBall a (R₀ + c * t)) (hUnderlying ⊤ 1 (u t))

/-- Local classical applicability, with no global finite-energy assumption. -/
def localSmoothApplicabilityStatement : Prop :=
  P201Specs.SmoothCone.localEnergyEstimateStatement ∧
  P201Specs.SmoothCone.vanishingStatement ∧
  P201Specs.SmoothCone.localUniquenessStatement

end P201Specs.Wave.Cone
