import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.EnergyWaveCauchy
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! Independent specification of paper.tex, Theorem `thm:pde-wave-energy`.
The shared spaces use the full H¹ norm. All time assertions include zero,
and no regularity of the forcing beyond local Bochner L¹ is imposed. -/
noncomputable section
open MeasureTheory Set
open P201Specs.Wave P201Specs.Wave.Cauchy
namespace P201Specs.Wave.Energy

/-- The L² norm of the genuine spatial weak gradient. -/
def gradientSize {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH1 n 𝕜) : ℝ := ‖hGradient u‖

def magnitude {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) : ℝ :=
  Real.sqrt (‖v‖ ^ 2 + c ^ 2 * (gradientSize u) ^ 2)

def energy {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) : ℝ :=
  magnitude c u v ^ 2 / 2

/-- The real inner product is the real part of the complex L² pairing. -/
def sourceWork {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f v : ℝ → WholeL2 n 𝕜) (s : ℝ) : ℝ := inner ℝ (f s) (v s)

abbrev gradientSizeType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → WholeH1 n 𝕜 → ℝ
abbrev stateQuantityType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  ℝ → WholeH1 n 𝕜 → WholeL2 n 𝕜 → ℝ
abbrev sourceWorkType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  (ℝ → WholeL2 n 𝕜) → (ℝ → WholeL2 n 𝕜) → ℝ → ℝ

/-- Work integrability and the exact identity on all forward subintervals,
together with absolute continuity on every compact time interval. -/
def EnergyBalance {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ)
    (f : ℝ → WholeL2 n 𝕜) (u : ℝ → WholeH1 n 𝕜)
    (v : ℝ → WholeL2 n 𝕜) : Prop :=
  (∀ T : ℝ, 0 ≤ T →
    AbsolutelyContinuousOnInterval (fun s => energy c (u s) (v s)) 0 T) ∧
  ∀ r t : ℝ, 0 ≤ r → r ≤ t →
    IntegrableOn (sourceWork f v) (Icc r t) ∧
    energy c (u t) (v t) - energy c (u r) (v r) =
      ∫ s in r..t, sourceWork f v s

/-- Both remaining displayed inequalities, with finite integrals. -/
def EnergyEstimates {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ)
    (f : ℝ → WholeL2 n 𝕜) (u : ℝ → WholeH1 n 𝕜)
    (v : ℝ → WholeL2 n 𝕜) : Prop :=
  ∀ r t : ℝ, 0 ≤ r → r ≤ t →
    IntegrableOn (fun s => ‖f s‖) (Icc r t) ∧
    IntegrableOn (fun s => magnitude c (u s) (v s)) (Icc r t) ∧
    magnitude c (u t) (v t) ≤ magnitude c (u r) (v r) + ∫ s in r..t, ‖f s‖ ∧
    ‖hUnderlying ⊤ 1 (u t)‖ ≤ ‖hUnderlying ⊤ 1 (u r)‖ +
      ∫ s in r..t, magnitude c (u s) (v s)

/-- Uniform H¹ × L² stability on [0,T]. The forcing distance is its
Bochner L¹ distance, so this is continuity in precisely C_t H¹ ∩ C¹_t L²
against H¹ × L² × L¹_t L², with no stronger forcing topology. -/
def UniformStability {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (W : WaveOperators n 𝕜) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧
    ∀ (g₁ g₂ : WholeH1 n 𝕜) (h₁ h₂ : WholeL2 n 𝕜)
      (f₁ f₂ : ℝ → WholeL2 n 𝕜),
      LocallyIntegrableForcing f₁ → LocallyIntegrableForcing f₂ →
      ∀ t ∈ Icc 0 T,
        ‖displacement W g₁ h₁ f₁ t - displacement W g₂ h₂ f₂ t‖ +
          ‖velocity W g₁ h₁ f₁ t - velocity W g₂ h₂ f₂ t‖ ≤
        K * (‖g₁ - g₂‖ + ‖h₁ - h₂‖ + ∫ s in Icc 0 T, ‖f₁ s - f₂ s‖)

/-- Existence, time topology, initial traces, distributional PDE, uniqueness,
all three displayed formulas, conservation, and continuous dependence. -/
def energyForField (n : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) : Prop :=
  ∃ W : WaveOperators n 𝕜, WaveFamilyLaws c κ W ∧
    UniformStability W ∧
    ∀ (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜),
      LocallyIntegrableForcing f →
      (∀ t ∈ Ici (0 : ℝ),
        IntegrableOn (fun s => W.S (t-s) (f s)) (Icc 0 t) ∧
        IntegrableOn (fun s => W.C0 (t-s) (f s)) (Icc 0 t)) ∧
      IsEnergySolution c g h f (displacement W g h f) (velocity W g h f) ∧
      (∀ u v, IsEnergySolution c g h f u v → ∀ t ∈ Ici (0 : ℝ),
        u t = displacement W g h f t ∧ v t = velocity W g h f t) ∧
      EnergyBalance c f (displacement W g h f) (velocity W g h f) ∧
      EnergyEstimates c f (displacement W g h f) (velocity W g h f) ∧
      (f = 0 → ∀ r t : ℝ, 0 ≤ r → r ≤ t →
        energy c (displacement W g h f t) (velocity W g h f t) =
        energy c (displacement W g h f r) (velocity W g h f r))

def waveEnergyStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ c : ℝ, 0 < c →
    energyForField n ℝ c Complex.ofRealCLM ∧
    energyForField n ℂ c (ContinuousLinearMap.id ℝ ℂ)

/-- Supporting obligations are stated for the entire original solution class. -/
def workIntegrableStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (f v : ℝ → WholeL2 n 𝕜),
    LocallyIntegrableForcing f → ContinuousOn v (Ici 0) →
    ∀ r t : ℝ, 0 ≤ r → r ≤ t → IntegrableOn (sourceWork f v) (Icc r t)

def displacementEstimateStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ)
    (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜),
    IsEnergySolution c g h f u v →
    ∀ r t : ℝ, 0 ≤ r → r ≤ t →
      ‖hUnderlying ⊤ 1 (u t)‖ ≤ ‖hUnderlying ⊤ 1 (u r)‖ +
        ∫ s in r..t, magnitude c (u s) (v s)

def uniformStabilityStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ)
    (W : WaveOperators n 𝕜), WaveFamilyLaws c κ W → UniformStability W

def homogeneousConservationStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ), 0 < c →
    ∀ (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
      (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜),
      IsEnergySolution c g h 0 u v →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → energy c (u t) (v t) = energy c (u r) (v r)

def estimatesOfBalanceStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ)
    (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜),
    LocallyIntegrableForcing f → IsEnergySolution c g h f u v →
    EnergyBalance c f u v → EnergyEstimates c f u v

/-- The balance property has the original forcing hypothesis
and the full comparison class, with no assumed derivative of the velocity. -/
def balanceForField (n : ℕ) (𝕜 : Type) [RCLike 𝕜] (c : ℝ) : Prop :=
  ∀ (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜),
    LocallyIntegrableForcing f → IsEnergySolution c g h f u v → EnergyBalance c f u v

def assemblyStatement : Prop :=
  (∀ n : ℕ, 1 ≤ n → ∀ c : ℝ, 0 < c →
    balanceForField n ℝ c ∧ balanceForField n ℂ c) → waveEnergyStatement

end P201Specs.Wave.Energy
