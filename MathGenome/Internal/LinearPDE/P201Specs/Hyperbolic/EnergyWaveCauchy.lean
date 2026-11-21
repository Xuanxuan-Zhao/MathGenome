import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.WaveMultipliers
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent statements for the whole-space forced wave Cauchy problem.
Time curves are defined on ℝ, but all solution conditions and uniqueness are
restricted to [0,∞). Endpoint derivatives are derivatives within that half-line.
The PDE below is tested on arbitrary spacetime tests, not just tensor products.
The scalar test pairing is linear (there is no conjugation in a distribution).
-/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal
namespace P201Specs.Wave.Cauchy

/-- Local Bochner L¹ on the closed positive half-line; no continuity of f. -/
def LocallyIntegrableForcing {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : ℝ → WholeL2 n 𝕜) : Prop :=
  ∀ T : ℝ, 0 ≤ T → IntegrableOn f (Icc 0 T)

/-- The two Duhamel terms are actual Bochner integrals in full H¹ and L². -/
def displacement {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (W : WaveOperators n 𝕜) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
    (f : ℝ → WholeL2 n 𝕜) (t : ℝ) : WholeH1 n 𝕜 :=
  W.C1 t g + W.S t h + ∫ s in Icc 0 t, W.S (t - s) (f s)

def velocity {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (W : WaveOperators n 𝕜) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
    (f : ℝ → WholeL2 n 𝕜) (t : ℝ) : WholeL2 n 𝕜 :=
  W.D t g + W.C0 t h + ∫ s in Icc 0 t, W.C0 (t - s) (f s)

/-- Smooth compact spacetime tests supported at strictly positive time. -/
abbrev SpacetimeTest (n : ℕ) (𝕜 : Type) [RCLike 𝕜] :=
  TestFunction (⟨Ioi (0 : ℝ) ×ˢ (univ : Set (Space n)),
    isOpen_Ioi.prod isOpen_univ⟩ : Opens (ℝ × Space n)) 𝕜 ⊤

/-- The transposed wave operator on a smooth spacetime test. -/
def testWaveOperator {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (φ : SpacetimeTest n 𝕜) (t : ℝ) (x : Space n) : 𝕜 :=
  deriv (fun s => deriv (fun r => φ (r, x)) s) t -
    (c ^ 2 : ℝ) • laplacian (fun y => φ (t, y)) x

/-- u_tt − c² Δu = f as a distribution on (0,∞) × ℝⁿ.
There is no hypothesis of a second strong time derivative. -/
def IsDistributionalWave {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (f : ℝ → WholeL2 n 𝕜) (u : ℝ → WholeH1 n 𝕜) : Prop :=
  ∀ φ : SpacetimeTest n 𝕜,
    (∫ t in Ioi (0 : ℝ), ∫ x : Space n,
      hUnderlying (⊤ : Domain n) 1 (u t) x * testWaveOperator c φ t x) =
    ∫ t in Ioi (0 : ℝ), ∫ x : Space n, f t x * φ (t, x)

/-- The complete comparison class, including one-sided initial derivative. -/
def IsEnergySolution {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
    (f : ℝ → WholeL2 n 𝕜) (u : ℝ → WholeH1 n 𝕜)
    (v : ℝ → WholeL2 n 𝕜) : Prop :=
  ContinuousOn u (Ici 0) ∧ ContinuousOn v (Ici 0) ∧
  (∀ t ∈ Ici (0 : ℝ),
    HasDerivWithinAt (fun s => hUnderlying (⊤ : Domain n) 1 (u s)) (v t) (Ici 0) t) ∧
  u 0 = g ∧ v 0 = h ∧ IsDistributionalWave c f u

/-- All data are quantified after choosing the genuine Fourier family.
The integrability assertions prevent use of a default, nonintegrable integral. -/
def cauchyForField (n : ℕ) (𝕜 : Type) [RCLike 𝕜] (c : ℝ)
    (κ : 𝕜 →L[ℝ] ℂ) : Prop :=
  ∃ W : WaveOperators n 𝕜, WaveFamilyLaws c κ W ∧
    ∀ (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜),
      LocallyIntegrableForcing f →
      (∀ t ∈ Ici (0 : ℝ),
        IntegrableOn (fun s => W.S (t - s) (f s)) (Icc 0 t) ∧
        IntegrableOn (fun s => W.C0 (t - s) (f s)) (Icc 0 t)) ∧
      IsEnergySolution c g h f (displacement W g h f) (velocity W g h f) ∧
      (∀ (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜),
        IsEnergySolution c g h f u v → ∀ t ∈ Ici (0 : ℝ),
          u t = displacement W g h f t ∧ v t = velocity W g h f t)

def energyWaveCauchyStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (c : ℝ), 0 < c →
    cauchyForField n ℝ c Complex.ofRealCLM ∧
    cauchyForField n ℂ c (ContinuousLinearMap.id ℝ ℂ)

/-- This is only the zero-forcing time regularity, not the wave PDE theorem. -/
def homogeneousRegularityStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ)
    (W : WaveOperators n 𝕜), WaveFamilyLaws c κ W →
    ∀ (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜),
      Continuous (displacement W g h 0) ∧ Continuous (velocity W g h 0) ∧
      (∀ t, HasDerivAt (fun s => hUnderlying (⊤ : Domain n) 1
        (displacement W g h 0 s)) (velocity W g h 0 t) t) ∧
      displacement W g h 0 0 = g ∧ velocity W g h 0 0 = h

def duhamelInitialStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ)
    (W : WaveOperators n 𝕜), WaveFamilyLaws c κ W →
    ∀ (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜),
      displacement W g h f 0 = g ∧ velocity W g h f 0 = h

def duhamelIntegrableStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ)
    (W : WaveOperators n 𝕜), WaveFamilyLaws c κ W →
    ∀ (f : ℝ → WholeL2 n 𝕜), LocallyIntegrableForcing f →
    ∀ (t : ℝ), 0 ≤ t →
      IntegrableOn (fun s => W.S (t - s) (f s)) (Icc 0 t) ∧
      IntegrableOn (fun s => W.C0 (t - s) (f s)) (Icc 0 t)

/-- Time regularity alone; this does not assume or assert the PDE. -/
def duhamelRegularityStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ)
    (W : WaveOperators n 𝕜), WaveFamilyLaws c κ W →
    ∀ (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜),
      LocallyIntegrableForcing f →
      ContinuousOn (displacement W g h f) (Ici 0) ∧
      ContinuousOn (velocity W g h f) (Ici 0) ∧
      (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun r => hUnderlying (⊤ : Domain n) 1
        (displacement W g h f r)) (velocity W g h f t) (Ici 0) t) ∧
      displacement W g h f 0 = g ∧ velocity W g h f 0 = h

/-- The complete construction and time regularity, without the PDE and
comparison conclusions that are required by `energyWaveCauchyStatement`. -/
def timeRegularForField (n : ℕ) (𝕜 : Type) [RCLike 𝕜] (c : ℝ)
    (κ : 𝕜 →L[ℝ] ℂ) : Prop :=
  ∃ W : WaveOperators n 𝕜, WaveFamilyLaws c κ W ∧
    ∀ (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜),
      LocallyIntegrableForcing f →
      (∀ t ∈ Ici (0 : ℝ),
        IntegrableOn (fun s => W.S (t - s) (f s)) (Icc 0 t) ∧
        IntegrableOn (fun s => W.C0 (t - s) (f s)) (Icc 0 t)) ∧
      ContinuousOn (displacement W g h f) (Ici 0) ∧
      ContinuousOn (velocity W g h f) (Ici 0) ∧
      (∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun r => hUnderlying (⊤ : Domain n) 1
        (displacement W g h f r)) (velocity W g h f t) (Ici 0) t) ∧
      displacement W g h f 0 = g ∧ velocity W g h f 0 = h

def waveTimeRegularityStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (c : ℝ), 0 < c →
    timeRegularForField n ℝ c Complex.ofRealCLM ∧
    timeRegularForField n ℂ c (ContinuousLinearMap.id ℝ ℂ)

end P201Specs.Wave.Cauchy
