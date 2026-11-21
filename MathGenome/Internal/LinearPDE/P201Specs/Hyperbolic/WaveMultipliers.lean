import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Function.Holder

/-! Independent specifications for the Fourier-multiplier part of W03.
The whole-space Sobolev space below is exactly the shared weak-derivative graph.
`waveMultipliersStatement` records the full real and complex operator theorem,
in addition to the scalar and L² statements. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform
namespace P201Specs.Wave

/-- Angular frequency for the manuscript's negative 2π Fourier phase. -/
def frequency (n : ℕ) (c : ℝ) (ξ : Space n) : ℝ := 2 * Real.pi * c * ‖ξ‖

def cosineSymbol (t w : ℝ) : ℝ := Real.cos (t * w)

/-- The zero-frequency value is t, including when t is negative. -/
def sineSymbol (t w : ℝ) : ℝ := if w = 0 then t else Real.sin (t * w) / w

def cosineDerivativeSymbol (t w : ℝ) : ℝ := -w * Real.sin (t * w)

abbrev frequencyType := (n : ℕ) → ℝ → Space n → ℝ
abbrev scalarSymbolType := ℝ → ℝ → ℝ

def scalarBoundsStatement : Prop := ∀ t w : ℝ,
    |sineSymbol t w| ≤ |t| ∧ |w * sineSymbol t w| ≤ 1 ∧ |cosineSymbol t w| ≤ 1

def scalarDerivativesStatement : Prop := ∀ t w : ℝ,
    HasDerivAt (fun s => sineSymbol s w) (cosineSymbol t w) t ∧
    HasDerivAt (fun s => cosineSymbol s w) (cosineDerivativeSymbol t w) t

def scalarContinuityStatement : Prop :=
    Continuous (fun p : ℝ × ℝ => sineSymbol p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => cosineSymbol p.1 p.2)

def scalarInitialStatement : Prop := ∀ w : ℝ,
    sineSymbol 0 w = 0 ∧ cosineSymbol 0 w = 1 ∧ cosineDerivativeSymbol 0 w = 0

abbrev FrequencyL2 (n : ℕ) := MeasureTheory.Lp (α := Space n) ℂ 2 volume
abbrev WholeL2 (n : ℕ) (𝕜 : Type) [RCLike 𝕜] := Lp 𝕜 (⊤ : Domain n) 2
abbrev WholeH1 (n : ℕ) (𝕜 : Type) [RCLike 𝕜] := H 𝕜 (⊤ : Domain n) 1

/-- The genuine Plancherel-conjugated L² multipliers. This partial interface
is useful independently of the H¹ range theorem. -/
def l2BoundedMultipliersStatement : Prop := ∀ (n : ℕ) (c : ℝ),
  ∃ C S : ℝ → FrequencyL2 n →L[ℂ] FrequencyL2 n,
    (∀ t f, (𝓕 (C t f) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (cosineSymbol t (frequency n c ξ) : ℂ) * (𝓕 f : FrequencyL2 n) ξ) ∧
    (∀ t f, (𝓕 (S t f) : FrequencyL2 n) =ᵐ[volume]
      fun ξ => (sineSymbol t (frequency n c ξ) : ℂ) * (𝓕 f : FrequencyL2 n) ξ) ∧
    (∀ t, ‖C t‖ ≤ 1 ∧ ‖S t‖ ≤ |t|) ∧
    C 0 = ContinuousLinearMap.id ℂ _ ∧ S 0 = 0 ∧
    (∀ f, Continuous (fun t => C t f)) ∧ (∀ f, Continuous (fun t => S t f)) ∧
    (∀ t f, HasDerivAt (fun s => S s f) (C t f) t) ∧
    (∀ t (f v : FrequencyL2 n),
      (v : Space n → ℂ) =ᵐ[volume]
        (fun ξ => (frequency n c ξ : ℂ) * (𝓕 f : FrequencyL2 n) ξ) →
      ∃ d : FrequencyL2 n, HasDerivAt (fun s => C s f) d t ∧
        (𝓕 d : FrequencyL2 n) =ᵐ[volume]
          fun ξ => (cosineDerivativeSymbol t (frequency n c ξ) : ℂ) *
            (𝓕 f : FrequencyL2 n) ξ)

/-- Remove only the restriction of volume to the whole space. -/
def wholeL2Standard (n : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    WholeL2 n 𝕜 ≃ₗᵢ[𝕜] MeasureTheory.Lp (α := Space n) 𝕜 2 volume where
  __ := MeasureTheory.Lp.compMeasurePreservingₗᵢ 𝕜 id (by
    change MeasurePreserving id volume (volume.restrict Set.univ)
    simpa only [Measure.restrict_univ] using MeasurePreserving.id volume)
  invFun := MeasureTheory.Lp.compMeasurePreserving id (by
    change MeasurePreserving id (volume.restrict Set.univ) volume
    simpa only [Measure.restrict_univ] using MeasurePreserving.id volume)
  left_inv f := by
    change MeasureTheory.Lp.compMeasurePreserving _ _
      (MeasureTheory.Lp.compMeasurePreserving _ _ f) = f
    rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply]
    exact MeasureTheory.Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change MeasureTheory.Lp.compMeasurePreserving _ _
      (MeasureTheory.Lp.compMeasurePreserving _ _ f) = f
    rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply]
    exact MeasureTheory.Lp.compMeasurePreserving_id_apply f

/-- The L² Fourier transform after a specified real-linear scalar embedding.
The final statement uses the identity for ℂ and ofReal for ℝ. -/
def embeddedFourier {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (κ : 𝕜 →L[ℝ] ℂ) (f : WholeL2 n 𝕜) : FrequencyL2 n :=
  𝓕 (κ.compLp (wholeL2Standard n 𝕜 f))

/-- Operator data, containing no proof certificates. -/
structure WaveOperators (n : ℕ) (𝕜 : Type) [RCLike 𝕜] where
  C0 : ℝ → WholeL2 n 𝕜 →L[𝕜] WholeL2 n 𝕜
  C1 : ℝ → WholeH1 n 𝕜 →L[𝕜] WholeH1 n 𝕜
  S : ℝ → WholeL2 n 𝕜 →L[𝕜] WholeH1 n 𝕜
  D : ℝ → WholeH1 n 𝕜 →L[𝕜] WholeL2 n 𝕜

/-- Full intended operator properties; in particular no Sobolev/Fourier bridge
is an extra hypothesis of the final theorem. -/
def WaveFamilyLaws {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (c : ℝ)
    (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜) : Prop :=
  let U := hUnderlying (𝕜 := 𝕜) (⊤ : Domain n) 1
  (∀ t f, (embeddedFourier κ (W.C0 t f) : Space n → ℂ) =ᵐ[volume]
      fun ξ => (cosineSymbol t (frequency n c ξ) : ℂ) * embeddedFourier κ f ξ) ∧
  (∀ t g, U (W.C1 t g) = W.C0 t (U g)) ∧
  (∀ t h, (embeddedFourier κ (U (W.S t h)) : Space n → ℂ) =ᵐ[volume]
      fun ξ => (sineSymbol t (frequency n c ξ) : ℂ) * embeddedFourier κ h ξ) ∧
  (∀ t g, (embeddedFourier κ (W.D t g) : Space n → ℂ) =ᵐ[volume]
      fun ξ => (cosineDerivativeSymbol t (frequency n c ξ) : ℂ) *
        embeddedFourier κ (U g) ξ) ∧
  (∀ t, ‖W.C0 t‖ ≤ 1 ∧ ‖W.C1 t‖ ≤ 1 ∧
      ‖W.S t‖ ≤ Real.sqrt (t ^ 2 + c⁻¹ ^ 2) ∧ ‖W.D t‖ ≤ c) ∧
  (∀ f, Continuous (fun t => W.C0 t f)) ∧
  (∀ g, Continuous (fun t => W.C1 t g)) ∧
  (∀ h, Continuous (fun t => W.S t h)) ∧
  (∀ g, Continuous (fun t => W.D t g)) ∧
  (∀ t g, HasDerivAt (fun s => U (W.C1 s g)) (W.D t g) t) ∧
  (∀ t h, HasDerivAt (fun s => U (W.S s h)) (W.C0 t h) t) ∧
  W.C0 0 = ContinuousLinearMap.id 𝕜 _ ∧
  W.C1 0 = ContinuousLinearMap.id 𝕜 _ ∧ W.S 0 = 0 ∧ W.D 0 = 0

def waveMultipliersStatement : Prop := ∀ (n : ℕ), 1 ≤ n → ∀ (c : ℝ), 0 < c →
    (∃ W : WaveOperators n ℂ, WaveFamilyLaws c (ContinuousLinearMap.id ℝ ℂ) W) ∧
    (∃ W : WaveOperators n ℝ, WaveFamilyLaws c Complex.ofRealCLM W)

end P201Specs.Wave
