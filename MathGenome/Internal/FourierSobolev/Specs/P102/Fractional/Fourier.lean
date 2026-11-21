import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Space
import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Density
import MathGenome.Internal.FourierSobolev.Specs.P102.U3.Plancherel
import Mathlib.Analysis.Distribution.Sobolev

/-! Independent objects and full statements for paper.tex:2268–2320.
All integrals defining energies take values in ENNReal; no finite-energy
hypothesis is imposed on the Fourier identity. Real scalars are included by
the canonical norm-preserving embedding into complex scalars before Plancherel.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace P102.Fractional

/-- Transport the whole-space graph's underlying L² class to Lebesgue measure. -/
def wholeSpaceL2 {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (domainMeasure (Set.univ : Set (Domain d)))) :
    Lp 𝕜 2 (volume : Measure (Domain d)) :=
  Lp.compMeasurePreserving id
    (by simpa only [domainMeasure, Measure.restrict_univ] using
      (MeasurePreserving.id (volume : Measure (Domain d)))) u

/-- Complexification of a real or complex L² class, without changing its norm. -/
def complexifyL2 {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) : Lp ℂ 2 (volume : Measure (Domain d)) :=
  (RCLike.map 𝕜 ℂ).compLp u

/-- A representative of the canonical U3 Plancherel transform. -/
def fourierRepresentative {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) : Domain d → ℂ :=
  P102.Specs.U3.Plancherel.fourierL2_value (Domain d) ℂ (complexifyL2 u)

/-- The directional multiplier integral; the spatial singularity has value zero. -/
def directionalIntegral {d : ℕ} (s : ℝ) (ξ : Domain d) : ℝ≥0∞ :=
  ∫⁻ h : Domain d, if h = 0 then 0 else
    ‖Complex.exp ((2 * Real.pi * inner ℝ h ξ : ℝ) * Complex.I) - 1‖ₑ ^ (2 : ℕ) /
      ENNReal.ofReal ‖h‖ ^ ((d : ℝ) + 2 * s)

/-- The source constant with its explicit first coordinate and 2π normalization. -/
def fourierConstant (d : ℕ) (hd : 0 < d) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ h : Domain d, if h = 0 then 0 else
    ‖Complex.exp ((2 * Real.pi * h ⟨0, hd⟩ : ℝ) * Complex.I) - 1‖ₑ ^ (2 : ℕ) /
      ENNReal.ofReal ‖h‖ ^ ((d : ℝ) + 2 * s)

/-- Homogeneous Fourier moment, allowed to be infinite. -/
def fourierMoment {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (s : ℝ)
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal ‖ξ‖ ^ (2 * s) * ‖fourierRepresentative u ξ‖ₑ ^ (2 : ℕ)

/-- Squared Bessel norm with an explicit frequency scale c.
The manuscript uses c = 4π²; Mathlib uses c = 1. -/
def besselEnergy {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (c s : ℝ)
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal ((1 + c * ‖ξ‖ ^ (2 : ℕ)) ^ s) *
    ‖fourierRepresentative u ξ‖ₑ ^ (2 : ℕ)

/-- The Bessel-potential Hˢ condition using the manuscript's Fourier convention. -/
def MemHs {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (s : ℝ)
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) : Prop :=
  besselEnergy (4 * Real.pi ^ 2) s u < ∞

/-- Hˢ norm on finite-energy classes. Its squared spectral integral has weight
(1 + 4π²|ξ|²)^s. -/
def hsNorm {d : ℕ} {𝕜 : Type*} [RCLike 𝕜] (s : ℝ)
    (u : Lp 𝕜 2 (volume : Measure (Domain d))) : ℝ :=
  Real.sqrt (besselEnergy (4 * Real.pi ^ 2) s u).toReal

end P102.Fractional

namespace Specs.P102.Fractional.Fourier
open _root_.P102.Fractional

/-- The zero frequency is treated before any rotation or division by |ξ|. -/
def ZeroFrequency : Prop := ∀ (d : ℕ) (s : ℝ), directionalIntegral (d := d) s 0 = 0

def ConstantBounds : Prop := ∀ (d : ℕ) (hd : 0 < d) (s : ℝ),
  0 < s → s < 1 → 0 < fourierConstant d hd s ∧ fourierConstant d hd s < ∞

def DirectionalScaling : Prop := ∀ (d : ℕ) (hd : 0 < d) (s : ℝ),
  0 < s → s < 1 → ∀ ξ : Domain d,
    directionalIntegral s ξ = fourierConstant d hd s * ENNReal.ofReal ‖ξ‖ ^ (2 * s)

/-- The direct Plancherel/Tonelli calculation before evaluating the kernel.
This is a proof interface, without a finite Gagliardo-energy assumption. -/
def DirectionalPlancherelIdentity : Prop :=
  ∀ (d : ℕ) (_hd : 0 < d) (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
    0 < s → s < 1 → ∀ u : Lp 𝕜 2 (volume : Measure (Domain d)),
      energy Set.univ s 2 u = ∫⁻ ξ,
        directionalIntegral s ξ * ‖fourierRepresentative u ξ‖ₑ ^ (2 : ℕ)

/-- The full identity, including inputs with infinite seminorm or Fourier moment. -/
def FourierIdentity : Prop := ∀ (d : ℕ) (hd : 0 < d) (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
  0 < s → s < 1 → ∀ u : Lp 𝕜 2 (volume : Measure (Domain d)),
    energy Set.univ s 2 u = fourierConstant d hd s * fourierMoment s u

/-- Quantitative comparison of all three pointwise squared-norm weights. -/
def WeightComparison : Prop := ∀ (s r : ℝ), 0 ≤ s → 0 ≤ r →
  (1 + r ^ (2 * s)) ≤ 2 * (1 + r ^ (2 : ℕ)) ^ s ∧
  (1 + r ^ (2 : ℕ)) ^ s ≤ (2 : ℝ) ^ s * (1 + r ^ (2 * s))

/-- Explicit bridge from the Mathlib frequency scale to the source scale. -/
def NormalizationComparison : Prop := ∀ (s r : ℝ), 0 ≤ s → 0 ≤ r →
  (1 + r ^ (2 : ℕ)) ^ s ≤ (1 + 4 * Real.pi ^ 2 * r ^ (2 : ℕ)) ^ s ∧
  (1 + 4 * Real.pi ^ 2 * r ^ (2 : ℕ)) ^ s ≤
    (4 * Real.pi ^ 2) ^ s * (1 + r ^ (2 : ℕ)) ^ s

def BesselEnergyComparison : Prop := ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
  0 ≤ s → ∀ u : Lp 𝕜 2 (volume : Measure (Domain d)),
    besselEnergy 1 s u ≤ besselEnergy (4 * Real.pi ^ 2) s u ∧
    besselEnergy (4 * Real.pi ^ 2) s u ≤
      ENNReal.ofReal ((4 * Real.pi ^ 2) ^ s) * besselEnergy 1 s u

/-- Bridge to Mathlib's actual Bessel-potential distribution condition, whose
multiplier is (1+|ξ|²)^(s/2). The input remains the original L² class. -/
def LibraryBesselIdentification : Prop := ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
  0 ≤ s → ∀ u : Lp 𝕜 2 (volume : Measure (Domain d)),
    MemHs s u ↔ TemperedDistribution.MemSobolev s 2
      (Lp.toTemperedDistribution (complexifyL2 u))

/-- Parseval for the chosen representatives, including real inputs. -/
def FourierMass : Prop := ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
  (u : Lp 𝕜 2 (volume : Measure (Domain d))),
    (∫⁻ ξ, ‖fourierRepresentative u ξ‖ₑ ^ (2 : ℕ)) = ‖u‖ₑ ^ (2 : ℕ)

def MomentEnergyComparison : Prop := ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
  0 ≤ s → ∀ u : Lp 𝕜 2 (volume : Measure (Domain d)),
    ‖u‖ₑ ^ (2 : ℕ) + fourierMoment s u ≤ 2 * besselEnergy 1 s u ∧
    besselEnergy 1 s u ≤ ENNReal.ofReal ((2 : ℝ) ^ s) *
      (‖u‖ₑ ^ (2 : ℕ) + fourierMoment s u)

def MomentFiniteness : Prop := ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
  0 ≤ s → ∀ u : Lp 𝕜 2 (volume : Measure (Domain d)),
    MemHs s u ↔ fourierMoment s u < ∞

/-- Equality as spaces of the original L² classes. -/
def SpaceIdentification : Prop := ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
  0 < s → s < 1 → ∀ u : Lp 𝕜 2 (domainMeasure (Set.univ : Set (Domain d))),
    (∃ v : Space 𝕜 Set.univ s 2, firstProjection v = u) ↔
      MemHs s (wholeSpaceL2 u)

/-- Equivalence with the exact upstream Gagliardo sum norm. -/
def NormEquivalence : Prop := ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜] (s : ℝ),
  0 < s → s < 1 → ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    ∀ v : Space 𝕜 (Set.univ : Set (Domain d)) s 2,
      A * ‖v‖ ≤ hsNorm s (wholeSpaceL2 (firstProjection v)) ∧
      hsNorm s (wholeSpaceL2 (firstProjection v)) ≤ B * ‖v‖


/-- The complete unnumbered proposition retains the prerequisite results. -/
def CompleteProposition : Prop :=
  Specs.P102.Fractional.banach.{0} ∧
  Specs.P102.Fractional.Density.SmoothCompactMembership ∧
  Specs.P102.Fractional.Density.SmoothCompactDensity ∧
  ConstantBounds ∧ FourierIdentity ∧ LibraryBesselIdentification ∧
  SpaceIdentification ∧ NormEquivalence

end Specs.P102.Fractional.Fourier
