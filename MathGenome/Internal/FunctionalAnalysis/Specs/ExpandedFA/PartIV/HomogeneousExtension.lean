import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HomogeneousMeromorphic
import Mathlib.Analysis.Distribution.TestFunction

/-! Independent statements for `paper.tex`, `fa2:p4:homogeneous-extension`.
The ordinary distribution conclusions quantify over the entire continuous dual
of the native LF test space. Temperedness is required of the constructed finite
part, and is not an assumption on competing extensions. The Euclidean norm is
the same one used by the accepted meromorphic family and spherical measure. -/

open MeasureTheory TopologicalSpace
open scoped SchwartzMap ContDiff Distributions Topology

noncomputable section

namespace ExpandedFA.PartIV.HomogeneousExtension

open ExpandedFA.Fourier ExpandedFA.PartIV.HomogeneousMeromorphic

abbrev CompactTest (d : ℕ) := TestFunction (⊤ : Opens (Euclidean d)) ℂ ⊤
abbrev Distribution (d : ℕ) := CompactTest d →L[ℂ] ℂ

def testToSchwartz {d : ℕ} (φ : CompactTest d) : Schwartz ℂ d :=
  φ.hasCompactSupport.toSchwartzMap φ.contDiff

/-- The genuine compactly supported test `x ↦ φ(x/a)`. -/
def compactTestDilation {d : ℕ} (a : ℝ) (ha : 0 < a) (φ : CompactTest d) :
    CompactTest d where
  toFun x := φ (a⁻¹ • x)
  contDiff' := φ.contDiff.comp (scalingEquiv a⁻¹ (inv_ne_zero ha.ne')).contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph
    (scalingEquiv a⁻¹ (inv_ne_zero ha.ne')).toHomeomorph
  tsupport_subset' := Set.subset_univ _

/-- Source dilation, expressed through every compact test. -/
def Homogeneous {d : ℕ} (u : Distribution d) (lam : ℂ) : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (φ : CompactTest d),
    ((a : ℂ) ^ d)⁻¹ * u (compactTestDilation a ha φ) = (a : ℂ) ^ lam * u φ

/-- Agreement with the smooth function on the punctured space. -/
def AgreesOffZero {d : ℕ} (u : Distribution d) (k : Euclidean d → ℂ) : Prop :=
  ∀ φ : CompactTest d, (0 : Euclidean d) ∉ tsupport φ →
    u φ = ∫ x, k x * φ x

def IsHomogeneousExtension {d : ℕ} (u : Distribution d)
    (k : Euclidean d → ℂ) (lam : ℂ) : Prop := Homogeneous u lam ∧ AgreesOffZero u k

/-- Restriction is tested on actual compact tests; continuity is not assumed. -/
def Represents {d : ℕ} (T : Tempered ℂ d) (u : Distribution d) : Prop :=
  ∀ φ : CompactTest d, u φ = T (testToSchwartz φ)

def TemperedAgreesOffZero {d : ℕ} (T : Tempered ℂ d) (k : Euclidean d → ℂ) : Prop :=
  ∀ φ : Schwartz ℂ d, HasCompactSupport φ → (0 : Euclidean d) ∉ tsupport φ →
    T φ = ∫ x, k x * φ x

def MomentsVanish {d : ℕ} (k : Euclidean d → ℂ) (m : ℕ) : Prop :=
  ∀ α : MultiIndex d, order α = m → moment k α = 0

/-- Each coefficient is free, and only the indices of exact order m occur. -/
def deltaCombination {d : ℕ} (m : ℕ) (c : MultiIndex d → ℂ) : Tempered ℂ d :=
  ∑ α ∈ indices d m, c α • deltaDerivative α

end ExpandedFA.PartIV.HomogeneousExtension

namespace Specs.ExpandedFA.PartIV.HomogeneousExtension
open _root_.ExpandedFA.Fourier
open _root_.ExpandedFA.PartIV.HomogeneousMeromorphic
open _root_.ExpandedFA.PartIV.HomogeneousExtension

def regularExtensionType : Prop :=
  ∀ (d : ℕ) (k : Euclidean d → ℂ) (lam : ℂ), SmoothHomogeneous k lam →
    lam ∈ regularSet d → ∃! u : Distribution d, IsHomogeneousExtension u k lam

def criticalExtensionType : Prop :=
  ∀ (d : ℕ) (k : Euclidean d → ℂ) (m : ℕ), SmoothHomogeneous k (pole d m) →
    ((∃ u : Distribution d, IsHomogeneousExtension u k (pole d m)) ↔ MomentsVanish k m)

/-- Both inclusion directions and realization for every coefficient family. -/
def criticalAmbiguityType : Prop :=
  ∀ (d : ℕ) (k : Euclidean d → ℂ) (m : ℕ), SmoothHomogeneous k (pole d m) →
    ∀ u : Distribution d, IsHomogeneousExtension u k (pole d m) →
      (∀ v : Distribution d, IsHomogeneousExtension v k (pole d m) ↔
        ∃ c : MultiIndex d → ℂ, Represents (deltaCombination m c) (v - u)) ∧
      (∀ c : MultiIndex d → ℂ, ∃ v : Distribution d,
        IsHomogeneousExtension v k (pole d m) ∧ Represents (deltaCombination m c) (v - u))

def finitePartType : Prop :=
  ∀ (d : ℕ) (k : Euclidean d → ℂ) (m : ℕ), SmoothHomogeneous k (pole d m) →
    ∃ F : Tempered ℂ d, TemperedAgreesOffZero F k ∧
      ∀ (a : ℝ) (ha : 0 < a),
        dilation a ha F = (a : ℂ) ^ (pole d m) • (F + (Real.log a : ℂ) • residue k m)

/-- A useful constructive portion of the noncritical conclusion. -/
def regularTemperedExtensionType : Prop :=
  ∀ (d : ℕ) (k : Euclidean d → ℂ) (lam : ℂ), SmoothHomogeneous k lam →
    lam ∈ regularSet d → ∃ T : Tempered ℂ d, TemperedAgreesOffZero T k ∧
      ∀ (a : ℝ) (ha : 0 < a), dilation a ha T = (a : ℂ) ^ lam • T

/-- Constructive existence, also exposed separately from uniqueness. -/
def regularExistenceType : Prop :=
  ∀ {d : ℕ} (k : Euclidean d → ℂ) (lam : ℂ), SmoothHomogeneous k lam →
    lam ∈ regularSet d → ∃ u : Distribution d, IsHomogeneousExtension u k lam

def criticalSufficiencyType : Prop :=
  ∀ {d : ℕ} (k : Euclidean d → ℂ) (m : ℕ), SmoothHomogeneous k (pole d m) →
    MomentsVanish k m → ∃ u : Distribution d, IsHomogeneousExtension u k (pole d m)

end Specs.ExpandedFA.PartIV.HomogeneousExtension
