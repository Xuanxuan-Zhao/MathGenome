import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.SlicingAndMoments
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Independent Riemann statements for paper.tex, d04:08:exponential-moments.
No continuity of the density is assumed. Dimensions include zero. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C08.ExponentialMoments.Model
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model

def tiltedDensity {n : ℕ} {S : Set (E n)} (ρ : S → ℝ) (p : E n) (x : S) : ℝ :=
  Real.exp (inner ℝ p (x : E n)) * ρ x

def partition {n : ℕ} {S : Set (E n)} (ρ : S → ℝ) (p : E n) : ℝ :=
  regionIntegral (tiltedDensity ρ p)

def momentDensity {n : ℕ} {S : Set (E n)} (ρ : S → ℝ)
    {j : ℕ} (v : Fin j → E n) (x : S) : ℝ :=
  (∏ i, inner ℝ (v i) (x : E n)) * ρ x

def logPartition {n : ℕ} {S : Set (E n)} (ρ : S → ℝ) (p : E n) : ℝ :=
  Real.log (partition ρ p)

def directionalMean {n : ℕ} {S : Set (E n)} (ρ : S → ℝ) (p h : E n) : ℝ :=
  regionIntegral (fun x => inner ℝ h (x : E n) * tiltedDensity ρ p x) / partition ρ p
end Specs.D04.C08.ExponentialMoments.Model

namespace Specs.D04.C08.ExponentialMoments
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.SlicingAndMoments.Model
open Model

abbrev tiltedDensityType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → E n → S → ℝ
def tiltedDensityValue : tiltedDensityType := @tiltedDensity
abbrev partitionType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → E n → ℝ
def partitionValue : partitionType := @partition
abbrev momentDensityType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → {j : ℕ} → (Fin j → E n) → S → ℝ
def momentDensityValue : momentDensityType := @momentDensity
abbrev logPartitionType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → E n → ℝ
def logPartitionValue : logPartitionType := @logPartition
abbrev directionalMeanType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → E n → E n → ℝ
def directionalMeanValue : directionalMeanType := @directionalMean

/-- Signed densities are allowed in the calculus assertion, a stronger statement
that specializes directly to the nonnegative densities in the source. -/
def moments_integrableType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → ∀ j (v : Fin j → E n) p,
  RegionIntegrable (fun x => (∏ i, inner ℝ (v i) (x : E n)) * tiltedDensity ρ p x)

def smoothType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → ∀ r : ℕ, ContDiff ℝ r (partition ρ)

def derivativesType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → ∀ j (v : Fin j → E n) p,
  iteratedFDeriv ℝ j (partition ρ) p v =
    regionIntegral (fun x => (∏ i, inner ℝ (v i) (x : E n)) * tiltedDensity ρ p x)

def first_secondType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → ∀ p h k,
  fderiv ℝ (partition ρ) p h =
    regionIntegral (fun x => inner ℝ h (x : E n) * tiltedDensity ρ p x) ∧
  iteratedFDeriv ℝ 2 (partition ρ) p ![h,k] =
    regionIntegral (fun x => inner ℝ h (x : E n) * inner ℝ k (x : E n) * tiltedDensity ρ p x)

/-- Uniform derivative and total-remainder estimates on each compact parameter
ball, at every moment order, directly for the possibly discontinuous density.
The modulus is uniform over x and both parameter points. -/
def uniform_estimatesType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → ∀ j (v : Fin j → E n),
  ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ p q : E n, ‖p‖ ≤ R → ‖q‖ ≤ R → ‖q-p‖ < δ → ∀ x : S,
  (∀ h : E n,
    |inner ℝ h (x : E n) *
      (tiltedDensity (momentDensity ρ v) q x - tiltedDensity (momentDensity ρ v) p x)| ≤ ε * ‖h‖) ∧
  |tiltedDensity (momentDensity ρ v) q x - tiltedDensity (momentDensity ρ v) p x -
    inner ℝ (q-p) (x : E n) * tiltedDensity (momentDensity ρ v) p x| ≤ ε * ‖q-p‖

def positiveType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → (∀ x, 0 ≤ ρ x) →
  0 < regionIntegral ρ → ∀ p, 0 < partition ρ p

def log_gradientType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → (∀ x, 0 ≤ ρ x) →
  0 < regionIntegral ρ →
  (∀ r : ℕ, ContDiff ℝ r (logPartition ρ)) ∧ ∀ p h,
  fderiv ℝ (logPartition ρ) p h = inner ℝ (center (tiltedDensity ρ p)) h ∧
  inner ℝ (center (tiltedDensity ρ p)) h = directionalMean ρ p h

def log_hessianType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → (∀ x, 0 ≤ ρ x) →
  0 < regionIntegral ρ → ∀ p h,
  RegionIntegrable (fun x => (inner ℝ h (x : E n) - directionalMean ρ p h)^2 * tiltedDensity ρ p x) ∧
  iteratedFDeriv ℝ 2 (logPartition ρ) p ![h,h] =
    regionIntegral (fun x => (inner ℝ h (x : E n) - directionalMean ρ p h)^2 * tiltedDensity ρ p x) / partition ρ p ∧
  0 ≤ iteratedFDeriv ℝ 2 (logPartition ρ) p ![h,h]
end Specs.D04.C08.ExponentialMoments
