import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.ImproperExhaustions
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Absolute convergence for the actual zero-extension Darboux integrals.
No exhaustion independence is imposed on conditionally convergent integrals.
The codomain `ℝ≥0∞` retains the infinite nonnegative-integral case. -/
noncomputable section
open Set Filter Topology
open scoped Classical ENNReal
namespace Specs.D04.C06.AbsoluteConvergence.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.ImproperExhaustions.Model

/-- A value convention, with existence and independence proved separately. -/
def improperIntegral {n : ℕ} (Ω : Set (E n)) (f : E n → ℝ) : ℝ :=
  if h : ∃ I : ℝ, ∀ K, RegularExhaustion Ω K → HasIntegralAlong f K I then
    Classical.choose h else 0

def LocallyVectorRiemannIntegrable {n k : ℕ} (Ω : Set (E n)) (f : E n → E k) : Prop :=
  ∀ i : Fin k, LocallyRiemannIntegrable Ω (fun x => f x i)

def vectorAbsoluteMass {n k : ℕ} (Ω : Set (E n)) (f : E n → E k) : ℝ≥0∞ :=
  absoluteMass Ω (fun x => ‖f x‖)

def VectorAbsolutelyConvergent {n k : ℕ} (Ω : Set (E n)) (f : E n → E k) : Prop :=
  LocallyVectorRiemannIntegrable Ω f ∧ vectorAbsoluteMass Ω f < ⊤

def vectorImproperIntegral {n k : ℕ} (Ω : Set (E n)) (f : E n → E k) : E k :=
  WithLp.toLp 2 (fun i => improperIntegral Ω (fun x => f x i))

def HasVectorIntegralAlong {n k : ℕ} (f : E n → E k)
    (K : ℕ → Set (E n)) (I : E k) : Prop :=
  Tendsto (fun j => vectorRegionIntegral (fun x : K j => f x)) atTop (𝓝 I)
end Specs.D04.C06.AbsoluteConvergence.Model

namespace Specs.D04.C06.AbsoluteConvergence
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.ImproperExhaustions.Model Model

abbrev improperIntegralType := {n : ℕ} → Set (E n) → (E n → ℝ) → ℝ
def improperIntegralValue : improperIntegralType := @Model.improperIntegral
abbrev LocallyVectorRiemannIntegrableType :=
  {n k : ℕ} → Set (E n) → (E n → E k) → Prop
def LocallyVectorRiemannIntegrableValue : LocallyVectorRiemannIntegrableType :=
  @Model.LocallyVectorRiemannIntegrable
abbrev vectorAbsoluteMassType := {n k : ℕ} → Set (E n) → (E n → E k) → ℝ≥0∞
def vectorAbsoluteMassValue : vectorAbsoluteMassType := @Model.vectorAbsoluteMass
abbrev VectorAbsolutelyConvergentType := LocallyVectorRiemannIntegrableType
def VectorAbsolutelyConvergentValue : VectorAbsolutelyConvergentType :=
  @Model.VectorAbsolutelyConvergent
abbrev vectorImproperIntegralType := {n k : ℕ} → Set (E n) → (E n → E k) → E k
def vectorImproperIntegralValue : vectorImproperIntegralType := @Model.vectorImproperIntegral
abbrev HasVectorIntegralAlongType :=
  {n k : ℕ} → (E n → E k) → (ℕ → Set (E n)) → E k → Prop
def HasVectorIntegralAlongValue : HasVectorIntegralAlongType := @Model.HasVectorIntegralAlong

/-- The supremum in the nonnegative case is exactly the paper's absolute mass,
since `f = |f|` on Ω. The real integrals increase; their extended nonnegative
values converge even when the supremum is infinite. -/
def nonnegative_exhaustionType : Prop := ∀ {n} {Ω : Set (E n)} {f : E n → ℝ},
  IsOpen Ω → LocallyRiemannIntegrable Ω f →
  (∀ x ∈ Ω, 0 ≤ f x) → ∀ {K : ℕ → Set (E n)}, RegularExhaustion Ω K →
  Monotone (fun j => regionIntegral (fun x : K j => f x)) ∧
  (⨆ j, ENNReal.ofReal (regionIntegral (fun x : K j => f x))) = absoluteMass Ω f ∧
  Tendsto (fun j => ENNReal.ofReal (regionIntegral (fun x : K j => f x)))
    atTop (𝓝 (absoluteMass Ω f))

def absolute_exhaustionType : Prop := ∀ {n} {Ω : Set (E n)} {f : E n → ℝ},
  IsOpen Ω → AbsolutelyConvergent Ω f →
  (∀ K, RegularExhaustion Ω K → HasIntegralAlong f K (improperIntegral Ω f)) ∧
  ∀ K, CompactJordanSubset Ω K →
    |improperIntegral Ω f - regionIntegral (fun x : K => f x)| ≤
      (absoluteMass Ω f).toReal - regionIntegral (fun x : K => |f x|)

def absolute_limit_uniqueType : Prop := ∀ {n} {Ω : Set (E n)} {f : E n → ℝ},
  IsOpen Ω → AbsolutelyConvergent Ω f → ∀ {K : ℕ → Set (E n)} {I : ℝ},
  RegularExhaustion Ω K → HasIntegralAlong f K I → I = improperIntegral Ω f

def vector_absolute_exhaustionType : Prop := ∀ {n} {Ω : Set (E n)} {k} {f : E n → E k},
  IsOpen Ω → VectorAbsolutelyConvergent Ω f →
  (∀ K, RegularExhaustion Ω K → HasVectorIntegralAlong f K (vectorImproperIntegral Ω f)) ∧
  ∀ K, CompactJordanSubset Ω K →
    ‖vectorImproperIntegral Ω f - vectorRegionIntegral (fun x : K => f x)‖ ≤
      (vectorAbsoluteMass Ω f).toReal - regionIntegral (fun x : K => ‖f x‖)
end Specs.D04.C06.AbsoluteConvergence
