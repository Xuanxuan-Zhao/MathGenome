import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions
import Mathlib.Topology.Compactness.SigmaCompact

/-! Independent interfaces for paper.tex, d04:06:improper-definition and the
existence/cofinality portion of d04:06:absolute-exhaustion. An ambient function
represents a function on Ω; all predicates and integrals ignore its values
outside Ω. Proper integrals are the previously constructed zero-extension
Darboux integrals, including evaluation in dimension zero. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal
open Set Filter Topology
namespace Specs.D04.C06.ImproperExhaustions.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model

def LocallyRiemannIntegrable {n : ℕ} (Ω : Set (E n)) (f : E n → ℝ) : Prop :=
  ∀ Q : Box n, carrier Q ⊆ Ω → Integrable f Q

def CompactJordanSubset {n : ℕ} (Ω K : Set (E n)) : Prop :=
  IsCompact K ∧ Jordan K ∧ K ⊆ Ω

def absoluteMass {n : ℕ} (Ω : Set (E n)) (f : E n → ℝ) : ℝ≥0∞ :=
  ⨆ (K : Set (E n)) (_ : CompactJordanSubset Ω K),
    ENNReal.ofReal (regionIntegral (fun x : K => |f x|))

def AbsolutelyConvergent {n : ℕ} (Ω : Set (E n)) (f : E n → ℝ) : Prop :=
  LocallyRiemannIntegrable Ω f ∧ absoluteMass Ω f < ⊤

def RegularExhaustion {n : ℕ} (Ω : Set (E n)) (K : ℕ → Set (E n)) : Prop :=
  (∀ j, CompactJordanSubset Ω (K j)) ∧
  (∀ j, K j ⊆ interior (K (j + 1))) ∧ (⋃ j, interior (K j)) = Ω

/-- A limit tied to the displayed sequence of truncations. -/
def HasIntegralAlong {n : ℕ} (f : E n → ℝ) (K : ℕ → Set (E n)) (I : ℝ) : Prop :=
  Tendsto (fun j => regionIntegral (fun x : K j => f x)) atTop (𝓝 I)

def ConditionalConvergesAlong {n : ℕ} (Ω : Set (E n)) (f : E n → ℝ)
    (K : ℕ → Set (E n)) (I : ℝ) : Prop :=
  LocallyRiemannIntegrable Ω f ∧ RegularExhaustion Ω K ∧
    ¬ AbsolutelyConvergent Ω f ∧ HasIntegralAlong f K I
end Specs.D04.C06.ImproperExhaustions.Model

namespace Specs.D04.C06.ImproperExhaustions
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model Model
abbrev LocallyRiemannIntegrableType := {n : ℕ} → Set (E n) → (E n → ℝ) → Prop
def LocallyRiemannIntegrableValue : LocallyRiemannIntegrableType := @Model.LocallyRiemannIntegrable
abbrev CompactJordanSubsetType := {n : ℕ} → Set (E n) → Set (E n) → Prop
def CompactJordanSubsetValue : CompactJordanSubsetType := @Model.CompactJordanSubset
abbrev absoluteMassType := {n : ℕ} → Set (E n) → (E n → ℝ) → ℝ≥0∞
def absoluteMassValue : absoluteMassType := @Model.absoluteMass
abbrev AbsolutelyConvergentType := LocallyRiemannIntegrableType
def AbsolutelyConvergentValue : AbsolutelyConvergentType := @Model.AbsolutelyConvergent
abbrev RegularExhaustionType := {n : ℕ} → Set (E n) → (ℕ → Set (E n)) → Prop
def RegularExhaustionValue : RegularExhaustionType := @Model.RegularExhaustion
abbrev HasIntegralAlongType := {n : ℕ} → (E n → ℝ) → (ℕ → Set (E n)) → ℝ → Prop
def HasIntegralAlongValue : HasIntegralAlongType := @Model.HasIntegralAlong
abbrev ConditionalConvergesAlongType := {n : ℕ} → Set (E n) → (E n → ℝ) →
  (ℕ → Set (E n)) → ℝ → Prop
def ConditionalConvergesAlongValue : ConditionalConvergesAlongType := @Model.ConditionalConvergesAlong

def locally_integrable_on_compact_jordanType : Prop := ∀ {n} {Ω K : Set (E n)}
  {f : E n → ℝ}, IsOpen Ω → LocallyRiemannIntegrable Ω f → CompactJordanSubset Ω K →
  RegionIntegrable (fun x : K => f x)

def regular_exhaustion_existsType : Prop := ∀ {n} (Ω : Set (E n)), IsOpen Ω →
  ∃ K, RegularExhaustion Ω K

def compact_contained_in_exhaustionType : Prop := ∀ {n} {Ω : Set (E n)}
  {K : ℕ → Set (E n)}, RegularExhaustion Ω K → ∀ {C : Set (E n)},
  IsCompact C → C ⊆ Ω → ∃ j, C ⊆ K j

def regular_exhaustion_monoType : Prop := ∀ {n} {Ω : Set (E n)}
  {K : ℕ → Set (E n)}, RegularExhaustion Ω K → Monotone K

def integral_along_uniqueType : Prop := ∀ {n} {f : E n → ℝ}
  {K : ℕ → Set (E n)} {I J : ℝ}, HasIntegralAlong f K I → HasIntegralAlong f K J → I = J

def zero_dimensionType : Prop := ∀ (Ω : Set (E 0)) (f : E 0 → ℝ),
  (Ω = ∅ ∨ Ω = univ) ∧ LocallyRiemannIntegrable Ω f ∧
  absoluteMass Ω f = (if (0 : E 0) ∈ Ω then ENNReal.ofReal |f 0| else 0) ∧
  AbsolutelyConvergent Ω f ∧ ∀ K, RegularExhaustion Ω K →
    HasIntegralAlong f K (if (0 : E 0) ∈ Ω then f 0 else 0)

def empty_absoluteMassType : Prop := ∀ {n} (f : E n → ℝ),
  absoluteMass ∅ f = 0
end Specs.D04.C06.ImproperExhaustions
