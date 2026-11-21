import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.ExceptionalSets
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.SubdivisionUniformVector
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Indicator

/-! Independent objects and full statements for paper.tex 2175–2186.
The integral is the upstream Darboux integral of the actual zero extension.
Enclosing boxes contain the ambient closure in their topological interior.
No boundary criterion is imposed in dimension zero. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set
open scoped BigOperators
namespace Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.SubdivisionUniformVector.Model

def Encloses {n : ℕ} (S : Set (E n)) (Q : Box n) : Prop :=
  closure S ⊆ interior (carrier Q)

/-- Choice of a box is only a convention for displaying a value. Independence
of this choice is a theorem below, not part of the definition. -/
def enclosingBox {n : ℕ} (S : Set (E n)) : Box n :=
  if h : ∃ Q : Box n, Encloses S Q then Classical.choose h
  else ⟨0, 0, fun _ => le_rfl⟩

def zeroExtension {n : ℕ} {V : Type} [Zero V] {S : Set (E n)}
    (f : S → V) (x : E n) : V :=
  if hx : x ∈ S then f ⟨x, hx⟩ else 0

def RegionBounded {n : ℕ} {V : Type} [Norm V] {S : Set (E n)} (f : S → V) : Prop :=
  ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M

def indicator {n : ℕ} (S : Set (E n)) : E n → ℝ := S.indicator (fun _ => 1)

def Jordan {n : ℕ} (S : Set (E n)) : Prop :=
  ∃ Q : Box n, Encloses S Q ∧ Integrable (indicator S) Q

def volume {n : ℕ} (S : Set (E n)) : ℝ := lowerIntegral (indicator S) (enclosingBox S)

def RegionIntegrable {n : ℕ} {S : Set (E n)} (f : S → ℝ) : Prop :=
  RegionBounded f ∧ ∃ Q : Box n, Encloses S Q ∧ Integrable (zeroExtension f) Q

def regionIntegral {n : ℕ} {S : Set (E n)} (f : S → ℝ) : ℝ :=
  lowerIntegral (zeroExtension f) (enclosingBox S)

/-- Relative discontinuity on the actual domain, with no ambient regularity
assumption on an arbitrary extension. -/
def regionDiscontinuities {n : ℕ} {S : Set (E n)} (f : S → ℝ) : Set (E n) :=
  {x | ∃ hx : x ∈ S, ¬ ContinuousAt f ⟨x, hx⟩}

def VectorRegionIntegrable {n k : ℕ} {S : Set (E n)} (f : S → E k) : Prop :=
  Bornology.IsBounded S ∧ ∀ i : Fin k, RegionIntegrable (fun x => f x i)

def vectorRegionIntegral {n k : ℕ} {S : Set (E n)} (f : S → E k) : E k :=
  WithLp.toLp 2 (fun i => regionIntegral (fun x => f x i))

/-- The ambient open domain itself is allowed to be unbounded or non-Jordan. -/
def OpenIntegrable {n : ℕ} {U : Set (E n)} (f : U → ℝ) : Prop :=
  IsOpen U ∧ Bornology.IsBounded (Function.support (zeroExtension f)) ∧
    ∃ Q : Box n, Encloses (Function.support (zeroExtension f)) Q ∧
      Integrable (zeroExtension f) Q

def openIntegral {n : ℕ} {U : Set (E n)} (f : U → ℝ) : ℝ :=
  lowerIntegral (zeroExtension f) (enclosingBox (Function.support (zeroExtension f)))
end Specs.D04.C06.JordanRegions.Model

namespace Specs.D04.C06.JordanRegions
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.NullCovers.Model
open Specs.D04.C06.DiscontinuityCriterion.Model
open Specs.D04.C06.SubdivisionUniformVector.Model Model

abbrev EnclosesType := {n : ℕ} → Set (E n) → Box n → Prop
def EnclosesValue : EnclosesType := @Model.Encloses
abbrev enclosingBoxType := {n : ℕ} → Set (E n) → Box n
def enclosingBoxValue : enclosingBoxType := @Model.enclosingBox
abbrev zeroExtensionType := {n : ℕ} → {V : Type} → [Zero V] → {S : Set (E n)} →
  (S → V) → E n → V
def zeroExtensionValue : zeroExtensionType := @Model.zeroExtension
abbrev RegionBoundedType := {n : ℕ} → {V : Type} → [Norm V] → {S : Set (E n)} →
  (S → V) → Prop
def RegionBoundedValue : RegionBoundedType := @Model.RegionBounded
abbrev indicatorType := {n : ℕ} → Set (E n) → E n → ℝ
def indicatorValue : indicatorType := @Model.indicator
abbrev JordanType := {n : ℕ} → Set (E n) → Prop
def JordanValue : JordanType := @Model.Jordan
abbrev volumeType := {n : ℕ} → Set (E n) → ℝ
def volumeValue : volumeType := @Model.volume
abbrev RegionIntegrableType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → Prop
def RegionIntegrableValue : RegionIntegrableType := @Model.RegionIntegrable
abbrev regionIntegralType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → ℝ
def regionIntegralValue : regionIntegralType := @Model.regionIntegral
abbrev regionDiscontinuitiesType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → Set (E n)
def regionDiscontinuitiesValue : regionDiscontinuitiesType := @Model.regionDiscontinuities
abbrev VectorRegionIntegrableType := {n k : ℕ} → {S : Set (E n)} → (S → E k) → Prop
def VectorRegionIntegrableValue : VectorRegionIntegrableType := @Model.VectorRegionIntegrable
abbrev vectorRegionIntegralType := {n k : ℕ} → {S : Set (E n)} → (S → E k) → E k
def vectorRegionIntegralValue : vectorRegionIntegralType := @Model.vectorRegionIntegral
abbrev OpenIntegrableType := {n : ℕ} → {U : Set (E n)} → (U → ℝ) → Prop
def OpenIntegrableValue : OpenIntegrableType := @Model.OpenIntegrable
abbrev openIntegralType := {n : ℕ} → {U : Set (E n)} → (U → ℝ) → ℝ
def openIntegralValue : openIntegralType := @Model.openIntegral

def encloses_exists_iff_boundedType : Prop := ∀ {n} (S : Set (E n)),
  (∃ Q, Encloses S Q) ↔ Bornology.IsBounded S

def indicator_discontinuitySetType : Prop := ∀ {n} {S : Set (E n)} {Q : Box n},
  Encloses S Q → discontinuitySet (indicator S) Q = frontier S

def jordan_iff_boundaryType : Prop := ∀ {n}, 0 < n → ∀ S : Set (E n),
  Bornology.IsBounded S → (Jordan S ↔ ContentZero (frontier S))

def integrable_iff_on_enclosing_boxType : Prop := ∀ {n} {S : Set (E n)} {Q : Box n}
  (f : S → ℝ), Encloses S Q →
  (RegionIntegrable f ↔ RegionBounded f ∧ Integrable (zeroExtension f) Q)

def integral_eq_on_enclosing_boxType : Prop := ∀ {n} {S : Set (E n)} {Q : Box n}
  (f : S → ℝ) (hf : RegionIntegrable f) (hQ : Encloses S Q),
  ∀ h : Integrable (zeroExtension f) Q,
    regionIntegral f = integral (zeroExtension f) Q h

def jordan_boundedType : Prop := ∀ {n} {S : Set (E n)}, Jordan S → Bornology.IsBounded S

def volume_eq_on_enclosing_boxType : Prop := ∀ {n} {S : Set (E n)} {Q : Box n} (hS : Jordan S), Encloses S Q → ∀ h : Integrable (indicator S) Q,
    volume S = integral (indicator S) Q h

def jordan_unionType : Prop := ∀ {n} {S T : Set (E n)},
  Jordan S → Jordan T → Jordan (S ∪ T)
def jordan_interType : Prop := ∀ {n} {S T : Set (E n)},
  Jordan S → Jordan T → Jordan (S ∩ T)
def jordan_diffType : Prop := ∀ {n} {S T : Set (E n)},
  Jordan S → Jordan T → Jordan (S \ T)
def jordan_finite_unionType : Prop := ∀ {n} {ι : Type} (s : Finset ι) (S : ι → Set (E n)),
  (∀ i ∈ s, Jordan (S i)) → Jordan (⋃ i ∈ s, S i)

def integral_disjoint_unionType : Prop := ∀ {n} {S T : Set (E n)} (f : E n → ℝ),
  Jordan S → Jordan T → Disjoint S T →
  RegionIntegrable (fun x : S => f x) → RegionIntegrable (fun x : T => f x) →
  RegionIntegrable (fun x : (S ∪ T : Set (E n)) => f x) ∧
  regionIntegral (fun x : (S ∪ T : Set (E n)) => f x) =
    regionIntegral (fun x : S => f x) + regionIntegral (fun x : T => f x)

def integral_finite_disjoint_unionType : Prop := ∀ {n} {ι : Type} (s : Finset ι)
  (S : ι → Set (E n)) (f : E n → ℝ),
  (∀ i ∈ s, Jordan (S i)) → (s : Set ι).PairwiseDisjoint S →
  (∀ i ∈ s, RegionIntegrable (fun x : S i => f x)) →
  RegionIntegrable (fun x : (⋃ i ∈ s, S i) => f x) ∧
  regionIntegral (fun x : (⋃ i ∈ s, S i) => f x) =
    ∑ i ∈ s, regionIntegral (fun x : S i => f x)

def integrable_of_null_relative_discontinuitiesType : Prop := ∀ {n} {S : Set (E n)}, 0 < n →
  ∀ (hS : Jordan S) (f : S → ℝ), RegionBounded f →
    Null (regionDiscontinuities f) → RegionIntegrable f

def integrable_continuous_on_closureType : Prop := ∀ {n} {S : Set (E n)}, 0 < n → Jordan S → ∀ f : closure S → ℝ,
  Continuous f → RegionIntegrable (fun x : S => f ⟨x, subset_closure x.property⟩)

def jordan_emptyType : Prop := ∀ n, Jordan (∅ : Set (E n))
def volume_nonnegType : Prop := ∀ {n} {S : Set (E n)}, Jordan S → 0 ≤ volume S
def volume_emptyType : Prop := ∀ n, volume (∅ : Set (E n)) = 0

def empty_regionType : Prop := ∀ {n} (f : (∅ : Set (E n)) → ℝ),
  RegionIntegrable f ∧ regionIntegral f = 0

def zero_volume_regionType : Prop := ∀ {n} {S : Set (E n)}, Jordan S → volume S = 0 →
  ∀ f : S → ℝ, RegionBounded f → RegionIntegrable f ∧ regionIntegral f = 0

def zero_dimensionType : Prop := ∀ (S : Set (E 0)), Jordan S ∧
  volume S = (if (0 : E 0) ∈ S then 1 else 0) ∧
  ∀ f : S → ℝ, RegionIntegrable f ∧
    regionIntegral f = (if h : (0 : E 0) ∈ S then f ⟨0, h⟩ else 0)

def vector_coordinateType : Prop := ∀ {n} {S : Set (E n)} {k} (f : S → E k) (i : Fin k),
  vectorRegionIntegral f i = regionIntegral (fun x => f x i)

def vector_integrable_iff_boxType : Prop := ∀ {n} {S : Set (E n)} {Q : Box n} {k} (f : S → E k), Encloses S Q →
  (VectorRegionIntegrable f ↔ VectorIntegrable (zeroExtension f) Q)

def vector_integrable_normType : Prop := ∀ {n} {S : Set (E n)} {k} (f : S → E k),
  VectorRegionIntegrable f → RegionIntegrable (fun x => ‖f x‖)

def vector_norm_boundType : Prop := ∀ {n} {S : Set (E n)} {k} (f : S → E k),
  VectorRegionIntegrable f → ‖vectorRegionIntegral f‖ ≤ regionIntegral (fun x => ‖f x‖)

def vector_uniform_boundType : Prop := ∀ {n} {S : Set (E n)} {k}, Jordan S →
  ∀ (f : S → E k), VectorRegionIntegrable f → ∀ M : ℝ, 0 ≤ M →
  (∀ x, ‖f x‖ ≤ M) → ‖vectorRegionIntegral f‖ ≤ M * volume S

def vector_integral_linearType : Prop := ∀ {n} {S : Set (E n)} {k m} (f : S → E k)
  (A : E k →ₗ[ℝ] E m), VectorRegionIntegrable f →
  VectorRegionIntegrable (fun x => A (f x)) ∧
  vectorRegionIntegral (fun x => A (f x)) = A (vectorRegionIntegral f)

def open_integral_eq_on_enclosing_boxType : Prop := ∀ {n} {U : Set (E n)}
  (f : U → ℝ), OpenIntegrable f → ∀ (Q : Box n),
  Encloses (Function.support (zeroExtension f)) Q →
  ∃ h : Integrable (zeroExtension f) Q, openIntegral f = integral (zeroExtension f) Q h

def jordan_finite_interType : Prop := ∀ {n} {ι : Type} (s : Finset ι) (S : ι → Set (E n)),
  s.Nonempty → (∀ i ∈ s, Jordan (S i)) → Jordan (⋂ i ∈ s, S i)

def regionIntegral_oneType : Prop := ∀ {n} (S : Set (E n)),
  regionIntegral (fun _ : S => (1 : ℝ)) = volume S

def volume_finite_disjoint_unionType : Prop := ∀ {n} {ι : Type} (s : Finset ι)
  (S : ι → Set (E n)), (∀ i ∈ s, Jordan (S i)) →
  (s : Set ι).PairwiseDisjoint S → volume (⋃ i ∈ s, S i) = ∑ i ∈ s, volume (S i)

def scalar_abs_boundType : Prop := ∀ {n} {S : Set (E n)} (f : S → ℝ),
  RegionIntegrable f → RegionIntegrable (fun x => |f x|) ∧
    |regionIntegral f| ≤ regionIntegral (fun x => |f x|)

def scalar_uniform_boundType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (f : S → ℝ), RegionIntegrable f → ∀ M : ℝ, 0 ≤ M →
  (∀ x, |f x| ≤ M) → |regionIntegral f| ≤ M * volume S

def vector_zero_dimensionType : Prop := ∀ {k} (S : Set (E 0)) (f : S → E k),
  VectorRegionIntegrable f ∧ vectorRegionIntegral f =
    (if h : (0 : E 0) ∈ S then f ⟨0, h⟩ else 0)

def vector_zero_targetType : Prop := ∀ {n} {S : Set (E n)}, Bornology.IsBounded S →
  ∀ f : S → E 0, VectorRegionIntegrable f ∧ vectorRegionIntegral f = 0

def vector_emptyType : Prop := ∀ {n k} (f : (∅ : Set (E n)) → E k),
  VectorRegionIntegrable f ∧ vectorRegionIntegral f = 0

def vector_zero_volumeType : Prop := ∀ {n} {S : Set (E n)} {k}, Jordan S → volume S = 0 →
  ∀ f : S → E k, RegionBounded f → VectorRegionIntegrable f ∧ vectorRegionIntegral f = 0

def jordan_integrable_on_boxType : Prop := ∀ {n} {S : Set (E n)} {Q : Box n},
  Jordan S → Encloses S Q → Integrable (indicator S) Q

def vectorRegionIntegral_eq_boxType : Prop := ∀ {n} {S : Set (E n)} {Q : Box n} {k}
  (f : S → E k), VectorRegionIntegrable f → Encloses S Q →
  ∀ hi : VectorIntegrable (zeroExtension f) Q,
    vectorRegionIntegral f = vectorIntegral (zeroExtension f) Q hi

def integral_disjoint_union_subtypeType : Prop := ∀ {n} {S T : Set (E n)}
  (f : (S ∪ T : Set (E n)) → ℝ), Jordan S → Jordan T → Disjoint S T →
  RegionIntegrable (fun x : S => f ⟨x, Or.inl x.property⟩) →
  RegionIntegrable (fun x : T => f ⟨x, Or.inr x.property⟩) →
  RegionIntegrable f ∧ regionIntegral f =
    regionIntegral (fun x : S => f ⟨x, Or.inl x.property⟩) +
      regionIntegral (fun x : T => f ⟨x, Or.inr x.property⟩)
end Specs.D04.C06.JordanRegions
