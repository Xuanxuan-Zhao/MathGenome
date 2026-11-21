import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxFubini
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.DistanceFunction
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-! Independent statements for d04:06:cavalieri. The dimension of the base
is p, so the total dimension p+1 is positive, including the base R^0.
Ambient endpoint functions are arbitrary extensions of the original functions
on cl A; continuity is required only on cl A. All integrals are the shared
Riemann/Darboux integrals, including the one-dimensional inner integral. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set
namespace Specs.D04.C06.SlicingAndMoments.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.DarbouxFubini.Model
open Specs.D04.C06.JordanRegions.Model

def basePoint {p : ℕ} (z : E (p+1)) : E p :=
  WithLp.toLp 2 (fun i => z (Fin.castAdd 1 i))
def height {p : ℕ} (z : E (p+1)) : ℝ := z (Fin.last p)
def stackPoint {p : ℕ} (x : E p) (t : ℝ) : E (p+1) :=
  productPoint x (scalarPoint t)
def graph {p : ℕ} (K : Set (E p)) (a : E p → ℝ) : Set (E (p+1)) :=
  {z | basePoint z ∈ K ∧ height z = a (basePoint z)}
def cylinder {p : ℕ} (K : Set (E p)) (l u : ℝ) : Set (E (p+1)) :=
  {z | basePoint z ∈ K ∧ height z ∈ Icc l u}
def between {p : ℕ} (A : Set (E p)) (a b : E p → ℝ)
    (includeLower includeUpper : Bool := true) : Set (E (p+1)) :=
  {z | basePoint z ∈ A ∧
    (if includeLower then a (basePoint z) ≤ height z else a (basePoint z) < height z) ∧
    (if includeUpper then height z ≤ b (basePoint z) else height z < b (basePoint z))}
def sliceBox {p : ℕ} (a b : E p → ℝ) (x : E p) : Box 1 :=
  intervalBox (min (a x) (b x)) (max (a x) (b x)) min_le_max
def sliceIntegral {p : ℕ} (a b : E p → ℝ) (f : E (p+1) → ℝ) (x : E p) : ℝ :=
  lowerIntegral (fun y => f (productPoint x y)) (sliceBox a b x)
/-- An arbitrary subtype function on a closure has a total extension; continuity
is asserted only on that closure, never outside it. -/
def closureExtension {n : ℕ} {S : Set (E n)} (f : closure S → ℝ) (x : E n) : ℝ :=
  if hx : x ∈ closure S then f ⟨x, hx⟩ else 0

def mass {n : ℕ} {S : Set (E n)} (ρ : S → ℝ) : ℝ := regionIntegral ρ
def firstMoment {n : ℕ} {S : Set (E n)} (ρ : S → ℝ) (i : Fin n) : ℝ :=
  regionIntegral (fun x => (x : E n) i * ρ x)
def center {n : ℕ} {S : Set (E n)} (ρ : S → ℝ) : E n :=
  WithLp.toLp 2 (fun i => firstMoment ρ i / mass ρ)
def inertia {n : ℕ} {S : Set (E n)} (ρ : S → ℝ)
    (L : AffineSubspace ℝ (E n)) (hL : (L : Set (E n)).Nonempty) : ℝ :=
  regionIntegral (fun x =>
    (Specs.D04.C01.DistanceFunction.Model.distanceToSet (L : Set (E n)) hL (x : E n))^2 * ρ x)
end Specs.D04.C06.SlicingAndMoments.Model

namespace Specs.D04.C06.SlicingAndMoments
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.DarbouxFubini.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.NullCovers.Model Model

abbrev basePointType := {p : ℕ} → E (p+1) → E p
def basePointValue : basePointType := @Model.basePoint

abbrev heightType := {p : ℕ} → E (p+1) → ℝ
def heightValue : heightType := @Model.height

abbrev stackPointType := {p : ℕ} → E p → ℝ → E (p+1)
def stackPointValue : stackPointType := @Model.stackPoint

abbrev graphType := {p : ℕ} → Set (E p) → (E p → ℝ) → Set (E (p+1))
def graphValue : graphType := @Model.graph

abbrev cylinderType := {p : ℕ} → Set (E p) → ℝ → ℝ → Set (E (p+1))
def cylinderValue : cylinderType := @Model.cylinder

abbrev betweenType := {p : ℕ} → Set (E p) → (E p → ℝ) → (E p → ℝ) → Bool → Bool → Set (E (p+1))
def betweenValue : betweenType := @Model.between

abbrev sliceBoxType := {p : ℕ} → (E p → ℝ) → (E p → ℝ) → E p → Box 1
def sliceBoxValue : sliceBoxType := @Model.sliceBox

abbrev sliceIntegralType := {p : ℕ} → (E p → ℝ) → (E p → ℝ) → (E (p+1) → ℝ) → E p → ℝ
def sliceIntegralValue : sliceIntegralType := @Model.sliceIntegral

abbrev closureExtensionType := {n : ℕ} → {S : Set (E n)} → (closure S → ℝ) → E n → ℝ
def closureExtensionValue : closureExtensionType := @Model.closureExtension

abbrev massType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → ℝ
def massValue : massType := @Model.mass

abbrev firstMomentType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → Fin n → ℝ
def firstMomentValue : firstMomentType := @Model.firstMoment

abbrev centerType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → E n
def centerValue : centerType := @Model.center

abbrev inertiaType := {n : ℕ} → {S : Set (E n)} → (S → ℝ) → (L : AffineSubspace ℝ (E n)) → (L : Set (E n)).Nonempty → ℝ
def inertiaValue : inertiaType := @Model.inertia


def graph_contentZeroType : Prop := ∀ {p} (K : Set (E p)) (a : E p → ℝ),
  IsCompact K → ContinuousOn a K → ContentZero (graph K a)
def cylinder_contentZeroType : Prop := ∀ {p} (K : Set (E p)) (l u : ℝ),
  ContentZero K → ContentZero (cylinder K l u)
def between_boundaryType : Prop := ∀ {p} (A : Set (E p)) (a b : E p → ℝ),
  ContinuousOn a (closure A) → ContinuousOn b (closure A) →
  (∀ x ∈ closure A, a x ≤ b x) → ∀ l u,
  (∀ x ∈ closure A, l ≤ a x ∧ b x ≤ u) →
  frontier (between A a b) ⊆
    cylinder (frontier A) l u ∪ graph (closure A) a ∪ graph (closure A) b

def slicingType : Prop := ∀ {p} (A : Set (E p)) (a b : E p → ℝ),
  Jordan A → ContinuousOn a (closure A) → ContinuousOn b (closure A) →
  (∀ x ∈ closure A, a x ≤ b x) →
  Bornology.IsBounded (between A a b) ∧ Jordan (between A a b) ∧
  ∀ f : E (p+1) → ℝ, ContinuousOn f (closure (between A a b)) →
    RegionIntegrable (fun z : between A a b => f z) ∧
    (∀ x ∈ A, Integrable (fun y => f (productPoint x y)) (sliceBox a b x)) ∧
    RegionIntegrable (fun x : A => sliceIntegral a b f x) ∧
    regionIntegral (fun z : between A a b => f z) =
      regionIntegral (fun x : A => sliceIntegral a b f x)

def endpointsType : Prop := ∀ {p} (A : Set (E p)) (a b : E p → ℝ),
  Jordan A → ContinuousOn a (closure A) → ContinuousOn b (closure A) →
  (∀ x ∈ closure A, a x ≤ b x) → ∀ (il iu : Bool),
  Jordan (between A a b il iu) ∧
  ∀ f : E (p+1) → ℝ, ContinuousOn f (closure (between A a b)) →
    RegionIntegrable (fun z : between A a b il iu => f z) ∧
    regionIntegral (fun z : between A a b il iu => f z) =
      regionIntegral (fun z : between A a b => f z)

def between_volumeType : Prop := ∀ {p} (A : Set (E p)) (a b : E p → ℝ),
  Jordan A → ContinuousOn a (closure A) → ContinuousOn b (closure A) →
  (∀ x ∈ closure A, a x ≤ b x) →
  RegionIntegrable (fun x : A => b x - a x) ∧
  volume (between A a b) = regionIntegral (fun x : A => b x - a x)

def weighted_integrableType : Prop := ∀ {n} {S : Set (E n)},
  Bornology.IsBounded S → ∀ (ρ : S → ℝ), RegionIntegrable ρ →
  ∀ w : E n → ℝ, Continuous w → RegionIntegrable (fun x => w x * ρ x)
def moments_existType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → (∀ x, 0 ≤ ρ x) →
  0 ≤ mass ρ ∧
  (∀ i : Fin n, RegionIntegrable (fun x => (x : E n) i * ρ x)) ∧
  (∀ (L : AffineSubspace ℝ (E n)) (hL : (L : Set (E n)).Nonempty),
    RegionIntegrable (fun x =>
      (Specs.D04.C01.DistanceFunction.Model.distanceToSet (L : Set (E n)) hL (x : E n))^2 * ρ x) ∧
    0 ≤ inertia ρ L hL)
def centered_momentType : Prop := ∀ {n} {S : Set (E n)}, Jordan S →
  ∀ (ρ : S → ℝ), RegionIntegrable ρ → (∀ x, 0 ≤ ρ x) → 0 < mass ρ →
  ∀ i : Fin n,
    RegionIntegrable (fun x => ((x : E n) i - center ρ i) * ρ x) ∧
    regionIntegral (fun x => ((x : E n) i - center ρ i) * ρ x) = 0

def base_zero_evaluationType : Prop := ∀ (A : Set (E 0)) (g : A → ℝ),
  RegionIntegrable g ∧ regionIntegral g =
    (if h : (0 : E 0) ∈ A then g ⟨0, h⟩ else 0)

def closureExtension_propertyType : Prop := ∀ {n} {S : Set (E n)} (f : closure S → ℝ),
  (∀ x : closure S, closureExtension f x = f x) ∧
  (Continuous f → ContinuousOn (closureExtension f) (closure S))

def slicing_closure_dataType : Prop := ∀ {p} (A : Set (E p)), Jordan A →
  ∀ (a b : closure A → ℝ), Continuous a → Continuous b → (∀ x, a x ≤ b x) →
  let E₀ := between A (closureExtension a) (closureExtension b)
  Bornology.IsBounded E₀ ∧ Jordan E₀ ∧
  ∀ f : closure E₀ → ℝ, Continuous f →
    RegionIntegrable (fun z : E₀ => f ⟨z, subset_closure z.property⟩) ∧
    (∀ x ∈ A, Integrable (fun y => closureExtension f (productPoint x y))
      (sliceBox (closureExtension a) (closureExtension b) x)) ∧
    RegionIntegrable (fun x : A => sliceIntegral (closureExtension a) (closureExtension b)
      (closureExtension f) x) ∧
    regionIntegral (fun z : E₀ => f ⟨z, subset_closure z.property⟩) =
      regionIntegral (fun x : A => sliceIntegral (closureExtension a) (closureExtension b)
        (closureExtension f) x)
end Specs.D04.C06.SlicingAndMoments
