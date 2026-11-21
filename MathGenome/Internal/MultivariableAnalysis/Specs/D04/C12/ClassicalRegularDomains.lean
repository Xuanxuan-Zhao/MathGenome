import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge
import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

/-! Classical regular domains, d04:12:domains. Ambient boundary always means
`frontier`; no connectedness condition is included. Local extendibility on an
arbitrary compact set is used for the closure convention, including order zero. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff BigOperators
namespace Specs.D04.C12.ClassicalRegularDomains
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
namespace Model

/-- A negative-side C¹ defining function on the ambient open set U. -/
structure IsDefiningFunction {n : ℕ} (D U : Set (E n)) (ρ : E n → ℝ) : Prop where
  isOpen : IsOpen U
  regular : ContDiffOn ℝ 1 ρ U
  negative : ∀ x ∈ U, x ∈ D ↔ ρ x < 0
  zero_level : ∀ x ∈ U, x ∈ frontier D ↔ ρ x = 0
  nonzero : ∀ x ∈ U, ρ x = 0 → fderiv ℝ ρ x ≠ 0

structure IsClassicalRegularDomain {n : ℕ} (D : Set (E n)) : Prop where
  dimension : 1 ≤ n
  bounded : Bornology.IsBounded D
  isOpen : IsOpen D
  defining : ∀ p ∈ frontier D, ∃ (U : Set (E n)) (ρ : E n → ℝ),
    p ∈ U ∧ IsDefiningFunction D U ρ

def domainClosure {n : ℕ} (D : Set (E n)) : Set (E n) := closure D

/-- The orientation assigned to a full-dimensional closure is the standard
ambient orientation. The manifold/integration bridge is a separate obligation. -/
def ambientOrientation (n : ℕ) : Orientation ℝ (E n) (Fin n) :=
  (standardBasis n).orientation

def normalFromDefining {n : ℕ} (ρ : E n → ℝ) (p : E n) : E n :=
  ‖scalarGradient ρ p‖⁻¹ • scalarGradient ρ p

def chosenNeighborhood {n : ℕ} {D : Set (E n)}
    (hD : IsClassicalRegularDomain D) (p : frontier D) : Set (E n) :=
  (hD.defining p p.property).choose

def chosenDefiningFunction {n : ℕ} {D : Set (E n)}
    (hD : IsClassicalRegularDomain D) (p : frontier D) : E n → ℝ :=
  (hD.defining p p.property).choose_spec.choose

def outwardNormal {n : ℕ} {D : Set (E n)}
    (hD : IsClassicalRegularDomain D) (p : frontier D) : E n :=
  normalFromDefining (chosenDefiningFunction hD p) p

/-- Values outside K are immaterial. This represents a function on K without
requiring it to have an extension before the theorem is proved. -/
def LocallyCrExtendible {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r : ℕ∞ω) (K : Set (E n)) (f : E n → Y) : Prop :=
  ∀ p ∈ K, ∃ (U : Set (E n)) (g : E n → Y),
    IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ r g U ∧ EqOn g f (K ∩ U)

/-- A finite smooth gluing, with each local extension and its support displayed.
The resulting extension is global; only agreement on K is required. -/
def FiniteExtension {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r : ℕ∞ω) (K : Set (E n)) (f : E n → Y) (F : E n → Y) : Prop :=
  ∃ (m : ℕ) (U : Fin m → Set (E n)) (g : Fin m → E n → Y)
    (w : Fin m → E n → ℝ) (V : Set (E n)),
    (∀ i, IsOpen (U i)) ∧ (∀ i, ContDiffOn ℝ r (g i) (U i)) ∧
    (∀ i, EqOn (g i) f (K ∩ U i)) ∧
    (∀ i, ContDiff ℝ ∞ (w i)) ∧ (∀ i x, 0 ≤ w i x) ∧
    (∀ i, IsCompact (tsupport (w i)) ∧ tsupport (w i) ⊆ U i) ∧
    IsOpen V ∧ K ⊆ V ∧ (∀ x ∈ V, ∑ i, w i x = 1) ∧
    (∀ x, F x = ∑ i, w i x • g i x) ∧ ContDiff ℝ r F ∧ EqOn F f K
end Model
open Model

abbrev IsDefiningFunctionType := {n : ℕ} → Set (E n) → Set (E n) → (E n → ℝ) → Prop
def IsDefiningFunctionValue : IsDefiningFunctionType := @Model.IsDefiningFunction
abbrev IsClassicalRegularDomainType := {n : ℕ} → Set (E n) → Prop
def IsClassicalRegularDomainValue : IsClassicalRegularDomainType := @Model.IsClassicalRegularDomain
abbrev domainClosureType := {n : ℕ} → Set (E n) → Set (E n)
def domainClosureValue : domainClosureType := @Model.domainClosure
abbrev ambientOrientationType := (n : ℕ) → Orientation ℝ (E n) (Fin n)
def ambientOrientationValue : ambientOrientationType := Model.ambientOrientation
abbrev normalFromDefiningType := {n : ℕ} → (E n → ℝ) → E n → E n
def normalFromDefiningValue : normalFromDefiningType := @Model.normalFromDefining
abbrev outwardNormalType := {n : ℕ} → {D : Set (E n)} →
  IsClassicalRegularDomain D → frontier D → E n
def outwardNormalValue : outwardNormalType := @Model.outwardNormal
abbrev LocallyCrExtendibleType := {n : ℕ} → {Y : Type} → [NormedAddCommGroup Y] →
  [NormedSpace ℝ Y] → ℕ∞ω → Set (E n) → (E n → Y) → Prop
def LocallyCrExtendibleValue : LocallyCrExtendibleType := @Model.LocallyCrExtendible
abbrev FiniteExtensionType := {n : ℕ} → {Y : Type} → [NormedAddCommGroup Y] →
  [NormedSpace ℝ Y] → ℕ∞ω → Set (E n) → (E n → Y) → (E n → Y) → Prop
def FiniteExtensionValue : FiniteExtensionType := @Model.FiniteExtension

def normal_independentType : Prop :=
  ∀ {n : ℕ} {D U V : Set (E n)} {ρ σ : E n → ℝ} {p : E n},
    IsDefiningFunction D U ρ → IsDefiningFunction D V σ →
    p ∈ U → p ∈ V → p ∈ frontier D →
    normalFromDefining ρ p = normalFromDefining σ p

def normal_propertiesType : Prop :=
  ∀ {n : ℕ} {D U : Set (E n)} {ρ : E n → ℝ} {p : E n},
    IsDefiningFunction D U ρ → p ∈ U → p ∈ frontier D →
    ‖normalFromDefining ρ p‖ = 1 ∧
    (∀ v, fderiv ℝ ρ p v = 0 → inner ℝ (normalFromDefining ρ p) v = 0) ∧
    fderiv ℝ ρ p (normalFromDefining ρ p) = ‖scalarGradient ρ p‖ ∧
    0 < fderiv ℝ ρ p (normalFromDefining ρ p)

def outwardNormal_formulaType : Prop :=
  ∀ {n : ℕ} {D U : Set (E n)} (hD : IsClassicalRegularDomain D)
    (p : frontier D) {ρ : E n → ℝ}, IsDefiningFunction D U ρ → (p : E n) ∈ U →
    outwardNormal hD p = normalFromDefining ρ p

def outwardNormal_unitType : Prop :=
  ∀ {n : ℕ} {D : Set (E n)} (hD : IsClassicalRegularDomain D) (p : frontier D),
    ‖outwardNormal hD p‖ = 1

def closure_compactType : Prop :=
  ∀ {n : ℕ} {D : Set (E n)}, IsClassicalRegularDomain D → IsCompact (domainClosure D)

def empty_domainType : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsClassicalRegularDomain (∅ : Set (E n))

def exists_finite_extensionType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r : ℕ∞ω), r ≤ ∞ → ∀ (K : Set (E n)) (f : E n → Y),
    IsCompact K → LocallyCrExtendible r K f → ∃ F, FiniteExtension r K f F

def closure_extensionType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (r : ℕ∞ω), r ≤ ∞ → ∀ {D : Set (E n)}, IsClassicalRegularDomain D →
    ∀ f : E n → Y, LocallyCrExtendible r (domainClosure D) f →
      ∃ F : E n → Y, ContDiff ℝ r F ∧ EqOn F f (domainClosure D)

end Specs.D04.C12.ClassicalRegularDomains
