import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.GaussDivergenceTheorem

/-! The three formulas of paper.tex, d04:12:parts. Boundary integration uses
exactly the existing unsigned Gram-density integral, including counting in
boundary dimension zero. All regular domains, including disconnected and empty
ones, are allowed. No integral existence is assumed in the conclusions. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology
open scoped ContDiff
namespace Specs.D04.C12.IntegrationByPartsAndGreenIdentities
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model

/-- Total value selector for the existing density integral. The formulas below
prove existence of this integral, so the default branch is never used there. -/
def boundaryIntegral {d : ℕ} {D : Set (E (d+1))} (ρ : frontier D → ℝ) : ℝ :=
  if h : ∃ I, HasDensityIntegral (d := d) ρ I then h.choose else 0

/-- The normal derivative uses the outward normal and the canonical gradient. -/
def normalDerivative {n : ℕ} {D : Set (E n)} (hD : IsClassicalRegularDomain D)
    (v : E n → ℝ) (x : frontier D) : ℝ :=
  inner ℝ (scalarGradient v x) (outwardNormal hD x)
end Model
open Model

abbrev boundaryIntegralType := {d : ℕ} → {D : Set (E (d+1))} → (frontier D → ℝ) → ℝ
def boundaryIntegralValue : boundaryIntegralType := @Model.boundaryIntegral
abbrev normalDerivativeType := {n : ℕ} → {D : Set (E n)} →
  IsClassicalRegularDomain D → (E n → ℝ) → frontier D → ℝ
def normalDerivativeValue : normalDerivativeType := @Model.normalDerivative

def integration_by_partsType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (U : Set (E (d+1))) (f g : E (d+1) → ℝ),
    IsOpen U → closure D ⊆ U → ContDiffOn ℝ 1 f U → ContDiffOn ℝ 1 g U →
    ∀ i : Fin (d+1),
    RegionIntegrable (fun x : D => f x * scalarPartialDerivative g x i) ∧
    RegionIntegrable (fun x : D => g x * scalarPartialDerivative f x i) ∧
    HasDensityIntegral (d := d) (fun x : frontier D => f x * g x * outwardNormal hD x i)
      (boundaryIntegral (fun x : frontier D => f x * g x * outwardNormal hD x i)) ∧
    regionIntegral (fun x : D => f x * scalarPartialDerivative g x i) =
      boundaryIntegral (fun x : frontier D => f x * g x * outwardNormal hD x i) -
      regionIntegral (fun x : D => g x * scalarPartialDerivative f x i)

def first_greenType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (U : Set (E (d+1))) (u v : E (d+1) → ℝ),
    IsOpen U → closure D ⊆ U → ContDiffOn ℝ 2 u U → ContDiffOn ℝ 2 v U →
    RegionIntegrable (fun x : D => u x * laplacian v x) ∧
    RegionIntegrable (fun x : D => inner ℝ (scalarGradient u x) (scalarGradient v x)) ∧
    RegionIntegrable (fun x : D => u x * laplacian v x +
      inner ℝ (scalarGradient u x) (scalarGradient v x)) ∧
    HasDensityIntegral (d := d) (fun x : frontier D => u x * normalDerivative hD v x)
      (regionIntegral (fun x : D => u x * laplacian v x +
        inner ℝ (scalarGradient u x) (scalarGradient v x))) ∧
    regionIntegral (fun x : D => u x * laplacian v x +
      inner ℝ (scalarGradient u x) (scalarGradient v x)) =
      boundaryIntegral (fun x : frontier D => u x * normalDerivative hD v x)

def second_greenType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (U : Set (E (d+1))) (u v : E (d+1) → ℝ),
    IsOpen U → closure D ⊆ U → ContDiffOn ℝ 2 u U → ContDiffOn ℝ 2 v U →
    RegionIntegrable (fun x : D => u x * laplacian v x - v x * laplacian u x) ∧
    HasDensityIntegral (d := d) (fun x : frontier D =>
      u x * normalDerivative hD v x - v x * normalDerivative hD u x)
      (regionIntegral (fun x : D => u x * laplacian v x - v x * laplacian u x)) ∧
    regionIntegral (fun x : D => u x * laplacian v x - v x * laplacian u x) =
      boundaryIntegral (fun x : frontier D =>
        u x * normalDerivative hD v x - v x * normalDerivative hD u x)

/-- A supported product covers the coordinate formula without requiring either
factor individually to have compact support. Boundedness of D makes the closed
support compact automatically. -/
def parts_boundary_compactType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (f g : E (d+1) → ℝ),
    tsupport (fun x => f x * g x) ⊆ D → ∀ i : Fin (d+1),
      boundaryIntegral (fun x : frontier D => f x * g x * outwardNormal hD x i) = 0

/-- This applies to either Green boundary flux, and to any other relevant
product vector field, whenever that field has support inside D. -/
def flux_boundary_compactType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (F : E (d+1) → E (d+1)),
    tsupport F ⊆ D → boundaryIntegral (normalFlux F (outwardNormal hD)) = 0

/-- Compact support of the first Green product suffices, independently of
compact support of either scalar factor. -/
def first_green_product_boundary_compactType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (u v : E (d+1) → ℝ),
    tsupport (fun x => u x • scalarGradient v x) ⊆ D →
    boundaryIntegral (fun x : frontier D => u x * normalDerivative hD v x) = 0

/-- The same assertion for the antisymmetric Green product. -/
def second_green_product_boundary_compactType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (u v : E (d+1) → ℝ),
    tsupport (fun x => u x • scalarGradient v x - v x • scalarGradient u x) ⊆ D →
    boundaryIntegral (fun x : frontier D =>
      u x * normalDerivative hD v x - v x * normalDerivative hD u x) = 0

def green_boundary_compactType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (u v : E (d+1) → ℝ),
    (tsupport u ⊆ D ∨ tsupport v ⊆ D) →
    boundaryIntegral (fun x : frontier D => u x * normalDerivative hD v x) = 0 ∧
    boundaryIntegral (fun x : frontier D =>
      u x * normalDerivative hD v x - v x * normalDerivative hD u x) = 0

/-- Zero extension is Cʳ for finite r if the function is Cʳ in D and its
relative support is compact in D; no boundary regularity is presumed. -/
def zero_extension_regularType : Prop := ∀ {n : ℕ} {D : Set (E n)}, IsOpen D →
    ∀ (r : ℕ) (u : E n → ℝ), ContDiffOn ℝ r u D →
    HasCompactSupport (fun x : D => u x) →
    ContDiff ℝ r (zeroExtension (fun x : D => u x))

/-- C_c²(D) is expressed by C² on D and compact relative support. Every
operator in this identity is applied to the proved C² zero extension. -/
def compact_energyType : Prop := ∀ {d : ℕ} {D : Set (E (d+1))}
    (hD : IsClassicalRegularDomain D) (u : E (d+1) → ℝ),
    ContDiffOn ℝ 2 u D → HasCompactSupport (fun x : D => u x) →
    let z := zeroExtension (fun x : D => u x)
    ContDiff ℝ 2 z ∧
    RegionIntegrable (fun x : D => z x * laplacian z x) ∧
    RegionIntegrable (fun x : D => ‖scalarGradient z x‖ ^ 2) ∧
    regionIntegral (fun x : D => z x * laplacian z x) =
      -regionIntegral (fun x : D => ‖scalarGradient z x‖ ^ 2)

end Specs.D04.C12.IntegrationByPartsAndGreenIdentities
