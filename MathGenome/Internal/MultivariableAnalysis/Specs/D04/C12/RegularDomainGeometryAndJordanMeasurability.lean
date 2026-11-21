import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.ClassicalRegularDomains
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.OutwardFirstBoundaryOrientation
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.JordanRegions

/-! Geometric and bounded-region parts of d04:12:region-interface.
The manifold integral comparison is a separately allocated obligation.
All boundaries in the hypotheses are ambient frontiers. -/
noncomputable section
open Set
open scoped ContDiff
namespace Specs.D04.C12.RegularDomainGeometryAndJordanMeasurability
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C06.NullCovers.Model
open Specs.D04.C06.JordanRegions.Model

/-- Compactness and the genuine shared embedded-manifold structure. -/
def closure_manifoldType : Prop :=
  ∀ {n : ℕ} {D : Set (E n)}, IsClassicalRegularDomain D →
    IsCompact (closure D) ∧ IsEmbeddedManifold 1 n (closure D)

def intrinsic_boundaryType : Prop :=
  ∀ {n : ℕ} {D : Set (E n)}, IsClassicalRegularDomain D →
    intrinsicBoundary 1 n (closure D) = frontier D

/-- The differential points to the exterior of the negative side; its metric
unit dual is the conormal of the shared manifold model. -/
def defining_normal_conormalType : Prop :=
  ∀ {d : ℕ} {D U : Set (E (d+1))} {ρ : E (d+1) → ℝ},
    IsClassicalRegularDomain D → IsDefiningFunction D U ρ →
    ∀ p ∈ frontier D ∩ U,
      IsOutwardUnitConormal 1 d (closure D) p (normalFromDefining ρ p)

def outward_normal_conormalType : Prop :=
  ∀ {d : ℕ} {D : Set (E (d+1))} (hD : IsClassicalRegularDomain D)
    (p : frontier D), IsOutwardUnitConormal 1 d (closure D) p (outwardNormal hD p)

/-- The intrinsic boundary also has the expected boundaryless regularity. -/
def boundary_manifoldType : Prop :=
  ∀ {d : ℕ} {D : Set (E (d+1))}, IsClassicalRegularDomain D →
    IsBoundarylessEmbeddedManifold 1 d (frontier D)

def boundary_contentZeroType : Prop :=
  ∀ {n : ℕ} {D : Set (E n)}, IsClassicalRegularDomain D → ContentZero (frontier D)

def boundary_finite_oneType : Prop :=
  ∀ {D : Set (E 1)}, IsClassicalRegularDomain D → (frontier D).Finite

def jordan_domain_and_closureType : Prop :=
  ∀ {n : ℕ} {D : Set (E n)}, IsClassicalRegularDomain D → Jordan D ∧ Jordan (closure D)

def closure_differenceType : Prop :=
  ∀ {n : ℕ} {D : Set (E n)}, IsClassicalRegularDomain D → closure D \ D = frontier D

/-- Scalar bounded-region Riemann integrals of continuous functions on K.
This uses the upstream Darboux integral of the actual zero extension. -/
def continuous_integralType : Prop :=
  ∀ {n : ℕ} {D : Set (E n)}, IsClassicalRegularDomain D →
    ∀ f : closure D → ℝ, Continuous f →
      RegionIntegrable f ∧
      RegionIntegrable (fun x : D => f ⟨x, subset_closure x.property⟩) ∧
      regionIntegral f = regionIntegral (fun x : D => f ⟨x, subset_closure x.property⟩)

end Specs.D04.C12.RegularDomainGeometryAndJordanMeasurability
