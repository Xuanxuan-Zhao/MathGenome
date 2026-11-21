import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.SurfaceAssembly
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Compact C¹ curve seams, with the surface and its area-null notion taken
from SurfaceAssembly. The curve need not be injective or regular. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff NNReal BigOperators RealInnerProductSpace
namespace Specs.D04.C10.NegligibleSeams
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C10.SurfaceAssembly.Model
namespace Model
structure CompactCurve (n : ℕ) where
  lower : ℝ
  upper : ℝ
  ordered : lower ≤ upper
  toFun : ℝ → E n
  regular : ContDiffOn ℝ 1 toFun (Icc lower upper)

def curveTrace {n : ℕ} (γ : CompactCurve n) : Set (E n) :=
  γ.toFun '' Icc γ.lower γ.upper

/-- A seam is a finite collection of whole compact curve traces and isolated
points. The containment in the surface is a hypothesis of the main theorem. -/
def FiniteSeam {n : ℕ} (Z : Set (E n)) : Prop :=
  ∃ (m : ℕ) (γ : Fin m → CompactCurve n) (p : Finset (E n)),
    Z = (⋃ i, curveTrace (γ i)) ∪ (p : Set (E n))
/-- A compact truncation assembled from regular compact Jordan chart pieces.
Boundary overlaps are allowed, with the canonical coordinate-null condition. -/
structure SurfaceTruncation {n : ℕ} (M Z : Set (E n)) where
  count : ℕ
  piece : Fin count → ChartPiece M
  avoids : ∀ i, pieceImage (piece i) ⊆ M \ Z
  overlaps : ∀ i j, i ≠ j → AreaNull M (pieceImage (piece i) ∩ pieceImage (piece j))

def truncationSet {n : ℕ} {M Z : Set (E n)} (T : SurfaceTruncation M Z) : Set (E n) :=
  ⋃ i, pieceImage (T.piece i)

def truncationIntegral {n : ℕ} {M Z : Set (E n)} (T : SurfaceTruncation M Z)
    (f : M → ℝ) : ℝ := ∑ i, pieceIntegral (T.piece i) f

/-- Compact cofinality is stronger than merely having union equal to the
complement. Nestedness is unnecessary when this eventual condition is used. -/
def ExhaustsComplement {n : ℕ} {M Z : Set (E n)} (T : ℕ → SurfaceTruncation M Z) : Prop :=
  ∀ K : Set (E n), IsCompact K → K ⊆ M \ Z →
    ∀ᶠ j in atTop, K ⊆ truncationSet (T j)
/-- Cofinal regular truncations of a fixed compact Jordan portion of a possibly
noncompact surface. Each truncation is contained in that portion. -/
def ExhaustsPortion {n : ℕ} {M Z : Set (E n)}
    (R : SurfaceTruncation M ∅) (T : ℕ → SurfaceTruncation M Z) : Prop :=
  (∀ j, truncationSet (T j) ⊆ truncationSet R) ∧
  ∀ K : Set (E n), IsCompact K → K ⊆ truncationSet R \ Z →
    ∀ᶠ j in atTop, K ⊆ truncationSet (T j)
/-- The actual Gram-density integrand on a compact parameter lift of a seam. -/
def seamRestrictionCoefficient {n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart 1 2 n M) (K Z : Set (E 2))
    (hKc : K ⊆ c.source) (f : M → ℝ) : ↑(K ∩ Z) → ℝ :=
  fun u => f (Specs.D04.C15.OrientedManifoldAndDensityIntegrals.Model.chartPoint c ⟨u, hKc u.property.1⟩) *
    Specs.D04.C14.MetricTopFormsAndDensities.Model.chartDensity c u
end Model
open Model

def lipschitz_curve_contentZeroType : Prop :=
  ∀ (a b : ℝ) (γ : ℝ → E 2) (L : ℝ≥0),
    LipschitzOnWith L γ (Icc a b) →
    Specs.D04.C06.NullCovers.Model.ContentZero (γ '' Icc a b)

def finite_seam_areaNullType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M →
    FiniteSeam Z → Z ⊆ M → IsCompact Z ∧ AreaNull M Z

/-- Finite covers, rather than just measure zero, on every compact parameter
restriction. The density estimate is developed in the implementation. -/
def compact_chart_seam_contentZeroType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M →
    FiniteSeam Z → Z ⊆ M → ∀ (c : EmbeddedChart 1 2 n M)
    (K : Set (E 2)), IsCompact K → K ⊆ c.source →
    Specs.D04.C06.NullCovers.Model.ContentZero (K ∩ c.toFun ⁻¹' Z)
/-- Quantitative control by omitted scalar area, for each regular truncation. -/
def truncation_error_boundType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    ∀ (T : SurfaceTruncation M Z) (f : M → ℝ), Continuous f →
    ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
      |surfaceIntegral M f - truncationIntegral T f| ≤
        B * (surfaceIntegral M (fun _ => 1) - truncationIntegral T (fun _ => 1))

/-- The scalar conclusion on compact surfaces. Compact portions of arbitrary
surfaces are treated separately below. -/
def seam_truncation_convergenceType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    FiniteSeam Z → Z ⊆ M → ∀ (f : M → ℝ), Continuous f →
    ∀ T : ℕ → SurfaceTruncation M Z, ExhaustsComplement T →
      Tendsto (fun j => truncationIntegral (T j) f) atTop (𝓝 (surfaceIntegral M f))

def seam_flux_truncation_convergenceType : Prop :=
  ∀ {M Z : Set (E 3)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    FiniteSeam Z → Z ⊆ M → ∀ (N : UnitNormalField M) (F : M → E 3),
    Continuous F → ∀ T : ℕ → SurfaceTruncation M Z, ExhaustsComplement T →
      Tendsto (fun j => truncationIntegral (T j) (fun x => ⟪F x, N.toFun x⟫))
        atTop (𝓝 (surfaceFlux N F))
/-- On noncompact surfaces the same statement holds for a continuous scalar
field with compact support; every integral involved is then defined. -/
def compact_support_seam_truncation_convergenceType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M →
    FiniteSeam Z → Z ⊆ M → ∀ (f : M → ℝ), Continuous f → HasCompactSupport f →
    ∀ T : ℕ → SurfaceTruncation M Z, ExhaustsComplement T →
      Tendsto (fun j => truncationIntegral (T j) f) atTop (𝓝 (surfaceIntegral M f))

/-- The complements of sufficiently large regular compact truncations are
relatively open neighborhoods of Z with arbitrarily small omitted Gram area.
The estimate uses any bound B on |f|, hence in particular its supremum. -/
def small_area_neighborhoodsType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M → IsCompact M →
    FiniteSeam Z → Z ⊆ M → ∀ T : ℕ → SurfaceTruncation M Z,
    ExhaustsComplement T → ∀ ε : ℝ, 0 < ε → ∃ j : ℕ,
      IsOpen {x : M | (x : E n) ∉ truncationSet (T j)} ∧
      Z ⊆ M \ truncationSet (T j) ∧
      0 ≤ surfaceIntegral M (fun _ => 1) - truncationIntegral (T j) (fun _ => 1) ∧
      surfaceIntegral M (fun _ => 1) - truncationIntegral (T j) (fun _ => 1) < ε ∧
      ∀ (f : M → ℝ), Continuous f → ∀ B : ℝ, 0 ≤ B → (∀ x, |f x| ≤ B) →
        |surfaceIntegral M f - truncationIntegral (T j) f| ≤
          B * (surfaceIntegral M (fun _ => 1) - truncationIntegral (T j) (fun _ => 1))
/-- Local interpretation on any finite regular compact Jordan portion; the
ambient embedded surface need not be compact. -/
def compact_portion_seam_convergenceType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M →
    FiniteSeam Z → Z ⊆ M → ∀ (R : SurfaceTruncation M ∅) (f : M → ℝ),
    Continuous f → ∀ T : ℕ → SurfaceTruncation M Z, ExhaustsPortion R T →
      Tendsto (fun j => truncationIntegral (T j) f) atTop (𝓝 (truncationIntegral R f))

def compact_portion_flux_convergenceType : Prop :=
  ∀ {M Z : Set (E 3)}, IsEmbeddedManifold 1 2 M →
    FiniteSeam Z → Z ⊆ M → ∀ (R : SurfaceTruncation M ∅)
    (N : UnitNormalField M) (F : M → E 3), Continuous F →
    ∀ T : ℕ → SurfaceTruncation M Z, ExhaustsPortion R T →
      Tendsto (fun j => truncationIntegral (T j) (fun x => ⟪F x, N.toFun x⟫))
        atTop (𝓝 (truncationIntegral R (fun x => ⟪F x, N.toFun x⟫)))

def compact_portion_error_boundType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M →
    ∀ (R : SurfaceTruncation M ∅) (T : SurfaceTruncation M Z),
    truncationSet T ⊆ truncationSet R → ∀ (f : M → ℝ), Continuous f →
    ∀ B : ℝ, 0 ≤ B → (∀ x : M, (x : E n) ∈ truncationSet R → |f x| ≤ B) →
      |truncationIntegral R f - truncationIntegral T f| ≤
        B * (truncationIntegral R (fun _ => 1) - truncationIntegral T (fun _ => 1))
/-- Zero area is expressed by a proved integrability statement and the actual
Jordan/Gram integral, not by a default value for an undefined integral. -/
def compact_chart_seam_integral_zeroType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M →
    FiniteSeam Z → Z ⊆ M → ∀ (c : EmbeddedChart 1 2 n M)
    (K : Set (E 2)), IsCompact K → ∀ hKc : K ⊆ c.source,
    ∀ f : M → ℝ, Continuous f →
      Specs.D04.C06.JordanRegions.Model.RegionIntegrable
        (seamRestrictionCoefficient c K (c.toFun ⁻¹' Z) hKc f) ∧
      Specs.D04.C06.JordanRegions.Model.regionIntegral
        (seamRestrictionCoefficient c K (c.toFun ⁻¹' Z) hKc f) = 0

/-- The small-area neighborhood and bound on an arbitrary compact portion. -/
def compact_portion_small_area_neighborhoodsType : Prop :=
  ∀ {n : ℕ} {M Z : Set (E n)}, IsEmbeddedManifold 1 2 M →
    FiniteSeam Z → Z ⊆ M → ∀ (R : SurfaceTruncation M ∅)
    (T : ℕ → SurfaceTruncation M Z), ExhaustsPortion R T →
    ∀ ε : ℝ, 0 < ε → ∃ j : ℕ,
      IsOpen {x : truncationSet R | (x : E n) ∉ truncationSet (T j)} ∧
      Z ∩ truncationSet R ⊆ truncationSet R \ truncationSet (T j) ∧
      0 ≤ truncationIntegral R (fun _ => 1) - truncationIntegral (T j) (fun _ => 1) ∧
      truncationIntegral R (fun _ => 1) - truncationIntegral (T j) (fun _ => 1) < ε ∧
      ∀ (f : M → ℝ), Continuous f → ∀ B : ℝ, 0 ≤ B →
      (∀ x : M, (x : E n) ∈ truncationSet R → |f x| ≤ B) →
        |truncationIntegral R f - truncationIntegral (T j) f| ≤
          B * (truncationIntegral R (fun _ => 1) - truncationIntegral (T j) (fun _ => 1))
end Specs.D04.C10.NegligibleSeams
