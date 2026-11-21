import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.RegionSubstitution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Geometric coordinate charts, paper.tex `d04:07:coordinates`.
Coordinates are ordered (r,θ), (r,θ,z), and (r,φ,θ), respectively.
The coordinate domains are open and omit the origin and the angular seam;
the spherical domain also omits both polar endpoints. Integration uses the
shared Riemann zero-extension definitions, with arbitrary bounded data.
-/
noncomputable section
open Set
namespace Specs.D04.C07.CoordinateCharts
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
namespace Model

def polar (p : E 2) : E 2 :=
  WithLp.toLp 2 ![p 0 * Real.cos (p 1), p 0 * Real.sin (p 1)]
def cylindrical (p : E 3) : E 3 :=
  WithLp.toLp 2 ![p 0 * Real.cos (p 1), p 0 * Real.sin (p 1), p 2]
def spherical (p : E 3) : E 3 :=
  WithLp.toLp 2 ![p 0 * Real.sin (p 1) * Real.cos (p 2),
    p 0 * Real.sin (p 1) * Real.sin (p 2), p 0 * Real.cos (p 1)]

def polarDomain (α : ℝ) : Set (E 2) :=
  {p | 0 < p 0 ∧ α < p 1 ∧ p 1 < α + 2 * Real.pi}
def cylindricalDomain (α : ℝ) : Set (E 3) :=
  {p | 0 < p 0 ∧ α < p 1 ∧ p 1 < α + 2 * Real.pi}
def sphericalDomain (α : ℝ) : Set (E 3) :=
  {p | 0 < p 0 ∧ 0 < p 1 ∧ p 1 < Real.pi ∧ α < p 2 ∧ p 2 < α + 2 * Real.pi}

/-- An actual open partial homeomorphism, with the displayed forward map,
exact source and exact image, and C¹ inverse. The Jacobian is signed. -/
def PositiveChart {n : ℕ} (f : E n → E n) (U : Set (E n)) (J : E n → ℝ) : Prop :=
  (∀ p ∈ U, (fderiv ℝ f p).det = J p ∧ 0 < J p) ∧
  ∃ e : OpenPartialHomeomorph (E n) (E n),
    e.source = U ∧ e.target = f '' U ∧ (e : E n → E n) = f ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target

/-- Every compact Jordan subregion, including the empty set, and every
bounded function on its image. No continuity or prior integrability is assumed. -/
def CoordinateSubstitution {n : ℕ} (f : E n → E n) (U : Set (E n))
    (J : E n → ℝ) : Prop :=
  ∀ K : Set (E n), Jordan K → IsCompact (closure K) → closure K ⊆ U →
    Bornology.IsBounded (f '' K) ∧ Jordan (f '' K) ∧
    (∀ h : (f '' K) → ℝ, RegionBounded h →
      let g : K → ℝ := fun x => h ⟨f x, mem_image_of_mem f x.property⟩ * J x
      RegionBounded g ∧ (RegionIntegrable h ↔ RegionIntegrable g) ∧
        ((RegionIntegrable h ∨ RegionIntegrable g) → regionIntegral h = regionIntegral g)) ∧
    RegionIntegrable (fun x : K => J x) ∧
      volume (f '' K) = regionIntegral (fun x : K => J x)

end Model
open Model

def polar_chartType : Prop :=
  ∀ α : ℝ, PositiveChart polar (polarDomain α) (fun p => p 0)
def cylindrical_chartType : Prop :=
  ∀ α : ℝ, PositiveChart cylindrical (cylindricalDomain α) (fun p => p 0)
def spherical_chartType : Prop :=
  ∀ α : ℝ, PositiveChart spherical (sphericalDomain α)
    (fun p => (p 0)^2 * Real.sin (p 1))

def polar_substitutionType : Prop :=
  ∀ α : ℝ, CoordinateSubstitution polar (polarDomain α) (fun p => p 0)
def cylindrical_substitutionType : Prop :=
  ∀ α : ℝ, CoordinateSubstitution cylindrical (cylindricalDomain α) (fun p => p 0)
def spherical_substitutionType : Prop :=
  ∀ α : ℝ, CoordinateSubstitution spherical (sphericalDomain α)
    (fun p => (p 0)^2 * Real.sin (p 1))

end Specs.D04.C07.CoordinateCharts
