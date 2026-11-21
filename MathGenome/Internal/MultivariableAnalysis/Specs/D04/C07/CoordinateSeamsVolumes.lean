import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.CoordinateCharts
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.LinearVolume
import Mathlib.Topology.MetricSpace.Thickening

/-! Independent statements for `d04:07:coordinates` (the seam extension) and
`d04:07:volumes`. Integrability means the shared Darboux integral of the actual
zero extension. Parameter faces may carry any bounded values. Subregions need
not be Jordan: their *functions' zero extensions* must be Riemann integrable.
The statements below in fact allow any such subregion of the indicated bounded
geometric set, and hence include the source's Jordan-truncation case. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C07.CoordinateSeamsVolumes
open Specs.D04.C01.EuclideanInterfaces.Model (coordinates)
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.NullCovers.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C07.CoordinateCharts.Model
namespace Model

/-- Closed parameter rectangles; the proofs of the full formulas use positive
radii, whereas zero radius remains meaningful as a degenerate box. -/
def polarBox (R α : ℝ) (hR : 0 ≤ R) : Box 2 where
  lower := WithLp.toLp 2 ![0, α]
  upper := WithLp.toLp 2 ![R, α + 2 * Real.pi]
  ordered := by intro i; fin_cases i <;> dsimp <;> linarith [Real.pi_pos]

def cylinderBox (R α a b : ℝ) (hR : 0 ≤ R) (hab : a ≤ b) : Box 3 where
  lower := WithLp.toLp 2 ![0, α, a]
  upper := WithLp.toLp 2 ![R, α + 2 * Real.pi, b]
  ordered := by intro i; fin_cases i <;> dsimp <;> linarith [Real.pi_pos]

def sphericalBox (R α : ℝ) (hR : 0 ≤ R) : Box 3 where
  lower := WithLp.toLp 2 ![0, 0, α]
  upper := WithLp.toLp 2 ![R, Real.pi, α + 2 * Real.pi]
  ordered := by intro i; fin_cases i <;> dsimp <;> linarith [Real.pi_pos]

def disk (R : ℝ) : Set (E 2) := Metric.closedBall 0 R

def solidCylinder (R a b : ℝ) : Set (E 3) :=
  {x | (x 0)^2 + (x 1)^2 ≤ R^2 ∧ a ≤ x 2 ∧ x 2 ≤ b}

def ball (R : ℝ) : Set (E 3) := Metric.closedBall 0 R

/-- The union of all faces, including exterior radial/z faces. -/
def faces {n : ℕ} (Q : Box n) : Set (E n) := carrier Q \ interior (carrier Q)

/-- An arbitrary bounded assignment agreeing with a weighted pullback away
from the parameter faces. This does not assume any integrability of g. -/
def FaceAssignment {n : ℕ} (Q : Box n) (F J : E n → ℝ)
    (Φ : E n → E n) (g : carrier Q → ℝ) : Prop :=
  RegionBounded g ∧ ∀ x : carrier Q, (x : E n) ∈ interior (carrier Q) →
    g x = F (Φ x) * J x

/-- The full coordinate conclusion also covers zero-extended subregions. -/
def FullFormula {n : ℕ} (Q : Box n) (T : Set (E n))
    (Φ : E n → E n) (J : E n → ℝ) : Prop :=
  ∀ S : Set (E n), S ⊆ T → ∀ f : S → ℝ, RegionIntegrable f →
    ∀ g : carrier Q → ℝ, FaceAssignment Q (zeroExtension f) J Φ g →
      RegionIntegrable g ∧ regionIntegral g = regionIntegral f

/-- Integrability part, independent of the limiting equality. -/
def FullIntegrability {n : ℕ} (Q : Box n) (T : Set (E n))
    (Φ : E n → E n) (J : E n → ℝ) : Prop :=
  ∀ S : Set (E n), S ⊆ T → ∀ f : S → ℝ, RegionIntegrable f →
    ∀ g : carrier Q → ℝ, FaceAssignment Q (zeroExtension f) J Φ g →
      RegionIntegrable g

/-- Uniform metric neighborhoods have arbitrarily small finite box covers. -/
def VanishingNeighborhoodContent {n : ℕ} (Z : Set (E n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
    ∃ (ι : Type) (_ : Finite ι) (Q : ι → Box n),
      Metric.thickening ρ Z ⊆ ⋃ i, openCarrier (Q i) ∧
      (∑' i, ENNReal.ofReal (content (Q i))) < ENNReal.ofReal ε

end Model
open Model

def polar_formulaType : Prop := ∀ (R α : ℝ) (hR : 0 < R),
  FullFormula (polarBox R α hR.le) (disk R) polar (fun p => p 0)
def cylindrical_formulaType : Prop := ∀ (R α a b : ℝ) (hR : 0 < R) (hab : a ≤ b),
  FullFormula (cylinderBox R α a b hR.le hab) (solidCylinder R a b)
    cylindrical (fun p => p 0)
def spherical_formulaType : Prop := ∀ (R α : ℝ) (hR : 0 < R),
  FullFormula (sphericalBox R α hR.le) (ball R) spherical
    (fun p => (p 0)^2 * Real.sin (p 1))

def polar_integrabilityType : Prop := ∀ (R α : ℝ) (hR : 0 < R),
  FullIntegrability (polarBox R α hR.le) (disk R) polar (fun p => p 0)
def cylindrical_integrabilityType : Prop := ∀ (R α a b : ℝ) (hR : 0 < R) (hab : a ≤ b),
  FullIntegrability (cylinderBox R α a b hR.le hab) (solidCylinder R a b)
    cylindrical (fun p => p 0)
def spherical_integrabilityType : Prop := ∀ (R α : ℝ) (hR : 0 < R),
  FullIntegrability (sphericalBox R α hR.le) (ball R) spherical
    (fun p => (p 0)^2 * Real.sin (p 1))

/-- Bounded changes on all parameter faces preserve both existence and value. -/
def face_modificationType : Prop := ∀ {n : ℕ}, 0 < n → ∀ (Q : Box n)
    (f g : carrier Q → ℝ), RegionIntegrable f → RegionBounded g →
    (∀ x : carrier Q, (x : E n) ∈ interior (carrier Q) → f x = g x) →
      RegionIntegrable g ∧ regionIntegral g = regionIntegral f

/-- Small Cartesian neighborhoods of the image of the singular parameter
faces have vanishing content. The shrinking is expressed by finite open box
covers of arbitrarily small total content. For the spherical poles/axis the
faces r=0, φ=0, φ=π are included. Ordinary outer radial/z faces need no removal.
This is the precise neighborhood-content assertion used in truncation. -/
def polar_seamsType : Prop := ∀ (R α : ℝ) (hR : 0 ≤ R),
  ContentZero (polar '' (carrier (polarBox R α hR) ∩
    {p | p 0 = 0 ∨ p 1 = α ∨ p 1 = α + 2 * Real.pi}))
def cylindrical_seamsType : Prop := ∀ (R α a b : ℝ) (hR : 0 ≤ R) (hab : a ≤ b),
  ContentZero (cylindrical '' (carrier (cylinderBox R α a b hR hab) ∩
    {p | p 0 = 0 ∨ p 1 = α ∨ p 1 = α + 2 * Real.pi}))
def spherical_seamsType : Prop := ∀ (R α : ℝ) (hR : 0 ≤ R),
  ContentZero (spherical '' (carrier (sphericalBox R α hR) ∩
    {p | p 0 = 0 ∨ p 1 = 0 ∨ p 1 = Real.pi ∨
      p 2 = α ∨ p 2 = α + 2 * Real.pi}))

def cartesian_neighborhoodsType : Prop :=
  (∀ (R α : ℝ) (hR : 0 ≤ R),
    VanishingNeighborhoodContent (polar '' faces (polarBox R α hR))) ∧
  (∀ (R α a b : ℝ) (hR : 0 ≤ R) (hab : a ≤ b),
    VanishingNeighborhoodContent (cylindrical '' faces (cylinderBox R α a b hR hab))) ∧
  (∀ (R α : ℝ) (hR : 0 ≤ R),
    VanishingNeighborhoodContent (spherical '' faces (sphericalBox R α hR)))

def disk_areaType : Prop := ∀ (R : ℝ), 0 ≤ R →
  Jordan (disk R) ∧ volume (disk R) = Real.pi * R^2 ∧
  Jordan (Metric.ball (0 : E 2) R) ∧ volume (Metric.ball (0 : E 2) R) = Real.pi * R^2

def ball_volumeType : Prop := ∀ (R : ℝ), 0 ≤ R →
  Jordan (ball R) ∧ volume (ball R) = 4 * Real.pi * R^3 / 3 ∧
  Jordan (Metric.ball (0 : E 3) R) ∧
    volume (Metric.ball (0 : E 3) R) = 4 * Real.pi * R^3 / 3

def ellipsoid_volumeType : Prop := ∀ (R : ℝ), 0 ≤ R →
  ∀ A : E 3 ≃ₗ[ℝ] E 3,
    Jordan (A '' Metric.ball (0 : E 3) R) ∧
    volume (A '' Metric.ball (0 : E 3) R) =
      |(A : E 3 →ₗ[ℝ] E 3).det| * (4 * Real.pi * R^3 / 3)

def basis_factorType : Prop := ∀ {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (E n)) (S : Set (E n)), Jordan S →
    let A : E n ≃ₗ[ℝ] E n := (coordinates n).trans b.equivFun.symm
    (∀ u : E n, A u = ∑ i, u i • b i) ∧
    Jordan (A '' S) ∧ volume (A '' S) = |Matrix.det (fun i j => b j i)| * volume S ∧
    ∀ f : (A '' S) → ℝ, RegionBounded f →
      let g : S → ℝ := fun x => f ⟨A x, mem_image_of_mem A x.property⟩
      (RegionIntegrable f ↔ RegionIntegrable g) ∧
        ((RegionIntegrable f ∨ RegionIntegrable g) →
          regionIntegral f = |Matrix.det (fun i j => b j i)| * regionIntegral g)

def zero_radiusType : Prop :=
  (∀ {n : ℕ}, 0 < n → Jordan (Metric.closedBall (0 : E n) 0) ∧
    volume (Metric.closedBall (0 : E n) 0) = 0 ∧
    Jordan (Metric.ball (0 : E n) 0) ∧ volume (Metric.ball (0 : E n) 0) = 0) ∧
  (∀ A : E 3 →ₗ[ℝ] E 3,
    volume (A '' Metric.ball (0 : E 3) 0) = 0 ∧
    volume (A '' Metric.closedBall (0 : E 3) 0) = 0)

def zero_cylinderType : Prop := ∀ (a b : ℝ) (hab : a ≤ b),
  Jordan (solidCylinder 0 a b) ∧ volume (solidCylinder 0 a b) = 0

/-- The unmodified weighted pullbacks are integrable without a separate
boundedness premise for the transformed integrand. -/
def natural_formulasType : Prop :=
  (∀ (R α : ℝ) (hR : 0 < R) (S : Set (E 2)), S ⊆ disk R →
    ∀ f : S → ℝ, RegionIntegrable f →
      let g : carrier (polarBox R α hR.le) → ℝ := fun p => zeroExtension f (polar p) * (p : E 2) 0
      RegionIntegrable g ∧ regionIntegral g = regionIntegral f) ∧
  (∀ (R α a b : ℝ) (hR : 0 < R) (hab : a ≤ b) (S : Set (E 3)), S ⊆ solidCylinder R a b →
    ∀ f : S → ℝ, RegionIntegrable f →
      let g : carrier (cylinderBox R α a b hR.le hab) → ℝ :=
        fun p => zeroExtension f (cylindrical p) * (p : E 3) 0
      RegionIntegrable g ∧ regionIntegral g = regionIntegral f) ∧
  (∀ (R α : ℝ) (hR : 0 < R) (S : Set (E 3)), S ⊆ ball R →
    ∀ f : S → ℝ, RegionIntegrable f →
      let g : carrier (sphericalBox R α hR.le) → ℝ :=
        fun p => zeroExtension f (spherical p) * (((p : E 3) 0)^2 * Real.sin ((p : E 3) 1))
      RegionIntegrable g ∧ regionIntegral g = regionIntegral f)

/-- Explicit identification with the original box Darboux integral, rather
than merely an integral on a larger zero-extension region. -/
def rectangle_integral_bridgeType : Prop := ∀ {n : ℕ}, 0 < n → ∀ (Q : Box n)
    (g : carrier Q → ℝ), RegionIntegrable g →
      Integrable (zeroExtension g) Q ∧ lowerIntegral (zeroExtension g) Q = regionIntegral g

end Specs.D04.C07.CoordinateSeamsVolumes
