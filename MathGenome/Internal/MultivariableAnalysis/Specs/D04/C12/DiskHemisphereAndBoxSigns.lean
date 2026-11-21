import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.OutwardFirstBoundaryOrientation
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.OrientedEuclideanDictionary
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.BoundarySquaredAndFaceSigns
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The sign examples d04:12:signs. Coordinates are zero based. The disk
and hemispheres are actual subsets of the shared Euclidean three-space.
Conormals use the existing intrinsic-boundary and outward-vector definitions.
Box faces are cells, including their corners, and use increasing free coordinates. -/
noncomputable section
open Set
open scoped RealInnerProductSpace BigOperators ContDiff
namespace Specs.D04.C12.DiskHemisphereAndBoxSigns
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.OutwardFirstBoundaryOrientation.Model
open Specs.D04.C15.CellsChainsAndIntegrals.Model
namespace Model

def disk (R : ℝ) : Set (E 3) :=
  {x | x 2 = 0 ∧ x 0 ^ 2 + x 1 ^ 2 ≤ R ^ 2}
def equator (R : ℝ) : Set (E 3) :=
  {x | x 2 = 0 ∧ x 0 ^ 2 + x 1 ^ 2 = R ^ 2}
def hemisphere (R : ℝ) (upper : Bool) : Set (E 3) :=
  {x | x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = R ^ 2 ∧
    (if upper then 0 ≤ x 2 else x 2 ≤ 0)}
def radial (R : ℝ) (x : E 3) : E 3 := R⁻¹ • x
def ccw (R : ℝ) (x : E 3) : E 3 :=
  WithLp.toLp 2 ![-x 1 / R, x 0 / R, 0]
def circle (R θ : ℝ) : E 3 :=
  WithLp.toLp 2 ![R * Real.cos θ, R * Real.sin θ, 0]

def boxMap {n : ℕ} (a b : E n) (u : E n) : E n :=
  WithLp.toLp 2 (fun i => a i + (b i - a i) * u i)
def boxFace {k : ℕ} (a b : E (k+1)) (i : Fin (k+1)) (upper : Bool) : E k → E (k+1) :=
  boxMap a b ∘ faceInsertion i upper

end Model
open Model

def disk_signsType : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ x ∈ equator R,
    x ∈ intrinsicBoundary 1 2 (disk R) ∧
    IsOutwardUnitConormal 1 1 (disk R) x (radial R x) ∧
    euclideanCross (standardBasis 3 2) (radial R x) = ccw R x ∧
    ‖ccw R x‖ = 1 ∧
    euclideanCross (radial R x) (ccw R x) = standardBasis 3 2

def hemisphere_signsType : Prop :=
  ∀ (R : ℝ), 0 < R → ∀ upper : Bool, ∀ x ∈ equator R,
    x ∈ intrinsicBoundary 1 2 (hemisphere R upper) ∧
    IsOutwardUnitConormal 1 1 (hemisphere R upper) x
      (if upper then -standardBasis 3 2 else standardBasis 3 2) ∧
    euclideanCross (radial R x)
      (if upper then -standardBasis 3 2 else standardBasis 3 2) =
      (if upper then ccw R x else -ccw R x) ∧
    euclideanCross (if upper then -standardBasis 3 2 else standardBasis 3 2)
      (if upper then ccw R x else -ccw R x) = radial R x

/-- Increasing angle is the usual counterclockwise traversal viewed from +z.
Its velocity is the positive speed R times the disk/upper-hemisphere tangent. -/
def circle_traversalType : Prop :=
  ∀ (R : ℝ), 0 < R →
    (∀ θ, circle R θ ∈ equator R ∧
      HasDerivAt (circle R) (R • ccw R (circle R θ)) θ) ∧
    (∀ x ∈ equator R, ∃ θ, circle R θ = x) ∧
    circle R (2 * Real.pi) = circle R 0

/-- The standard angular parametrization has no repeated point before its
terminal endpoint. Together with the surjectivity and endpoint equality above,
this certifies a single traversal of the seam. -/
def circle_single_traversalType : Prop :=
  ∀ R : ℝ, 0 < R → Set.InjOn (circle R) (Set.Ico 0 (2 * Real.pi))

def hemisphere_unionType : Prop :=
  ∀ R : ℝ,
    hemisphere R true ∪ hemisphere R false =
      {x : E 3 | x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = R ^ 2} ∧
    hemisphere R true ∩ hemisphere R false = equator R

/-- The affine cell covers the whole geometric box, with multiplicity one. -/
def box_parametrizationType : Prop :=
  ∀ {n : ℕ} (a b : E n), (∀ i, a i < b i) →
    boxMap a b '' cube n = {x | ∀ i, a i ≤ x i ∧ x i ≤ b i} ∧
    Function.Injective (boxMap a b)

/-- Actual tangent columns of the affine box face. -/
def box_face_derivativeType : Prop :=
  ∀ {k : ℕ} (a b : E (k+1)) (i : Fin (k+1)) (upper : Bool)
    (u : E k) (j : Fin k),
    totalDerivative (boxFace a b i upper) u (standardBasis k j) =
      (b (i.succAbove j) - a (i.succAbove j)) •
        standardBasis (k+1) (i.succAbove j)

/-- The determinant is normalized by the positive face density. Thus its sign
is the outward-first orientation of the *actual* face parametrization. -/
def box_face_signsType : Prop :=
  ∀ {k : ℕ} (a b : E (k+1)), (∀ j, a j < b j) →
    ∀ (i : Fin (k+1)) (upper : Bool) (u : E k),
    let ν := if upper then standardBasis (k+1) i else -standardBasis (k+1) i
    let d := (standardBasis (k+1)).det
      (Fin.cons ν (fun j : Fin k =>
        totalDerivative (boxFace a b i upper) u (standardBasis k j)))
    let s := if upper then (-1 : ℝ)^i.val else -(-1 : ℝ)^i.val
    d = s * ∏ j : Fin k, (b (i.succAbove j) - a (i.succAbove j)) ∧
    Real.sign d = s

def box_face_normalType : Prop :=
  ∀ {k : ℕ} (a b : E (k+1)), (∀ j, a j < b j) →
    ∀ (i : Fin (k+1)) (upper : Bool) (u : E k), u ∈ cube k →
    let ν := if upper then standardBasis (k+1) i else -standardBasis (k+1) i
    boxFace a b i upper u ∈ {x | ∀ j, a j ≤ x j ∧ x j ≤ b j} ∧
    ‖ν‖ = 1 ∧ (∀ w : E (k+1), w i = 0 → ⟪ν, w⟫ = 0) ∧
    ∀ t : ℝ, 0 < t →
      boxFace a b i upper u + t • ν ∉ {x | ∀ j, a j ≤ x j ∧ x j ≤ b j}

/-- The common equator is traversed once by the increasing-angle circle cell.
The two induced orientations are its positive and negative signed chains;
their actual directed integrals cancel for every ambient one-form. -/
def hemisphere_seamType : Prop :=
  ∀ R : ℝ, 0 < R → ∃ c : Cell 1 1 (Set.univ : Set (E 3)),
    (∀ u : cube 1, (c.toFun u).val = circle R (2 * Real.pi * u.val 0)) ∧
    Set.range (fun u : cube 1 => (c.toFun u).val) = equator R ∧
    ∀ eta : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 3 1,
      chainIntegral eta (Finsupp.single c 1) +
        chainIntegral eta (-Finsupp.single c 1) = 0

/-- The seam integrals are proper Riemann integrals for ambient continuous
forms defined on any neighborhood of the equator, rather than merely values
of the totalized integral selector. -/
def equator_integrableType : Prop :=
  ∀ R : ℝ, 0 < R → ∀ c : Cell 1 1 (Set.univ : Set (E 3)),
    (∀ u : cube 1, (c.toFun u).val = circle R (2 * Real.pi * u.val 0)) →
    ∀ (V : Set (E 3)) (eta : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField 3 1),
      Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 0) V eta → equator R ⊆ V →
      ∃ hi : Specs.D04.C06.DarbouxIntegral.Model.Integrable (cellCoefficient c eta) (cubeBox 1),
        cellIntegral c eta = Specs.D04.C06.DarbouxIntegral.Model.integral
          (cellCoefficient c eta) (cubeBox 1) hi

/-- A genuine affine box cell, with the complete C¹ ambient Stokes formula.
No smooth-boundary-manifold structure is imposed at its corners. -/
def box_cell_stokesType : Prop :=
  ∀ {k : ℕ} (a b : E (k+1)), (∀ i, a i < b i) →
    ∃ c : Cell 1 (k+1) (Set.univ : Set (E (k+1))),
      (∀ u : cube (k+1), (c.toFun u).val = boxMap a b u) ∧
      ∀ (V : Set (E (k+1)))
        (eta : Specs.D04.C13.NormalizedFormsAndWedge.Model.FormField (k+1) k),
        Specs.D04.C13.NormalizedFormsAndWedge.Model.IsCrForm (some 1) V eta →
        (∀ u ∈ cube (k+1), boxMap a b u ∈ V) →
        cellIntegral c (Specs.D04.C13.ExteriorDerivative.Model.exteriorDerivative eta) =
          ∑ i : Fin (k+1), (-1 : ℝ)^i.val *
            (cellIntegral (cellFace c i true) eta - cellIntegral (cellFace c i false) eta)

end Specs.D04.C12.DiskHemisphereAndBoxSigns
