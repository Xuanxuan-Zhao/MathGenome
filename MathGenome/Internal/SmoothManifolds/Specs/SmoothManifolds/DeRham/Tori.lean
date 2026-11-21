import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.SpheresAndTori
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.PathIntegration

/-! Independent statement of the torus clause of M11.04 (paper.tex 2320–2327,
2347–2376). Use the permitted model S¹ = ℝ/ℤ, with its standard angle atlas.
The homogeneous pieces below are the actual exterior powers of ℝ^r. Their
wedge is exterior-algebra multiplication, including its graded signs.
No averaging operator or cohomological calculation is part of the hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace SmoothManifolds.TorusDeRhamData
open ModelData AtlasData TangentData TangentBundleData BundleOperationsData
  CovectorData ExteriorData DeRhamData SphereTorusData PathIntegrationData

/-- The degree-k part of the exterior algebra on r degree-one generators. -/
abbrev ExteriorModel (r k : ℕ) := ⋀[ℝ]^k (Euclidean r)

/-- The jth positively oriented coordinate loop, with period one. -/
def coordinateLoop {r : ℕ} (j : Fin r) (t : ℝ) : FlatTorus r :=
  quotientProjection r (Pi.single j t)

/-- The underlying covector field of an intrinsic exterior one-form. -/
def covectorField {r : ℕ} {S : SmoothManifold r .euclidean (FlatTorus r)}
    (ω : Field S 1) : CovectorField S :=
  fun p => exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p)) (ω p)

/-- In every genuine local lift of the quotient, this form is dx^i. In
particular this specifies the descent of dt with normalization one, not 2π. -/
def IsCoordinateForm {r : ℕ} {S : SmoothManifold r .euclidean (FlatTorus r)}
    (C : CotangentBundle S) (i : Fin r) (ω : Field S 1) : Prop :=
  ∀ (c : ModelChart r .euclidean (FlatTorus r)) (hc : c ∈ S.smoothStructure.val)
    (z : Euclidean r) (ε : ℝ),
    0 < ε → ε < 1 / 4 → IsAngleChart z ε c →
    ∀ (p : FlatTorus r) (hp : p ∈ c.source),
      covectorField ω p = coordinateCovector C.tangent.fiberCoordinates c hc p hp i

/-- A graded real algebra isomorphism, specified in every degree and on each
coordinate generator. The input product is the one induced by actual wedge
(as asserted in the theorem hypothesis IsGradedProduct). -/
structure Presentation {r : ℕ} {S : SmoothManifold r .euclidean (FlatTorus r)}
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (P : K.GradedProduct) where
  theta : Fin r → K.closed 1
  coordinate : ∀ i, IsCoordinateForm C i (theta i).val.val
  loop_smooth : ∀ j : Fin r, PiecewiseSmoothOn S (coordinateLoop j) 0 1
  loop_closed : ∀ j : Fin r, coordinateLoop j 0 = coordinateLoop j 1
  period : ∀ i j : Fin r,
    pathIntegral S (covectorField (theta i).val.val) (coordinateLoop j) 0 1 =
      if i = j then 1 else 0
  equiv : ∀ k, ExteriorModel r k ≃ₗ[ℝ] K.Cohomology k
  generator : ∀ i : Fin r,
    equiv 1 ((exteriorPower.oneEquiv ℝ (Euclidean r)).symm (Pi.single i 1)) =
      K.classOf 1 (theta i)
  one : equiv 0 ((exteriorPower.zeroEquiv ℝ (Euclidean r)).symm 1) = P.one
  mul : ∀ k l (x : ExteriorModel r k) (y : ExteriorModel r l),
    equiv (k+l) (exteriorPower.wedge ℝ (Euclidean r) k l x y) =
      P.mul k l (equiv k x) (equiv l y)

end SmoothManifolds.TorusDeRhamData

namespace Specs.SmoothManifolds.DeRham.Tori
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.DeRhamData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.TorusDeRhamData

/-- Full torus algebra computation for every nonnegative r, including the
empty product (a point). There are no extra topological or calculus hypotheses:
the atlas equality identifies the standard smooth structure, and Calculus and
IsGradedProduct identify the already constructed intrinsic de Rham objects.
Negative degrees have the fixed zero-space convention of M11.01. -/
def torus_algebraType : Prop :=
  ∀ (r : ℕ) (S : SmoothManifold r .euclidean (FlatTorus r)),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas r) →
    ∀ (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
      (K : Calculus C B) (P : K.GradedProduct),
      K.IsGradedProduct P → Nonempty (Presentation K P)

end Specs.SmoothManifolds.DeRham.Tori
