import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Boundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.StandardCoverings

/-! The sphere and projective plane here are the literal constructions of Chapter 1.
The radial test below spells out the outward-first convention in the ambient
ordered coordinates: the radial vector p points out of {squareSum ≤ 1} and is
inserted before the tangential determinant vector. Ambient tangent coordinates
are evaluated on actual smooth germs, rather than on an arbitrary linear map.
-/
set_option autoImplicit false
noncomputable section

namespace SmoothManifolds.ProjectiveOrientationData
open ModelData AtlasData TangentData OrientationData SphereTorusData ProjectiveData
  BoundaryOrientationData Filter

/-- The derivative of the literal inclusion S² → ℝ³, expressed in the fixed
ambient coordinates by its action on coordinate germs. -/
def IsAmbientDifferential (S : SmoothManifold 2 .euclidean (Sphere 2))
    (p : Sphere 2) (L : TangentSpace S p →ₗ[ℝ] Euclidean 3) : Prop :=
  ∀ i : Fin 3, ∃ g : SmoothGerm S p,
    g.val = Germ.ofFun (fun q : Sphere 2 => q.val i) ∧
      ∀ v, L v i = v.val g

/-- Evaluation in the standard ordered determinant line of ℝ³. -/
def ambientDeterminant : (⋀[ℝ]^3 (Euclidean 3)) →ₗ[ℝ] ℝ :=
  exteriorPower.alternatingMapLinearEquiv
    (@Module.Basis.det ℝ _ (Euclidean 3) _ _ (Fin 3) _ _ (Pi.basisFun ℝ (Fin 3)))

/-- Outward-first orientation of the actual unit sphere: the first vector is
its outward radial normal. Existence of the actual ambient derivative is part
of this property, so the positivity condition is never vacuous. -/
def IsOutwardSphereOrientation (S : SmoothManifold 2 .euclidean (Sphere 2))
    (o : Orientation S) : Prop :=
  (∀ p, ∃ L, IsAmbientDifferential S p L) ∧
  ∀ p L, IsAmbientDifferential S p L → ∀ η : DeterminantLine S p,
    (IsPositive (o.val p) η ↔
      0 < ambientDeterminant (normalWedge L p.val η))

end SmoothManifolds.ProjectiveOrientationData

namespace Specs.SmoothManifolds.Orientations.ProjectivePlane
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.SphereTorusData
  _root_.SmoothManifolds.ProjectiveData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.OrientationProductData _root_.SmoothManifolds.ProjectiveOrientationData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData

/-- The standard sphere admits its smooth unit-ball outward-first orientation,
characterized on its actual embedded tangent determinant lines. -/
def sphere_boundary_orientationType : Prop :=
  ∀ S : SmoothManifold 2 .euclidean (Sphere 2),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2) →
    ∃! o : Orientation S, IsOutwardSphereOrientation S o

/-- The antipodal diffeomorphism reverses every orientation of S², in particular
the outward-first one. The maps on determinant rays are the actual d(antipode). -/
def antipodal_reversesType : Prop :=
  ∀ S : SmoothManifold 2 .euclidean (Sphere 2),
    S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas 2) →
    IsLocalDiffeomorphism S S antipode ∧
    ∀ (o : Orientation S)
      (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace S (antipode p)),
      (∀ p, IsDifferential S S antipode p (E p).toLinearMap) →
      ∀ p, Module.Ray.map (determinantMap 2 (E p)) (o.val p) = -o.val (antipode p)

/-- Nonorientability for every realization of the standard ratio atlas on the
literal antipodal quotient, with no hypothetical orientability assumption. -/
def projective_nonorientableType : Prop :=
  ∀ P : SmoothManifold 2 .euclidean (RealProjectiveSpace 2),
    P.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas 2) →
    ¬Nonempty (Orientation P)

end Specs.SmoothManifolds.Orientations.ProjectivePlane
