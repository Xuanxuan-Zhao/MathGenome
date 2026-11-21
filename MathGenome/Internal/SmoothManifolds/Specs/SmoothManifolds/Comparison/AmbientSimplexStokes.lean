import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.SmoothSingularComplex
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.Stokes
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Ambient simplex Stokes, paper.tex:2000–2068 and 2741–2775.
All forms, derivatives, measures and affine faces are the shared genuine ones.
The local C¹ extension hypothesis is imposed only along the compact simplex.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Topology

namespace SmoothManifolds.IntegrationCochainData
open ModelData CornerData SmoothSingularData

/-- Decreases the corresponding affine barycentric face function by one. -/
def faceOutward {q : ℕ} (j : Fin (q+2)) : Euclidean (q+1) :=
  Fin.cases (Pi.single 0 1) (fun i => -(Pi.single i 1)) j

/-- Outward vector followed by the edges of the actual ordered face map. -/
def orderedFaceFrame {q : ℕ} (j : Fin (q+2)) : Fin (q+1) → Euclidean (q+1) :=
  Fin.cons (faceOutward j)
    (fun k : Fin q => faceAmbient j (Pi.single k 1) - faceAmbient j 0)
end SmoothManifolds.IntegrationCochainData

namespace SmoothManifolds.AmbientSimplexData
open ModelData LocalStokesData CornerData SmoothSingularData Set MeasureTheory Filter

/-- Coefficient of the exterior derivative in the ambient source orientation. -/
def bulkCoefficient {q : ℕ} (α : CoordinateForm (q+1) q) (x : Euclidean (q+1)) : ℝ :=
  extDerivWithin α (simplexSet (q+1)) x (frame (q+1))

/-- The pullback coefficient along the ordered affine face parametrization. -/
def faceCoefficient {q : ℕ} (α : CoordinateForm (q+1) q)
    (j : Fin (q+2)) (y : Euclidean q) : ℝ :=
  α (faceAmbient j y) (fun i => fderiv ℝ (faceAmbient j) y (frame q i))

/-- The actual global barycentric face subset germ, including face intersections. -/
def simplexFaceGerm {n : ℕ} (p : CornerData.Simplex n) (j : Fin (n+1)) :
    Germ (𝓝 p) Prop :=
  Germ.ofFun (fun x : CornerData.Simplex n => simplexBarycentric x.val j = 0)

/-- Geometric properties of the existing affine corner chart family. No face,
orientation, differential-form, or Stokes certificate is assumed. -/
structure IsSimplexChartFamily {n : ℕ}
    (S : CornerManifold n (CornerData.Simplex n))
    (c : Fin (n+1) → CornerChart n (CornerData.Simplex n)) : Prop where
  atlas : S.atlas = cornerMaximalExtension (range c)
  mem_atlas : ∀ j, c j ∈ S.atlas
  constraints : ∀ j, (c j).1 = Fin.last n
  source : ∀ j, (c j).2.source = {x | 0 < simplexBarycentric x.val j}
  target : ∀ j, (c j).2.target = {y | ∑ r, y.val r < 1}
  apply : ∀ j x, x ∈ (c j).2.source → ((c j).2 x).val = simplexOmitBarycentric j x.val
  symm_apply : ∀ j y, y ∈ (c j).2.target →
    ((c j).2.symm y).val = simplexRestoreBarycentric j y.val

end SmoothManifolds.AmbientSimplexData

namespace Specs.SmoothManifolds.Comparison.AmbientSimplexStokes
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.LocalStokesData
  _root_.SmoothManifolds.CornerData _root_.SmoothManifolds.SmoothSingularData
  _root_.SmoothManifolds.IntegrationCochainData _root_.SmoothManifolds.AmbientSimplexData
  _root_.SmoothManifolds.CornerStokesData _root_.SmoothManifolds.CornerOrientationData
  Set MeasureTheory

def face_outwardType : Prop :=
  ∀ {q : ℕ} (j : Fin (q+2)),
    simplexBarycentric (faceOutward j) j - simplexBarycentric (0 : Euclidean (q+1)) j = -1

def face_orientationType : Prop :=
  ∀ {q : ℕ} (j : Fin (q+2)),
    (Matrix.of (fun r k : Fin (q+1) => orderedFaceFrame j k r)).det = (-1 : ℝ)^j.val

def simplex_compactType : Prop := ∀ n : ℕ, IsCompact (simplexSet n)

/-- Every displayed ordered edge really is the derivative of the affine face. -/
def face_derivativeType : Prop :=
  ∀ {q : ℕ} (j : Fin (q+2)) (y : Euclidean q) (i : Fin q),
    fderiv ℝ (faceAmbient j) y (frame q i) =
      faceAmbient j (Pi.single i 1) - faceAmbient j 0

/-- C¹ regularity alone supplies both bulk and all face integrability. -/
def integrabilityType : Prop :=
  ∀ (q : ℕ) (α : CoordinateForm (q+1) q),
    LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val) →
    IntegrableOn (AmbientSimplexData.bulkCoefficient α) (simplexSet (q+1)) ∧
      ∀ j : Fin (q+2), IntegrableOn (faceCoefficient α j) (simplexSet q)

/-- Full ambient Stokes; for q=0 this is right-positive/left-negative evaluation. -/
def stokesType : Prop :=
  ∀ (q : ℕ) (α : CoordinateForm (q+1) q),
    LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val) →
    IntegrableOn (AmbientSimplexData.bulkCoefficient α) (simplexSet (q+1)) ∧
    (∀ j : Fin (q+2), IntegrableOn (faceCoefficient α j) (simplexSet q)) ∧
    (∫ x in simplexSet (q+1), AmbientSimplexData.bulkCoefficient α x) =
      ∑ j : Fin (q+2), (-1 : ℝ)^j.val *
        ∫ y in simplexSet q, faceCoefficient α j y

/-- The entire resolved boundary is the disjoint union of the ordered faces.
The germ identity ensures sheets are distinct even over a multiple corner. -/
def resolved_facesType : Prop :=
  ∀ (q : ℕ) (S : CornerManifold (q+1) (CornerData.Simplex (q+1)))
    (c : Fin (q+2) → CornerChart (q+1) (CornerData.Simplex (q+1))),
    IsSimplexChartFamily S c →
    ∃ E : (Fin (q+2) × CornerData.Simplex q) ≃ₜ ResolvedFaceSpace S,
      (∀ j y, (E (j,y)).1 = face j y) ∧
      ∀ j y, (E (j,y)).2.val = simplexFaceGerm (E (j,y)).1 j

/-- The existing simplex source geometry supplies this interface. -/
def source_geometryType : Prop :=
  ∀ n : ℕ, ∃ (S : CornerManifold n (CornerData.Simplex n))
    (c : Fin (n+1) → CornerChart n (CornerData.Simplex n)),
    IsSimplexChartFamily S c ∧
    ∃ o : CornerOrientation S,
      ∀ j (hc : c j ∈ S.atlas) (p : (c j).2.source),
        _root_.SmoothManifolds.OrientationData.signValue (o.sign (c j) hc p) = (-1 : ℝ)^j.val

/-- Right-positive, left-negative endpoints, with the empty-product measure. -/
def endpoint_sumType : Prop :=
  ∀ α : CoordinateForm 1 0,
    (∑ j : Fin 2, (-1 : ℝ)^j.val * ∫ y in simplexSet 0, faceCoefficient α j y) =
      α 1 (fun i : Fin 0 => Fin.elim0 i) - α 0 (fun i : Fin 0 => Fin.elim0 i)

/-- Coordinate forms on the compact simplex must be realized by genuine corner
forms and the coordinate-compatible integrals used in corner Stokes. This is an
existence conclusion, never a new assumption on α. -/
def corner_integral_bridgeType : Prop :=
  ∀ (q : ℕ) (α : CoordinateForm (q+1) q),
    LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val) →
    ∃ (S : CornerManifold (q+1) (CornerData.Simplex (q+1)))
      (c : Fin (q+2) → CornerChart (q+1) (CornerData.Simplex (q+1)))
      (o : CornerOrientation S),
      IsSimplexChartFamily S c ∧
      (∀ j (hc : c j ∈ S.atlas) (p : (c j).2.source),
        _root_.SmoothManifolds.OrientationData.signValue (o.sign (c j) hc p) = (-1 : ℝ)^j.val) ∧
      ∃ ω : Form S q,
        IsRegularForm 1 ω ∧ IsCompact (formSupport ω) ∧
        (∀ j (hc : c j ∈ S.atlas) (p : (c j).2.source),
          ω.field (c j) hc p = (α p.val.val).compContinuousLinearMap
            (fderiv ℝ (simplexRestoreBarycentric j) ((c j).2 p.val).val)) ∧
        ∃ (T : CornerManifold q (ResolvedFaceSpace S)) (b : CornerOrientation T)
          (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
          IsResolvedOrientation o b ∧ IsIntegral o I ∧ IsIntegral b J ∧
          ∀ (η : CompactTopForm S) (β : CompactTopForm T),
            HasDerivative ω η.form → IsFaceRestriction ω β.form →
            I η = (∫ x in simplexSet (q+1), AmbientSimplexData.bulkCoefficient α x) ∧
            J β = (∑ j : Fin (q+2), (-1 : ℝ)^j.val *
              ∫ y in simplexSet q, faceCoefficient α j y)

end Specs.SmoothManifolds.Comparison.AmbientSimplexStokes
