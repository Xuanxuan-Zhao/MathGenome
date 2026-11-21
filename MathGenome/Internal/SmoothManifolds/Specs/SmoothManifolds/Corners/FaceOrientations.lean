import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.Products
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Boundary
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Real.Sign

/-! Outward-first orientation data for smoothly extendible corner charts.

The orientation is a locally constant signed-coordinate ray in every chart,
with the usual Jacobian compatibility. Compatibility is the definition of an
orientation, not an assumption of an induced orientation on the resolved faces.
Normal directions are measured in the actual quotient by the face hyperplane.
-/
noncomputable section
open scoped Classical

namespace SmoothManifolds.CornerOrientationData
open ModelData CornerData OrientationData Set
universe u

/-- The tangent hyperplane of the coordinate face, even at a multiple corner. -/
def faceHyperplane {n : ℕ} (i : Fin n) : Submodule ℝ (Euclidean n) :=
  LinearMap.ker (LinearMap.proj i)

abbrev FaceNormalLine {n : ℕ} (i : Fin n) := Euclidean n ⧸ faceHyperplane i

def coordinateInwardRay {n : ℕ} (i : Fin n) : Set (FaceNormalLine i) :=
  Submodule.Quotient.mk '' {v | 0 < v i}

def coordinateOutwardRay {n : ℕ} (i : Fin n) : Set (FaceNormalLine i) :=
  Submodule.Quotient.mk '' {v | v i < 0}

/-- Insert a zero coordinate: the actual derivative of the face inclusion. -/
def faceInsertion {n : ℕ} (i : Fin (n+1)) : Euclidean n →ₗ[ℝ] Euclidean (n+1) where
  toFun := fun v => i.insertNth (0 : ℝ) v
  map_add' := by
    intro v w
    funext r
    refine Fin.succAboveCases i ?_ (fun j => ?_) r <;> simp
  map_smul' := by
    intro a v
    funext r
    refine Fin.succAboveCases i ?_ (fun j => ?_) r <;> simp

/-- The outward-first sign in the coordinate frame with coordinate i deleted. -/
def faceSign {n : ℕ} (ε : ℝ) (i : Fin n) : ℝ := ε * (-1 : ℝ)^(i.val+1)

/-- Deletion is a linear map in the ordered tangential coordinates. -/
def faceDeletion {n : ℕ} (i : Fin (n+1)) : Euclidean (n+1) →ₗ[ℝ] Euclidean n where
  toFun := i.removeNth
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The derivative on a coordinate face is deletion after the ambient
transition derivative after zero insertion. -/
def faceDerivative {n : ℕ} (L : Euclidean (n+1) →ₗ[ℝ] Euclidean (n+1))
    (i j : Fin (n+1)) : Euclidean n →ₗ[ℝ] Euclidean n :=
  (faceDeletion j).comp (L.comp (faceInsertion i))

/-- The ordered coordinate determinant, also in degree zero. -/
def coordinateVolume (n : ℕ) : ⋀[ℝ]^n (Euclidean n) :=
  exteriorPower.ιMulti ℝ n (Pi.basisFun ℝ (Fin n))

/-- Signed charts for the full maximal corner atlas. This retains both signs
in dimension zero and never requires a reflection of a constrained coordinate. -/
structure CornerOrientation {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) where
  sign : ∀ c : CornerChart n M, c ∈ S.atlas → c.2.source → Bool
  locallyConstant : ∀ c hc, IsLocallyConstant (sign c hc)
  compatible : ∀ (c d : CornerChart n M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p)),
    signValue (sign d hd ⟨p,hq⟩) = signValue (sign c hc ⟨p,hp⟩) *
      Real.sign (LinearMap.det (fderiv ℝ H.map (c.2 p).val).toLinearMap)

/-- Compatible signed coordinates on a generating atlas. This is the local
input to descent, with no orientation on its maximal extension assumed. -/
structure CornerAtlasOrientation {n : ℕ} {M : Type u} [TopologicalSpace M]
    (A : Set (CornerChart n M)) where
  sign : ∀ c : CornerChart n M, c ∈ A → c.2.source → Bool
  locallyConstant : ∀ c hc, IsLocallyConstant (sign c hc)
  compatible : ∀ (c d : CornerChart n M) (hc : c ∈ A) (hd : d ∈ A)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p)),
    signValue (sign d hd ⟨p,hq⟩) = signValue (sign c hc ⟨p,hp⟩) *
      Real.sign (LinearMap.det (fderiv ℝ H.map (c.2 p).val).toLinearMap)

/-- An outward-first orientation on the full resolved space. Its value is
specified in every coordinate-deletion chart, also over a multiple corner. -/
def IsResolvedOrientation {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S)
    {T : CornerManifold n (ResolvedFaceSpace S)} (b : CornerOrientation T) : Prop :=
  T.atlas = cornerMaximalExtension {e | IsResolvedFaceChart S e} ∧
  ∀ (c : CornerChart (n+1) M) (hc : c ∈ S.atlas)
    (i : Fin (n+1)) (hi : i.val < c.1.val)
    (e : CornerChart n (ResolvedFaceSpace S)) (he : e ∈ T.atlas),
    e.1 = faceConstraintCount c.1 → e.2.source = faceSheet S c i univ →
    (∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val)) →
    ∀ (q : ResolvedFaceSpace S) (hq : q ∈ e.2.source)
      (hp : q.1 ∈ c.2.source),
      signValue (b.sign e he ⟨q,hq⟩) = faceSign (signValue (o.sign c hc ⟨q.1,hp⟩)) i

/-- The same base point in the linearly converted ordinary chart. -/
def ordinaryPoint {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (E : CornerProductData.ModelOrthantCoordinates n a) (c : ModelChart n a M)
    (p : c.source) : (CornerProductData.ordinaryCornerChart E c).2.source :=
  ⟨p.val, by simpa [CornerProductData.ordinaryCornerChart] using p.property⟩

/-- Compare to the existing intrinsic ordinary determinant rays through their
proved signed-chart formulation. The ambient coordinate change contributes its
own determinant sign, so an orientation-reversing model permutation is allowed. -/
def IsOrdinaryOrientation {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : AtlasData.SmoothManifold n a M) (E : CornerProductData.ModelOrthantCoordinates n a)
    (R : CornerManifold n M)
    (hsub : CornerProductData.ordinaryCornerAtlas E S.smoothStructure.val ⊆ R.atlas)
    (o : CornerOrientation R) (r : Orientation S) : Prop :=
  ∃ s : SignedCharts S, RepresentsSignedCharts r.val s ∧
    ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source),
      signValue (s.sign c hc p) =
        signValue (o.sign (CornerProductData.ordinaryCornerChart E c)
          (hsub ⟨c,hc,rfl⟩) (ordinaryPoint E c p)) *
          Real.sign (LinearMap.det E.linearEquiv.toLinearMap)

/-- Ordered product determinant in the actual generating product coordinates.
Its inverse coordinate map is the projection tangent splitting. -/
def coordinateProductVector {m n : ℕ} {k : Fin (m+1)} {l : Fin (n+1)}
    (C : CornerProductData.OrthantProductCoordinates m n k l)
    (v : ⋀[ℝ]^m (Euclidean m)) (w : ⋀[ℝ]^n (Euclidean n)) :
    ⋀[ℝ]^(m+n) (Euclidean (m+n)) :=
  OrientationProductData.determinantMap (m+n) C.linearEquiv.toLinearEquiv
    (OrientationProductData.orderedWedge m n (Euclidean m) (Euclidean n) v w)

/-- Strict positivity in a signed coordinate determinant line, including degree zero. -/
def CoordinatePositive {n : ℕ} (b : Bool) (v : ⋀[ℝ]^n (Euclidean n)) : Prop :=
  ∃ a : ℝ, 0 < a ∧ v = a • (signValue b • coordinateVolume n)

/-- The ordered determinant product in the actual generating product charts.
The inverse model identification is the projection tangent splitting. -/
def IsCornerProductOrientation {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : CornerManifold m M} {T : CornerManifold n N}
    {P : CornerManifold (m+n) (M × N)}
    (C : CornerProductData.ProductCoordinateFamily m n)
    (o : CornerOrientation S) (q : CornerOrientation T) (r : CornerOrientation P) : Prop :=
  ∀ (c : CornerChart m M) (hc : c ∈ S.atlas)
    (d : CornerChart n N) (hd : d ∈ T.atlas)
    (he : CornerProductData.productChart C c d ∈ P.atlas)
    (p : M × N) (hp : p ∈ c.2.source ×ˢ d.2.source)
    (hP : p ∈ (CornerProductData.productChart C c d).2.source)
    (v : ⋀[ℝ]^m (Euclidean m)) (w : ⋀[ℝ]^n (Euclidean n)),
      CoordinatePositive (o.sign c hc ⟨p.1,hp.1⟩) v →
      CoordinatePositive (q.sign d hd ⟨p.2,hp.2⟩) w →
      CoordinatePositive (r.sign (CornerProductData.productChart C c d) he ⟨p,hP⟩)
        (coordinateProductVector (C c.1 d.1) v w)

end SmoothManifolds.CornerOrientationData

namespace Specs.SmoothManifolds.Corners.FaceOrientations
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.CornerData
  _root_.SmoothManifolds.CornerOrientationData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.BoundaryOrientationData Set

/-- Descent from any covering subatlas to the full maximal corner atlas. -/
def orientation_extensionType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (A : Set (CornerChart n M)) (hsub : A ⊆ S.atlas),
    (∀ p : M, ∃ c ∈ A, p ∈ c.2.source) →
    ∀ a : CornerAtlasOrientation A, ∃! o : CornerOrientation S,
      ∀ c (hc : c ∈ A) (p : c.2.source), o.sign c (hsub hc) p = a.sign c hc p

/-- Every pair of outward normals represents the same positive half-line
in the actual quotient by the face tangent hyperplane. -/
def normal_half_lineType : Prop :=
  ∀ {n : ℕ} (i : Fin n) (v w : Euclidean n), v i < 0 → w i < 0 →
    ∃ a : ℝ, 0 < a ∧ w - a • v ∈ faceHyperplane i ∧
      (Submodule.Quotient.mk w : FaceNormalLine i) = a • Submodule.Quotient.mk v

/-- Tangential changes and positive rescaling of an outward vector have no
orientation effect, expressed in the original exterior algebra. -/
def outward_independentType : Prop :=
  ∀ {n : ℕ} (i : Fin (n+1)) (v w : Euclidean (n+1)), v i < 0 → w i < 0 →
    ∃ a : ℝ, 0 < a ∧ ∀ η : ⋀[ℝ]^n (Euclidean n),
      normalWedge (faceInsertion i) w η = a • normalWedge (faceInsertion i) v η

/-- The signed outward-first formula for every deleted coordinate. -/
def coordinate_face_signType : Prop :=
  ∀ {n : ℕ} (i : Fin (n+1)) (b : Fin (n+1) → Euclidean (n+1)),
    ExteriorAlgebra.ι ℝ (-b i) *
      ExteriorAlgebra.ιMulti ℝ n (i.removeNth b) =
      (-1 : ℝ)^(i.val+1) • ExteriorAlgebra.ιMulti ℝ (n+1) b

/-- The cone isomorphism preserves the normal quotient ray and the
outward-first determinant sign of every corresponding local face. -/
def cone_face_orientationType : Prop :=
  ∀ {n : ℕ} {k l : Fin (n+2)} (x : Orthant (n+1) k) (y : Orthant (n+1) l)
    (E : Euclidean (n+1) ≃ₗ[ℝ] Euclidean (n+1)),
    E '' modelCone x = modelCone y →
    ∃ σ : activeCoordinates y ≃ activeCoordinates x,
      ∃ a : activeCoordinates y → ℝ, (∀ j, 0 < a j) ∧
      (∀ v j, E v j.val = a j * v (σ j).val) ∧
      (∀ v j, E v ∈ faceHyperplane j.val ↔ v ∈ faceHyperplane (σ j).val) ∧
      (∀ v j, E v j.val < 0 ↔ v (σ j).val < 0) ∧
      ∀ j, faceSign 1 j.val * LinearMap.det E.toLinearMap =
        a j * (faceSign 1 (σ j).val *
          LinearMap.det (faceDerivative E.toLinearMap (σ j).val j.val))

/-- The local cofactor identity implies the compatibility of the prescribed
signs of two face charts. The source normal coefficient is positive. -/
def face_sign_gluingType : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (i j : Fin (n+1)) (a ε δ : ℝ),
    0 < a → A j i = a → (∀ r, r ≠ i → A j r = 0) →
    δ = ε * Real.sign A.det →
    faceSign δ j = faceSign ε i * Real.sign (A.submatrix j.succAbove i.succAbove).det

/-- The full canonical orientation; no orientation of the face space is an
assumption. Its source is the original maximal corner atlas. -/
def resolved_orientationType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S),
    ∃ (T : CornerManifold n (ResolvedFaceSpace S)) (b : CornerOrientation T),
      IsResolvedOrientation o b


/-- The induced orientation is determined on the entire maximal face atlas,
not just on the generating coordinate-deletion charts. -/
def resolved_orientation_uniqueType : Prop :=
  ∀ {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S)
    {T : CornerManifold n (ResolvedFaceSpace S)} (b b' : CornerOrientation T),
    IsResolvedOrientation o b → IsResolvedOrientation o b' → b = b'

/-- A positive normal row induces an actual linear equivalence on normal
quotients carrying both distinguished half-lines to the corresponding ones. -/
def normal_quotient_transportType : Prop :=
  ∀ {n : ℕ} (i j : Fin n) (E : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (a : ℝ), 0 < a → (∀ v, E v j = a * v i) →
    ∃ Q : FaceNormalLine i ≃ₗ[ℝ] FaceNormalLine j,
      (∀ v, Q (Submodule.Quotient.mk v) = Submodule.Quotient.mk (E v)) ∧
      Q '' coordinateOutwardRay i = coordinateOutwardRay j ∧
      Q '' coordinateInwardRay i = coordinateInwardRay j

/-- A local outward-first determinant ray is constructed, rather than
assumed. It has the stated deleted-coordinate sign and works for every
outward vector and every tangential determinant vector, including n=0. -/
def local_face_rayType : Prop :=
  ∀ {n : ℕ} (i : Fin (n+1)) (ε : ℝ), ε ≠ 0 →
    ∀ r : Module.Ray ℝ (⋀[ℝ]^(n+1) (Euclidean (n+1))),
      IsPositive r (ε • coordinateVolume (n+1)) →
      ∃! s : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)),
        IsPositive s (faceSign ε i • coordinateVolume n) ∧
        ∀ v : Euclidean (n+1), v i < 0 → ∀ η : ⋀[ℝ]^n (Euclidean n),
          IsPositive s η ↔ IsPositive r (normalWedge (faceInsertion i) v η)

/-- Restriction to an ordinary smooth manifold recovers an actual continuous
ray field on its original intrinsic determinant line. -/
def ordinary_orientationType : Prop :=
  ∀ {n : ℕ} {a : _root_.SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : _root_.SmoothManifolds.AtlasData.SmoothManifold n a M)
    (E : _root_.SmoothManifolds.CornerProductData.ModelOrthantCoordinates n a)
    (R : CornerManifold n M)
    (hsub : _root_.SmoothManifolds.CornerProductData.ordinaryCornerAtlas E S.smoothStructure.val ⊆ R.atlas)
    (o : CornerOrientation R), ∃ r : Orientation S, IsOrdinaryOrientation S E R hsub o r

/-- The ordinary intrinsic determinant-line orientation and the signed
corner orientation are equivalent on the full converted maximal structure.
The relation includes the determinant sign of the model identification. -/
def ordinary_orientation_equivType : Prop :=
  ∀ {n : ℕ} {a : _root_.SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : _root_.SmoothManifolds.AtlasData.SmoothManifold n a M)
    (E : _root_.SmoothManifolds.CornerProductData.ModelOrthantCoordinates n a)
    (R : CornerManifold n M)
    (hsub : _root_.SmoothManifolds.CornerProductData.ordinaryCornerAtlas E S.smoothStructure.val ⊆ R.atlas),
    ∃ e : CornerOrientation R ≃ Orientation S,
      ∀ o, IsOrdinaryOrientation S E R hsub o (e o)

/-- Every genuine corner product has its unique ordered determinant orientation.
Both factors may have boundary; zero-dimensional and empty factors are included. -/
def product_orientationType : Prop :=
  ∀ {m n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (C : _root_.SmoothManifolds.CornerProductData.ProductCoordinateFamily m n)
    (P : CornerManifold (m+n) (M × N))
    (hsub : _root_.SmoothManifolds.CornerProductData.productAtlas C S.atlas T.atlas ⊆ P.atlas)
    (o : CornerOrientation S) (q : CornerOrientation T),
      ∃! r : CornerOrientation P, IsCornerProductOrientation C o q r

/-- Local product rays use the fixed ordered wedge and the actual
projection tangent splitting. Includes empty coordinate blocks in degree zero. -/
def local_product_rayType : Prop :=
  ∀ {m n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (C : _root_.SmoothManifolds.CornerProductData.ProductCoordinateFamily m n)
    (c : CornerChart m M) (d : CornerChart n N),
    let L := (C c.1 d.1).linearEquiv
    (∀ x ∈ (_root_.SmoothManifolds.CornerProductData.productChart C c d).2.target,
      ((c.2 ((_root_.SmoothManifolds.CornerProductData.productChart C c d).2.symm x).1).val,
       (d.2 ((_root_.SmoothManifolds.CornerProductData.productChart C c d).2.symm x).2).val) = L.symm x.val) ∧
    (∀ z, HasFDerivAt (fun w => L.symm w) L.symm.toContinuousLinearMap z) ∧
    ∀ (r : Module.Ray ℝ (⋀[ℝ]^m (Euclidean m)))
      (s : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n))),
      ∃! t : Module.Ray ℝ (⋀[ℝ]^(m+n) (Euclidean (m+n))),
        ∀ v w, IsPositive r v → IsPositive s w →
          IsPositive t (coordinateProductVector (C c.1 d.1) v w)

/-- The first factor normal precedes both tangential blocks. This is the
ordered exterior identity in the actual product coordinate identification. -/
def product_left_wedgeType : Prop :=
  ∀ {m n : ℕ} {k : Fin (m+2)} {l : Fin (n+1)}
    (C : _root_.SmoothManifolds.CornerProductData.OrthantProductCoordinates (m+1) n k l)
    (i : Fin (m+1)) (v : Euclidean (m+1))
    (η : ⋀[ℝ]^m (Euclidean m)) (θ : ⋀[ℝ]^n (Euclidean n)),
    castExterior (Nat.add_right_comm m n 1)
      (normalWedge (C.linearEquiv.toLinearMap.comp
        ((faceInsertion i).prodMap (LinearMap.id : Euclidean n →ₗ[ℝ] Euclidean n)))
        (C.linearEquiv (v,0))
        (_root_.SmoothManifolds.OrientationProductData.orderedWedge m n _ _ η θ)) =
      coordinateProductVector C (normalWedge (faceInsertion i) v η) θ

/-- A second-factor normal crosses all m first-factor tangent directions. -/
def product_right_wedgeType : Prop :=
  ∀ {m n : ℕ} {k : Fin (m+1)} {l : Fin (n+2)}
    (C : _root_.SmoothManifolds.CornerProductData.OrthantProductCoordinates m (n+1) k l)
    (j : Fin (n+1)) (v : Euclidean (n+1))
    (η : ⋀[ℝ]^m (Euclidean m)) (θ : ⋀[ℝ]^n (Euclidean n)),
    castExterior (Nat.add_assoc m n 1)
      (normalWedge (C.linearEquiv.toLinearMap.comp
        ((LinearMap.id : Euclidean m →ₗ[ℝ] Euclidean m).prodMap (faceInsertion j)))
        (C.linearEquiv (0,v))
        (_root_.SmoothManifolds.OrientationProductData.orderedWedge m n _ _ η θ)) =
      (-1 : ℝ)^m • coordinateProductVector C η (normalWedge (faceInsertion j) v θ)

end Specs.SmoothManifolds.Corners.FaceOrientations


namespace Specs.SmoothManifolds.Corners.FaceOrientations
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.CornerData
  _root_.SmoothManifolds.CornerOrientationData
  _root_.SmoothManifolds.CornerProductData _root_.SmoothManifolds.OrientationData Set

/-- The ordered simplex carries the source orientation dt₁∧⋯∧dtₙ in its actual affine charts. -/
def simplex_source_orientationType : Prop :=
  ∀ n : ℕ, ∃ (S : CornerManifold n (Simplex n)) (c : Fin (n+1) → CornerChart n (Simplex n)),
    S.atlas = cornerMaximalExtension (range c) ∧
    (∀ j, c j ∈ S.atlas ∧ (c j).1 = Fin.last n ∧
      (c j).2.source = {x | 0 < simplexBarycentric x.val j} ∧
      (c j).2.target = {y | ∑ r, y.val r < 1} ∧
      (∀ x ∈ (c j).2.source, ((c j).2 x).val = simplexOmitBarycentric j x.val) ∧
      (∀ y ∈ (c j).2.target, ((c j).2.symm y).val = simplexRestoreBarycentric j y.val)) ∧
    (∀ x, ∃ j, x ∈ (c j).2.source) ∧
    (∀ j : Fin (n+1), ContDiff ℝ (⊤ : ℕ∞) (simplexOmitBarycentric j) ∧
      ContDiff ℝ (⊤ : ℕ∞) (simplexRestoreBarycentric j)) ∧
    (∀ j : Fin (n+1), ∃ A : Euclidean n ≃ᵃ[ℝ] Euclidean n,
      (∀ x, A x = simplexOmitBarycentric j x) ∧
      (∀ y, A.symm y = simplexRestoreBarycentric j y)) ∧
    ∃! o : CornerOrientation S, ∀ j : Fin (n+1),
      ∀ (hc : c j ∈ S.atlas) (p : (c j).2.source),
        signValue (o.sign (c j) hc p) = (-1 : ℝ)^j.val

/-- Every source box, including the zero-dimensional box, has its ambient coordinate orientation. -/
def box_source_orientationType : Prop :=
  ∀ {n : ℕ} (a b : Euclidean n), (∀ i, a i < b i) →
    ∃ (S : CornerManifold n (ClosedBox a b))
      (c : (Fin n → Bool) → CornerChart n (ClosedBox a b)),
      S.atlas = cornerMaximalExtension (range c) ∧
      (∀ ε, c ε ∈ S.atlas ∧ (c ε).1 = Fin.last n ∧
        (c ε).2.source = boxChartSource a b ε ∧
        (c ε).2.target = {y | ∀ i, y.val i < b i - a i} ∧
        (∀ x, ((c ε).2 x).val = boxCoordinate a b ε x.val) ∧
        (∀ y ∈ (c ε).2.target, ((c ε).2.symm y).val =
          fun i => if ε i then b i - y.val i else a i + y.val i)) ∧
      (∀ x, ∃ ε, x ∈ (c ε).2.source) ∧
      (∀ ε : Fin n → Bool, ∃ A : Euclidean n ≃ᵃ[ℝ] Euclidean n,
        (∀ x, A x = boxCoordinate a b ε x) ∧
        (∀ y, A.symm y = fun i => if ε i then b i - y i else a i + y i) ∧
        ContDiff ℝ (⊤ : ℕ∞) (fun x => A x) ∧
        ContDiff ℝ (⊤ : ℕ∞) (fun y => A.symm y)) ∧
      ∃! o : CornerOrientation S, ∀ ε : Fin n → Bool,
        ∀ (hc : c ε ∈ S.atlas) (p : (c ε).2.source),
          signValue (o.sign (c ε) hc p) = ∏ i, (if ε i then (-1 : ℝ) else 1)

/-- The actual positive real interval has unique chart signs and outward-first endpoint signs. -/
def interval_source_orientationType : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (I : CornerManifold 1 (Icc a b))
    (c : Bool → CornerChart 1 (Icc a b)) (hI : IsIntervalChartPair a b I c),
    ∃! o : CornerOrientation I,
      (∀ s (hc : c s ∈ I.atlas) (p : (c s).2.source),
        signValue (o.sign (c s) hc p) = if s then (-1 : ℝ) else 1) ∧
      ∀ s, ∃ p : (c s).2.source,
        p.val.val = (if s then b else a) ∧
          faceSign (signValue (o.sign (c s) (hI.1 s).1 p)) (0 : Fin 1) =
            if s then 1 else -1

end Specs.SmoothManifolds.Corners.FaceOrientations

namespace Specs.SmoothManifolds.Corners.FaceOrientations
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.CornerData
  _root_.SmoothManifolds.CornerOrientationData _root_.SmoothManifolds.CornerProductData
  _root_.SmoothManifolds.OrientationData Set

/-- The actual resolved zero-dimensional interval faces have their outward-first endpoint signs. -/
def interval_resolved_endpointsType : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (I : CornerManifold 1 (Icc a b))
    (c : Bool → CornerChart 1 (Icc a b)) (hI : IsIntervalChartPair a b I c),
    ∃ (o : CornerOrientation I) (T : CornerManifold 0 (ResolvedFaceSpace I))
      (bdy : CornerOrientation T),
      (∀ s (hc : c s ∈ I.atlas) (p : (c s).2.source),
        signValue (o.sign (c s) hc p) = if s then (-1 : ℝ) else 1) ∧
      IsResolvedOrientation o bdy ∧
      ∀ s, ∃ (e : CornerChart 0 (ResolvedFaceSpace I)) (he : e ∈ T.atlas)
        (q : e.2.source), q.val.1.val = (if s then b else a) ∧
          e.2.source = faceSheet I (c s) (0 : Fin 1) univ ∧
          signValue (bdy.sign e he q) = if s then 1 else -1

end Specs.SmoothManifolds.Corners.FaceOrientations

namespace Specs.SmoothManifolds.Corners.FaceOrientations
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.CornerData
  _root_.SmoothManifolds.CornerOrientationData _root_.SmoothManifolds.CornerProductData Set

/-- The ordered orientation is canonical under all allowed ambient product coordinates. -/
def product_orientation_coordinates_independentType : Prop :=
  ∀ {m n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (C D : ProductCoordinateFamily m n) (P : CornerManifold (m+n) (M × N)),
    productAtlas C S.atlas T.atlas ⊆ P.atlas →
    productAtlas D S.atlas T.atlas ⊆ P.atlas →
    ∀ (o : CornerOrientation S) (q : CornerOrientation T) (r : CornerOrientation P),
      IsCornerProductOrientation C o q r → IsCornerProductOrientation D o q r

end Specs.SmoothManifolds.Corners.FaceOrientations

namespace Specs.SmoothManifolds.Corners.FaceOrientations
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.CornerData
  _root_.SmoothManifolds.CornerOrientationData _root_.SmoothManifolds.CornerProductData Set

/-- One global ordered orientation works simultaneously in every allowed product coordinate family. -/
def product_orientation_all_coordinatesType : Prop :=
  ∀ {m n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (C : ProductCoordinateFamily m n) (P : CornerManifold (m+n) (M × N)),
    P.atlas = cornerMaximalExtension (productAtlas C S.atlas T.atlas) →
    ∀ (o : CornerOrientation S) (q : CornerOrientation T),
      ∃! r : CornerOrientation P, ∀ D : ProductCoordinateFamily m n,
        productAtlas D S.atlas T.atlas ⊆ P.atlas ∧ IsCornerProductOrientation D o q r

end Specs.SmoothManifolds.Corners.FaceOrientations

namespace Specs.SmoothManifolds.Corners.FaceOrientations
universe u
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.CornerData
  _root_.SmoothManifolds.CornerOrientationData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.BoundaryOrientationData _root_.SmoothManifolds.CornerProductData
  _root_.SmoothManifolds.OrientationProductData Set Module Filter

def product_left_resolved_sheet_orientationType : Prop := ∀ {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : CornerManifold (m+1) M} {T : CornerManifold n N}
    {P : CornerManifold ((m+1)+n) (M × N)}
    (C : ProductCoordinateFamily (m+1) n)
    (oS : CornerOrientation S) (oT : CornerOrientation T) (oP : CornerOrientation P)
    (hprod : IsCornerProductOrientation C oS oT oP)
    (c : CornerChart (m+1) M) (hc : c ∈ S.atlas)
    (d : CornerChart n N) (hd : d ∈ T.atlas)
    (L : ProductLabels (C c.1 d.1)) (he : productChart C c d ∈ P.atlas)
    (q : ResolvedFaceSpace P) (hp : q.1 ∈ c.2.source ×ˢ d.2.source)
    (hP : q.1 ∈ (productChart C c d).2.source)
    (i : activeCoordinates (c.2 q.1.1))
    (hg : q.2.val = factorFaceGerm c d q.1 (Sum.inl i))
    (rS : Module.Ray ℝ (⋀[ℝ]^(m+1) (Euclidean (m+1))))
    (rT : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)))
    (rP : Module.Ray ℝ (⋀[ℝ]^((m+1)+n) (Euclidean ((m+1)+n))))
    (hrS : IsPositive rS (signValue (oS.sign c hc ⟨q.1.1,hp.1⟩) • coordinateVolume (m+1)))
    (hrT : IsPositive rT (signValue (oT.sign d hd ⟨q.1.2,hp.2⟩) • coordinateVolume n))
    (hrP : IsPositive rP (signValue (oP.sign (productChart C c d) he ⟨q.1,hP⟩) •
      coordinateVolume ((m+1)+n))),
    ∃ a : activeCoordinates ((productChart C c d).2 q.1),
      ∃ rA : Module.Ray ℝ (⋀[ℝ]^m (Euclidean m)),
      ∃ rB : Module.Ray ℝ (⋀[ℝ]^(m+n) (Euclidean m × Euclidean n)),
      q.2 = chartFaceAt P (productChart C c d) he q.1 hP a ∧
      (∀ z : Euclidean m × Euclidean n,
        (C c.1 d.1).linearEquiv (faceInsertion i.val z.1,z.2) a.val = 0) ∧
      IsPositive rA (faceSign (signValue (oS.sign c hc ⟨q.1.1,hp.1⟩)) i.val • coordinateVolume m) ∧
      (∀ η θ, IsPositive rA η → IsPositive rT θ →
        IsPositive rB (orderedWedge m n (Euclidean m) (Euclidean n) η θ)) ∧
      ∀ v : Euclidean (m+1), v i.val < 0 →
        (C c.1 d.1).linearEquiv (v,0) a.val < 0 ∧
        ∀ ζ, IsPositive rB ζ ↔
          IsPositive rP (castExterior (Nat.add_right_comm m n 1)
            (normalWedge ((C c.1 d.1).linearEquiv.toLinearMap.comp
              ((faceInsertion i.val).prodMap (LinearMap.id : Euclidean n →ₗ[ℝ] Euclidean n)))
              ((C c.1 d.1).linearEquiv (v,0)) ζ))

def product_right_resolved_sheet_orientationType : Prop := ∀ {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : CornerManifold m M} {T : CornerManifold (n+1) N}
    {P : CornerManifold (m+(n+1)) (M × N)}
    (C : ProductCoordinateFamily m (n+1))
    (oS : CornerOrientation S) (oT : CornerOrientation T) (oP : CornerOrientation P)
    (hprod : IsCornerProductOrientation C oS oT oP)
    (c : CornerChart m M) (hc : c ∈ S.atlas)
    (d : CornerChart (n+1) N) (hd : d ∈ T.atlas)
    (L : ProductLabels (C c.1 d.1)) (he : productChart C c d ∈ P.atlas)
    (q : ResolvedFaceSpace P) (hp : q.1 ∈ c.2.source ×ˢ d.2.source)
    (hP : q.1 ∈ (productChart C c d).2.source)
    (j : activeCoordinates (d.2 q.1.2))
    (hg : q.2.val = factorFaceGerm c d q.1 (Sum.inr j))
    (rS : Module.Ray ℝ (⋀[ℝ]^m (Euclidean m)))
    (rT : Module.Ray ℝ (⋀[ℝ]^(n+1) (Euclidean (n+1))))
    (rP : Module.Ray ℝ (⋀[ℝ]^(m+(n+1)) (Euclidean (m+(n+1)))))
    (hrS : IsPositive rS (signValue (oS.sign c hc ⟨q.1.1,hp.1⟩) • coordinateVolume m))
    (hrT : IsPositive rT (signValue (oT.sign d hd ⟨q.1.2,hp.2⟩) • coordinateVolume (n+1)))
    (hrP : IsPositive rP (signValue (oP.sign (productChart C c d) he ⟨q.1,hP⟩) •
      coordinateVolume (m+(n+1)))),
    ∃ a : activeCoordinates ((productChart C c d).2 q.1),
      ∃ rA : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)),
      ∃ rB : Module.Ray ℝ (⋀[ℝ]^(m+n) (Euclidean m × Euclidean n)),
      q.2 = chartFaceAt P (productChart C c d) he q.1 hP a ∧
      (∀ z : Euclidean m × Euclidean n,
        (C c.1 d.1).linearEquiv (z.1,faceInsertion j.val z.2) a.val = 0) ∧
      IsPositive rA (faceSign (signValue (oT.sign d hd ⟨q.1.2,hp.2⟩)) j.val • coordinateVolume n) ∧
      (∀ η θ, IsPositive rS η → IsPositive rA θ →
        IsPositive rB (orderedWedge m n (Euclidean m) (Euclidean n) η θ)) ∧
      ∀ v : Euclidean (n+1), v j.val < 0 →
        (C c.1 d.1).linearEquiv (0,v) a.val < 0 ∧
        ∀ ζ, IsPositive (if Even m then rB else -rB) ζ ↔
          IsPositive rP (castExterior (Nat.add_assoc m n 1)
            (normalWedge ((C c.1 d.1).linearEquiv.toLinearMap.comp
              ((LinearMap.id : Euclidean m →ₗ[ℝ] Euclidean m).prodMap (faceInsertion j.val)))
              ((C c.1 d.1).linearEquiv (0,v)) ζ))

def product_factor_face_germs_distinctType : Prop := ∀ {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily m n) (c : CornerChart m M) (d : CornerChart n N)
    (L : ProductLabels (C c.1 d.1)) (P : CornerManifold (m+n) (M × N))
    (he : productChart C c d ∈ P.atlas) (p : M × N)
    (hp : p ∈ c.2.source ×ˢ d.2.source)
    (i : activeCoordinates (c.2 p.1)) (j : activeCoordinates (d.2 p.2)),
    factorFaceGerm c d p (Sum.inl i) ≠ factorFaceGerm c d p (Sum.inr j)


end Specs.SmoothManifolds.Corners.FaceOrientations
