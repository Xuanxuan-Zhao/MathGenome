import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.LocalAndResolvedGeometry
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Product corner charts. Both factors use their actual topology; a product
model has the sum of their numbers of constrained coordinates. -/
namespace SmoothManifolds.CornerProductData
open ModelData CornerData Set
open scoped Topology
universe u v

def constraintSum {n m : ℕ} (k : Fin (n+1)) (l : Fin (m+1)) : Fin (n+m+1) :=
  ⟨k.val + l.val, by have := k.isLt; have := l.isLt; omega⟩

/-- Ambient linear coordinates carrying the product model exactly onto an orthant. -/
structure OrthantProductCoordinates (n m : ℕ) (k : Fin (n+1)) (l : Fin (m+1)) where
  linearEquiv : (Euclidean n × Euclidean m) ≃L[ℝ] Euclidean (n+m)
  mem_orthant : ∀ z, linearEquiv z ∈ orthantSet (n+m) (constraintSum k l) ↔
    z.1 ∈ orthantSet n k ∧ z.2 ∈ orthantSet m l

def OrthantProductCoordinates.homeomorph {n m : ℕ} {k : Fin (n+1)} {l : Fin (m+1)}
    (C : OrthantProductCoordinates n m k l) :
    (Orthant n k × Orthant m l) ≃ₜ Orthant (n+m) (constraintSum k l) :=
  (Homeomorph.Set.prod (orthantSet n k) (orthantSet m l)).symm.trans
    (C.linearEquiv.toHomeomorph.subtype (fun z => (C.mem_orthant z).symm))

/-- A family of coordinate choices permits different numbers of constraints in
individual charts. Existence of such a family is a theorem below. -/
abbrev ProductCoordinateFamily (n m : ℕ) :=
  (k : Fin (n+1)) → (l : Fin (m+1)) → OrthantProductCoordinates n m k l

def productChart {n m : ℕ} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily n m) (c : CornerChart n M) (d : CornerChart m N) :
    CornerChart (n+m) (M × N) :=
  ⟨constraintSum c.1 d.1, (c.2.prod d.2).trans (C c.1 d.1).homeomorph.toOpenPartialHomeomorph⟩

def productAtlas {n m : ℕ} {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily n m) (A : Set (CornerChart n M))
    (B : Set (CornerChart m N)) : Set (CornerChart (n+m) (M × N)) :=
  {e | ∃ c ∈ A, ∃ d ∈ B, e = productChart C c d}

/-- An ordinary half-space has one constraint in positive dimension and none
in dimension zero; a Euclidean model has none. -/
def modelConstraintCount : (n : ℕ) → _root_.SmoothManifolds.ModelKind → Fin (n+1)
  | 0, _ => 0
  | n+1, .halfSpace => ⟨1, by omega⟩
  | _+1, .euclidean => 0

structure ModelOrthantCoordinates (n : ℕ) (a : _root_.SmoothManifolds.ModelKind) where
  linearEquiv : Euclidean n ≃L[ℝ] Euclidean n
  mem_model : ∀ x, linearEquiv x ∈ orthantSet n (modelConstraintCount n a) ↔ x ∈ modelSet n a

def ModelOrthantCoordinates.homeomorph {n : ℕ} {a : _root_.SmoothManifolds.ModelKind}
    (E : ModelOrthantCoordinates n a) : ModelSpace n a ≃ₜ Orthant n (modelConstraintCount n a) :=
  E.linearEquiv.toHomeomorph.subtype (fun x => (E.mem_model x).symm)

def ordinaryCornerChart {n : ℕ} {a : _root_.SmoothManifolds.ModelKind}
    {M : Type u} [TopologicalSpace M] (E : ModelOrthantCoordinates n a)
    (c : ModelChart n a M) : CornerChart n M :=
  ⟨modelConstraintCount n a, c.trans E.homeomorph.toOpenPartialHomeomorph⟩

def ordinaryCornerAtlas {n : ℕ} {a : _root_.SmoothManifolds.ModelKind}
    {M : Type u} [TopologicalSpace M] (E : ModelOrthantCoordinates n a)
    (A : Set (ModelChart n a M)) : Set (CornerChart n M) := ordinaryCornerChart E '' A

/-- Labels of a coordinate permutation, preserving the two factor blocks of
normal directions. Their construction is proved, rather than assumed of a product. -/
structure ProductLabels {n m : ℕ} {k : Fin (n+1)} {l : Fin (m+1)}
    (C : OrthantProductCoordinates n m k l) where
  indexEquiv : Fin (n+m) ≃ (Fin n ⊕ Fin m)
  constrained : ∀ i, i.val < k.val+l.val ↔
    Sum.elim (fun j : Fin n => j.val < k.val) (fun j : Fin m => j.val < l.val) (indexEquiv i)
  coordinate : ∀ z i, C.linearEquiv z i = Sum.elim z.1 z.2 (indexEquiv i)

def factorFaceGerm {n m : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (c : CornerChart n M) (d : CornerChart m N) (p : M × N) :
    (activeCoordinates (c.2 p.1) ⊕ activeCoordinates (d.2 p.2)) → Filter.Germ (𝓝 p) Prop :=
  Sum.elim (fun i => (chartFaceGerm c p.1 i.val).compTendsto Prod.fst continuous_fst.continuousAt)
    (fun i => (chartFaceGerm d p.2 i.val).compTendsto Prod.snd continuous_snd.continuousAt)

/-- Endpoint charts of the actual real closed interval. False labels the left
endpoint and True labels the right endpoint. -/
def IsIntervalChartPair (a b : ℝ) (I : CornerManifold 1 (Icc a b))
    (c : Bool → CornerChart 1 (Icc a b)) : Prop :=
  (∀ s, c s ∈ I.atlas ∧ (c s).1 = 1 ∧
    (c s).2.source = {x | if s then a < x.val else x.val < b} ∧
    ∀ x, ((c s).2 x).val 0 = if s then b - x.val else x.val - a) ∧
  (∀ x : Icc a b, ∃ s, x ∈ (c s).2.source) ∧
  ∀ (s : Bool) (x : Icc a b) (i : Fin 1),
    i ∈ activeCoordinates ((c s).2 x) ↔ x.val = if s then b else a

end SmoothManifolds.CornerProductData

namespace Specs.SmoothManifolds.Corners.Products
universe u
open _root_.SmoothManifolds.ModelData _root_.SmoothManifolds.CornerData
  _root_.SmoothManifolds.CornerProductData Set

/-- No boundaryless, positive-dimensional, or nonempty hypotheses. -/
def orthant_product_coordinatesType : Prop :=
  ∀ n m : ℕ, Nonempty (ProductCoordinateFamily n m)

def product_chartType : Prop :=
  ∀ {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily n m) (c : CornerChart n M) (d : CornerChart m N),
    (productChart C c d).2.source = c.2.source ×ˢ d.2.source ∧
      ∀ p : M × N, ((productChart C c d).2 p).val =
        (C c.1 d.1).linearEquiv ((c.2 p.1).val, (d.2 p.2).val)

def product_atlasType : Prop :=
  ∀ {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily n m) (A : Set (CornerChart n M))
    (B : Set (CornerChart m N)),
    IsSmoothCornerAtlas A → IsSmoothCornerAtlas B →
    IsSmoothCornerAtlas (productAtlas C A B)

def product_corner_structureType : Prop :=
  ∀ {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold n M) (T : CornerManifold m N)
    (C : ProductCoordinateFamily n m),
    ∃ P : CornerManifold (n+m) (M × N),
      P.atlas = cornerMaximalExtension (productAtlas C S.atlas T.atlas) ∧
      productAtlas C S.atlas T.atlas ⊆ P.atlas

def ordinary_model_coordinatesType : Prop :=
  ∀ n a, Nonempty (ModelOrthantCoordinates n a)

def ordinary_corner_bridgeType : Prop :=
  ∀ {n : ℕ} {a : _root_.SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : _root_.SmoothManifolds.AtlasData.SmoothManifold n a M)
    (E : ModelOrthantCoordinates n a),
    ∃ R : CornerManifold n M,
      R.atlas = cornerMaximalExtension (ordinaryCornerAtlas E S.smoothStructure.val) ∧
      ordinaryCornerAtlas E S.smoothStructure.val ⊆ R.atlas

def product_projectionsType : Prop :=
  ∀ {n m : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold n M) (T : CornerManifold m N)
    (C : ProductCoordinateFamily n m) (P : CornerManifold (n+m) (M × N)),
    P.atlas = cornerMaximalExtension (productAtlas C S.atlas T.atlas) →
    CornerMapContDiff (⊤ : ℕ∞) P S Prod.fst ∧ CornerMapContDiff (⊤ : ℕ∞) P T Prod.snd

def product_inclusionsType : Prop :=
  ∀ {n m : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold n M) (T : CornerManifold m N)
    (C : ProductCoordinateFamily n m) (P : CornerManifold (n+m) (M × N)),
    P.atlas = cornerMaximalExtension (productAtlas C S.atlas T.atlas) →
    (∀ q : N, CornerMapContDiff (⊤ : ℕ∞) S P (fun p => (p,q))) ∧
    (∀ p : M, CornerMapContDiff (⊤ : ℕ∞) T P (fun q => (p,q)))

attribute [local instance] Classical.propDecidable

/-- The ordinary boundary-manifold product is explicitly obtained by the bridge
and the actual product charts, even when both models have a constraint. -/
def boundary_productType : Prop :=
  ∀ {n m : ℕ} {a b : _root_.SmoothManifolds.ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : _root_.SmoothManifolds.AtlasData.SmoothManifold n a M)
    (T : _root_.SmoothManifolds.AtlasData.SmoothManifold m b N),
    ∃ (E : ModelOrthantCoordinates n a) (F : ModelOrthantCoordinates m b)
      (R : CornerManifold n M) (Q : CornerManifold m N)
      (C : ProductCoordinateFamily n m) (P : CornerManifold (n+m) (M × N)),
      R.atlas = cornerMaximalExtension (ordinaryCornerAtlas E S.smoothStructure.val) ∧
      Q.atlas = cornerMaximalExtension (ordinaryCornerAtlas F T.smoothStructure.val) ∧
      P.atlas = cornerMaximalExtension (productAtlas C R.atlas Q.atlas) ∧
      CornerMapContDiff (⊤ : ℕ∞) P R Prod.fst ∧ CornerMapContDiff (⊤ : ℕ∞) P Q Prod.snd ∧
    (∀ q : N, CornerMapContDiff (⊤ : ℕ∞) R P (fun p => (p,q))) ∧
      (∀ p : M, CornerMapContDiff (⊤ : ℕ∞) Q P (fun q => (p,q))) ∧
      (∀ p : M, Nat.card (LocalFaceGerm R p) =
        if p ∈ _root_.SmoothManifolds.BoundaryData.intrinsicBoundary S then 1 else 0) ∧
      (∀ q : N, Nat.card (LocalFaceGerm Q q) =
        if q ∈ _root_.SmoothManifolds.BoundaryData.intrinsicBoundary T then 1 else 0)

/-- Derivatives of the actual generating-chart projections and inclusions are
the ordered direct-sum maps. Equality on chart domains ties the ambient maps to
the geometric projections, including at a corner point. -/
def coordinate_tangent_sumType : Prop :=
  ∀ {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily n m) (c : CornerChart n M) (d : CornerChart m N),
    let L := (C c.1 d.1).linearEquiv
    (∀ x ∈ (productChart C c d).2.target,
      ((c.2 ((productChart C c d).2.symm x).1).val,
       (d.2 ((productChart C c d).2.symm x).2).val) = L.symm x.val) ∧
    (∀ z : Euclidean (n+m),
      HasFDerivAt (fun w => (L.symm w).1)
        ((ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean m)).comp L.symm.toContinuousLinearMap) z ∧
      HasFDerivAt (fun w => (L.symm w).2)
        ((ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean m)).comp L.symm.toContinuousLinearMap) z) ∧
    (∀ (q : N) x, x ∈ c.2.target →
      ((productChart C c d).2 (c.2.symm x,q)).val = L (x.val,(d.2 q).val)) ∧
    (∀ (p : M) y, y ∈ d.2.target →
      ((productChart C c d).2 (p,d.2.symm y)).val = L ((c.2 p).val,y.val)) ∧
    (∀ (v : Euclidean m) (x : Euclidean n),
      HasFDerivAt (fun z => L (z,v))
        (L.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean m))) x) ∧
    (∀ (u : Euclidean n) (y : Euclidean m),
      HasFDerivAt (fun z => L (u,z))
        (L.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean m))) y)

/-- Changes between two ordered product coordinate systems act by the direct
sum of the two factor derivatives, conjugated by the linear identifications. -/
def transition_derivativeType : Prop :=
  ∀ {n m : ℕ} {k k' : Fin (n+1)} {l l' : Fin (m+1)}
    (C : OrthantProductCoordinates n m k l) (D : OrthantProductCoordinates n m k' l')
    (F : Euclidean n → Euclidean n) (G : Euclidean m → Euclidean m)
    (x : Euclidean (n+m))
    (A : Euclidean n →L[ℝ] Euclidean n) (B : Euclidean m →L[ℝ] Euclidean m),
    HasFDerivAt F A (C.linearEquiv.symm x).1 →
    HasFDerivAt G B (C.linearEquiv.symm x).2 →
    HasFDerivAt (fun z => D.linearEquiv (F (C.linearEquiv.symm z).1, G (C.linearEquiv.symm z).2))
      (D.linearEquiv.toContinuousLinearMap.comp ((A.prodMap B).comp C.linearEquiv.symm.toContinuousLinearMap)) x

def labelled_product_coordinatesType : Prop :=
  ∀ n m : ℕ, ∃ C : ProductCoordinateFamily n m, ∀ k l, Nonempty (ProductLabels (C k l))

/-- All local sheets are exactly the two tagged families of factor faces.
Bijectivity retains two distinct germs at intersections of the two families. -/
def product_face_germsType : Prop :=
  ∀ {n m : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily n m) (c : CornerChart n M) (d : CornerChart m N)
    (_L : ProductLabels (C c.1 d.1)) (P : CornerManifold (n+m) (M × N))
    (_he : productChart C c d ∈ P.atlas) (p : M × N)
    (_hp : p ∈ c.2.source ×ˢ d.2.source),
    ∃ f : (activeCoordinates (c.2 p.1) ⊕ activeCoordinates (d.2 p.2)) → LocalFaceGerm P p,
      Function.Bijective f ∧ ∀ i, (f i).val = factorFaceGerm c d p i

def interval_chartsType : Prop :=
  ∀ a b : ℝ, a < b → ∃ (I : CornerManifold 1 (Icc a b))
    (c : Bool → CornerChart 1 (Icc a b)), IsIntervalChartPair a b I c

/-- Interval times any source boundary manifold, on the Cartesian product of
the real interval and the original base. The face bijections include both
endpoint sheets and every factor-face sheet, at all intersections. -/
def interval_boundary_productType : Prop :=
  ∀ (a b : ℝ), a < b → ∀ {n : ℕ} {k : _root_.SmoothManifolds.ModelKind}
    {N : Type} [TopologicalSpace N]
    (T : _root_.SmoothManifolds.AtlasData.SmoothManifold n k N),
    ∃ (I : CornerManifold 1 (Icc a b)) (c : Bool → CornerChart 1 (Icc a b))
      (E : ModelOrthantCoordinates n k) (Q : CornerManifold n N)
      (C : ProductCoordinateFamily 1 n) (P : CornerManifold (1+n) (Icc a b × N)),
      IsIntervalChartPair a b I c ∧
      Q.atlas = cornerMaximalExtension (ordinaryCornerAtlas E T.smoothStructure.val) ∧
      P.atlas = cornerMaximalExtension (productAtlas C I.atlas Q.atlas) ∧
      CornerMapContDiff (⊤ : ℕ∞) P I Prod.fst ∧ CornerMapContDiff (⊤ : ℕ∞) P Q Prod.snd ∧
      (∀ q : N, Nat.card (LocalFaceGerm Q q) =
        if q ∈ _root_.SmoothManifolds.BoundaryData.intrinsicBoundary T then 1 else 0) ∧
      (∀ (s : Bool) (d : CornerChart n N), d ∈ Q.atlas →
        productChart C (c s) d ∈ P.atlas ∧
        ∀ p ∈ (c s).2.source ×ˢ d.2.source,
          ∃ f : (activeCoordinates ((c s).2 p.1) ⊕ activeCoordinates (d.2 p.2)) → LocalFaceGerm P p,
            Function.Bijective f ∧ ∀ i, (f i).val = factorFaceGerm (c s) d p i)

/-- The maximal product atlas is already generated by products of the original
ordinary smooth charts, after the displayed ambient linear identifications. -/
def boundary_product_original_chartsType : Prop :=
  ∀ {n m : ℕ} {a b : _root_.SmoothManifolds.ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : _root_.SmoothManifolds.AtlasData.SmoothManifold n a M)
    (T : _root_.SmoothManifolds.AtlasData.SmoothManifold m b N),
    ∃ (E : ModelOrthantCoordinates n a) (F : ModelOrthantCoordinates m b)
      (C : ProductCoordinateFamily n m) (P : CornerManifold (n+m) (M × N)),
      P.atlas = cornerMaximalExtension (productAtlas C
        (ordinaryCornerAtlas E S.smoothStructure.val) (ordinaryCornerAtlas F T.smoothStructure.val)) ∧
      (∀ c ∈ S.smoothStructure.val, ∀ d ∈ T.smoothStructure.val,
        productChart C (ordinaryCornerChart E c) (ordinaryCornerChart F d) ∈ P.atlas ∧
        (productChart C (ordinaryCornerChart E c) (ordinaryCornerChart F d)).2.source = c.source ×ˢ d.source ∧
        ∀ p : M × N, ((productChart C (ordinaryCornerChart E c) (ordinaryCornerChart F d)).2 p).val =
          (C (modelConstraintCount n a) (modelConstraintCount m b)).linearEquiv
            (E.linearEquiv (c p.1).val, F.linearEquiv (d p.2).val))

/-- The maximal corner structure is independent of the ambient product
coordinate identifications. -/
def product_canonicalType : Prop :=
  ∀ {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold n M) (T : CornerManifold m N)
    (C D : ProductCoordinateFamily n m) (P Q : CornerManifold (n+m) (M × N)),
    P.atlas = cornerMaximalExtension (productAtlas C S.atlas T.atlas) →
    Q.atlas = cornerMaximalExtension (productAtlas D S.atlas T.atlas) → P.atlas = Q.atlas

/-- Changing the smooth linear identification of the ordinary model with an
orthant gives the same maximal corner atlas on the original base. -/
def ordinary_canonicalType : Prop :=
  ∀ {n : ℕ} {a : _root_.SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : _root_.SmoothManifolds.AtlasData.SmoothManifold n a M)
    (E F : ModelOrthantCoordinates n a) (R Q : CornerManifold n M),
    R.atlas = cornerMaximalExtension (ordinaryCornerAtlas E S.smoothStructure.val) →
    Q.atlas = cornerMaximalExtension (ordinaryCornerAtlas F S.smoothStructure.val) →
    R.atlas = Q.atlas

/-- The bridge has precisely the intrinsic ordinary boundary as its depth-one
locus, and no higher corner depth, including the empty boundary in dimension zero. -/
def ordinary_boundary_facesType : Prop :=
  ∀ {n : ℕ} {a : _root_.SmoothManifolds.ModelKind} {M : Type*} [TopologicalSpace M]
    (S : _root_.SmoothManifolds.AtlasData.SmoothManifold n a M),
    ∃ (E : ModelOrthantCoordinates n a) (R : CornerManifold n M),
      R.atlas = cornerMaximalExtension (ordinaryCornerAtlas E S.smoothStructure.val) ∧
      ∀ p : M, Nat.card (LocalFaceGerm R p) =
        if p ∈ _root_.SmoothManifolds.BoundaryData.intrinsicBoundary S then 1 else 0

end Specs.SmoothManifolds.Corners.Products
