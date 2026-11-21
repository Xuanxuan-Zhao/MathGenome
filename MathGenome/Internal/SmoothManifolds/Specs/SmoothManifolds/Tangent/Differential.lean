import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Models
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Products

/-! The differential is specified intrinsically by its action on every germ.
Existence and uniqueness construct the linear map without choosing coordinates.
All manifolds below have arbitrary dimension and either permitted model kind.
The product statements concern precisely the product smooth structures constructed
from `ProductCoordinates`, including the zero-dimensional cases. -/
namespace SmoothManifolds.DifferentialData
open ModelData AtlasData MapData TangentData ProductData
open Filter Set
open scoped Topology
universe u

/-- The defining action of a tangent map on germs. Representatives need only
agree near the relevant point; no global smoothness is required of them. -/
def IsDifferential {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N) (p : M) (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) : Prop :=
  ∀ (v : TangentSpace S p) (h : SmoothGerm T (f p)) (k : SmoothGerm S p)
    (r : N → ℝ), Germ.ofFun r = h.val → Germ.ofFun (r ∘ f) = k.val →
      (L v).val h = v.val k

/-- A chart realization uses exactly the evaluations on its coordinate germs. -/
def IsChartCoordinates {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) (e : ModelChart n a M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) : Prop :=
  ∃ coords : Fin n → SmoothGerm S p,
    (∀ i, (coords i).val = Germ.ofFun (fun y => (e y).val i)) ∧
    ∀ v i, E v i = v.val (coords i)

end SmoothManifolds.DifferentialData

namespace Specs.SmoothManifolds.Tangent.Differential
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.ProductData
  _root_.SmoothManifolds.DifferentialData
open Filter Set
open scoped Topology
universe u

section Maps
variable {n m l : ℕ} {a b c : ModelKind} {M N Q : Type u}
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]

def differential_existsType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N), IsSmoothMap S T f → ∀ p : M,
    ∃! L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p), IsDifferential S T f p L

def differential_idType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M],
  ∀ (S : SmoothManifold n a M) (p : M),
    IsDifferential S S id p (LinearMap.id : TangentSpace S p →ₗ[ℝ] TangentSpace S p)

def differential_compType : Prop :=
  ∀ {n m l : ℕ} {a b c : ModelKind} {M N Q : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q],
  ∀ (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (U : SmoothManifold l c Q) (f : M → N) (g : N → Q),
    IsSmoothMap S T f → IsSmoothMap T U g → ∀ (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (K : TangentSpace T (f p) →ₗ[ℝ] TangentSpace U (g (f p))),
    IsDifferential S T f p L → IsDifferential T U g (f p) K →
    IsDifferential S U (g ∘ f) p (K.comp L)

/-- Every ambient smooth coordinate representative gives the same Jacobian,
including at a face. Both coordinate equivalences are the intrinsic ones. -/
def differential_jacobianType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N), IsSmoothMap S T f → ∀ (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    IsDifferential S T f p L →
    ∀ (e : ModelChart n a M) (d : ModelChart m b N),
      e ∈ S.smoothStructure.val → d ∈ T.smoothStructure.val →
      p ∈ e.source → f p ∈ d.source →
    ∀ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (F : TangentSpace T (f p) ≃ₗ[ℝ] Euclidean m),
      IsChartCoordinates S p e E → IsChartCoordinates T (f p) d F →
    ∀ (V : Set (Euclidean n)) (H : Euclidean n → Euclidean m),
      IsOpen V → (e p).val ∈ V → ContDiffOn ℝ (⊤ : ℕ∞) H V →
      (fun y => H (e y).val) =ᶠ[𝓝 p] (fun y => (d (f y)).val) →
    ∀ v : TangentSpace S p, F (L v) = fderiv ℝ H (e p).val (E v)

def differential_curveType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (f : M → N), IsSmoothMap S T f → ∀ (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    IsDifferential S T f p L → ∀ (side : CurveSide) (c : ℝ → M)
      (v : TangentSpace S p), CurveRepresentsDerivation S p side c v →
        CurveRepresentsDerivation T (f p) side (f ∘ c) (L v)

/-- The linear equivalence is the differential of the given diffeomorphism. -/
def differential_diffeomorphType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N],
  ∀ (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (h : Diffeomorph S.smoothStructure.val T.smoothStructure.val) (p : M),
    ∃ E : TangentSpace S p ≃ₗ[ℝ] TangentSpace T (h.toEquiv p),
      IsDifferential S T h.toEquiv p E.toLinearMap
end Maps

/-- The finite direct sum of two real vector spaces is their product.
The equivalence here has the two projection differentials as its components. -/
def differential_productType : Prop :=
  ∀ {n m : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : ProductCoordinates n a m b k)
    (P : SmoothManifold (n + m) k (M × N)),
    P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val) →
    IsSmoothMap P S Prod.fst ∧ IsSmoothMap P T Prod.snd ∧
    ∀ p : M × N, ∃ E : TangentSpace P p ≃ₗ[ℝ]
        (TangentSpace S p.1 × TangentSpace T p.2),
      IsDifferential P S Prod.fst p ((LinearMap.fst ℝ _ _).comp E.toLinearMap) ∧
      IsDifferential P T Prod.snd p ((LinearMap.snd ℝ _ _).comp E.toLinearMap)

def differential_pairType : Prop :=
  ∀ {n m l : ℕ} {a b c k : ModelKind} {M N Q : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (U : SmoothManifold l c Q) (C : ProductCoordinates n a m b k)
    (P : SmoothManifold (n + m) k (M × N)),
    P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val) →
    ∀ (f : Q → M) (g : Q → N), IsSmoothMap U S f → IsSmoothMap U T g →
    IsSmoothMap U P (fun x => (f x, g x)) ∧
    ∀ (p : Q)
      (Lf : TangentSpace U p →ₗ[ℝ] TangentSpace S (f p))
      (Lg : TangentSpace U p →ₗ[ℝ] TangentSpace T (g p))
      (L : TangentSpace U p →ₗ[ℝ] TangentSpace P (f p, g p))
      (E : TangentSpace P (f p, g p) ≃ₗ[ℝ]
        (TangentSpace S (f p) × TangentSpace T (g p))),
      IsDifferential U S f p Lf → IsDifferential U T g p Lg →
      IsDifferential U P (fun x => (f x, g x)) p L →
      IsDifferential P S Prod.fst (f p, g p)
        ((LinearMap.fst ℝ _ _).comp E.toLinearMap) →
      IsDifferential P T Prod.snd (f p, g p)
        ((LinearMap.snd ℝ _ _).comp E.toLinearMap) →
      E.toLinearMap.comp L = Lf.prod Lg

end Specs.SmoothManifolds.Tangent.Differential
