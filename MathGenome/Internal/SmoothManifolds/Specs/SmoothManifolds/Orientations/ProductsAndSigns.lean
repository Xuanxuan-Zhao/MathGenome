import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Equivalences
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! Independent statements for the product and local-sign clauses of M09.02,
paper.tex 1724--1730. The wedge is multiplication in the actual exterior algebra,
with the first summand embedded before the second. No positivity of boundary
charts is required. Local diffeomorphisms have smooth local inverses; invertibility
of their intrinsic differential is a conclusion, not part of that definition.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct

namespace SmoothManifolds.OrientationProductData
open ModelData AtlasData MapData TangentData DifferentialData ProductData
  OrientationData BoundaryData Set
universe u v

/-- The ordered exterior product on a direct sum, valid also in degree zero. -/
def orderedWedge (m n : ℕ) (V W : Type u) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] :
    (⋀[ℝ]^m V) →ₗ[ℝ] (⋀[ℝ]^n W) →ₗ[ℝ] (⋀[ℝ]^(m+n) (V × W)) :=
  ((exteriorPower.wedge ℝ (V × W) m n).compl₁₂
    (exteriorPower.map m (LinearMap.inl ℝ V W))
    (exteriorPower.map n (LinearMap.inr ℝ V W)))

/-- The canonical map det(V) ⊗ det(W) → det(V ⊕ W), with V first. -/
def determinantSumMap (m n : ℕ) (V W : Type u) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] :
    (⋀[ℝ]^m V) ⊗[ℝ] (⋀[ℝ]^n W) →ₗ[ℝ] (⋀[ℝ]^(m+n) (V × W)) :=
  TensorProduct.lift (orderedWedge m n V W)

/-- Exterior transport by an actual linear equivalence. -/
def determinantMap {V : Type u} {W : Type v} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (n : ℕ) (E : V ≃ₗ[ℝ] W) :
    (⋀[ℝ]^n V) ≃ₗ[ℝ] (⋀[ℝ]^n W) :=
  LinearEquiv.ofBijective (exteriorPower.map n E.toLinearMap)
    ⟨exteriorPower.map_injective_field E.injective,
      exteriorPower.map_surjective E.surjective⟩

/-- The tangent direct-sum identification is characterized by the two actual
projection differentials, so arbitrary unrelated linear identifications do not
qualify. -/
def IsProductDifferential {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (P : SmoothManifold (m+n) k (M × N)) (p : M × N)
    (E : TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2)) : Prop :=
  IsDifferential P S Prod.fst p ((LinearMap.fst ℝ _ _).comp E.toLinearMap) ∧
  IsDifferential P T Prod.snd p ((LinearMap.snd ℝ _ _).comp E.toLinearMap)

/-- The inverse tangent identification transports the ordered wedge to T(M×N). -/
def productVector {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold m a M} {T : SmoothManifold n b N}
    {P : SmoothManifold (m+n) k (M × N)} {p : M × N}
    (E : TangentSpace P p ≃ₗ[ℝ] (TangentSpace S p.1 × TangentSpace T p.2))
    (v : DeterminantLine S p.1) (w : DeterminantLine T p.2) : DeterminantLine P p :=
  determinantMap (m+n) E.symm (orderedWedge m n _ _ v w)

/-- Quantification over all positive vectors gives independence of positive
local generators; quantification over all projection splittings gives canonicity. -/
def IsProductOrientation {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold m a M} {T : SmoothManifold n b N}
    {P : SmoothManifold (m+n) k (M × N)}
    (o : Orientation S) (q : Orientation T) (r : Orientation P) : Prop :=
  ∀ p E, IsProductDifferential S T P p E →
    ∀ v w, IsPositive (o.val p.1) v → IsPositive (q.val p.2) w →
      IsPositive (r.val p) (productVector E v w)

/-- A local diffeomorphism in the original smooth structures, including boundary
points. Values of a partial homeomorphism outside its source are irrelevant. -/
def IsLocalDiffeomorphism {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N) : Prop :=
  ∀ p, ∃ e : OpenPartialHomeomorph M N, p ∈ e.source ∧ EqOn e f e.source ∧
    ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val e e.source ∧
    ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val e.symm e.target

/-- Preservation is +1; reversal is -1. The differential witness is kept explicit
so independent Specs do not have to import an existence proof. -/
def orientationSign {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold n b N} {f : M → N}
    (o : Orientation S) (q : Orientation T)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p)) (p : M) : Bool :=
  if Module.Ray.map (determinantMap n (E p)) (o.val p) = q.val (f p)
    then true else false

end SmoothManifolds.OrientationProductData

namespace Specs.SmoothManifolds.Orientations.ProductsAndSigns
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.ProductData _root_.SmoothManifolds.BoundaryData
  _root_.SmoothManifolds.OrientationData _root_.SmoothManifolds.OrientationProductData Set
universe u

/-- The ordered determinant-line isomorphism, purely algebraic and therefore
also available for the later product corner construction. -/
def determinant_directSumType : Prop :=
  ∀ (m n : ℕ) (V W : Type u) [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W],
    Module.finrank ℝ V = m → Module.finrank ℝ W = n →
      Function.Bijective (determinantSumMap m n V W)

/-- The unique product orientation on every generating product smooth structure,
including zero-dimensional and empty factors. -/
def product_orientationType : Prop :=
  ∀ {m n : ℕ} {a b k : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (C : ProductCoordinates m a n b k) (P : SmoothManifold (m+n) k (M × N)),
    P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (productAtlas C S.smoothStructure.val T.smoothStructure.val) →
    ∀ (o : Orientation S) (q : Orientation T),
      ∃! r : Orientation P, IsProductOrientation o q r

/-- Existence for ordinary products with at most one boundary factor, expressed
intrinsically so a boundaryless factor may have either original model kind.
The smooth universal property specifies the original product structure. -/
def ordinary_productType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (o : Orientation S) (q : Orientation T),
    (intrinsicBoundary S = ∅ ∨ intrinsicBoundary T = ∅) →
    ∃ k, ∃ P : SmoothManifold (m+n) k (M × N),
      IsSmoothMap P S Prod.fst ∧ IsSmoothMap P T Prod.snd ∧
      (∀ {l : ℕ} {c : ModelKind} {Q : Type u} [TopologicalSpace Q]
        (R : SmoothManifold l c Q) (f : Q → M) (g : Q → N),
        IsSmoothMap R S f → IsSmoothMap R T g →
          IsSmoothMap R P (fun x => (f x, g x))) ∧
      (∀ p, ∃ E, IsProductDifferential S T P p E) ∧
      ∃! r : Orientation P, IsProductOrientation o q r

/-- The family used to define the sign exists uniquely and is the actual dF. -/
def local_differentialType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsLocalDiffeomorphism S T f →
    ∃! E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p),
      ∀ p, IsDifferential S T f p (E p).toLinearMap

/-- This gives both local constancy and the preservation/reversal meaning of the
sign on the actual determinant rays. In particular the sign never vanishes. -/
def local_signType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsLocalDiffeomorphism S T f → ∀ (o : Orientation S) (q : Orientation T)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, IsDifferential S T f p (E p).toLinearMap) →
    IsLocallyConstant (orientationSign o q E) ∧
      ∀ p, Module.Ray.map (determinantMap n (E p)) (o.val p) =
        if orientationSign o q E p then q.val (f p) else -q.val (f p)

/-- The local signs multiply in the order sign(G)(F(p)) sign(F)(p). -/
def sign_compType : Prop :=
  ∀ {n : ℕ} {a b c : ModelKind} {M N Q : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (R : SmoothManifold n c Q) (f : M → N) (g : N → Q),
    IsLocalDiffeomorphism S T f → IsLocalDiffeomorphism T R g →
    ∀ (o : Orientation S) (q : Orientation T) (r : Orientation R)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p))
    (F : ∀ p, TangentSpace T p ≃ₗ[ℝ] TangentSpace R (g p))
    (H : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace R ((g ∘ f) p)),
    (∀ p, IsDifferential S T f p (E p).toLinearMap) →
    (∀ p, IsDifferential T R g p (F p).toLinearMap) →
    (∀ p, IsDifferential S R (g ∘ f) p (H p).toLinearMap) →
    ∀ p, signValue (orientationSign o r H p) =
      signValue (orientationSign q r F (f p)) * signValue (orientationSign o q E p)

end Specs.SmoothManifolds.Orientations.ProductsAndSigns
