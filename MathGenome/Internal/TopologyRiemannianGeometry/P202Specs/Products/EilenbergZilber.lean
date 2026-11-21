import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.EZProductHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.EZTensorHomotopy
import Mathlib.Algebra.Homology.Homotopy

/-!
Independent obligations for paper.tex, Theorem `thm:p202-ez`, including its
naturality, its subspace use at `lem:p202-projective-thom`, and the smooth
restriction after the theorem. The maps below are the *specified* AW and
oriented shuffle, on the shared finite singular chains and ordinary tensor
complex. No chain identity or homotopy is assumed as a global certificate.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace P202Specs.EilenbergZilber
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.ShuffleModel
universe u w
variable (R : Type u) [CommRing R]

/-- The shared singular boundary with its finite-chain module type exposed. -/
def differential (X : TopCat.{w}) (n : ℕ) :
    Chains R X (n+1) →ₗ[R] Chains R X n := boundary R R X n

/-- The two prescribed maps packaged as chain maps. This is data to construct,
not a hypothesis added to Eilenberg--Zilber. -/
structure Comparison (X Y : TopCat.{w}) where
  toTensor : complex R R (productSpace X Y) ⟶ tensorComplex R X Y
  fromTensor : tensorComplex R X Y ⟶ complex R R (productSpace X Y)
  toTensor_f : ∀ n, toTensor.f n = ModuleCat.ofHom (aw R X Y n)
  fromTensor_f : ∀ n, fromTensor.f n = ModuleCat.ofHom (shuffle R X Y n)

/-- The canonical upstream family of product-side chain homotopies. -/
abbrev ProductHomotopy := P202Specs.EZProductHomotopy.ProductHomotopy.{u,w} R

/-- The canonical upstream family of tensor-side chain homotopies. -/
abbrev TensorHomotopy := P202Specs.EZTensorHomotopy.TensorHomotopy.{u,w} R

/-- The same product-side homotopy preserves corner-smooth singular chains. -/
abbrev ProductHomotopy.Smooth (h : ProductHomotopy.{u,w} R) : Prop :=
  P202Specs.EZProductHomotopy.ProductHomotopy.Smooth R h

/-- The same tensor-side homotopy admits a linear lift on smooth tensors. -/
abbrev TensorHomotopy.Smooth (h : TensorHomotopy.{u,w} R) : Prop :=
  P202Specs.EZTensorHomotopy.TensorHomotopy.Smooth.{u,w,w,w,w,w} R h

/-- The smooth restriction of the specified AW map. The shuffle restriction
and boundary stability already belong to the upstream shuffle goal. -/
def smoothAW_type : Prop :=
  ∀ (R : Type u) [CommRing R] {E F H K : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace K] (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] (n : ℕ),
    ∃ L : smoothChains R (H := ModelProd H K) (fun z => (I z.1, J z.2))
        (productSpace X Y) n →ₗ[R] SmoothTotal R I J X Y n,
      (smoothTotalInclusion R I J X Y n).comp L =
        (aw R X Y n).comp (smoothChains R (H := ModelProd H K)
          (fun z => (I z.1, J z.2)) (productSpace X Y) n).subtype

/-- The inclusion of an arbitrary subspace, with its induced topology. -/
def subspaceInclusion (X : TopCat.{w}) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The subcomplex C(A×Y)+C(X×B) relevant to relative products. -/
def productPair (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (n : ℕ) :
    Submodule R (Chains R (productSpace X Y) n) :=
  LinearMap.range ((chainMap R R (productMap (subspaceInclusion X A) (𝟙 Y))).f n).hom ⊔
    LinearMap.range ((chainMap R R (productMap (𝟙 X) (subspaceInclusion Y B))).f n).hom

/-- The corresponding subcomplex in the total tensor grading. -/
def tensorPair (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (n : ℕ) :
    Submodule R (Total R X Y n) :=
  LinearMap.range (totalMap R (subspaceInclusion X A) (𝟙 Y) n) ⊔
    LinearMap.range (totalMap R (𝟙 X) (subspaceInclusion Y B) n)

/-! Full theorem types; all coefficient rings and topological spaces are arbitrary. -/
def comparison_type : Prop := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}),
  Nonempty (Comparison R X Y)

def naturalHomotopies_type : Prop := ∀ (R : Type u) [CommRing R],
  ∃ (h : ProductHomotopy.{u,w} R) (k : TensorHomotopy.{u,w} R),
    h.Smooth R ∧ k.Smooth R

/-- Pointwise chain homotopy equivalence with exactly the prescribed maps.
The stronger `naturalHomotopies_type` stipulates natural choices of both homotopies. -/
def equivalence_type : Prop := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}),
  ∃ e : HomotopyEquiv (complex R R (productSpace X Y)) (tensorComplex R X Y),
    (∀ n, e.hom.f n = ModuleCat.ofHom (aw R X Y n)) ∧
    (∀ n, e.inv.f n = ModuleCat.ofHom (shuffle R X Y n))

/-- Naturality implies compatibility with both arbitrary subspaces and their
sum, so the maps and homotopies descend to the relative quotients. -/
def relativeCompatibility_type : Prop := ∀ (R : Type u) [CommRing R]
    (h : ProductHomotopy.{u,w} R) (k : TensorHomotopy.{u,w} R)
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (n : ℕ),
  (productPair R X Y A B n).map (aw R X Y n) ≤ tensorPair R X Y A B n ∧
  (tensorPair R X Y A B n).map (shuffle R X Y n) ≤ productPair R X Y A B n ∧
  (productPair R X Y A B n).map (h.hom X Y n) ≤ productPair R X Y A B (n+1) ∧
  (tensorPair R X Y A B n).map (k.hom X Y n) ≤ tensorPair R X Y A B (n+1)

/-- Exact library bridge from the paper's integer-indexed ordinary homology
to the nonnegative homology used in the external-product formula below. -/
def ordinaryHomologyIso (X : TopCat.{w}) (n : ℕ) :
    homology R R X (n : ℤ) ≅ (complex R R X).homology n :=
  (complex R R X).extendHomologyIso (degreeEmbedding 0)
    (by change (0 : ℤ) + (n : ℤ) = n; omega)

/-- A natural homological external product, with its exact value on every
pair of cycle representatives. In particular the shuffle, not an unspecified
chain map inducing an isomorphism, determines this operation. -/
structure ExternalProduct where
  map : ∀ (X Y : TopCat.{w}) (p q : ℕ),
    (complex R R X).homology p ⊗[R] (complex R R Y).homology q →ₗ[R]
      (complex R R (productSpace X Y)).homology (p+q)
  represents : ∀ (X Y : TopCat.{w}) (p q : ℕ)
      (a : (complex R R X).cycles p) (b : (complex R R Y).cycles q),
    ∃ z : (complex R R (productSpace X Y)).cycles (p+q),
      (complex R R (productSpace X Y)).iCycles (p+q) z =
        shuffleComponent R X Y p q
          ((complex R R X).iCycles p a ⊗ₜ[R] (complex R R Y).iCycles q b) ∧
      map X Y p q ((complex R R X).homologyπ p a ⊗ₜ[R]
        (complex R R Y).homologyπ q b) =
          (complex R R (productSpace X Y)).homologyπ (p+q) z
  naturality : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ),
    (HomologicalComplex.homologyMap (chainMap R R (productMap f g)) (p+q)).hom.comp
      (map X Y p q) =
    (map X' Y' p q).comp (TensorProduct.map
      (HomologicalComplex.homologyMap (chainMap R R f) p).hom
      (HomologicalComplex.homologyMap (chainMap R R g) q).hom)

def externalProduct_type : Prop := ∀ (R : Type u) [CommRing R],
  Nonempty (ExternalProduct.{u,w} R)

/-- Both prescribed maps form natural families before proving they are
homotopy inverses. -/
def naturalComparison_type : Prop := ∀ (R : Type u) [CommRing R],
  ∃ c : ∀ (X Y : TopCat.{w}), Comparison R X Y,
    (∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
      (totalMap R f g n).comp ((c X Y).toTensor.f n).hom =
        ((c X' Y').toTensor.f n).hom.comp ((chainMap R R (productMap f g)).f n).hom) ∧
    (∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
      ((chainMap R R (productMap f g)).f n).hom.comp ((c X Y).fromTensor.f n).hom =
        ((c X' Y').fromTensor.f n).hom.comp (totalMap R f g n))

end P202Specs.EilenbergZilber
