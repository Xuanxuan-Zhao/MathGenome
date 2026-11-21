import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.ThomClass
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CapProducts
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.TransverseNormalCoordinates
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.LocalThomProjection
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.RelativeCupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.EilenbergZilber
import Mathlib.Topology.Homeomorph.Lemmas

/-!
Independent specifications for the transverse-product part of
`lem:p202-projective-thom`, paper.tex 2545–2548 and 2576–2588.

The current independent targets cover relative chain evaluation, evaluation
on every actual relative cup representative, actual orientation-dual normal
fiber cycles, finite ordered normal-model generators, the nullary unit, the
empty-intersection endpoint, and the full one-member Thom conclusion.
Actual Thom factors and their ordered products are constructed for every
nonempty finite family. The full geometric target includes every normalized transverse normal slice.
No simultaneous normal-coordinate theorem or disk-fiber orientation theorem
is assumed by the definitions below.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped TensorProduct
universe u w
namespace P202Specs.TransverseThomProduct
open P202Specs.SingularChains P202Specs.AlexanderWhitney
  P202Specs.ShuffleModel P202Specs.CupProduct P202Specs.EilenbergZilber

variable (R : Type u) [CommRing R]

/-- Evaluation in the ordered bidegree `(p,q)` of a total tensor chain. -/
def orderedPairing {X Y : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q) (n : ℕ) (h : p+q=n) :
    Total R X Y n →ₗ[R] R :=
  (tensorPairing R a b).comp (LinearMap.proj (R := R)
    (φ := fun j : Diagonal n => Summand R X Y j.val.1 j.val.2) ⟨(p,q),h⟩)

/-- A cochain annihilates all chains of the indicated subspace. This is a
condition on the actual singular chain inclusion, with no openness assumed. -/
def VanishesOn {X : TopCat.{w}} (A : Set X) {p : ℕ} (a : Cochain R X p) : Prop :=
  ∀ c : Chains R (TopCat.of A) p,
    a (((chainMap R R (subspaceInclusion X A)).f p).hom c) = 0

/-- Relative cycle condition in the total tensor complex, including the
ordinary degree-zero endpoint. The subspace is the sum of the two faces. -/
def IsRelativeTensorCycle (X Y : TopCat.{w}) (A : Set X) (B : Set Y) :
    (n : ℕ) → Total R X Y n → Prop
  | 0, _ => True
  | n+1, z => totalBoundary R X Y n z ∈ tensorPair R X Y A B n

/-- A relative cycle in the finite singular chain model. -/
def IsRelativeCycle (X : TopCat.{w}) (A : Set X) :
    (n : ℕ) → Chains R X n → Prop
  | 0, _ => True
  | n+1, c => c |> boundary R R X n |> fun z =>
      z ∈ LinearMap.range ((chainMap R R (subspaceInclusion X A)).f n).hom

/-- The union of the two relative product faces, as an actual subspace of
`X × Y`. A singular simplex in this union need not lie in one face. -/
def productFaces (X Y : TopCat.{w}) (A : Set X) (B : Set Y) :
    Set (productSpace X Y) :=
  {z | z.1 ∈ A ∨ z.2 ∈ B}

/-- Ordered external cochain: first pull back along the first projection,
then along the second, and apply the given front/back cup formula. -/
def externalCochain (X Y : TopCat.{w}) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R Y q) :
    Cochain R (productSpace X Y) (p+q) :=
  cup R (productSpace X Y) p q
    (pullback R (firstProjection X Y) p a)
    (pullback R (secondProjection X Y) q b)

/-- The ordered two subspaces used for the external relative cup product. -/
def productSubspaces (X Y : TopCat.{w}) (A : Set X) (B : Set Y) :
    P202Specs.RelativeCupProduct.TwoSubspaces :=
  ⟨productSpace X Y, {z | z.1 ∈ A}, {z | z.2 ∈ B}⟩

/-- Openness of the two product faces is exactly the hypothesis needed for
relative cup products; no submanifold itself is assumed open. -/
theorem productSubspaces_isOpen (X Y : TopCat.{w}) (A : Set X) (B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) : (productSubspaces X Y A B).IsOpen :=
  ⟨hA.preimage continuous_fst, hB.preimage continuous_snd⟩

/-- A cycle modulo the sum of the two actual face chain submodules. This
retains the distinction from cycles modulo chains in the union. -/
def IsSumRelativeCycle (P : P202Specs.RelativeCupProduct.TwoSubspaces.{w}) :
    (n : ℕ) → Chains R P.space n → Prop
  | 0, _ => True
  | n+1, c => boundary R R P.space n c ∈
      P202Specs.RelativeCupProduct.sumChains R P n

/-- First projection, with the first relative face. -/
def productLeftProjection (X Y : TopCat.{w}) (A : Set X) (B : Set Y) :
    (productSubspaces X Y A B).leftPair ⟶
      (⟨X, A⟩ : P202Specs.RelativeSingularChains.Pair) :=
  ⟨firstProjection X Y, fun _ h => h⟩

/-- Second projection, with the second relative face. -/
def productRightProjection (X Y : TopCat.{w}) (A : Set X) (B : Set Y) :
    (productSubspaces X Y A B).rightPair ⟶
      (⟨Y, B⟩ : P202Specs.RelativeSingularChains.Pair) :=
  ⟨secondProjection X Y, fun _ h => h⟩

/-- The homotopy evaluation bridge, with both relative face conditions.
This is an auxiliary obligation, not the complete transverse Thom theorem. -/
def evaluation_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R Y q),
    delta R X p a = 0 → delta R Y q b = 0 →
    VanishesOn R A a → VanishesOn R B b →
    ∀ z : Total R X Y (p+q), IsRelativeTensorCycle R X Y A B (p+q) z →
      externalCochain R X Y p q a b (shuffle R X Y (p+q) z) =
        orderedPairing R a b (p+q) rfl z

/-- Evaluation one for actual relative chains, in their fixed factor order.
No positivity restriction is imposed on either degree. -/
def evaluationOne_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (p q : ℕ)
    (a : Cochain R X p) (b : Cochain R Y q)
    (c : Chains R X p) (d : Chains R Y q),
    delta R X p a = 0 → delta R Y q b = 0 →
    VanishesOn R A a → VanishesOn R B b →
    IsRelativeCycle R X A p c → IsRelativeCycle R Y B q d →
    a c = 1 → b d = 1 →
      externalCochain R X Y p q a b
        (shuffleComponent R X Y p q (c ⊗ₜ[R] d)) = 1


section ModelProducts
open P202Specs.ThomClass SmoothManifolds.ModelData P202Specs.RelativeSingularChains

/-- The first normal block occupies castAdd indices, the second natAdd indices. -/
def orderedModelHomeomorph (p q : ℕ) :
    ((modelPair.{w} p).space × (modelPair.{w} q).space) ≃ₜ
      (modelPair.{w} (p+q)).space :=
  ((Homeomorph.ulift.prodCongr Homeomorph.ulift).trans
    (Fin.appendHomeomorph (X := ℝ) p q)).trans Homeomorph.ulift.symm

lemma orderedModelHomeomorph_apply (p q : ℕ)
    (x : (modelPair.{w} p).space) (y : (modelPair.{w} q).space) :
    (orderedModelHomeomorph p q (x,y)).down = Fin.append x.down y.down := rfl

lemma orderedModelHomeomorph_zero (p q : ℕ) :
    orderedModelHomeomorph p q (⟨0⟩,⟨0⟩) = ⟨0⟩ := by
  apply ULift.ext
  change Fin.append (0 : Euclidean p) (0 : Euclidean q) = 0
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp
  · intro j
    simp

lemma orderedModelHomeomorph_zero_iff (p q : ℕ)
    (z : (modelPair.{w} p).space × (modelPair.{w} q).space) :
    (orderedModelHomeomorph p q z).down = 0 ↔ z.1.down = 0 ∧ z.2.down = 0 := by
  constructor
  · intro h
    have hz : orderedModelHomeomorph p q z = orderedModelHomeomorph p q (⟨0⟩,⟨0⟩) :=
      (ULift.ext h).trans (orderedModelHomeomorph_zero p q).symm
    have hprod := (orderedModelHomeomorph p q).injective hz
    exact ⟨congrArg (fun z => z.1.down) hprod, congrArg (fun z => z.2.down) hprod⟩
  · rintro ⟨hx,hy⟩
    have hprod : z = (⟨0⟩,⟨0⟩) := Prod.ext (ULift.ext hx) (ULift.ext hy)
    rw [hprod, orderedModelHomeomorph_zero]

/-- The union of all two-block punctured faces is the punctured total normal space. -/
def orderedModelProductIso (p q : ℕ) :
    (productSubspaces (modelPair.{w} p).space (modelPair.{w} q).space
      (modelPair.{w} p).subspace (modelPair.{w} q).subspace).unionPair ≅
      modelPair.{w} (p+q) where
  hom := {
    map := TopCat.ofHom ⟨orderedModelHomeomorph p q, (orderedModelHomeomorph p q).continuous⟩
    mapsTo := by
      intro z hz hzero
      have he := (orderedModelHomeomorph_zero_iff p q z).mp hzero
      exact hz.elim (fun h => h he.1) (fun h => h he.2) }
  inv := {
    map := TopCat.ofHom ⟨(orderedModelHomeomorph p q).symm, (orderedModelHomeomorph p q).symm.continuous⟩
    mapsTo := by
      intro z hz
      change ((orderedModelHomeomorph p q).symm z).1.down ≠ 0 ∨
        ((orderedModelHomeomorph p q).symm z).2.down ≠ 0
      by_contra h
      push Not at h
      apply hz
      have he := (orderedModelHomeomorph_zero_iff p q ((orderedModelHomeomorph p q).symm z)).mpr h
      simpa only [Homeomorph.apply_symm_apply] using he }
  hom_inv_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    exact ContinuousMap.ext (orderedModelHomeomorph p q).symm_apply_apply
  inv_hom_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    exact ContinuousMap.ext (orderedModelHomeomorph p q).apply_symm_apply

lemma orderedModelProductIso_left (p q : ℕ)
    (x : (modelPair.{w} p).space) (y : (modelPair.{w} q).space) (i : Fin p) :
    ((orderedModelProductIso p q).hom.map (x,y)).down (Fin.castAdd q i) = x.down i :=
  Fin.append_left _ _ _

lemma orderedModelProductIso_right (p q : ℕ)
    (x : (modelPair.{w} p).space) (y : (modelPair.{w} q).space) (i : Fin q) :
    ((orderedModelProductIso p q).hom.map (x,y)).down (Fin.natAdd p i) = y.down i :=
  Fin.append_right _ _ _

end ModelProducts

section RelativeProductEvaluation
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
  P202Specs.RelativeCupProduct

/-- Evaluation on any actual cocycle representative of the prescribed external
relative cup class. The two factors are relative cohomology classes, and the
product lies in cohomology relative to the union of the two product faces.
This bridge does not assert the still-unproved construction of disk cycles
from smooth normal-bundle orientation data. -/
def relativeProductEvaluation_type : Prop := ∀ (R : Type u) [CommRing R]
    (μ : NaturalRelativeCupProduct.{u,w} R)
    (X Y : TopCat.{w}) (A : Set X) (B : Set Y) (hA : IsOpen A) (hB : IsOpen B)
    (p q : ℕ)
    (a : (relativeCochains R R (⟨X,A⟩ : Pair)).cycles (p : ℤ))
    (b : (relativeCochains R R (⟨Y,B⟩ : Pair)).cycles (q : ℤ))
    (c : Chains R X p) (d : Chains R Y q),
    IsRelativeCycle R X A p c → IsRelativeCycle R Y B q d →
    relativeCocycleValue R (⟨X,A⟩ : Pair) p a c = 1 →
    relativeCocycleValue R (⟨Y,B⟩ : Pair) q b d = 1 →
    ∀ e : (relativeCochains R R (productSubspaces X Y A B).unionPair).cycles
        ((p+q : ℕ) : ℤ),
      (relativeCochains R R (productSubspaces X Y A B).unionPair).homologyπ
          ((p+q : ℕ) : ℤ) e =
        μ.product (productSubspaces X Y A B) (productSubspaces_isOpen X Y A B hA hB) p q
          (relativePullback R (productLeftProjection X Y A B) p
            ((relativeCochains R R (⟨X,A⟩ : Pair)).homologyπ (p : ℤ) a) ⊗ₜ[R]
           relativePullback R (productRightProjection X Y A B) q
            ((relativeCochains R R (⟨Y,B⟩ : Pair)).homologyπ (q : ℤ) b)) →
      relativeCocycleValue R (productSubspaces X Y A B).unionPair (p+q) e
        (shuffleComponent R X Y p q (c ⊗ₜ[R] d)) = 1

end RelativeProductEvaluation

/-- Empty support means the actual relative group of `(X,X)` is zero. -/
def emptySupport_type : Prop := ∀ (R : Type u) [CommRing R]
    (X : TopCat.{w}) (s : Set X), s = ∅ → ∀ n : ℤ,
    CategoryTheory.Limits.IsZero
      (P202Specs.CohomologyPairs.relativeCohomology R R
        (⟨X,sᶜ⟩ : P202Specs.RelativeSingularChains.Pair) n)

section GeometricData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData SmoothManifolds.TangentData

/-- Input data for one member, using the same actual smooth manifolds and
quotient normal bundle as the frozen Thom interface. No Thom class is input. -/
structure OrientedSubmanifold {n : ℕ} (M : TopCat.{w})
    (S : SmoothManifold n .euclidean M) where
  source : TopCat.{w}
  compact : CompactSpace source
  dimension : ℕ
  atlas : SmoothManifold dimension .euclidean source
  inclusion : source → M
  embedding : IsSmoothEmbedding atlas S inclusion
  normal : NormalBundle atlas S inclusion
  codimension : ℕ
  rank : ∀ _ : source, codimension = n - dimension
  orientation : P202Specs.ThomClass.Orientation R normal codimension

variable {n k : ℕ} {M : TopCat.{w}} {S : SmoothManifold n .euclidean M}

def OrientedSubmanifold.support (N : OrientedSubmanifold R M S) : Set M :=
  Set.range N.inclusion

/-- Forget orientation while retaining exactly the same smooth embedding and
quotient normal bundle. This adapter changes no underlying geometric object. -/
def OrientedSubmanifold.embeddedData (N : OrientedSubmanifold R M S) :
    P202Specs.TransverseNormalCoordinates.EmbeddedData S where
  dimension := N.dimension
  source := N.source
  topology := inferInstance
  compact := N.compact
  manifold := N.atlas
  inclusion := N.inclusion
  embedding := N.embedding
  normal := N.normal

/-- The family is ordered by `Fin k`; no permutation of factors is implicit. -/
def intersectionSupport (F : Fin k → OrientedSubmanifold R M S) : Set M :=
  ⋂ j, (F j).support

def totalCodimension (F : Fin k → OrientedSubmanifold R M S) : ℕ :=
  ∑ j, (F j).codimension


set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
/-- The quotient projection from an ambient tangent fiber to one actual normal
fiber. The equality identifies the embedded point with the common ambient point. -/
def normalProjectionAt (N : OrientedSubmanifold R M S)
    (p : N.source) (x : M) (h : N.inclusion p = x) :
    TangentSpace S x → NormalFiber N.normal p := by
  subst x
  exact Submodule.Quotient.mk

/-- Mutual transversality at a common point is surjectivity onto the ordered
product of all normal quotient fibers. Pairwise transversality would be weaker
for three or more members. No simultaneous-coordinate certificate is assumed. -/
def IsTransverse (F : Fin k → OrientedSubmanifold R M S) : Prop :=
  ∀ (x : M) (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x),
    Function.Surjective (fun v : TangentSpace S x =>
      fun j => normalProjectionAt R (F j) (p j) x (h j) v)


/-- Simultaneous smooth normal coordinates and a normalized smooth local
slice exist for the original oriented family. Their differential consists of
the actual ordered quotient normal projections; no coordinates are input. -/
def normalCoordinates_type : Prop := ∀ (R : Type u) [CommRing R]
    (n k : ℕ) (M : TopCat.{w}) (S : SmoothManifold n .euclidean M)
    (F : Fin k → OrientedSubmanifold R M S), IsTransverse R F →
    ∀ (x : M) (p : ∀ j, (F j).source)
      (h : ∀ j, (F j).inclusion (p j) = x),
      Nonempty (P202Specs.TransverseNormalCoordinates.SimultaneousCoordinates
        (fun j => (F j).embeddedData R) x p h)

/-- The empty-intersection conclusion for the actual ambient relative pair.
No transversality is needed for this endpoint. -/
def emptyIntersection_type : Prop := ∀ (R : Type u) [CommRing R]
    (n k : ℕ) (M : TopCat.{w}) (S : SmoothManifold n .euclidean M)
    (F : Fin k → OrientedSubmanifold R M S),
    intersectionSupport R F = ∅ → ∀ q : ℤ,
    CategoryTheory.Limits.IsZero
      (P202Specs.CohomologyPairs.relativeCohomology R R
        (⟨M,(intersectionSupport R F)ᶜ⟩ : P202Specs.RelativeSingularChains.Pair) q)

end GeometricData

section LocalModels
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
  P202Specs.RelativeCupProduct P202Specs.ThomClass

/-- The literal restriction of an ambient supported pair to a neighborhood. -/
def restrictionPair (X : TopCat.{w}) (support V : Set X) : Pair.{w} :=
  ⟨TopCat.of V, {y | y.val ∉ support}⟩

def restrictionInclusion (X : TopCat.{w}) (support V : Set X) :
    restrictionPair X support V ⟶ (⟨X,supportᶜ⟩ : Pair) :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ hy => hy⟩

/-- Local projection data for every factor on one actual ambient neighborhood.
The classes and maps are conclusions of the local-model existence theorem;
none is part of the original transverse-family input. -/
structure LocalThomModels {n k : ℕ} {M : TopCat.{w}}
    {S : SmoothManifold n .euclidean M}
    (F : Fin k → OrientedSubmanifold R M S)
    (c : ∀ j, HR R (⟨M,((F j).support)ᶜ⟩ : Pair) (F j).codimension) (x : M) where
  neighborhood : Set M
  isOpen_neighborhood : IsOpen neighborhood
  mem_neighborhood : x ∈ neighborhood
  generator : ∀ j, HR R (modelPair.{w} (n-(F j).dimension)) (F j).codimension
  generates : ∀ j, Function.Bijective (fun r : R => r • generator j)
  projection : ∀ j, restrictionPair M (F j).support neighborhood ⟶
    modelPair.{w} (n-(F j).dimension)
  zero_equations : ∀ j (y : neighborhood),
    ((projection j).map y).down = 0 ↔ y.val ∈ (F j).support
  class_formula : ∀ j,
    relativePullback R (restrictionInclusion M (F j).support neighborhood)
      (F j).codimension (c j) =
    relativePullback R (projection j) (F j).codimension (generator j)

/-- Every collection of actual Thom factors has simultaneous local projection
formulas on a common neighborhood of each full intersection point. No
transversality is needed until constructing normal slices. -/
def localThomModels_type : Prop := ∀ (R : Type u) [CommRing R]
    (n k : ℕ) (M : TopCat.{w}) (S : SmoothManifold n .euclidean M)
    (F : Fin k → OrientedSubmanifold R M S)
    (c : ∀ j, HR R (⟨M,((F j).support)ᶜ⟩ : Pair) (F j).codimension),
    (∀ j, HasFiberValues R (F j).orientation (c j)) →
    ∀ x ∈ intersectionSupport R F, Nonempty (LocalThomModels R F c x)

end LocalModels

section OrderedProducts
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
  P202Specs.RelativeCupProduct

/-- A homogeneous class with closed support, on the original relative pair.
This is product input data; it asserts neither the existence nor the fiber
values of any Thom class. -/
structure SupportedClass (X : TopCat.{w}) where
  support : Set X
  closed : IsClosed support
  degree : ℕ
  value : HR R (⟨X, supportᶜ⟩ : Pair) degree

/-- The actual binary relative cup product, retaining the left-to-right order.
Closed support supplies exactly the openness needed by the frozen interface. -/
def supportedCup {X : TopCat.{w}} (μ : NaturalRelativeCupProduct R)
    (a b : SupportedClass R X) : SupportedClass R X where
  support := a.support ∩ b.support
  closed := a.closed.inter b.closed
  degree := a.degree + b.degree
  value := by
    let P : TwoSubspaces := ⟨X, a.supportᶜ, b.supportᶜ⟩
    have hP : P.IsOpen := ⟨a.closed.isOpen_compl, b.closed.isOpen_compl⟩
    simpa only [Set.compl_inter] using
      μ.product P hP a.degree b.degree (a.value ⊗ₜ[R] b.value)

/-- Right-associated cup product of a nonempty finite ordered family.
The one-member product is the given class, without multiplying by a chosen unit.
The nullary unit is a separate endpoint, not part of this auxiliary definition. -/
def orderedCup {X : TopCat.{w}} (μ : NaturalRelativeCupProduct R) :
    (k : ℕ) → (Fin (k+1) → SupportedClass R X) → SupportedClass R X
  | 0, F => F 0
  | k+1, F => supportedCup R μ (F 0) (orderedCup μ k (fun j => F j.succ))

end OrderedProducts

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.AbstractTubularData
open P202Specs.RelativeCupProduct P202Specs.RelativeSingularChains

/-- The one-member geometric endpoint uses the frozen Thom orientation and
all normalized tubular slices. Its singleton relative product is the class
itself for every ordered binary relative cup operation. -/
def singleMember_type : Prop := ∀ (R : Type u) [CommRing R]
    (n : ℕ) (M : TopCat.{w}) (S : SmoothManifold n .euclidean M)
    (N : OrientedSubmanifold R M S),
    (∃ K : TubularNeighborhood N.normal, P202Specs.ThomClass.NormalCompatible N.normal K) ∧
      ∃! c : HR R (⟨M, N.supportᶜ⟩ : Pair) N.codimension,
        P202Specs.ThomClass.HasFiberValues R N.orientation c ∧
          ∃ hclosed : IsClosed N.support,
            ∀ μ : NaturalRelativeCupProduct.{u,w} R,
              orderedCup R μ 0 (fun _ =>
                (⟨N.support, hclosed, N.codimension, c⟩ : SupportedClass R M)) =
                  (⟨N.support, hclosed, N.codimension, c⟩ : SupportedClass R M)

/-- Actual classes and their ordered relative products for every nonempty finite
family. All support and degree identifications preserve the prescribed order. -/
def orderedThomClasses_type : Prop := ∀ (R : Type u) [CommRing R]
    (n k : ℕ) (M : TopCat.{w}) (S : SmoothManifold n .euclidean M)
    (F : Fin (k+1) → OrientedSubmanifold R M S),
    ∃ (c : ∀ j, HR R (⟨M, ((F j).support)ᶜ⟩ : Pair) (F j).codimension)
      (hclosed : ∀ j, IsClosed (F j).support),
      (∀ j, P202Specs.ThomClass.HasFiberValues R (F j).orientation (c j)) ∧
      ∀ μ : NaturalRelativeCupProduct R,
        let p := orderedCup R μ k (fun j =>
          (⟨(F j).support, hclosed j, (F j).codimension, c j⟩ : SupportedClass R M))
        p.support = intersectionSupport R F ∧
          p.degree = totalCodimension R F ∧
          (intersectionSupport R F = ∅ → p.value = 0)


section OrientationCycles
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.BundleOperationsData SmoothManifolds.AbstractTubularData
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
  P202Specs.RelativeCupProduct P202Specs.ThomClass
attribute [local instance] normalTopology

/-- Every prescribed cohomological orientation generator on an actual normal
fiber has an actual finite relative singular cycle evaluating to one. The
punctured relative face is retained, and no positivity or coefficient restriction
is imposed. -/
def orientationCycle_type : Prop :=
  ∀ (R : Type u) [CommRing R] (m n d : ℕ)
    (P M : Type w) [TopologicalSpace P] [TopologicalSpace M]
    (T : SmoothManifold m .euclidean P) (S : SmoothManifold n .euclidean M)
    (i : P → M) (N : NormalBundle T S i), d = n-m →
    ∀ (o : Orientation R N d) (p : P),
      ∃ c : Chains R (fiberPair N p).space d,
        IsRelativeCycle R (fiberPair N p).space (fiberPair N p).subspace d c ∧
        ∀ a : (relativeCochains R R (fiberPair N p)).cycles (d : ℤ),
          (relativeCochains R R (fiberPair N p)).homologyπ (d : ℤ) a = o.generator p →
          relativeCocycleValue R (fiberPair N p) d a c = 1

end OrientationCycles

section ModelProductGenerator
open P202Specs.ThomClass P202Specs.RelativeSingularChains
  P202Specs.RelativeCupProduct

lemma modelPair_isOpen (d : ℕ) : IsOpen (modelPair.{w} d).subspace :=
  isOpen_ne_fun continuous_uliftDown continuous_const

/-- The external relative cup product preserves the first and second normal
coordinate blocks and uses their actual punctured relative faces. -/
def modelExternalProduct (μ : NaturalRelativeCupProduct.{u,w} R) (p q : ℕ)
    (a : HR R (modelPair.{w} p) p) (b : HR R (modelPair.{w} q) q) :
    HR R (productSubspaces (modelPair.{w} p).space (modelPair.{w} q).space
      (modelPair.{w} p).subspace (modelPair.{w} q).subspace).unionPair (p+q) :=
  μ.product _ (productSubspaces_isOpen _ _ _ _ (modelPair_isOpen p) (modelPair_isOpen q)) p q
    (relativePullback R (productLeftProjection _ _ _ _) p a ⊗ₜ[R]
      relativePullback R (productRightProjection _ _ _ _) q b)

/-- The ordered external relative cup product of actual normal-model
cohomology generators is itself a generator, for every degree and commutative
coefficient ring. This is the algebraic model conclusion, before comparison
with simultaneous smooth normal coordinates. -/
def modelProductGenerator_type : Prop := ∀ (R : Type u) [CommRing R]
    (μ : NaturalRelativeCupProduct.{u,w} R) (p q : ℕ)
    (a : HR R (modelPair.{w} p) p) (b : HR R (modelPair.{w} q) q),
    Function.Surjective (fun r : R => r • a) →
    Function.Surjective (fun r : R => r • b) →
    Function.Bijective (fun r : R => r • modelExternalProduct R μ p q a b)

def orderedModelProductOrientation (μ : NaturalRelativeCupProduct.{u,w} R) (p q : ℕ)
    (a : HR R (modelPair.{w} p) p) (b : HR R (modelPair.{w} q) q) :
    HR R (modelPair.{w} (p+q)) (p+q) :=
  relativePullback R (orderedModelProductIso p q).inv (p+q)
    (modelExternalProduct R μ p q a b)


structure ModelClass where
  degree : ℕ
  value : HR R (modelPair.{w} degree) degree

def modelCup (μ : NaturalRelativeCupProduct.{u,w} R) (a b : ModelClass.{u,w} R) :
    ModelClass.{u,w} R where
  degree := a.degree + b.degree
  value := orderedModelProductOrientation R μ a.degree b.degree a.value b.value

def orderedModelCup (μ : NaturalRelativeCupProduct.{u,w} R) :
    (k : ℕ) → (Fin (k+1) → ModelClass.{u,w} R) → ModelClass.{u,w} R
  | 0, F => F 0
  | k+1, F => modelCup R μ (F 0) (orderedModelCup μ k (fun j => F j.succ))


/-- The ordered finite product has the total normal degree and is a generator
whenever all factors are generators. The one-member case is included; no
permutation of normal coordinate blocks is performed. -/
def orderedModelOrientation_type : Prop := ∀ (R : Type u) [CommRing R]
    (μ : NaturalRelativeCupProduct.{u,w} R) (k : ℕ)
    (F : Fin (k+1) → ModelClass.{u,w} R),
    (orderedModelCup R μ k F).degree = ∑ j, (F j).degree ∧
      ((∀ j, Function.Surjective (fun r : R => r • (F j).value)) →
        Function.Bijective (fun r : R => r • (orderedModelCup R μ k F).value))

end ModelProductGenerator

section NullaryUnit
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
  P202Specs.RelativeCupProduct

/-- The nullary product is the unique degree-zero relative unit on (X,∅),
including empty X, characterized on every actual cocycle representative by
value one on every point cycle. -/
def nullaryUnit_type : Prop := ∀ (R : Type u) [CommRing R] (X : TopCat.{w}),
  ∃! c : HR R (⟨X,∅⟩ : Pair) 0,
    ∀ a : (relativeCochains R R (⟨X,∅⟩ : Pair)).cycles 0,
      (relativeCochains R R (⟨X,∅⟩ : Pair)).homologyπ 0 a = c →
      ∀ x : X, relativeCocycleValue R (⟨X,∅⟩ : Pair) 0 a
        (Finsupp.single ((simplexEquiv X 0).symm (ContinuousMap.const _ x)) 1) = 1

end NullaryUnit

section FullGeometricProduct
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData SmoothManifolds.TangentData SmoothManifolds.DifferentialData
open P202Specs.RelativeSingularChains P202Specs.CohomologyPairs
  P202Specs.RelativeCupProduct P202Specs.ThomClass
attribute [local instance] normalTopology
variable (R : Type u) [CommRing R]
variable {n k : ℕ} {M : TopCat.{w}} {S : SmoothManifold n .euclidean M}

/-- The original normal blocks, with their given Fin order. -/
abbrev normalBlocks (F : Fin k → OrientedSubmanifold R M S) :=
  ∀ j, Euclidean (n - (F j).dimension)

abbrev normalBlockSpace (F : Fin k → OrientedSubmanifold R M S) : TopCat.{w} :=
  TopCat.of (ULift.{w} (normalBlocks R F))

def zeroBlockSupport (F : Fin k → OrientedSubmanifold R M S) :
    Set (normalBlockSpace R F) := {z | z.down = 0}

/-- Original fiber charts and classes transporting to precisely the prescribed
orientation values. A generator condition or product identity is not an input. -/
structure ModelOrientationAt (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) where
  chartPoint : ∀ j, (F j).source
  base_mem : ∀ j, p j ∈ (normalBundle (F j).normal).baseSet (chartPoint j)
  value : ∀ j, HR R (modelPair.{w} (n - (F j).dimension)) (F j).codimension
  prescribed : ∀ j,
    relativePullback R (fiberCoordinates (F j).normal (chartPoint j) (p j) (base_mem j))
      (F j).codimension (value j) = (F j).orientation.generator (p j)

/-- A projection with exactly its own punctured normal face. -/
def blockProjectionPair (F : Fin k → OrientedSubmanifold R M S) (j : Fin k) :
    (⟨normalBlockSpace R F, {z | z.down j ≠ 0}⟩ : Pair.{w}) ⟶
      modelPair.{w} (n - (F j).dimension) where
  map := TopCat.ofHom ⟨fun z => ULift.up (z.down j),
    continuous_uliftUp.comp ((continuous_apply j).comp continuous_uliftDown)⟩
  mapsTo := fun _ hz => hz

/-- The actual pulled-back jth orientation class on the ordered normal blocks. -/
def blockSupportedFactor (F : Fin k → OrientedSubmanifold R M S)
    (p : ∀ j, (F j).source) (b : ModelOrientationAt R F p) (j : Fin k) :
    SupportedClass R (normalBlockSpace R F) where
  support := {z | z.down j = 0}
  closed := isClosed_eq ((continuous_apply j).comp continuous_uliftDown) continuous_const
  degree := (F j).codimension
  value := relativePullback R (blockProjectionPair R F j) (F j).codimension (b.value j)

/-- An actual smooth normal slice, normalized by the original quotient normal
maps. Its domain is arbitrary; no simultaneous coordinate or cohomology identity
is an input. Off the origin it misses the intersection. -/
structure NormalizedIntersectionSlice (F : Fin k → OrientedSubmanifold R M S)
    (x : M) (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x)
    (b : ModelOrientationAt R F p) where
  domain : Set (normalBlocks R F)
  domain_open : IsOpen domain
  domain_zero : 0 ∈ domain
  slice : normalBlocks R F → M
  center : slice 0 = x
  chart : ModelChart n .euclidean M
  chart_mem : chart ∈ S.smoothStructure.val
  in_chart : ∀ z ∈ domain, slice z ∈ chart.source
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (chart (slice z)).val) domain
  continuous : ContinuousOn slice domain
  injective : Set.InjOn slice domain
  tangentCoordinates : TangentSpace S x ≃ₗ[ℝ] Euclidean n
  tangent_isCoordinates : IsChartCoordinates S x chart tangentCoordinates
  derivative : normalBlocks R F →L[ℝ] Euclidean n
  has_derivative : HasFDerivAt (fun z => (chart (slice z)).val) derivative 0
  normal_derivative : ∀ (v : normalBlocks R F) j,
    normalProjectionAt R (F j) (p j) x (h j)
      (tangentCoordinates.symm (derivative v)) =
      (fiberLinearCoordinates (F j).normal (b.chartPoint j) (p j) (b.base_mem j)).symm (v j)
  avoids : ∀ z ∈ domain, z ≠ 0 → slice z ∉ intersectionSupport R F

namespace NormalizedIntersectionSlice
variable {R} {F : Fin k → OrientedSubmanifold R M S}
  {x : M} {p : ∀ j, (F j).source} {h : ∀ j, (F j).inclusion (p j) = x}
  {b : ModelOrientationAt R F p}

def pair (s : NormalizedIntersectionSlice R F x p h b) : Pair.{w} :=
  ⟨TopCat.of {z : ULift.{w} (normalBlocks R F) // z.down ∈ s.domain},
    {z | z.val.down ≠ 0}⟩

def toAmbient (s : NormalizedIntersectionSlice R F x p h b)
    (A : SupportedClass R M) (hA : A.support = intersectionSupport R F) :
    s.pair ⟶ (⟨M, A.supportᶜ⟩ : Pair.{w}) where
  map := TopCat.ofHom ⟨fun z => s.slice z.val.down,
    s.continuous.comp_continuous (continuous_uliftDown.comp continuous_subtype_val)
      (fun z => z.property)⟩
  mapsTo := by
    intro z hz
    change s.slice z.val.down ∉ A.support
    rw [hA]
    exact s.avoids z.val.down z.property hz

def toBlocks (s : NormalizedIntersectionSlice R F x p h b)
    (B : SupportedClass R (normalBlockSpace R F))
    (hB : B.support = zeroBlockSupport R F) :
    s.pair ⟶ (⟨normalBlockSpace R F, B.supportᶜ⟩ : Pair.{w}) where
  map := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  mapsTo := by
    intro z hz
    change z.val ∉ B.support
    rw [hB]
    exact hz

end NormalizedIntersectionSlice

/-- Equality transport changes only the ordinary cohomological degree. -/
def castRelativeDegree {P : Pair.{w}} {d e : ℕ} (h : d = e)
    (c : HR R P d) : HR R P e := h ▸ c

/-- The complete nonempty finite geometric assertion. The actual cup product
restricts on EVERY normalized normal slice to the product of the ORIGINAL
orientation values in the prescribed block order. Both the existence of slices
and the generator property of the product are conclusions. -/
def nonemptyTransverseProduct_type : Prop :=
  ∀ (R : Type u) [CommRing R] (n k : ℕ) (M : TopCat.{w})
    (S : SmoothManifold n .euclidean M)
    (F : Fin (k+1) → OrientedSubmanifold R M S), IsTransverse R F →
    ∃ (c : ∀ j, HR R (⟨M, ((F j).support)ᶜ⟩ : Pair) (F j).codimension)
      (hclosed : ∀ j, IsClosed (F j).support),
      (∀ j, HasFiberValues R (F j).orientation (c j)) ∧
      ∀ μ : NaturalRelativeCupProduct.{u,w} R,
        let A := orderedCup R μ k (fun j =>
          (⟨(F j).support, hclosed j, (F j).codimension, c j⟩ : SupportedClass R M))
        ∃ (hA : A.support = intersectionSupport R F)
          (hAd : A.degree = totalCodimension R F),
          ∀ (x : M) (p : ∀ j, (F j).source) (h : ∀ j, (F j).inclusion (p j) = x),
            Nonempty (ModelOrientationAt R F p) ∧
            ∀ b : ModelOrientationAt R F p,
              Nonempty (NormalizedIntersectionSlice R F x p h b) ∧
              let B := orderedCup R μ k (blockSupportedFactor R F p b)
              ∃ (hB : B.support = zeroBlockSupport R F)
                (hBd : B.degree = totalCodimension R F),
                Function.Bijective (fun r : R => r • B.value) ∧
                ∀ s : NormalizedIntersectionSlice R F x p h b,
                  castRelativeDegree R hAd
                    (relativePullback R (s.toAmbient A hA) A.degree A.value) =
                  castRelativeDegree R hBd
                    (relativePullback R (s.toBlocks B hB) B.degree B.value)

/-- Nullary products have support M, degree zero, and the pointwise unit
orientation. The existing nullaryUnit target is its actual cocycle formula. -/
def fullTransverseProduct_type : Prop :=
  nonemptyTransverseProduct_type.{u,w} ∧ nullaryUnit_type.{u,w}


end FullGeometricProduct

end P202Specs.TransverseThomProduct
