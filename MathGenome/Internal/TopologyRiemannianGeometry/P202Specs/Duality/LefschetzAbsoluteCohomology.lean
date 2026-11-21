import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.LefschetzRelativeCohomology

/-! The second cap isomorphism of T31 (paper.tex 2307–2319, 2372–2386).
The diagram below is stated for arbitrary pairs and arbitrary relative classes.
Its specialization to the shared relative fundamental class uses its already
proved positive-boundary equation; it does not assume either cap isomorphism.
All complexes are the existing integer-graded ordinary singular complexes.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u v
namespace P202Specs.LefschetzAbsoluteCohomology
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.RelativeFundamentalClass P202Specs.ChainLES

/-- Ordinary cap, specified by the same front/back representative formula as
PairProducts. This contains no isomorphism or manifold certificate. Existence
of this structure is a separate theorem target. -/
structure OrdinaryProducts (R : Type u) [CommRing R] where
  op : ∀ (X : TopCat.{v}) (p : ℕ) (q : ℤ),
    ordinaryCohomology R R X (p : ℤ) →ₗ[R]
      homology R R X q →ₗ[R] homology R R X (q-p)
  represents : ∀ (X : TopCat.{v}) (p : ℕ) (q : ℤ)
    (a : (ordinaryCochains R R X).cycles (p : ℤ))
    (z : (ordinaryComplex R R X).cycles q),
    ∃ w : (ordinaryComplex R R X).cycles (q-p),
      (ordinaryComplex R R X).iCycles (q-p) w =
        P202Specs.CapProducts.cap R X p q
          (P202Specs.CupProduct.cocycleValue R X p a)
          ((ordinaryComplex R R X).iCycles q z) ∧
      op X p q ((ordinaryCochains R R X).homologyπ (p : ℤ) a)
        ((ordinaryComplex R R X).homologyπ q z) =
          (ordinaryComplex R R X).homologyπ (q-p) w

variable (R : Type u) [CommRing R]

/-- Degree equality transports only, on the existing bundled groups. -/
def degreeCast (H : ℤ → ModuleCat.{max u v} R) {i j : ℤ} (h : i = j) :
    H i →ₗ[R] H j := h ▸ LinearMap.id

def absoluteCapNat (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p : ℕ) (q : ℤ) (z : relativeHomology R R P q) :
    ordinaryCohomology R R P.space (p : ℤ) →ₗ[R] relativeHomology R R P (q-p) :=
  (c.absolute P p q).comp ((TensorProduct.mk R _ _).flip z)

def relativeCapNat (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p : ℕ) (q : ℤ) (z : relativeHomology R R P q) :
    relativeCohomology R R P (p : ℤ) →ₗ[R] homology R R P.space (q-p) :=
  (c.relative P p q).comp ((TensorProduct.mk R _ _).flip z)

/-- The all-degree second cap map; the negative-cohomology branch is zero. -/
def absoluteCap (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p q : ℤ) (z : relativeHomology R R P q) :
    ordinaryCohomology R R P.space p →ₗ[R] relativeHomology R R P (q-p) := by
  by_cases hp : 0 ≤ p
  · exact (Int.toNat_of_nonneg hp) ▸ absoluteCapNat R c P p.toNat q z
  · exact 0

def relativeCap (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (P : Pair.{v}) (p q : ℤ) (z : relativeHomology R R P q) :
    relativeCohomology R R P p →ₗ[R] homology R R P.space (q-p) := by
  by_cases hp : 0 ≤ p
  · exact (Int.toNat_of_nonneg hp) ▸ relativeCapNat R c P p.toNat q z
  · exact 0

def ordinaryCap (c : OrdinaryProducts.{u,v} R) (X : TopCat.{v})
    (p q : ℤ) (z : homology R R X q) :
    ordinaryCohomology R R X p →ₗ[R] homology R R X (q-p) := by
  by_cases hp : 0 ≤ p
  · exact (Int.toNat_of_nonneg hp) ▸ (c.op X p.toNat q).flip z
  · exact 0

/-- Compatibility of all three kinds of arrows of the two long exact
sequences. The homological boundary square has exactly (-1)^p; the
cohomological boundary square has positive sign. The latter is the equality
[δa cap c]=[a cap ∂c], since their difference is (-1)^(p+1)∂(a cap c).
The degree casts express q-(p+1)=(q-1)-p and (q-1)-p=q-p-1. -/
structure CapDiagram (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (b : OrdinaryProducts.{u,v} R) (P : Pair.{v}) (q : ℤ)
    (z : relativeHomology R R P q)
    (hH : DegreewiseShortExact (sequence (ordinaryFunctor R R) P))
    (hC : DegreewiseShortExact (cochainSequence R R P)) : Prop where
  quotient : ∀ (p : ℤ) (a : relativeCohomology R R P p),
    absoluteCap R c P p q z (homologyMap (relativeToAbsolute R R P) p a) =
      homologyMap (projection (ordinaryFunctor R R) P) (q-p)
        (relativeCap R c P p q z a)
  boundary : ∀ (p : ℤ) (a : ordinaryCohomology R R P.space p),
    connecting hH (q-p) (q-p-1) (by simp)
      (absoluteCap R c P p q z a) =
      (-1 : ℤ)^p.natAbs • degreeCast R (homology R R P.sub)
        (by omega : (q-1)-p=q-p-1)
        (ordinaryCap R b P.sub p (q-1)
          (connecting hH q (q-1) (by simp) z)
          (homologyMap (restriction R R P) p a))
  connecting : ∀ (p : ℤ) (a : ordinaryCohomology R R P.sub p),
    degreeCast R (homology R R P.space) (by omega : q-(p+1)=(q-1)-p)
      (relativeCap R c P (p+1) q z (P202Specs.ChainLES.connecting hC p (p+1) (by simp) a)) =
      homologyMap (inclusion (ordinaryFunctor R R) P) ((q-1)-p)
        (ordinaryCap R b P.sub p (q-1)
          (P202Specs.ChainLES.connecting hH q (q-1) (by simp) z) a)

namespace Expected

def ordinaryProducts : Prop :=
  ∀ (R : Type u) [CommRing R], Nonempty (OrdinaryProducts.{u,v} R)

/-- The full signed pair comparison, before any use of duality. -/
def diagram : Prop :=
  ∀ (R : Type u) [CommRing R]
    (c : P202Specs.CapProducts.PairProducts.{u,v} R) (b : OrdinaryProducts.{u,v} R)
    (P : Pair.{v}) (q : ℤ) (z : relativeHomology R R P q)
    (hH : DegreewiseShortExact (sequence (ordinaryFunctor R R) P))
    (hC : DegreewiseShortExact (cochainSequence R R P)), CapDiagram R c b P q z hH hC

/-- On the original positive-dimensional manifold, the same signed diagram
uses the induced outward-normal-first boundary fundamental class. The
zero-dimensional boundary is empty, and is covered by the all-pair diagram. -/
def comparison : Prop :=
  ∀ (R : Type u) [CommRing R]
    (c : P202Specs.CapProducts.PairProducts.{u,v} R) (b : OrdinaryProducts.{u,v} R)
    (q : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold (q+1) .halfSpace M),
    let B := manifoldBoundary A
    ∀ (collar : Collar B) (AI : Manifold (q+1) (Interior B)) (AB : Manifold q B)
      (o : Orientation R AI) (oB : Orientation R AB),
      IsOutwardNormalFirst R B collar q o.val oB.val →
      IsCompact (Set.univ : Set M) →
      ∀ (hH : DegreewiseShortExact (sequence (ordinaryFunctor R R) (boundaryPair M B)))
        (hC : DegreewiseShortExact (cochainSequence R R (boundaryPair M B))),
        CapDiagram R c b (boundaryPair M B) ((q+1 : ℕ) : ℤ)
          (fundamentalClass R B (q+1) o.val) hH hC ∧
        degreeCast R (homology R R (TopCat.of B)) (by omega : ((q+1 : ℕ) : ℤ)-1=(q : ℤ))
          (connecting hH ((q+1 : ℕ) : ℤ) (((q+1 : ℕ) : ℤ)-1) (by simp)
            (fundamentalClass R B (q+1) o.val)) = boundaryClass R B q oB.val

/-- The second cap isomorphism for the same shared relative fundamental
class as the first one. The atlas includes Hausdorff and second-countability;
the collar is geometric only. No orientation, connectivity, nonemptiness,
positive-dimension or nonempty-boundary restrictions are added. -/
def duality : Prop :=
  ∀ (R : Type u) [CommRing R] (c : P202Specs.CapProducts.PairProducts.{u,v} R)
    (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : SmoothManifolds.ModelData.TopologicalManifold n .halfSpace M),
    let B := manifoldBoundary A
    ∀ (_collar : Collar B) (AI : Manifold n (Interior B)) (o : Orientation R AI),
      IsCompact (Set.univ : Set M) → ∀ p : ℤ,
      Function.Bijective (absoluteCap R c (boundaryPair M B) p (n : ℤ)
        (fundamentalClass R B n o.val))

/-- Required dimension-vanishing consequences, using ordinary finite chains. -/
def aboveDimension : Prop := P202Specs.LefschetzRelativeCohomology.Expected.aboveDimension.{u,v}

end Expected
end P202Specs.LefschetzAbsoluteCohomology
