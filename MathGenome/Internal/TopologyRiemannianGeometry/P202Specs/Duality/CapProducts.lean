import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.CupProduct

/-! The front/back cap operation of `prop:p202-cap`, paper.tex 2156–2192.
The coefficients are an arbitrary commutative ring; no topological restrictions
are imposed. `capAt` keeps all degree equalities explicit. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite HomologicalComplex
open scoped TensorProduct Simplicial
namespace P202Specs.CapProducts
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains P202Specs.CupProduct
universe u w
variable (R : Type u) [CommRing R]

/-- Cap on the finite singular basis, in any nonnegative complementary degree. -/
def capAt (X : TopCat.{w}) (p n k : ℕ) (h : p+k=n) :
    Cochain R X p →ₗ[R] Chains R X n →ₗ[R] Chains R X k where
  toFun a := Finsupp.llift (Chains R X k) R R (Simplex X n) (fun s =>
    a (Finsupp.single (interval s 0 p (by omega)) 1) •
      Finsupp.single (interval s p k (by omega)) 1)
  map_add' := by
    intro a b
    apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X n)).ext
    intro s
    simp [Finsupp.llift_apply, Finsupp.lift_apply, add_smul]
  map_smul' := by
    intro r a
    apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X n)).ext
    intro s
    simp [Finsupp.llift_apply, Finsupp.lift_apply]

/-- Identifications for arbitrary nonnegative integer degrees. -/
def chainDegreeEquiv (X : TopCat.{w}) (q : ℤ) (hq : 0 ≤ q) :
    (ordinaryComplex R R X).X q ≃ₗ[R] Chains R X q.toNat :=
  (eqToIso (by rw [Int.toNat_of_nonneg hq])).toLinearEquiv.trans
    (ordinaryNonnegativeIso R R X q.toNat).toLinearEquiv

/-- The actual integer-graded ordinary operation. In degrees below p it is zero,
with target the ordinary complex in the negative degree q-p. -/
def cap (X : TopCat.{w}) (p : ℕ) (q : ℤ) :
    Cochain R X p →ₗ[R]
      (ordinaryComplex R R X).X q →ₗ[R] (ordinaryComplex R R X).X (q-p) := by
  by_cases h : (p : ℤ) ≤ q
  · exact (LinearMap.llcomp R _ _ _
      ((chainDegreeEquiv R X (q-p) (by omega)).symm.toLinearMap)).comp ((LinearMap.compl₂ (capAt R X p q.toNat (q-p).toNat (by omega)))
        (chainDegreeEquiv R X q (by omega)).toLinearMap)
  · exact 0

/-! Full independent laws; the integer grading includes the ordinary zero
negative groups. Pair descent statements are added below. -/
def formula_type : Prop := ∀ (R : Type u) [CommRing R] (X : TopCat.{w})
    (p n k : ℕ) (h : p+k=n) (a : Cochain R X p) (s : Simplex X n) (r : R),
  capAt R X p n k h a (Finsupp.single s r) =
    (r * a (Finsupp.single (interval s 0 p (by omega)) 1)) •
      Finsupp.single (interval s p k (by omega)) 1

def pairing_type : Prop := ∀ (R : Type u) [CommRing R] (X : TopCat.{w})
    (p n k : ℕ) (h : p+k=n) (a : Cochain R X p) (b : Cochain R X k)
    (c : Chains R X n),
  b (capAt R X p n k h a c) = castCochain R h (cup R X p k a b) c

def boundary_type : Prop := ∀ (R : Type u) [CommRing R] (X : TopCat.{w})
    (p n k : ℕ) (h : p+k=n) (a : Cochain R X p) (c : Chains R X (n+1)),
  boundary R R X k (capAt R X p (n+1) (k+1) (by omega) a c) =
    (-1 : ℤ)^p • (capAt R X p n k h a (boundary R R X n c) -
      capAt R X (p+1) (n+1) k (by omega) (delta R X p a) c)

def naturality_type : Prop := ∀ (R : Type u) [CommRing R] {X Y : TopCat.{w}}
    (f : X ⟶ Y) (p n k : ℕ) (h : p+k=n) (a : Cochain R Y p)
    (c : Chains R X n),
  ((chainMap R R f).f k).hom (capAt R X p n k h (pullback R f p a) c) =
    capAt R Y p n k h a (((chainMap R R f).f n).hom c)

def capAt_type := ∀ (R : Type u) [CommRing R] (X : TopCat.{w})
  (p n k : ℕ) (h : p+k=n),
  Cochain R X p →ₗ[R] Chains R X n →ₗ[R] Chains R X k
abbrev capAt_value := @capAt

def cap_type := ∀ (R : Type u) [CommRing R] (X : TopCat.{w}) (p : ℕ) (q : ℤ),
  Cochain R X p →ₗ[R]
    (ordinaryComplex R R X).X q →ₗ[R] (ordinaryComplex R R X).X (q-p)
abbrev cap_value := @cap

/-- Transport along an equality of ordinary degrees. -/
def castOrdinary {X : TopCat.{w}} {i j : ℤ} (h : i=j) :
    (ordinaryComplex R R X).X i →ₗ[R] (ordinaryComplex R R X).X j :=
  (eqToIso (congrArg (fun n => (ordinaryComplex R R X).X n) h)).hom.hom

/-- Full boundary identity, including all zero and negative degrees. -/
def ordinaryBoundary_type : Prop := ∀ (R : Type u) [CommRing R]
    (X : TopCat.{w}) (p : ℕ) (q : ℤ) (a : Cochain R X p)
    (c : (ordinaryComplex R R X).X q),
  (ordinaryComplex R R X).d (q-p) (q-p-1) (cap R X p q a c) =
    (-1 : ℤ)^p •
      (castOrdinary R (by omega : (q-1)-(p : ℤ)=q-p-1)
        (cap R X p (q-1) a ((ordinaryComplex R R X).d q (q-1) c)) -
       castOrdinary R (by omega : q-((p+1 : ℕ) : ℤ)=q-p-1)
        (cap R X (p+1) q (delta R X p a) c))

def ordinaryNaturality_type : Prop := ∀ (R : Type u) [CommRing R]
    {X Y : TopCat.{w}} (f : X ⟶ Y) (p : ℕ) (q : ℤ)
    (a : Cochain R Y p) (c : (ordinaryComplex R R X).X q),
  ((ordinaryFunctor R R).map f).f (q-p) (cap R X p q (pullback R f p a) c) =
    cap R Y p q a (((ordinaryFunctor R R).map f).f q c)

def zeroAbove_type : Prop := ∀ (R : Type u) [CommRing R]
    (X : TopCat.{w}) (p : ℕ) (q : ℤ), q < p → cap R X p q = 0

/-- The two pair products on the existing ordinary (co)homology. The
representative clauses require precisely capAt's convention, via `cap`.
Every lift of a relative cycle is allowed, including degree zero. -/
structure PairProducts where
  absolute : ∀ (P : Pair.{w}) (p : ℕ) (q : ℤ),
    (ordinaryCohomology R R P.space (p : ℤ) ⊗[R] relativeHomology R R P q) →ₗ[R]
      relativeHomology R R P (q-p)
  relative : ∀ (P : Pair.{w}) (p : ℕ) (q : ℤ),
    (relativeCohomology R R P (p : ℤ) ⊗[R] relativeHomology R R P q) →ₗ[R]
      homology R R P.space (q-p)
  absolute_represents : ∀ (P : Pair.{w}) (p : ℕ) (q : ℤ)
    (a : (ordinaryCochains R R P.space).cycles (p : ℤ))
    (z : (ordinary R R P).cycles q)
    (c : (ordinaryComplex R R P.space).X q)
    (_hc : (projection (ordinaryFunctor R R) P).f q c = (ordinary R R P).iCycles q z),
    ∃ v : (ordinary R R P).cycles (q-p),
      (ordinary R R P).iCycles (q-p) v =
        (projection (ordinaryFunctor R R) P).f (q-p)
          (cap R P.space p q (cocycleValue R P.space p a) c) ∧
      absolute P p q
        ((ordinaryCochains R R P.space).homologyπ (p : ℤ) a ⊗ₜ[R]
          (ordinary R R P).homologyπ q z) = (ordinary R R P).homologyπ (q-p) v
  relative_represents : ∀ (P : Pair.{w}) (p : ℕ) (q : ℤ)
    (a : (relativeCochains R R P).cycles (p : ℤ))
    (z : (ordinary R R P).cycles q)
    (c : (ordinaryComplex R R P.space).X q)
    (_hc : (projection (ordinaryFunctor R R) P).f q c = (ordinary R R P).iCycles q z),
    ∃ v : (ordinaryComplex R R P.space).cycles (q-p),
      (ordinaryComplex R R P.space).iCycles (q-p) v =
        cap R P.space p q
          (ordinaryCochainsEquiv R R P.space p
            ((relativeToAbsolute R R P).f (p : ℤ)
              ((relativeCochains R R P).iCycles (p : ℤ) a))) c ∧
      relative P p q
        ((relativeCochains R R P).homologyπ (p : ℤ) a ⊗ₜ[R]
          (ordinary R R P).homologyπ q z) =
            (ordinaryComplex R R P.space).homologyπ (q-p) v
  absolute_zero_above : ∀ (P : Pair.{w}) (p : ℕ) (q : ℤ), q < (p : ℤ) → absolute P p q = 0
  relative_zero_above : ∀ (P : Pair.{w}) (p : ℕ) (q : ℤ), q < (p : ℤ) → relative P p q = 0

def pairProducts_type : Prop := ∀ (R : Type u) [CommRing R],
  Nonempty (PairProducts.{u,w} R)

end P202Specs.CapProducts
