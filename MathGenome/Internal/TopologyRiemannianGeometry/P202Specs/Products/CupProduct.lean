import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.AlexanderWhitney
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.DirectSum.Algebra

/-!
Theorem `thm:p202-cup`, paper.tex 1932–1964. Cochains are unrestricted
algebraic duals of the shared ordinary finite singular chains. All coefficient
rings, spaces, and nonnegative degrees are arbitrary. The definitions below
are canonical data, not assumed cup-product identities or homotopy certificates.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite HomologicalComplex
open scoped TensorProduct DirectSum Simplicial
namespace P202Specs.CupProduct
open P202Specs.SingularChains P202Specs.AlexanderWhitney
open P202Specs.CohomologyPairs
universe u w
variable (R : Type u) [CommRing R]

abbrev Cochain (X : TopCat.{w}) (n : ℕ) := Chains R X n →ₗ[R] R

def chainBoundary (X : TopCat.{w}) (n : ℕ) :
    Chains R X (n+1) →ₗ[R] Chains R X n := boundary R R X n

/-- Precomposition with the ordinary boundary, with no additional sign. -/
def delta (X : TopCat.{w}) (n : ℕ) :
    Cochain R X n →ₗ[R] Cochain R X (n+1) :=
  LinearMap.lcomp R R (chainBoundary R X n)

/-- The exact front/back formula, extended from the free singular basis. -/
def cup (X : TopCat.{w}) (p q : ℕ) :
    Cochain R X p →ₗ[R] Cochain R X q →ₗ[R] Cochain R X (p+q) where
  toFun a :=
    { toFun := fun b => Finsupp.llift R R R (Simplex X (p+q)) (fun s =>
        a (Finsupp.single (interval s 0 p (by omega)) 1) *
        b (Finsupp.single (interval s p q (by omega)) 1))
      map_add' := by
        intro b c
        rw [← map_add]
        congr 1
        funext s
        simp only [LinearMap.add_apply, Pi.add_apply, mul_add]
      map_smul' := by
        intro r b
        rw [← map_smul]
        congr 1
        funext s
        simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro c
    apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X (p+q))).ext
    intro s
    simp [Finsupp.llift_apply, Finsupp.lift_apply, add_mul]
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro b
    apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X (p+q))).ext
    intro s
    simp [Finsupp.llift_apply, Finsupp.lift_apply, mul_assoc]

/-- Constant one on point simplices, including the empty space. -/
def oneCochain (X : TopCat.{w}) : Cochain R X 0 := augmentationLinear R R X

/-- Pullback is precomposition with the actual singular chain map. -/
def pullback {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    Cochain R Y n →ₗ[R] Cochain R X n :=
  LinearMap.lcomp R R ((chainMap R R f).f n).hom

/-- Transport only the degree; no choice of cochains or chain maps is involved. -/
def castCochain {X : TopCat.{w}} {p q : ℕ} (h : p=q)
    (a : Cochain R X p) : Cochain R X q := h ▸ a

/-- Evaluation of a homogeneous tensor by two cochains. -/
def tensorPairing {X Y : TopCat.{w}} {p q : ℕ}
    (a : Cochain R X p) (b : Cochain R Y q) : Summand R X Y p q →ₗ[R] R :=
  (LinearMap.mul' R R).comp (TensorProduct.map a b)

/-- The chain diagonal D = AW Δ, on the ordinary nonnegative complex. -/
def diagonalMap (X : TopCat.{w}) : X ⟶ productSpace X X :=
  TopCat.ofHom ⟨fun x => (x,x), continuous_id.prodMk continuous_id⟩

def chainDiagonal (X : TopCat.{w}) (n : ℕ) : Chains R X n →ₗ[R] Total R X X n :=
  (aw R X X n).comp ((chainMap R R (diagonalMap X)).f n).hom

/-- The Koszul interchange, in the same finite-diagonal coordinates as AW. -/
def interchange (X : TopCat.{w}) (n : ℕ) : Total R X X n →ₗ[R] Total R X X n where
  toFun z i := (-1 : ℤ)^(i.val.1*i.val.2) •
    (TensorProduct.comm R (Chains R X i.val.2) (Chains R X i.val.1))
      (z ⟨(i.val.2,i.val.1), by have := i.property; omega⟩)
  map_add' := by intro a b; ext i; simp [map_add, smul_add]
  map_smul' := by
    intro r z
    ext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    exact smul_comm _ _ _

/-- A natural chain homotopy D - TD = ∂H + H∂, including degree zero.
Its existence is a theorem obligation below, not an extra premise. -/
structure DiagonalHomotopy where
  hom : ∀ (X : TopCat.{w}) (n : ℕ), Chains R X n →ₗ[R] Total R X X (n+1)
  zero : ∀ X, chainDiagonal R X 0 - (interchange R X 0).comp (chainDiagonal R X 0) =
    (totalBoundary R X X 0).comp (hom X 0)
  succ : ∀ X n,
    chainDiagonal R X (n+1) - (interchange R X (n+1)).comp (chainDiagonal R X (n+1)) =
      (totalBoundary R X X (n+1)).comp (hom X (n+1)) +
        (hom X n).comp (chainBoundary R X n)
  naturality : ∀ {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ),
    (totalMap R f f (n+1)).comp (hom X n) =
      (hom Y n).comp ((chainMap R R f).f n).hom

/-- Full cochain laws before passing to cohomology. -/
def CochainLaws : Prop :=
  (∀ (X : TopCat.{w}) (p q : ℕ) (a : Cochain R X p) (b : Cochain R X q)
      (s : Simplex X (p+q)),
    cup R X p q a b (Finsupp.single s 1) =
      a (Finsupp.single (interval s 0 p (by omega)) 1) *
      b (Finsupp.single (interval s p q (by omega)) 1)) ∧
  (∀ (X : TopCat.{w}) (p q : ℕ) (a : Cochain R X p) (b : Cochain R X q),
    delta R X (p+q) (cup R X p q a b) =
      castCochain R (by omega) (cup R X (p+1) q (delta R X p a) b) +
        (-1 : ℤ)^p • castCochain R (by omega) (cup R X p (q+1) a (delta R X q b))) ∧
  (∀ (X : TopCat.{w}) (p q r : ℕ) (a : Cochain R X p)
      (b : Cochain R X q) (c : Cochain R X r),
    castCochain R (Nat.add_assoc p q r) (cup R X (p+q) r (cup R X p q a b) c) =
      cup R X p (q+r) a (cup R X q r b c)) ∧
  (∀ (X : TopCat.{w}) (p : ℕ) (a : Cochain R X p),
    castCochain R (Nat.zero_add p) (cup R X 0 p (oneCochain R X) a) = a ∧
      castCochain R (Nat.add_zero p) (cup R X p 0 a (oneCochain R X)) = a) ∧
  (∀ {X Y : TopCat.{w}} (f : X ⟶ Y) (p q : ℕ)
      (a : Cochain R Y p) (b : Cochain R Y q),
    pullback R f (p+q) (cup R Y p q a b) =
      cup R X p q (pullback R f p a) (pullback R f q b)) ∧
  (∀ (X : TopCat.{w}) (p q : ℕ) (a : Cochain R X p) (b : Cochain R X q)
      (c : Chains R X (p+q)),
    cup R X p q a b c = tensorPairing R a b
      (chainDiagonal R X (p+q) c ⟨(p,q),rfl⟩))

/-- Use the existing ordinary, integer-indexed cohomology, not a newly chosen
quotient with no connection to ordinary singular cohomology. -/
abbrev H (X : TopCat.{w}) (n : ℕ) : Type (max u w) := ordinaryCohomology R R X (n : ℤ)
abbrev HStar (X : TopCat.{w}) := ⨁ n : ℕ, H R X n

/-- The cochain represented by an actual cycle in the ordinary dual complex. -/
def cocycleValue (X : TopCat.{w}) (n : ℕ)
    (a : (ordinaryCochains R R X).cycles (n : ℤ)) : Cochain R X n :=
  ordinaryCochainsEquiv R R X n ((ordinaryCochains R R X).iCycles (n : ℤ) a)

abbrev hPullback {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) : H R Y n →ₗ[R] H R X n :=
  ((ordinaryCohomologyFunctor R R (n : ℤ)).map f.op).hom

/-- A genuine graded ring on the existing cohomology modules. `GRing` supplies
associativity, a degree-zero unit and distributivity on the direct sum;
`GAlgebra` supplies the algebra over R with the existing module structures. -/
structure CohomologyRing (X : TopCat.{w}) where
  gradedRing : DirectSum.GRing (H R X)
  algebra : letI := gradedRing; DirectSum.GAlgebra R (H R X)
  product : ∀ p q, H R X p →ₗ[R] H R X q →ₗ[R] H R X (p+q)
  product_eq : letI := gradedRing
    ∀ p q (a : H R X p) (b : H R X q),
      GradedMonoid.GMul.mul a b = product p q a b
  represents : ∀ (p q : ℕ) (a : (ordinaryCochains R R X).cycles (p : ℤ))
      (b : (ordinaryCochains R R X).cycles (q : ℤ)),
    ∃ c : (ordinaryCochains R R X).cycles ((p+q : ℕ) : ℤ),
      cocycleValue R X (p+q) c = cup R X p q (cocycleValue R X p a) (cocycleValue R X q b) ∧
      product p q ((ordinaryCochains R R X).homologyπ (p : ℤ) a)
        ((ordinaryCochains R R X).homologyπ (q : ℤ) b) =
          (ordinaryCochains R R X).homologyπ ((p+q : ℕ) : ℤ) c
  unit_represents : letI := gradedRing
    ∃ a : (ordinaryCochains R R X).cycles 0,
      cocycleValue R X 0 a = oneCochain R X ∧
        (GradedMonoid.GOne.one : H R X 0) = (ordinaryCochains R R X).homologyπ 0 a
  graded_commutative : ∀ p q (a : H R X p) (b : H R X q),
    GradedMonoid.mk (p+q) (product p q a b) =
      GradedMonoid.mk (q+p) ((-1 : ℤ)^(p*q) • product q p b a)

/-- A natural family of unital associative graded R-algebras, with pullbacks
being actual algebra homomorphisms whose homogeneous parts are the supplied
ordinary cohomology pullbacks. -/
structure NaturalCohomologyRing where
  ring : ∀ X : TopCat.{w}, CohomologyRing R X
  pullback : ∀ {X Y : TopCat.{w}} (f : X ⟶ Y),
    letI := (ring X).gradedRing
    letI := (ring X).algebra
    letI := (ring Y).gradedRing
    letI := (ring Y).algebra
    HStar R Y →ₐ[R] HStar R X
  pullback_homogeneous : ∀ {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) (a : H R Y n),
    pullback f (DirectSum.of (H R Y) n a) = DirectSum.of (H R X) n (hPullback R f n a)

/-! Complete independent theorem statements, with no homotopy or comparison premises. -/
def cochainLaws_type : Prop := ∀ (R : Type u) [CommRing R], CochainLaws.{u,w} R

def diagonalHomotopy_type : Prop := ∀ (R : Type u) [CommRing R],
  Nonempty (DiagonalHomotopy.{u,w} R)

def cohomologyRing_type : Prop := ∀ (R : Type u) [CommRing R],
  Nonempty (NaturalCohomologyRing.{u,w} R)

end P202Specs.CupProduct
