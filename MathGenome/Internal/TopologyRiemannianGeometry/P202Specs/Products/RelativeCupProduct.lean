import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.CupProduct
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-! `prop:p202-relative-cup`, paper.tex 1966–1996.
The intermediate complex is the actual quotient by C(U)+C(V), not by
C(U ∪ V). Openness is imposed only on the comparison and final product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open scoped TensorProduct
namespace P202Specs.RelativeCupProduct
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.CupProduct
universe u w

/-- Two ordered, arbitrary subspaces of one space. -/
structure TwoSubspaces where
  space : TopCat.{w}
  left : Set space
  right : Set space

abbrev TwoSubspaces.leftPair (P : TwoSubspaces.{w}) : Pair := ⟨P.space, P.left⟩
abbrev TwoSubspaces.rightPair (P : TwoSubspaces.{w}) : Pair := ⟨P.space, P.right⟩
abbrev TwoSubspaces.unionPair (P : TwoSubspaces.{w}) : Pair := ⟨P.space, P.left ∪ P.right⟩
def TwoSubspaces.IsOpen (P : TwoSubspaces.{w}) : Prop := _root_.IsOpen P.left ∧ _root_.IsOpen P.right

structure TwoSubspaces.Map (P Q : TwoSubspaces.{w}) where
  map : P.space ⟶ Q.space
  left : Set.MapsTo map P.left Q.left
  right : Set.MapsTo map P.right Q.right

def TwoSubspaces.Map.leftMap {P Q : TwoSubspaces.{w}} (f : P.Map Q) :
    P.leftPair ⟶ Q.leftPair := ⟨f.map, f.left⟩
def TwoSubspaces.Map.rightMap {P Q : TwoSubspaces.{w}} (f : P.Map Q) :
    P.rightPair ⟶ Q.rightPair := ⟨f.map, f.right⟩
def TwoSubspaces.Map.unionMap {P Q : TwoSubspaces.{w}} (f : P.Map Q) :
    P.unionPair ⟶ Q.unionPair :=
  ⟨f.map, fun _ h => h.elim (fun h => Or.inl (f.left h)) (fun h => Or.inr (f.right h))⟩

variable (R : Type u) [CommRing R]

/-- Its range is exactly the sum of the two subspace chain modules. -/
def sumInclusion (P : TwoSubspaces.{w}) :=
  biprod.desc (inclusion (ordinaryFunctor R R) P.leftPair)
    (inclusion (ordinaryFunctor R R) P.rightPair)

abbrev sumQuotient (P : TwoSubspaces.{w}) := cokernel (sumInclusion R P)
abbrev sumProjection (P : TwoSubspaces.{w}) := cokernel.π (sumInclusion R P)

lemma inclusion_projection_of_subset (X : TopCat.{w}) (U W : Set X) (h : U ⊆ W) :
    inclusion (ordinaryFunctor R R) (⟨X,U⟩ : Pair) ≫
      projection (ordinaryFunctor R R) (⟨X,W⟩ : Pair) = 0 := by
  let f : (⟨X,U⟩ : Pair) ⟶ (⟨X,W⟩ : Pair) := ⟨𝟙 X, h⟩
  have hf := inclusion_square (ordinaryFunctor R R) f
  have hi : inclusion (ordinaryFunctor R R) (⟨X,U⟩ : Pair) =
      (ordinaryFunctor R R).map f.restrict ≫ inclusion (ordinaryFunctor R R) (⟨X,W⟩ : Pair) := by
    simpa [f] using hf
  rw [hi, Category.assoc]
  simp [projection, inclusion]

/-- The canonical surjection C(X)/(C(U)+C(V)) → C(X,U ∪ V). -/
def sumToUnion (P : TwoSubspaces.{w}) : sumQuotient R P ⟶ ordinary R R P.unionPair :=
  cokernel.desc (sumInclusion R P) (projection (ordinaryFunctor R R) P.unionPair) (by
    apply biprod.hom_ext' <;> simp only [sumInclusion, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, comp_zero]
    · exact inclusion_projection_of_subset R P.space P.left (P.left ∪ P.right) Set.subset_union_left
    · exact inclusion_projection_of_subset R P.space P.right (P.left ∪ P.right) Set.subset_union_right)

/-- Algebraic dual of the genuine sum quotient, with no coefficient restrictions. -/
abbrev sumCochains (P : TwoSubspaces.{w}) :=
  (dualComplexFunctor R R (ComplexShape.down ℤ)).obj (op (sumQuotient R P))
abbrev sumToAbsolute (P : TwoSubspaces.{w}) :
    sumCochains R P ⟶ ordinaryCochains R R P.space :=
  (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumProjection R P).op
abbrev unionComparison (P : TwoSubspaces.{w}) :
    relativeCochains R R P.unionPair ⟶ sumCochains R P :=
  (dualComplexFunctor R R (ComplexShape.down ℤ)).map (sumToUnion R P).op

abbrev HR (P : Pair.{w}) (n : ℕ) := relativeCohomology R R P (n : ℤ)
abbrev forget (P : Pair.{w}) (n : ℕ) : HR R P n →ₗ[R] H R P.space n :=
  (homologyMap (relativeToAbsolute R R P) (n : ℤ)).hom
abbrev relativePullback {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ) : HR R Q n →ₗ[R] HR R P n :=
  ((relativeCohomologyFunctor R R (n : ℤ)).map f.op).hom

def relativeCocycleValue (P : Pair.{w}) (n : ℕ)
    (a : (relativeCochains R R P).cycles (n : ℤ)) : Cochain R P.space n :=
  ordinaryCochainsEquiv R R P.space n
    ((relativeToAbsolute R R P).f (n : ℤ) ((relativeCochains R R P).iCycles (n : ℤ) a))

def sumCocycleValue (P : TwoSubspaces.{w}) (n : ℕ)
    (a : (sumCochains R P).cycles (n : ℤ)) : Cochain R P.space n :=
  ordinaryCochainsEquiv R R P.space n
    ((sumToAbsolute R P).f (n : ℤ) ((sumCochains R P).iCycles (n : ℤ) a))

/-- Sum of the two images in the nonnegative singular chain module. -/
def sumChains (P : TwoSubspaces.{w}) (n : ℕ) : Submodule R (Chains R P.space n) :=
  ((chainMap R R P.leftPair.inclusion).f n).hom.range ⊔
    ((chainMap R R P.rightPair.inclusion).f n).hom.range

/-- The cup formula annihilates the sum for arbitrary subspaces. -/
def cochainVanishing_type : Prop := ∀ (R : Type u) [CommRing R]
    (P : TwoSubspaces.{w}) (p q : ℕ) (a : Cochain R P.space p) (b : Cochain R P.space q),
    a ∈ vanishingCochains R R P.leftPair p →
    b ∈ vanishingCochains R R P.rightPair q →
    ∀ c ∈ sumChains R P (p+q), cup R P.space p q a b c = 0

/-- The cochain operation lands in the dual of the sum quotient, for arbitrary
subspaces. This precedes the open-set comparison on cohomology. -/
def cochainProduct_type : Prop := ∀ (R : Type u) [CommRing R]
    (P : TwoSubspaces.{w}) (p q : ℕ),
    ∃ μ : (relativeCochains R R P.leftPair).X (p : ℤ) →ₗ[R]
      (relativeCochains R R P.rightPair).X (q : ℤ) →ₗ[R]
        (sumCochains R P).X ((p+q : ℕ) : ℤ),
    ∀ a b, ordinaryCochainsEquiv R R P.space (p+q)
      ((sumToAbsolute R P).f ((p+q : ℕ) : ℤ) (μ a b)) =
      cup R P.space p q
        (ordinaryCochainsEquiv R R P.space p ((relativeToAbsolute R R P.leftPair).f (p : ℤ) a))
        (ordinaryCochainsEquiv R R P.space q ((relativeToAbsolute R R P.rightPair).f (q : ℤ) b))

/-- Full comparison obligation; no small-chain or duality certificate is assumed. -/
def comparison_type : Prop := ∀ (R : Type u) [CommRing R]
    (P : TwoSubspaces.{w}), P.IsOpen → ∀ n : ℤ,
      IsIso (homologyMap (unionComparison R P) n)

/-- The product is on the pre-existing relative cohomology, and the
representation law fixes it by the singular front/back formula after the
canonical sum-quotient comparison. -/
structure NaturalRelativeCupProduct where
  product : ∀ (P : TwoSubspaces.{w}), P.IsOpen → ∀ p q : ℕ,
    HR R P.leftPair p ⊗[R] HR R P.rightPair q →ₗ[R] HR R P.unionPair (p+q)
  represents : ∀ (P : TwoSubspaces.{w}) (h : P.IsOpen) (p q : ℕ)
      (a : (relativeCochains R R P.leftPair).cycles (p : ℤ))
      (b : (relativeCochains R R P.rightPair).cycles (q : ℤ)),
    ∃ c : (sumCochains R P).cycles ((p+q : ℕ) : ℤ),
      sumCocycleValue R P (p+q) c = cup R P.space p q
        (relativeCocycleValue R P.leftPair p a) (relativeCocycleValue R P.rightPair q b) ∧
      homologyMap (unionComparison R P) ((p+q : ℕ) : ℤ)
        (product P h p q
          ((relativeCochains R R P.leftPair).homologyπ (p : ℤ) a ⊗ₜ[R]
           (relativeCochains R R P.rightPair).homologyπ (q : ℤ) b)) =
        (sumCochains R P).homologyπ ((p+q : ℕ) : ℤ) c
  naturality : ∀ (P Q : TwoSubspaces.{w}) (hP : P.IsOpen) (hQ : Q.IsOpen)
      (f : P.Map Q) (p q : ℕ) (a : HR R Q.leftPair p) (b : HR R Q.rightPair q),
    relativePullback R f.unionMap (p+q) (product Q hQ p q (a ⊗ₜ[R] b)) =
      product P hP p q (relativePullback R f.leftMap p a ⊗ₜ[R]
        relativePullback R f.rightMap q b)
  absolute : ∀ (P : TwoSubspaces.{w}) (hP : P.IsOpen) (p q : ℕ)
      (a : HR R P.leftPair p) (b : HR R P.rightPair q)
      (ordinaryRing : CohomologyRing R P.space),
    forget R P.unionPair (p+q) (product P hP p q (a ⊗ₜ[R] b)) =
      ordinaryRing.product p q (forget R P.leftPair p a) (forget R P.rightPair q b)

def product_type : Prop := ∀ (R : Type u) [CommRing R],
  Nonempty (NaturalRelativeCupProduct.{u,w} R)

/-- The final clause is unchanged from the unrestricted pair theorem. -/
def pairLongExact_type : Prop := ∀ (R : Type u) [CommRing R],
  P202Specs.CohomologyPairs.Expected.longExact.{u,u,w} R R

end P202Specs.RelativeCupProduct
