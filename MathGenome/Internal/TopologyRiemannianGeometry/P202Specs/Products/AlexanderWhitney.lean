import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularChains
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.BigOperators.Fin

/-! The ordinary nonnegative tensor grading, with finite diagonal products as
coordinates for the direct sums. All chains and simplex maps are the shared ones. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct DirectSum
namespace P202Specs.AlexanderWhitney
open P202Specs.SingularChains
universe u w
variable (R : Type u) [CommRing R]

abbrev Diagonal (n : ℕ) := {pq : ℕ × ℕ // pq.1 + pq.2 = n}

instance (n : ℕ) : Fintype (Diagonal n) :=
  Fintype.ofEquiv (Fin (n+1))
    { toFun := fun p => ⟨(p, n-p), by omega⟩
      invFun := fun i => ⟨i.val.1, by have := i.property; omega⟩
      left_inv := by intro p; rfl
      right_inv := by intro ⟨⟨p,q⟩,h⟩; apply Subtype.ext; dsimp; congr 1; omega }

abbrev Summand (X Y : TopCat.{w}) (p q : ℕ) := Chains R X p ⊗[R] Chains R Y q
abbrev Total (X Y : TopCat.{w}) (n : ℕ) :=
  (i : Diagonal n) → Summand R X Y i.val.1 i.val.2

/-- This is a direct sum: its indexing diagonal is finite. -/
def totalDirectSumEquiv (X Y : TopCat.{w}) (n : ℕ) :
    Total R X Y n ≃ₗ[R] ⨁ i : Diagonal n, Summand R X Y i.val.1 i.val.2 :=
  (DirectSum.linearEquivFunOnFintype R _ _).symm

def leftBoundary (X Y : TopCat.{w}) (p q : ℕ) :
    Summand R X Y (p+1) q →ₗ[R] Summand R X Y p q :=
  (boundary R R X p).rTensor (Chains R Y q)

def rightBoundary (X Y : TopCat.{w}) (p q : ℕ) :
    Summand R X Y p (q+1) →ₗ[R] Summand R X Y p q :=
  (boundary R R Y q).lTensor (Chains R X p)

/-- Component form of ∂a ⊗ b + (-1)^p a ⊗ ∂b. Neither
component asks for a boundary out of degree zero. -/
def totalBoundary (X Y : TopCat.{w}) (n : ℕ) :
    Total R X Y (n+1) →ₗ[R] Total R X Y n where
  toFun z i :=
    leftBoundary R X Y i.val.1 i.val.2
      (z ⟨(i.val.1+1,i.val.2), by have := i.property; omega⟩) +
    (-1 : ℤ)^i.val.1 • rightBoundary R X Y i.val.1 i.val.2
      (z ⟨(i.val.1,i.val.2+1), by have := i.property; omega⟩)
  map_add' z z' := by ext i; simp [map_add, smul_add]; abel
  map_smul' r z := by
    ext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add]
    rw [smul_comm r]

lemma leftBoundary_squared (X Y : TopCat.{w}) (p q : ℕ)
    (z : Summand R X Y (p+1+1) q) :
    leftBoundary R X Y p q (leftBoundary R X Y (p+1) q z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b =>
    change (boundary R R X p (boundary R R X (p+1) a)) ⊗ₜ[R] b = 0
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((complex R R X).d_comp_d (p+2) (p+1) p)) a
    change boundary R R X p (boundary R R X (p+1) a) = 0 at h
    rw [h, TensorProduct.zero_tmul]

lemma rightBoundary_squared (X Y : TopCat.{w}) (p q : ℕ)
    (z : Summand R X Y p (q+1+1)) :
    rightBoundary R X Y p q (rightBoundary R X Y p (q+1) z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b =>
    change a ⊗ₜ[R] (boundary R R Y q (boundary R R Y (q+1) b)) = 0
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((complex R R Y).d_comp_d (q+2) (q+1) q)) b
    change boundary R R Y q (boundary R R Y (q+1) b) = 0 at h
    rw [h, TensorProduct.tmul_zero]

lemma boundaries_commute (X Y : TopCat.{w}) (p q : ℕ)
    (z : Summand R X Y (p+1) (q+1)) :
    leftBoundary R X Y p q (rightBoundary R X Y (p+1) q z) =
      rightBoundary R X Y p q (leftBoundary R X Y p (q+1) z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b => rfl

lemma totalBoundary_square (X Y : TopCat.{w}) (n : ℕ) :
    (totalBoundary R X Y n).comp (totalBoundary R X Y (n+1)) = 0 := by
  apply LinearMap.ext
  intro z
  funext i
  simp only [LinearMap.comp_apply, totalBoundary, LinearMap.coe_mk, AddHom.coe_mk,
    map_add, map_zsmul, leftBoundary_squared, rightBoundary_squared,
    boundaries_commute, smul_zero, zero_add, add_zero, pow_succ, mul_smul,
    neg_one_zsmul, smul_neg, map_neg, neg_add_cancel, LinearMap.zero_apply, Pi.zero_apply]

/-- The canonical ordinary total tensor complex in finite diagonal coordinates. -/
def tensorComplex (X Y : TopCat.{w}) : ChainComplex (ModuleCat.{max u w} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (Total R X Y n))
    (fun n => ModuleCat.ofHom (totalBoundary R X Y n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact totalBoundary_square R X Y n)

/-- The ordered affine inclusion of an interval of vertices. -/
def intervalInclusion (a k n : ℕ) (h : a+k ≤ n) : ⦋k⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun j => ⟨a+j.val, by dsimp at *; omega⟩, by intro i j hij; exact Nat.add_le_add_left hij a⟩

/-- Restrict a shared singular simplex to an ordered interval face. -/
def interval {X : TopCat.{w}} {n : ℕ} (s : Simplex X n)
    (a k : ℕ) (h : a+k ≤ n) : Simplex X k :=
  (TopCat.toSSet.obj X).map (intervalInclusion a k n h).op s

def postSimplex {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    Simplex X n → Simplex Y n := (TopCat.toSSet.map f).app (op ⦋n⦌)

def productSpace (X Y : TopCat.{w}) : TopCat.{w} := TopCat.of (X × Y)
def firstProjection (X Y : TopCat.{w}) : productSpace X Y ⟶ X :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
def secondProjection (X Y : TopCat.{w}) : productSpace X Y ⟶ Y :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
def productMap {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') :
    productSpace X Y ⟶ productSpace X' Y' :=
  TopCat.ofHom ⟨fun z => (f z.1, g z.2), (f.hom.continuous.comp continuous_fst).prodMk
    (g.hom.continuous.comp continuous_snd)⟩

/-- A single AW component at the split p+q=n. -/
def awComponent (X Y : TopCat.{w}) (n : ℕ) (s : Simplex (productSpace X Y) n)
    (p q : ℕ) (h : p+q=n) : Summand R X Y p q :=
  Finsupp.single (interval (postSimplex (firstProjection X Y) n s) 0 p (by omega)) 1 ⊗ₜ[R]
    Finsupp.single (interval (postSimplex (secondProjection X Y) n s) p q (by omega)) 1

/-- Extension of the prescribed formula from the finite singular basis. -/
def aw (X Y : TopCat.{w}) (n : ℕ) :
    Chains R (productSpace X Y) n →ₗ[R] Total R X Y n :=
  Finsupp.lsum R (fun s =>
    { toFun := fun r i => r • awComponent R X Y n s i.val.1 i.val.2 i.property
      map_add' := by intros; ext i; apply add_smul
      map_smul' := by intros; ext i; exact mul_smul _ _ _ })

def totalMap {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    Total R X Y n →ₗ[R] Total R X' Y' n where
  toFun z i := TensorProduct.map ((chainMap R R f).f i.val.1).hom
    ((chainMap R R g).f i.val.2).hom (z i)
  map_add' := by intros; ext i; apply map_add
  map_smul' r z := by
    ext i
    change TensorProduct.map _ _ (r • z i) = r • _
    exact map_smul _ _ _

/-! Full independent obligations. -/
def tensorComplex_type := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}),
  ChainComplex (ModuleCat.{max u w} R) ℕ
abbrev tensorComplex_value := @tensorComplex

def totalDirectSumEquiv_type := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ),
  Total R X Y n ≃ₗ[R] ⨁ i : Diagonal n, Summand R X Y i.val.1 i.val.2
abbrev totalDirectSumEquiv_value := @totalDirectSumEquiv

def alexanderWhitney_type := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ),
  Chains R (productSpace X Y) n →ₗ[R] Total R X Y n
abbrev alexanderWhitney_value := @aw

def formula_type : Prop := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ)
  (s : Simplex (productSpace X Y) n) (r : R) (i : Diagonal n),
  aw R X Y n (Finsupp.single s r) i =
    r • (Finsupp.single (interval (postSimplex (firstProjection X Y) n s) 0 i.val.1
      (by have := i.property; omega)) 1 ⊗ₜ[R]
    Finsupp.single (interval (postSimplex (secondProjection X Y) n s) i.val.1 i.val.2
      (by have := i.property; omega)) 1)

def totalBoundary_squared_type : Prop := ∀ (R : Type u) [CommRing R]
  (X Y : TopCat.{w}) (n : ℕ),
  (totalBoundary R X Y n).comp (totalBoundary R X Y (n+1)) = 0

def chain_identity_type : Prop := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ),
  (totalBoundary R X Y n).comp (aw R X Y (n+1)) =
    (aw R X Y n).comp (boundary R R (productSpace X Y) n)

def naturality_type : Prop := ∀ (R : Type u) [CommRing R] {X X' Y Y' : TopCat.{w}}
  (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
  (totalMap R f g n).comp (aw R X Y n) =
    (aw R X' Y' n).comp ((chainMap R R (productMap f g)).f n).hom

/-- The degree-zero endpoint is ordinary, with no augmentation term. -/
def zero_endpoint_type : Prop := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w})
  (s : Simplex (productSpace X Y) 0),
  aw R X Y 0 (Finsupp.single s 1) ⟨(0,0),rfl⟩ =
    Finsupp.single (postSimplex (firstProjection X Y) 0 s) 1 ⊗ₜ[R]
      Finsupp.single (postSimplex (secondProjection X Y) 0 s) 1

def interval_continuous_type : Prop := ∀ {X : TopCat.{w}} {n : ℕ}
  (s : Simplex X n) (a k : ℕ) (h : a+k ≤ n),
  simplexEquiv X k (interval s a k h) =
    (simplexEquiv X n s).comp (SimplexCategory.toTop₀.map (intervalInclusion a k n h)).hom

def interval_weights_type : Prop := ∀ (a k n : ℕ) (h : a+k ≤ n)
  (x : Convexity.StdSimplex ℝ (Fin (k+1))),
  ((SimplexCategory.toTop₀.map (intervalInclusion a k n h)).hom x).weights =
    x.weights.mapDomain (fun j => (⟨a+j.val, by omega⟩ : Fin (n+1)))

def directSum_formula_type : Prop := ∀ (R : Type u) [CommRing R]
  (X Y : TopCat.{w}) (n : ℕ) (s : Simplex (productSpace X Y) n) (r : R),
  totalDirectSumEquiv R X Y n (aw R X Y n (Finsupp.single s r)) =
    ∑ i : Diagonal n, DirectSum.lof R (Diagonal n)
      (fun i => Summand R X Y i.val.1 i.val.2) i
      (r • awComponent R X Y n s i.val.1 i.val.2 i.property)

/-- Realization as an ordinary nonnegative chain complex and a chain map.
The isomorphisms display exactly the prescribed graded modules and differential. -/
def tensorComplex_realization_type : Prop := ∀ (R : Type u) [CommRing R]
  (X Y : TopCat.{w}),
  ∃ (K : ChainComplex (ModuleCat.{max u w} R) ℕ)
    (e : ∀ n, K.X n ≅ ModuleCat.of R (Total R X Y n)),
    (∀ n, (e (n+1)).inv ≫ K.d (n+1) n ≫ (e n).hom =
      ModuleCat.ofHom (totalBoundary R X Y n)) ∧
    (∀ n, K.d 0 n = 0) ∧
    ∃ F : complex R R (productSpace X Y) ⟶ K,
      ∀ n, F.f n ≫ (e n).hom = ModuleCat.ofHom (aw R X Y n)

def totalMap_boundary_type : Prop := ∀ (R : Type u) [CommRing R]
  {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
  (totalBoundary R X' Y' n).comp (totalMap R f g (n+1)) =
    (totalMap R f g n).comp (totalBoundary R X Y n)

def totalMap_id_type : Prop := ∀ (R : Type u) [CommRing R]
  (X Y : TopCat.{w}) (n : ℕ), totalMap R (𝟙 X) (𝟙 Y) n = LinearMap.id

def totalMap_comp_type : Prop := ∀ (R : Type u) [CommRing R]
  {X X' X'' Y Y' Y'' : TopCat.{w}}
  (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') (n : ℕ),
  totalMap R (f ≫ f') (g ≫ g') n = (totalMap R f' g' n).comp (totalMap R f g n)

end P202Specs.AlexanderWhitney
