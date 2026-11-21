import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.AlexanderWhitney
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct DirectSum
namespace P202.AlexanderWhitney
open P202Specs.SingularChains P202Specs.AlexanderWhitney
universe u w
variable (R : Type u) [CommRing R]

def totalDirectSumEquiv (X Y : TopCat.{w}) (n : ℕ) :
    Total R X Y n ≃ₗ[R] ⨁ i : Diagonal n, Summand R X Y i.val.1 i.val.2 :=
  P202Specs.AlexanderWhitney.totalDirectSumEquiv R X Y n

def alexanderWhitney (X Y : TopCat.{w}) (n : ℕ) :
    Chains R (productSpace X Y) n →ₗ[R] Total R X Y n := aw R X Y n

@[simp] theorem formula (X Y : TopCat.{w}) (n : ℕ)
    (s : Simplex (productSpace X Y) n) (r : R) (i : Diagonal n) :
    aw R X Y n (Finsupp.single s r) i = r • awComponent R X Y n s i.val.1 i.val.2 i.property := by
  simp only [aw, Finsupp.lsum_single]
  rfl

lemma interval_self {X : TopCat.{w}} {n : ℕ} (s : Simplex X n) :
    interval s 0 n (by omega) = s := by
  have h : intervalInclusion 0 n n (by omega) = 𝟙 _ := by ext j; simp [intervalInclusion]
  simp [interval, h]

lemma post_interval {X Y : TopCat.{w}} (f : X ⟶ Y) {n : ℕ}
    (s : Simplex X n) (a k : ℕ) (h : a+k ≤ n) :
    postSimplex f k (interval s a k h) = interval (postSimplex f n s) a k h := by
  exact ((TopCat.toSSet.map f).naturality_apply (intervalInclusion a k n h).op s).symm

lemma post_face {X Y : TopCat.{w}} (f : X ⟶ Y) {n : ℕ}
    (s : Simplex X (n+1)) (j : Fin (n+2)) :
    postSimplex f n (face j s) = face j (postSimplex f (n+1) s) := by
  exact ((TopCat.toSSet.map f).naturality_apply (SimplexCategory.δ j).op s).symm

lemma post_comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (s : Simplex X n) :
    postSimplex g n (postSimplex f n s) = postSimplex (f ≫ g) n s := by
  simp [postSimplex, Functor.map_comp]

lemma first_productMap {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') :
    productMap f g ≫ firstProjection X' Y' = firstProjection X Y ≫ f := rfl
lemma second_productMap {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') :
    productMap f g ≫ secondProjection X' Y' = secondProjection X Y ≫ g := rfl

theorem zero_endpoint (X Y : TopCat.{w}) (s : Simplex (productSpace X Y) 0) :
    aw R X Y 0 (Finsupp.single s 1) ⟨(0,0),rfl⟩ =
      Finsupp.single (postSimplex (firstProjection X Y) 0 s) 1 ⊗ₜ[R]
        Finsupp.single (postSimplex (secondProjection X Y) 0 s) 1 := by
  simp [formula, awComponent, interval_self]

theorem naturality {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (totalMap R f g n).comp (aw R X Y n) =
      (aw R X' Y' n).comp ((chainMap R R (productMap f g)).f n).hom := by
  apply Finsupp.lhom_ext
  intro s r
  funext i
  change TensorProduct.map (Finsupp.lmapDomain R R (postSimplex f i.val.1))
    (Finsupp.lmapDomain R R (postSimplex g i.val.2))
    (aw R X Y n (Finsupp.single s r) i) =
    aw R X' Y' n (Finsupp.mapDomain (postSimplex (productMap f g) n) (Finsupp.single s r)) i
  rw [formula, Finsupp.mapDomain_single, formula, map_smul]
  congr 1
  simp only [awComponent, TensorProduct.map_tmul, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  simp only [← post_interval, post_comp, first_productMap, second_productMap]

theorem totalBoundary_squared (X Y : TopCat.{w}) (n : ℕ) :
    (totalBoundary R X Y n).comp (totalBoundary R X Y (n+1)) = 0 :=
  P202Specs.AlexanderWhitney.totalBoundary_square R X Y n

/-! Ordered face calculations for the component proof. -/
lemma front_face_left (p q : ℕ) (j : Fin (p+1)) :
    intervalInclusion 0 p (p+q) (by omega) ≫
      SimplexCategory.δ (⟨j.val, by omega⟩ : Fin (p+q+2)) =
    SimplexCategory.δ j.castSucc ≫ intervalInclusion 0 (p+1) (p+q+1) (by omega) := by
  ext k
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    ]
  change (Fin.succAbove _ ⟨0+k.val, _⟩).val = 0 + (j.castSucc.succAbove k).val
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Nat.zero_add]
  split <;> simp_all

lemma back_face_left (p q : ℕ) (j : Fin (p+1)) :
    intervalInclusion p q (p+q) (by omega) ≫
      SimplexCategory.δ (⟨j.val, by omega⟩ : Fin (p+q+2)) =
    intervalInclusion (p+1) q (p+q+1) (by omega) := by
  ext k
  change (Fin.succAbove _ ⟨p+k.val, _⟩).val = p+1+k.val
  rw [Fin.succAbove_of_le_castSucc _ _ (by change j.val ≤ p+k.val; omega)]
  dsimp
  omega

lemma front_face_right (p q : ℕ) (j : Fin (q+1)) :
    intervalInclusion 0 p (p+q) (by omega) ≫
      SimplexCategory.δ (⟨p+1+j.val, by omega⟩ : Fin (p+q+2)) =
    intervalInclusion 0 p (p+q+1) (by omega) := by
  ext k
  change (Fin.succAbove _ ⟨0+k.val, _⟩).val = 0+k.val
  rw [Fin.succAbove_of_castSucc_lt _ _ (by change 0+k.val < p+1+j.val; have := k.isLt; dsimp at *; omega)]
  rfl

lemma back_face_right (p q : ℕ) (j : Fin (q+1)) :
    intervalInclusion p q (p+q) (by omega) ≫
      SimplexCategory.δ (⟨p+1+j.val, by omega⟩ : Fin (p+q+2)) =
    SimplexCategory.δ j.succ ≫ intervalInclusion p (q+1) (p+q+1) (by omega) := by
  ext k
  change (Fin.succAbove _ ⟨p+k.val, _⟩).val = p + (j.succ.succAbove k).val
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  split <;> split <;> simp_all <;> omega

lemma front_last (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p+1)) ≫
      intervalInclusion 0 (p+1) (p+q+1) (by omega) =
    intervalInclusion 0 p (p+q+1) (by omega) := by
  ext k
  change 0 + ((Fin.last (p+1)).succAbove k).val = 0+k.val
  rw [Fin.succAbove_of_castSucc_lt _ _ (by change k.val < p+1; have := k.isLt; dsimp at *; omega)]
  rfl

lemma back_zero (p q : ℕ) :
    SimplexCategory.δ (0 : Fin (q+2)) ≫
      intervalInclusion p (q+1) (p+q+1) (by omega) =
    intervalInclusion (p+1) q (p+q+1) (by omega) := by
  ext k
  change p + ((0 : Fin (q+2)).succAbove k).val = p+1+k.val
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.zero_le _)]
  dsimp
  omega

lemma restrict_comp {X : TopCat.{w}} {a b c : ℕ}
    (α : ⦋a⦌ ⟶ ⦋b⦌) (β : ⦋b⦌ ⟶ ⦋c⦌) (s : Simplex X c) :
    (TopCat.toSSet.obj X).map α.op ((TopCat.toSSet.obj X).map β.op s) =
      (TopCat.toSSet.obj X).map (α ≫ β).op s := by
  simp only [op_comp, Functor.map_comp, types_comp_apply]

lemma interval_face_front_left {X : TopCat.{w}} (p q : ℕ)
    (s : Simplex X (p+q+1)) (j : Fin (p+1)) :
    interval (face (⟨j.val, by omega⟩ : Fin (p+q+2)) s) 0 p (by omega) =
      face j.castSucc (interval s 0 (p+1) (by omega)) := by
  simp only [interval, face, SimplicialObject.δ, restrict_comp, front_face_left]

lemma interval_face_back_left {X : TopCat.{w}} (p q : ℕ)
    (s : Simplex X (p+q+1)) (j : Fin (p+1)) :
    interval (face (⟨j.val, by omega⟩ : Fin (p+q+2)) s) p q (by omega) =
      interval s (p+1) q (by omega) := by
  simp only [interval, face, SimplicialObject.δ, restrict_comp, back_face_left]

lemma interval_face_front_right {X : TopCat.{w}} (p q : ℕ)
    (s : Simplex X (p+q+1)) (j : Fin (q+1)) :
    interval (face (⟨p+1+j.val, by omega⟩ : Fin (p+q+2)) s) 0 p (by omega) =
      interval s 0 p (by omega) := by
  simp only [interval, face, SimplicialObject.δ, restrict_comp, front_face_right]

lemma interval_face_back_right {X : TopCat.{w}} (p q : ℕ)
    (s : Simplex X (p+q+1)) (j : Fin (q+1)) :
    interval (face (⟨p+1+j.val, by omega⟩ : Fin (p+q+2)) s) p q (by omega) =
      face j.succ (interval s p (q+1) (by omega)) := by
  simp only [interval, face, SimplicialObject.δ, restrict_comp, back_face_right]

lemma face_interval_front_last {X : TopCat.{w}} (p q : ℕ) (s : Simplex X (p+q+1)) :
    face (Fin.last (p+1)) (interval s 0 (p+1) (by omega)) =
      interval s 0 p (by omega) := by
  simp only [interval, face, SimplicialObject.δ, restrict_comp, front_last]

lemma face_interval_back_zero {X : TopCat.{w}} (p q : ℕ) (s : Simplex X (p+q+1)) :
    face (0 : Fin (q+2)) (interval s p (q+1) (by omega)) =
      interval s (p+1) q (by omega) := by
  simp only [interval, face, SimplicialObject.δ, restrict_comp, back_zero]

lemma leftBoundary_basis (X Y : TopCat.{w}) (p q : ℕ)
    (x : Simplex X (p+1)) (y : Simplex Y q) :
    leftBoundary R X Y p q (Finsupp.single x 1 ⊗ₜ[R] Finsupp.single y 1) =
      ∑ j : Fin (p+2), (-1 : ℤ)^j.val •
        (Finsupp.single (face j x) 1 ⊗ₜ[R] Finsupp.single y 1) := by
  change boundary R R X p (Finsupp.single x 1) ⊗ₜ[R] Finsupp.single y 1 = _
  rw [P202.SingularChains.boundary_single]
  simp only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul']

lemma rightBoundary_basis (X Y : TopCat.{w}) (p q : ℕ)
    (x : Simplex X p) (y : Simplex Y (q+1)) :
    rightBoundary R X Y p q (Finsupp.single x 1 ⊗ₜ[R] Finsupp.single y 1) =
      ∑ j : Fin (q+2), (-1 : ℤ)^j.val •
        (Finsupp.single x 1 ⊗ₜ[R] Finsupp.single (face j y) 1) := by
  change Finsupp.single x 1 ⊗ₜ[R] boundary R R Y q (Finsupp.single y 1) = _
  rw [P202.SingularChains.boundary_single]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul]

lemma sum_split {A : Type*} [AddCommMonoid A] (p q : ℕ) (f : Fin (p+q+2) → A) :
    ∑ k, f k =
      (∑ j : Fin (p+1), f ⟨j.val, by omega⟩) +
      (∑ j : Fin (q+1), f ⟨p+1+j.val, by omega⟩) := by
  have h : p+q+2 = (p+1)+(q+1) := by omega
  let g : Fin ((p+1)+(q+1)) → A := fun k => f ⟨k.val, by omega⟩
  have he : ∑ k, f k = ∑ k, g k := by
    apply Fintype.sum_equiv (finCongr h)
    intro k
    rfl
  rw [he, Fin.sum_univ_add]
  rfl

lemma component_identity (X Y : TopCat.{w}) (p q : ℕ)
    (x : Simplex X (p+q+1)) (y : Simplex Y (p+q+1)) :
    leftBoundary R X Y p q
      (Finsupp.single (interval x 0 (p+1) (by omega)) 1 ⊗ₜ[R]
       Finsupp.single (interval y (p+1) q (by omega)) 1) +
    (-1 : ℤ)^p • rightBoundary R X Y p q
      (Finsupp.single (interval x 0 p (by omega)) 1 ⊗ₜ[R]
       Finsupp.single (interval y p (q+1) (by omega)) 1) =
    ∑ k : Fin (p+q+2), (-1 : ℤ)^k.val •
      (Finsupp.single (interval (face k x) 0 p (by omega)) 1 ⊗ₜ[R]
       Finsupp.single (interval (face k y) p q (by omega)) 1) := by
  rw [leftBoundary_basis, rightBoundary_basis]
  rw [Fin.sum_univ_castSucc (n := p+1), Fin.sum_univ_succ (n := q+1)]
  rw [sum_split p q]
  simp only [interval_face_front_left, interval_face_back_left,
    interval_face_front_right, interval_face_back_right,
    face_interval_front_last, face_interval_back_zero,
    Fin.val_castSucc, Fin.val_last, Fin.val_zero, Fin.val_succ,
    pow_zero, one_smul, pow_add, mul_smul, smul_add, Finset.smul_sum,
    neg_one_zsmul, smul_neg, pow_succ]
  abel

theorem chain_identity (X Y : TopCat.{w}) (n : ℕ) :
    (totalBoundary R X Y n).comp (aw R X Y (n+1)) =
      (aw R X Y n).comp (boundary R R (productSpace X Y) n) := by
  apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R (productSpace X Y) (n+1))).ext
  intro s
  change totalBoundary R X Y n (aw R X Y (n+1) (Finsupp.single s 1)) =
    aw R X Y n (boundary R R (productSpace X Y) n (Finsupp.single s 1))
  rw [P202.SingularChains.boundary_single]
  simp only [map_sum, map_zsmul]
  funext i
  rcases i with ⟨⟨p,q⟩,h⟩
  dsimp at h
  subst n
  change leftBoundary R X Y p q
    (aw R X Y (p+q+1) (Finsupp.single s 1) ⟨(p+1,q), by omega⟩) +
    (-1 : ℤ)^p • rightBoundary R X Y p q
    (aw R X Y (p+q+1) (Finsupp.single s 1) ⟨(p,q+1), by omega⟩) = _
  simp only [Finset.sum_apply, Pi.smul_apply, formula, one_smul, awComponent, post_face]
  exact component_identity R X Y p q
    (postSimplex (firstProjection X Y) _ s) (postSimplex (secondProjection X Y) _ s)

/-- The actual affine restrictions on the ordered real simplex. -/
theorem interval_continuous {X : TopCat.{w}} {n : ℕ}
    (s : Simplex X n) (a k : ℕ) (h : a+k ≤ n) :
    simplexEquiv X k (interval s a k h) =
      (simplexEquiv X n s).comp (SimplexCategory.toTop₀.map (intervalInclusion a k n h)).hom := by
  ext x
  rfl

theorem interval_weights (a k n : ℕ) (h : a+k ≤ n)
    (x : Convexity.StdSimplex ℝ (Fin (k+1))) :
    ((SimplexCategory.toTop₀.map (intervalInclusion a k n h)).hom x).weights =
      x.weights.mapDomain (fun j => (⟨a+j.val, by omega⟩ : Fin (n+1))) := rfl

theorem directSum_formula (X Y : TopCat.{w}) (n : ℕ)
    (s : Simplex (productSpace X Y) n) (r : R) :
    P202Specs.AlexanderWhitney.totalDirectSumEquiv R X Y n
      (aw R X Y n (Finsupp.single s r)) =
    ∑ i : Diagonal n, DirectSum.lof R (Diagonal n)
      (fun i => Summand R X Y i.val.1 i.val.2) i
      (r • awComponent R X Y n s i.val.1 i.val.2 i.property) := by
  classical
  apply (DirectSum.linearEquivFunOnFintype R (Diagonal n)
    (fun i => Summand R X Y i.val.1 i.val.2)).injective
  simp only [P202Specs.AlexanderWhitney.totalDirectSumEquiv,
    LinearEquiv.apply_symm_apply, map_sum, DirectSum.linearEquivFunOnFintype_lof]
  funext i
  simp [Finset.sum_apply, formula]

/-- The ordinary total tensor complex, in the finite diagonal coordinates. -/
def tensorComplex (X Y : TopCat.{w}) : ChainComplex (ModuleCat.{max u w} R) ℕ :=
  P202Specs.AlexanderWhitney.tensorComplex R X Y

/-- The AW family packaged as an actual chain map from the shared singular complex. -/
def awChainMap (X Y : TopCat.{w}) :
    complex R R (productSpace X Y) ⟶ tensorComplex R X Y :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (aw R X Y n)) (by
    intro n
    simp only [tensorComplex, P202Specs.AlexanderWhitney.tensorComplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    exact chain_identity R X Y n)

theorem tensorComplex_realization (X Y : TopCat.{w}) :
    ∃ (K : ChainComplex (ModuleCat.{max u w} R) ℕ)
      (e : ∀ n, K.X n ≅ ModuleCat.of R (Total R X Y n)),
      (∀ n, (e (n+1)).inv ≫ K.d (n+1) n ≫ (e n).hom =
        ModuleCat.ofHom (totalBoundary R X Y n)) ∧
      (∀ n, K.d 0 n = 0) ∧
      ∃ F : complex R R (productSpace X Y) ⟶ K,
        ∀ n, F.f n ≫ (e n).hom = ModuleCat.ofHom (aw R X Y n) := by
  refine ⟨tensorComplex R X Y, fun n => Iso.refl _, ?_, ?_, awChainMap R X Y, ?_⟩
  · intro n
    simp [tensorComplex, P202Specs.AlexanderWhitney.tensorComplex]
  · intro n
    apply HomologicalComplex.shape
    simp [ComplexShape.down_Rel]
  · intro n
    simp [awChainMap]

lemma leftBoundary_natural {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ) (z : Summand R X Y (p+1) q) :
    leftBoundary R X' Y' p q
      (TensorProduct.map ((chainMap R R f).f (p+1)).hom ((chainMap R R g).f q).hom z) =
    TensorProduct.map ((chainMap R R f).f p).hom ((chainMap R R g).f q).hom
      (leftBoundary R X Y p q z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b =>
    change boundary R R X' p (((chainMap R R f).f (p+1)).hom a) ⊗ₜ[R]
      (((chainMap R R g).f q).hom b) =
      (((chainMap R R f).f p).hom (boundary R R X p a)) ⊗ₜ[R]
      (((chainMap R R g).f q).hom b)
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((chainMap R R f).comm (p+1) p)) a
    exact congrArg (fun c => c ⊗ₜ[R] (((chainMap R R g).f q).hom b)) h

lemma rightBoundary_natural {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') (p q : ℕ) (z : Summand R X Y p (q+1)) :
    rightBoundary R X' Y' p q
      (TensorProduct.map ((chainMap R R f).f p).hom ((chainMap R R g).f (q+1)).hom z) =
    TensorProduct.map ((chainMap R R f).f p).hom ((chainMap R R g).f q).hom
      (rightBoundary R X Y p q z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [map_add, hz, hz']
  | tmul a b =>
    change (((chainMap R R f).f p).hom a) ⊗ₜ[R]
      (boundary R R Y' q (((chainMap R R g).f (q+1)).hom b)) =
      (((chainMap R R f).f p).hom a) ⊗ₜ[R]
      (((chainMap R R g).f q).hom (boundary R R Y q b))
    have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      ((chainMap R R g).comm (q+1) q)) b
    exact congrArg (fun c => (((chainMap R R f).f p).hom a) ⊗ₜ[R] c) h

theorem totalMap_boundary {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (totalBoundary R X' Y' n).comp (totalMap R f g (n+1)) =
      (totalMap R f g n).comp (totalBoundary R X Y n) := by
  apply LinearMap.ext
  intro z
  funext i
  simp only [LinearMap.comp_apply, totalMap, totalBoundary, LinearMap.coe_mk,
    AddHom.coe_mk, map_add, map_zsmul, leftBoundary_natural, rightBoundary_natural]

theorem totalMap_id (X Y : TopCat.{w}) (n : ℕ) :
    totalMap R (𝟙 X) (𝟙 Y) n = LinearMap.id := by
  apply LinearMap.ext
  intro z
  funext i
  simp [totalMap]

theorem totalMap_comp {X X' X'' Y Y' Y'' : TopCat.{w}}
    (f : X ⟶ X') (f' : X' ⟶ X'') (g : Y ⟶ Y') (g' : Y' ⟶ Y'') (n : ℕ) :
    totalMap R (f ≫ f') (g ≫ g') n = (totalMap R f' g' n).comp (totalMap R f g n) := by
  apply LinearMap.ext
  intro z
  funext i
  simp only [totalMap, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    P202.SingularChains.chainMap_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp]
  exact (LinearMap.congr_fun (TensorProduct.map_comp
    ((chainMap R R f').f i.val.1).hom ((chainMap R R g').f i.val.2).hom
    ((chainMap R R f).f i.val.1).hom ((chainMap R R g).f i.val.2).hom) (z i))

/-- Continuous factor maps induce chain maps on the ordinary tensor total complex. -/
def tensorChainMap {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') :
    tensorComplex R X Y ⟶ tensorComplex R X' Y' :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (totalMap R f g n)) (by
    intro n
    simp only [tensorComplex, P202Specs.AlexanderWhitney.tensorComplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    exact totalMap_boundary R f g n)

/-- Naturality also holds for the packaged chain maps. -/
theorem awChainMap_natural {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') :
    chainMap R R (productMap f g) ≫ awChainMap R X' Y' =
      awChainMap R X Y ≫ tensorChainMap R f g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact (naturality R f g n).symm

end P202.AlexanderWhitney
