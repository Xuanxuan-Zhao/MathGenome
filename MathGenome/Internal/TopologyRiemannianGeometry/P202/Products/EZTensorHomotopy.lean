import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.EZTensorHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.AlexanderWhitney
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleChains
import Mathlib.AlgebraicTopology.ExtraDegeneracy

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct
namespace P202.EZTensorHomotopy
open P202Specs.SingularChains P202Specs.AlexanderWhitney P202Specs.ShuffleModel
universe u w vE vF vH vK
variable (R : Type u) [CommRing R]

/-- Exposed module types prevent categorical module-instance wrappers from
obscuring tensor-product rewrites. Both are definitionally the upstream maps. -/
def differential (X : TopCat.{w}) (n : ℕ) :
    Chains R X (n+1) →ₗ[R] Chains R X n := P202Specs.SingularChains.boundary R R X n

def push {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ) :
    Chains R X n →ₗ[R] Chains R Y n := ((chainMap R R f).f n).hom

/-- The chain-map difference whose natural null-homotopy is required. -/
def defect (X Y : TopCat.{w}) (n : ℕ) : Total R X Y n →ₗ[R] Total R X Y n :=
  (aw R X Y n).comp (shuffle R X Y n) - LinearMap.id

lemma defect_natural {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (totalMap R f g n).comp (defect R X Y n) =
      (defect R X' Y' n).comp (totalMap R f g n) := by
  simp only [defect, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id,
    LinearMap.id_comp, ← LinearMap.comp_assoc]
  rw [P202.AlexanderWhitney.naturality, LinearMap.comp_assoc,
    P202.ShuffleChains.naturality]
  rw [LinearMap.comp_assoc]

lemma defect_boundary (X Y : TopCat.{w}) (n : ℕ) :
    (totalBoundary R X Y n).comp (defect R X Y (n+1)) =
      (defect R X Y n).comp (totalBoundary R X Y n) := by
  simp only [defect, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id,
    LinearMap.id_comp, ← LinearMap.comp_assoc]
  rw [P202.AlexanderWhitney.chain_identity, LinearMap.comp_assoc,
    P202.ShuffleChains.chain_identity]
  rw [LinearMap.comp_assoc]

lemma diagonal_zero (i : Diagonal 0) : i = ⟨(0,0), rfl⟩ := by
  rcases i with ⟨⟨p,q⟩,h⟩
  have hp : p=0 := by omega
  have hq : q=0 := by omega
  subst p q
  rfl

lemma shuffle_zero (X Y : TopCat.{w}) (z : Total R X Y 0) :
    shuffle R X Y 0 z = shuffleComponent R X Y 0 0 (z ⟨(0,0),rfl⟩) := by
  classical
  letI : Unique (Diagonal 0) := { default := ⟨(0,0),rfl⟩, uniq := diagonal_zero }
  simp only [shuffle, LinearMap.sum_apply, Finset.univ_unique, Finset.sum_singleton]
  rw [diagonal_zero default]
  rfl

lemma shuffle_zero_projections {X Y : TopCat.{w}}
    (σ : Simplex X 0) (τ : Simplex Y 0) :
    postSimplex (firstProjection X Y) 0 (shuffleSimplex (zeroLeft 0) σ τ) = σ ∧
    postSimplex (secondProjection X Y) 0 (shuffleSimplex (zeroLeft 0) σ τ) = τ := by
  have hh : (zeroLeft 0).horizontal.toFun = id := by
    funext i
    apply Fin.ext
    have hi := i.isLt
    have hj := ((zeroLeft 0).horizontal i).isLt
    omega
  have hv : (zeroLeft 0).vertical.toFun = id := by
    funext i
    apply Fin.ext
    have hi := i.isLt
    have hj := ((zeroLeft 0).vertical i).isLt
    omega
  constructor
  · apply (simplexEquiv X 0).injective
    ext z
    simp only [postSimplex, P202.SingularChains.simplexEquiv_postcomp]
    change (simplexEquiv (productSpace X Y) 0 (shuffleSimplex (zeroLeft 0) σ τ) z).1 = _
    erw [P202.ShuffleChains.simplex_formula]
    change simplexEquiv X 0 σ (z.map (zeroLeft 0).horizontal.toFun) = _
    rw [hh, Convexity.StdSimplex.map_id]
  · apply (simplexEquiv Y 0).injective
    ext z
    simp only [postSimplex, P202.SingularChains.simplexEquiv_postcomp]
    change (simplexEquiv (productSpace X Y) 0 (shuffleSimplex (zeroLeft 0) σ τ) z).2 = _
    erw [P202.ShuffleChains.simplex_formula]
    change simplexEquiv Y 0 τ (z.map (zeroLeft 0).vertical.toFun) = _
    rw [hv, Convexity.StdSimplex.map_id]

lemma aw_shuffle_zero_component (X Y : TopCat.{w}) :
    ((LinearMap.proj (⟨(0,0),rfl⟩ : Diagonal 0)).comp (aw R X Y 0)).comp
      (shuffleComponent R X Y 0 0) = LinearMap.id := by
  apply ((Finsupp.basisSingleOne : Module.Basis (Simplex X 0) R (Chains R X 0)).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (Simplex Y 0) R (Chains R Y 0))).ext
  intro ⟨σ,τ⟩
  simp only [Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne]
  change aw R X Y 0 (shuffleComponent R X Y 0 0
    (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1)) ⟨(0,0),rfl⟩ = _
  rw [P202.ShuffleChains.component_zero_left, P202.AlexanderWhitney.zero_endpoint]
  rw [(shuffle_zero_projections σ τ).1, (shuffle_zero_projections σ τ).2]
  rfl

lemma defect_zero (X Y : TopCat.{w}) : defect R X Y 0 = 0 := by
  apply LinearMap.ext
  intro z
  funext i
  rw [diagonal_zero i]
  change aw R X Y 0 (shuffle R X Y 0 z) ⟨(0,0),rfl⟩ - z ⟨(0,0),rfl⟩ = 0
  rw [shuffle_zero]
  have h := LinearMap.congr_fun (aw_shuffle_zero_component R X Y) (z ⟨(0,0),rfl⟩)
  exact sub_eq_zero.mpr h

/-! Finite ordered vertex models. Their contraction uses only affine vertex
maps, so it can be realized inside smooth singular chains as well. -/
namespace VertexModel

abbrev Simplex (p n : ℕ) := ⦋n⦌ ⟶ ⦋p⦌
abbrev Chains (p n : ℕ) := Simplex p n →₀ R

def face {p n : ℕ} (i : Fin (n+2)) (s : Simplex p (n+1)) : Simplex p n :=
  SimplexCategory.δ i ≫ s

def boundary (p n : ℕ) : Chains R p (n+1) →ₗ[R] Chains R p n :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.lmapDomain R R (face i)

def cone (p n : ℕ) : Chains R p n →ₗ[R] Chains R p (n+1) :=
  Finsupp.lmapDomain R R SSet.Augmented.StandardSimplex.shift

def baseVertex (p : ℕ) : Simplex p 0 :=
  SimplexCategory.Hom.mk (OrderHom.const _ 0)

def projection (p : ℕ) : Chains R p 0 →ₗ[R] Chains R p 0 :=
  (Finsupp.lsingle (baseVertex p)).comp (sumCoefficients R R (Simplex p 0))

lemma face_cone_zero {p n : ℕ} (s : Simplex p n) :
    face (0 : Fin (n+2)) (SSet.Augmented.StandardSimplex.shift s) = s := by
  ext j
  simp [face, SimplexCategory.δ, SSet.Augmented.StandardSimplex.shift,
    SSet.Augmented.StandardSimplex.shiftFun]

lemma face_cone_succ {p n : ℕ} (s : Simplex p (n+1)) (i : Fin (n+2)) :
    face i.succ (SSet.Augmented.StandardSimplex.shift s) =
      SSet.Augmented.StandardSimplex.shift (face i s) := by
  ext j
  cases j using Fin.cases <;>
    simp [face, SimplexCategory.δ, SSet.Augmented.StandardSimplex.shift,
      SSet.Augmented.StandardSimplex.shiftFun]

lemma face_cone_one {p : ℕ} (s : Simplex p 0) :
    face (1 : Fin 2) (SSet.Augmented.StandardSimplex.shift s) = baseVertex p := by
  ext j
  fin_cases j
  rfl

@[simp] lemma boundary_single (p n : ℕ) (s : Simplex p (n+1)) (r : R) :
    boundary R p n (Finsupp.single s r) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (face i s) r := by
  simp [boundary, LinearMap.sum_apply, Finsupp.lmapDomain_apply]

@[simp] lemma cone_single (p n : ℕ) (s : Simplex p n) (r : R) :
    cone R p n (Finsupp.single s r) =
      Finsupp.single (SSet.Augmented.StandardSimplex.shift s) r := by
  exact Finsupp.mapDomain_single

@[simp] lemma projection_single (p : ℕ) (s : Simplex p 0) (r : R) :
    projection R p (Finsupp.single s r) = Finsupp.single (baseVertex p) r := by
  simp [projection, sumCoefficients]

lemma contraction_zero (p : ℕ) :
    (boundary R p 0).comp (cone R p 0) = LinearMap.id - projection R p := by
  apply Finsupp.lhom_ext
  intro s r
  simp only [LinearMap.comp_apply, cone_single, boundary_single, Nat.reduceAdd, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_zsmul,
    face_cone_zero, face_cone_one, LinearMap.sub_apply, LinearMap.id_apply,
    projection_single, sub_eq_add_neg]

lemma contraction_succ (p n : ℕ) :
    (boundary R p (n+1)).comp (cone R p (n+1)) +
      (cone R p n).comp (boundary R p n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s r
  simp only [LinearMap.add_apply, LinearMap.comp_apply, cone_single, boundary_single]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, face_cone_zero,
    Fin.val_succ, pow_succ, mul_neg_one, neg_smul, face_cone_succ,
    map_sum, map_zsmul, cone_single, Finset.sum_neg_distrib, LinearMap.id_apply]
  abel

/-- Realization of an ordered vertex map as an affine pullback of an input simplex. -/
def realizeSimplex {X : TopCat.{w}} {p : ℕ} (σ : P202Specs.SingularChains.Simplex X p)
    {n : ℕ} (s : Simplex p n) : P202Specs.SingularChains.Simplex X n :=
  (TopCat.toSSet.obj X).map s.op σ

def realize {X : TopCat.{w}} {p : ℕ} (σ : P202Specs.SingularChains.Simplex X p) (n : ℕ) :
    Chains R p n →ₗ[R] P202Specs.SingularChains.Chains R X n :=
  Finsupp.lmapDomain R R (realizeSimplex σ)

@[simp] lemma realize_single {X : TopCat.{w}} {p n : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (s : Simplex p n) (r : R) :
    realize R σ n (Finsupp.single s r) = Finsupp.single (realizeSimplex σ s) r :=
  Finsupp.mapDomain_single

lemma realize_face {X : TopCat.{w}} {p n : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (s : Simplex p (n+1)) (i : Fin (n+2)) :
    realizeSimplex σ (face i s) = P202Specs.SingularChains.face i (realizeSimplex σ s) := by
  simp [realizeSimplex, face, P202Specs.SingularChains.face, SimplicialObject.δ,
    Functor.map_comp]

lemma realize_boundary {X : TopCat.{w}} {p : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (n : ℕ) :
    (differential R X n).comp (realize R σ (n+1)) =
      (realize R σ n).comp (boundary R p n) := by
  apply Finsupp.lhom_ext
  intro s r
  change P202Specs.SingularChains.boundary R R X n (realize R σ (n+1) (Finsupp.single s r)) =
    realize R σ n (boundary R p n (Finsupp.single s r))
  rw [realize_single, P202.SingularChains.boundary_single, boundary_single]
  simp only [map_sum, map_zsmul, realize_single, realize_face]

lemma realize_natural {X Y : TopCat.{w}} (f : X ⟶ Y) {p : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (n : ℕ) :
    (push R f n).comp (realize R σ n) =
      realize R (postSimplex f p σ) n := by
  apply Finsupp.lhom_ext
  intro s r
  change ((chainMap R R f).f n).hom (realize R σ n (Finsupp.single s r)) =
    realize R (postSimplex f p σ) n (Finsupp.single s r)
  rw [realize_single, realize_single, P202.SingularChains.chainMap_single]
  exact congrArg (fun t => Finsupp.single t r)
    ((TopCat.toSSet.map f).naturality_apply s.op σ).symm

lemma realize_continuous {X : TopCat.{w}} {p n : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (s : Simplex p n) :
    simplexEquiv X n (realizeSimplex σ s) =
      (simplexEquiv X p σ).comp (SimplexCategory.toTop₀.map s).hom := by
  rfl

lemma realize_smooth {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : H → E) {X : TopCat.{w}} [ChartedSpace H X]
    {p n : ℕ} (σ : P202Specs.SingularChains.Simplex X p) (hσ : SmoothSimplex I X σ)
    (s : Simplex p n) : SmoothSimplex I X (realizeSimplex σ s) := by
  unfold SmoothSimplex
  rw [realize_continuous]
  exact P202.ShuffleModel.charts_pullback I _ hσ s.toOrderHom

lemma realize_mem_smoothChains {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : H → E) {X : TopCat.{w}} [ChartedSpace H X]
    {p n : ℕ} (σ : P202Specs.SingularChains.Simplex X p) (hσ : SmoothSimplex I X σ)
    (c : Chains R p n) : realize R σ n c ∈ smoothChains R I X n := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using (Submodule.add_mem _ ha hb)
  | single s r =>
    rw [realize_single]
    exact Finsupp.single_mem_supported _ _ (realize_smooth I σ hσ s)

lemma projection_boundary (p : ℕ) :
    (projection R p).comp (boundary R p 0) = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  change projection R p (boundary R p 0 (Finsupp.single s r)) = 0
  rw [boundary_single]
  simp only [Nat.reduceAdd, Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_one_zsmul, map_add, map_neg, projection_single,
    add_neg_cancel]

/-- Linear realization into the actual supported smooth-chain submodule. -/
def smoothRealize {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : H → E) {X : TopCat.{w}} [ChartedSpace H X]
    {p : ℕ} (σ : P202Specs.SingularChains.Simplex X p) (hσ : SmoothSimplex I X σ)
    (n : ℕ) : Chains R p n →ₗ[R] smoothChains R I X n :=
  (realize R σ n).codRestrict _ (realize_mem_smoothChains R I σ hσ)

lemma smoothRealize_inclusion {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : H → E) {X : TopCat.{w}} [ChartedSpace H X]
    {p : ℕ} (σ : P202Specs.SingularChains.Simplex X p) (hσ : SmoothSimplex I X σ)
    (n : ℕ) :
    (smoothChains R I X n).subtype.comp (smoothRealize R I σ hσ n) = realize R σ n := rfl

/-- The topological universal simplex, lifted to the same space universe. -/
def space (p : ℕ) : TopCat.{w} := TopCat.of (ULift.{w} (StdSimplex p))

def universal (p : ℕ) : P202Specs.SingularChains.Simplex (space.{w} p) p :=
  (simplexEquiv _ p).symm ⟨ULift.up, continuous_uliftUp⟩

lemma realize_universal_apply {p n : ℕ} (s : Simplex p n) (z : StdSimplex n) :
    simplexEquiv (space.{w} p) n (realizeSimplex (universal p) s) z =
      ULift.up (z.map s.toOrderHom) := by
  rw [realize_continuous]
  simp only [universal, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  rfl

lemma realize_universal_injective (p n : ℕ) :
    Function.Injective (realizeSimplex (universal.{w} p) : Simplex p n → _) := by
  intro s t h
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro j
  have hv := congrArg
    (fun a => (simplexEquiv (space.{w} p) n a (Convexity.StdSimplex.single j)).down) h
  simp only [realize_universal_apply, Convexity.StdSimplex.map_single] at hv
  exact Convexity.StdSimplex.single_injective hv

/-- Restrict a universal singular-chain coefficient function to the embedded
affine monotone vertex simplices. It is a linear left inverse to realization. -/
def decode (p n : ℕ) : P202Specs.SingularChains.Chains R (space.{w} p) n →ₗ[R] Chains R p n :=
  Finsupp.lcomapDomain (realizeSimplex (universal p)) (realize_universal_injective p n)

lemma decode_realize (p n : ℕ) :
    (decode.{u,w} R p n).comp (realize R (universal p) n) = LinearMap.id := by
  apply LinearMap.ext
  exact Finsupp.leftInverse_lcomapDomain_mapDomain (R := R) (M := R) _ (realize_universal_injective p n)

/-! The ordinary tensor of the two finite affine vertex models. -/
namespace TensorModel

abbrev Total (p q n : ℕ) :=
  (i : Diagonal n) → Chains R p i.val.1 ⊗[R] Chains R q i.val.2

def boundary (p q n : ℕ) : Total R p q (n+1) →ₗ[R] Total R p q n where
  toFun z i :=
    TensorProduct.map (VertexModel.boundary R p i.val.1) LinearMap.id
      (z ⟨(i.val.1+1,i.val.2), by have := i.property; omega⟩) +
    (-1 : ℤ)^i.val.1 • TensorProduct.map LinearMap.id (VertexModel.boundary R q i.val.2)
      (z ⟨(i.val.1,i.val.2+1), by have := i.property; omega⟩)
  map_add' z z' := by ext i; simp only [Pi.add_apply, map_add, smul_add]; abel
  map_smul' r z := by
    ext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add]
    rw [smul_comm r]

/-- Prepend the base vertex in the first factor, increasing its degree. -/
def coneLeft (p q n : ℕ) : Total R p q n →ₗ[R] Total R p q (n+1) where
  toFun z i := by
    rcases i with ⟨⟨a,b⟩,h⟩
    cases a with
    | zero => exact 0
    | succ a =>
      exact TensorProduct.map (cone R p a) LinearMap.id
        (z ⟨(a,b), by dsimp at h; omega⟩)
  map_add' z z' := by
    funext ⟨⟨a,b⟩,h⟩
    cases a <;> simp [map_add]
  map_smul' r z := by
    funext ⟨⟨a,b⟩,h⟩
    cases a <;> simp [map_smul]

/-- The second part of the tensor contraction: P_C ⊗ h_D. The projection
P_C is zero in positive degree, so its Koszul sign here is always +1. -/
def coneRight (p q n : ℕ) : Total R p q n →ₗ[R] Total R p q (n+1) where
  toFun z i := by
    rcases i with ⟨⟨a,b⟩,h⟩
    cases a with
    | succ a => exact 0
    | zero =>
      cases b with
      | zero => exact 0
      | succ b =>
        exact TensorProduct.map (projection R p) (cone R q b)
          (z ⟨(0,b), by dsimp at h; omega⟩)
  map_add' z z' := by
    funext ⟨⟨a,b⟩,h⟩
    cases a with
    | succ a => exact (add_zero _).symm
    | zero => cases b <;> simp_all [map_add]
  map_smul' r z := by
    funext ⟨⟨a,b⟩,h⟩
    cases a with
    | succ a => exact (smul_zero r).symm
    | zero => cases b <;> simp_all [map_smul]

def cone (p q n : ℕ) : Total R p q n →ₗ[R] Total R p q (n+1) :=
  coneLeft R p q n + coneRight R p q n

@[simp] lemma coneLeft_zero (p q n b : ℕ) (h : 0+b=n+1) (z : Total R p q n) :
    coneLeft R p q n z ⟨(0,b),h⟩ = 0 := rfl

@[simp] lemma coneLeft_succ (p q n a b : ℕ) (h : (a+1)+b=n+1)
    (z : Total R p q n) :
    coneLeft R p q n z ⟨(a+1,b),h⟩ =
      TensorProduct.map (VertexModel.cone R p a) LinearMap.id
        (z ⟨(a,b),by omega⟩) := rfl

@[simp] lemma coneRight_succ (p q n a b : ℕ) (h : (a+1)+b=n+1)
    (z : Total R p q n) : coneRight R p q n z ⟨(a+1,b),h⟩ = 0 := rfl

@[simp] lemma coneRight_zero (p q n b : ℕ) (h : 0+(b+1)=n+1)
    (z : Total R p q n) :
    coneRight R p q n z ⟨(0,b+1),h⟩ =
      TensorProduct.map (projection R p) (VertexModel.cone R q b)
        (z ⟨(0,b),by omega⟩) := rfl

@[simp] lemma boundary_apply (p q n : ℕ) (z : Total R p q (n+1)) (i : Diagonal n) :
    boundary R p q n z i =
    TensorProduct.map (VertexModel.boundary R p i.val.1) LinearMap.id
      (z ⟨(i.val.1+1,i.val.2), by have := i.property; omega⟩) +
    (-1 : ℤ)^i.val.1 • TensorProduct.map LinearMap.id (VertexModel.boundary R q i.val.2)
      (z ⟨(i.val.1,i.val.2+1), by have := i.property; omega⟩) := rfl

lemma contraction_succ (p q n : ℕ) :
    (boundary R p q (n+1)).comp (cone R p q (n+1)) +
      (cone R p q n).comp (boundary R p q n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  funext ⟨⟨a,b⟩,hi⟩
  cases a with
  | zero =>
    cases b with
    | zero => dsimp at hi; omega
    | succ b =>
      simp only [LinearMap.add_apply, LinearMap.comp_apply, Pi.add_apply,
        boundary_apply, cone, coneLeft_zero, coneLeft_succ, coneRight_zero,
        coneRight_succ, zero_add, add_zero, pow_zero, one_smul, LinearMap.id_apply,
        map_add, map_zero, map_zsmul, TensorProduct.map_map,
        LinearMap.comp_id, LinearMap.id_comp]
      simp only [VertexModel.projection_boundary, TensorProduct.map_zero_left, LinearMap.zero_apply,
        zero_add]
      have hc := LinearMap.congr_fun (congrArg
        (fun L => L.rTensor (Chains R q (b+1))) (VertexModel.contraction_zero R p))
          (z ⟨(0,b+1),hi⟩)
      have hs := LinearMap.rTensor_sub
        (LinearMap.id : Chains R p 0 →ₗ[R] Chains R p 0) (projection R p)
        (Q := Chains R q (b+1))
      simp only [LinearMap.rTensor, TensorProduct.map_id] at hs
      simp only [LinearMap.rTensor] at hc
      rw [hs] at hc
      change TensorProduct.map _ _ (z ⟨(0,b+1),hi⟩) =
        z ⟨(0,b+1),hi⟩ - TensorProduct.map (projection R p) LinearMap.id (z ⟨(0,b+1),hi⟩) at hc
      have hd := LinearMap.congr_fun (congrArg
        (fun L => TensorProduct.map (projection R p) L) (VertexModel.contraction_succ R q b))
          (z ⟨(0,b+1),hi⟩)
      simp only [TensorProduct.map_add_right, LinearMap.add_apply] at hd
      rw [hc]
      calc
        _ = z ⟨(0,b+1),hi⟩ - TensorProduct.map (projection R p) LinearMap.id
              (z ⟨(0,b+1),hi⟩) +
            (TensorProduct.map (projection R p)
                ((VertexModel.boundary R q (b+1)).comp (VertexModel.cone R q (b+1)))
                (z ⟨(0,b+1),hi⟩) +
              TensorProduct.map (projection R p)
                ((VertexModel.cone R q b).comp (VertexModel.boundary R q b))
                (z ⟨(0,b+1),hi⟩)) := by abel
        _ = _ := by rw [hd]; abel
  | succ a =>
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Pi.add_apply,
      boundary_apply, cone, coneLeft_zero, coneLeft_succ, coneRight_zero,
      coneRight_succ, zero_add, add_zero, pow_zero, one_smul, LinearMap.id_apply,
      map_add, map_zero, map_zsmul, TensorProduct.map_map,
      LinearMap.comp_id, LinearMap.id_comp, smul_zero]
    have hc := LinearMap.congr_fun (congrArg
      (fun L => TensorProduct.map L (LinearMap.id : Chains R q b →ₗ[R] Chains R q b))
      (VertexModel.contraction_succ R p a)) (z ⟨(a+1,b),hi⟩)
    simp only [TensorProduct.map_add_left, LinearMap.add_apply,
      TensorProduct.map_id, LinearMap.id_apply] at hc
    simp only [pow_succ, mul_neg_one, neg_smul, add_zero]
    convert hc using 1 <;> abel

/-- Every positive-degree cycle has an explicit affine filling. -/
lemma fill_cycle (p q n : ℕ) (z : Total R p q (n+1))
    (hz : boundary R p q n z = 0) :
    boundary R p q (n+1) (cone R p q (n+1) z) = z := by
  have h := LinearMap.congr_fun (contraction_succ R p q n) z
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero,
    add_zero, LinearMap.id_apply] using h

/-- Realization of a tensor-model chain using the two input simplices. -/
def realize {X Y : TopCat.{w}} {p q : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (n : ℕ) : Total R p q n →ₗ[R] P202Specs.AlexanderWhitney.Total R X Y n where
  toFun z i := TensorProduct.map (VertexModel.realize R σ i.val.1)
    (VertexModel.realize R τ i.val.2) (z i)
  map_add' z z' := by ext i; exact map_add _ _ _
  map_smul' r z := by
    funext i
    change TensorProduct.map _ _ (r • z i) = r • _
    exact map_smul _ _ _

lemma realize_boundary {X Y : TopCat.{w}} {p q : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (n : ℕ) :
    (totalBoundary R X Y n).comp (realize R σ τ (n+1)) =
      (realize R σ τ n).comp (boundary R p q n) := by
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map (differential R X i.val.1) LinearMap.id
      (TensorProduct.map (VertexModel.realize R σ (i.val.1+1))
        (VertexModel.realize R τ i.val.2) (z ⟨(i.val.1+1,i.val.2),by have := i.property; omega⟩)) +
    (-1 : ℤ)^i.val.1 •
      TensorProduct.map LinearMap.id (differential R Y i.val.2)
        (TensorProduct.map (VertexModel.realize R σ i.val.1)
          (VertexModel.realize R τ (i.val.2+1)) (z ⟨(i.val.1,i.val.2+1),by have := i.property; omega⟩)) = _
  simp only [LinearMap.comp_apply, realize, LinearMap.coe_mk, AddHom.coe_mk,
    boundary_apply, map_add, map_zsmul, TensorProduct.map_map, LinearMap.comp_id,
    LinearMap.id_comp, VertexModel.realize_boundary]

lemma realize_natural {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') {p q : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (n : ℕ) :
    (totalMap R f g n).comp (realize R σ τ n) =
      realize R (postSimplex f p σ) (postSimplex g q τ) n := by
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map (push R f i.val.1) (push R g i.val.2)
      (TensorProduct.map (VertexModel.realize R σ i.val.1)
        (VertexModel.realize R τ i.val.2) (z i)) = _
  simp only [TensorProduct.map_map, VertexModel.realize_natural]
  rfl

/-- A coefficientwise left inverse on both factors. -/
def decode (p q n : ℕ) :
    P202Specs.AlexanderWhitney.Total R (VertexModel.space.{w} p) (VertexModel.space.{w} q) n →ₗ[R]
      Total R p q n where
  toFun z i := TensorProduct.map (VertexModel.decode R p i.val.1)
    (VertexModel.decode R q i.val.2) (z i)
  map_add' z z' := by funext i; exact map_add _ _ _
  map_smul' r z := by
    funext i
    change TensorProduct.map _ _ (r • z i) = r • _
    exact map_smul _ _ _

lemma decode_realize (p q n : ℕ) :
    (decode.{u,w} R p q n).comp
      (realize R (VertexModel.universal p) (VertexModel.universal q) n) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map _ _ (TensorProduct.map _ _ (z i)) = z i
  rw [TensorProduct.map_map, VertexModel.decode_realize, VertexModel.decode_realize,
    TensorProduct.map_id, LinearMap.id_apply]

lemma realize_universal_injective (p q n : ℕ) :
    Function.Injective (realize R (VertexModel.universal.{w} p) (VertexModel.universal q) n) := by
  apply Function.LeftInverse.injective (g := decode R p q n)
  exact LinearMap.congr_fun (decode_realize R p q n)

/-- A cycle check can be performed in the actual upstream total tensor
complex, then reflected to the finite affine model and filled there. -/
lemma fill_of_realized_cycle (p q n : ℕ) (z : Total R p q (n+1))
    (hz : totalBoundary R (VertexModel.space.{w} p) (VertexModel.space.{w} q) n
      (realize R (VertexModel.universal p) (VertexModel.universal q) (n+1) z) = 0) :
    boundary R p q (n+1) (cone R p q (n+1) z) = z := by
  apply fill_cycle
  apply realize_universal_injective R p q n
  rw [map_zero]
  have h := LinearMap.congr_fun
    (realize_boundary R (VertexModel.universal.{w} p) (VertexModel.universal q) n) z
  exact h.symm.trans hz

/-- The model realization has a genuine linear smooth lift whenever both
input simplices are smooth in charts. -/
def smoothRealize {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F) {X Y : TopCat.{w}} [ChartedSpace H X] [ChartedSpace K Y]
    {p q : ℕ} (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (hσ : SmoothSimplex I X σ) (hτ : SmoothSimplex J Y τ) (n : ℕ) :
    Total R p q n →ₗ[R] SmoothTotal R I J X Y n where
  toFun z i := TensorProduct.map (VertexModel.smoothRealize R I σ hσ i.val.1)
    (VertexModel.smoothRealize R J τ hτ i.val.2) (z i)
  map_add' z z' := by funext i; exact map_add _ _ _
  map_smul' r z := by
    funext i
    change TensorProduct.map _ _ (r • z i) = r • _
    exact map_smul _ _ _

lemma smoothRealize_inclusion {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F) {X Y : TopCat.{w}} [ChartedSpace H X] [ChartedSpace K Y]
    {p q : ℕ} (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (hσ : SmoothSimplex I X σ) (hτ : SmoothSimplex J Y τ) (n : ℕ) :
    (smoothTotalInclusion R I J X Y n).comp (smoothRealize R I J σ τ hσ hτ n) =
      realize R σ τ n := by
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map _ _ (TensorProduct.map _ _ (z i)) = _
  rw [TensorProduct.map_map, VertexModel.smoothRealize_inclusion,
    VertexModel.smoothRealize_inclusion]
  rfl

end TensorModel
end VertexModel

namespace UniversalExtension
open VertexModel

/-- A universal affine filling in each source bidegree of a fixed total degree. -/
abbrev Models (n : ℕ) := ∀ i : Diagonal n, VertexModel.TensorModel.Total R i.val.1 i.val.2 (n+1)

/-- Linear extension on one tensor of singular bases. -/
def component {n : ℕ} (A : Models R n) (X Y : TopCat.{w}) (i : Diagonal n) :
    Summand R X Y i.val.1 i.val.2 →ₗ[R] P202Specs.AlexanderWhitney.Total R X Y (n+1) :=
  ((Finsupp.basisSingleOne : Module.Basis (P202Specs.SingularChains.Simplex X i.val.1) R
    (P202Specs.SingularChains.Chains R X i.val.1)).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (P202Specs.SingularChains.Simplex Y i.val.2) R
    (P202Specs.SingularChains.Chains R Y i.val.2))).constr R
      (fun st => VertexModel.TensorModel.realize R st.1 st.2 (n+1) (A i))

lemma component_basis {n : ℕ} (A : Models R n) (X Y : TopCat.{w}) (i : Diagonal n)
    (σ : P202Specs.SingularChains.Simplex X i.val.1) (τ : P202Specs.SingularChains.Simplex Y i.val.2) :
    component R A X Y i (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1) =
      VertexModel.TensorModel.realize R σ τ (n+1) (A i) := by
  let b : Module.Basis (P202Specs.SingularChains.Simplex X i.val.1) R
      (P202Specs.SingularChains.Chains R X i.val.1) := Finsupp.basisSingleOne
  let c : Module.Basis (P202Specs.SingularChains.Simplex Y i.val.2) R
      (P202Specs.SingularChains.Chains R Y i.val.2) := Finsupp.basisSingleOne
  simpa only [component, b, c, Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne] using
    ((b.tensorProduct c).constr_basis R
      (fun st => VertexModel.TensorModel.realize R st.1 st.2 (n+1) (A i)) (σ,τ))

lemma component_natural {n : ℕ} (A : Models R n) {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') (i : Diagonal n) :
    (totalMap R f g (n+1)).comp (component R A X Y i) =
      (component R A X' Y' i).comp (TensorProduct.map (push R f i.val.1) (push R g i.val.2)) := by
  apply ((Finsupp.basisSingleOne : Module.Basis (P202Specs.SingularChains.Simplex X i.val.1) R
    (P202Specs.SingularChains.Chains R X i.val.1)).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (P202Specs.SingularChains.Simplex Y i.val.2) R
    (P202Specs.SingularChains.Chains R Y i.val.2))).ext
  intro ⟨σ,τ⟩
  simp only [Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne, LinearMap.comp_apply]
  change totalMap R f g (n+1)
      (component R A X Y i (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1)) =
    component R A X' Y' i (TensorProduct.map (push R f i.val.1) (push R g i.val.2)
      (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1))
  rw [component_basis, TensorProduct.map_tmul]
  change totalMap R f g (n+1) (VertexModel.TensorModel.realize R σ τ (n+1) (A i)) =
    component R A X' Y' i
      (((chainMap R R f).f i.val.1).hom (Finsupp.single σ 1) ⊗ₜ[R]
        ((chainMap R R g).f i.val.2).hom (Finsupp.single τ 1))
  rw [P202.SingularChains.chainMap_single, P202.SingularChains.chainMap_single, component_basis]
  exact LinearMap.congr_fun (VertexModel.TensorModel.realize_natural R f g σ τ (n+1)) (A i)

/-- Extend by linearity and the finite grading diagonal. -/
def extend {n : ℕ} (A : Models R n) (X Y : TopCat.{w}) :
    P202Specs.AlexanderWhitney.Total R X Y n →ₗ[R] P202Specs.AlexanderWhitney.Total R X Y (n+1) :=
  ∑ i : Diagonal n, (component R A X Y i).comp (LinearMap.proj i)

lemma extend_natural {n : ℕ} (A : Models R n) {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (totalMap R f g (n+1)).comp (extend R A X Y) =
      (extend R A X' Y').comp (totalMap R f g n) := by
  apply LinearMap.ext
  intro z
  simp only [extend, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact LinearMap.congr_fun (component_natural R A f g i) (z i)

lemma component_zero (n : ℕ) (X Y : TopCat.{w}) (i : Diagonal n) :
    component R (fun _ => 0) X Y i = 0 := by
  apply ((Finsupp.basisSingleOne : Module.Basis (P202Specs.SingularChains.Simplex X i.val.1) R
    (P202Specs.SingularChains.Chains R X i.val.1)).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (P202Specs.SingularChains.Simplex Y i.val.2) R
    (P202Specs.SingularChains.Chains R Y i.val.2))).ext
  intro ⟨σ,τ⟩
  simp only [Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne,
    component_basis, map_zero, LinearMap.zero_apply]

lemma extend_zero (n : ℕ) (X Y : TopCat.{w}) :
    extend R (fun _ : Diagonal n => 0) X Y = 0 := by
  classical
  simp only [extend, component_zero, LinearMap.zero_comp, Finset.sum_const_zero]

/-- The induction starts with the zero table and the ordinary degree-zero equation. -/
lemma base_identity (X Y : TopCat.{w}) :
    defect R X Y 0 =
      (totalBoundary R X Y 0).comp (extend R (fun _ : Diagonal 0 => 0) X Y) := by
  rw [defect_zero, extend_zero, LinearMap.comp_zero]

section Smooth
variable {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  (I : H → E) (J : K → F) (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]

/-- Splitting the inclusions of the supported basis subsets before tensoring.
This uses no flatness of an arbitrary submodule. -/
def smoothProjection (n : ℕ) :
    P202Specs.AlexanderWhitney.Total R X Y n →ₗ[R] SmoothTotal R I J X Y n := by
  classical
  exact
    { toFun := fun z i => TensorProduct.map
        (Finsupp.restrictDom R R {σ | SmoothSimplex I X σ})
        (Finsupp.restrictDom R R {τ | SmoothSimplex J Y τ}) (z i)
      map_add' := by intros; funext i; exact map_add _ _ _
      map_smul' := by
        intro r z
        funext i
        change TensorProduct.map _ _ (r • z i) = r • _
        exact map_smul _ _ _ }

lemma smoothProjection_inclusion (n : ℕ) :
    (smoothProjection R I J X Y n).comp (smoothTotalInclusion R I J X Y n) =
      LinearMap.id := by
  classical
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map _ _ (TensorProduct.map _ _ (z i)) = z i
  simp only [TensorProduct.map_map, smoothChains, Finsupp.restrictDom_comp_subtype,
    TensorProduct.map_id, LinearMap.id_apply]

lemma component_smooth_tmul {n : ℕ} (A : Models R n) (i : Diagonal n)
    (a : smoothChains R I X i.val.1) (b : smoothChains R J Y i.val.2) :
    component R A X Y i (a.val ⊗ₜ[R] b.val) ∈
      LinearMap.range (smoothTotalInclusion R I J X Y (n+1)) := by
  let S := LinearMap.range (smoothTotalInclusion R I J X Y (n+1))
  apply P202.ShuffleModel.map_smoothChains R I X
    ((component R A X Y i).comp ((TensorProduct.mk R _ _).flip b.val)) S ?_ a.val a.property
  intro σ hσ
  apply P202.ShuffleModel.map_smoothChains R J Y
    ((component R A X Y i).comp ((TensorProduct.mk R _ _) (Finsupp.single σ 1))) S ?_ b.val b.property
  intro τ hτ
  change component R A X Y i (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1) ∈ S
  rw [component_basis]
  refine ⟨VertexModel.TensorModel.smoothRealize R I J σ τ hσ hτ (n+1) (A i), ?_⟩
  exact LinearMap.congr_fun
    (VertexModel.TensorModel.smoothRealize_inclusion R I J σ τ hσ hτ (n+1)) (A i)

lemma component_smooth_tensor {n : ℕ} (A : Models R n) (i : Diagonal n)
    (z : smoothChains R I X i.val.1 ⊗[R] smoothChains R J Y i.val.2) :
    component R A X Y i
      (TensorProduct.map (smoothChains R I X i.val.1).subtype
        (smoothChains R J Y i.val.2).subtype z) ∈
      LinearMap.range (smoothTotalInclusion R I J X Y (n+1)) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | tmul a b => exact component_smooth_tmul R I J X Y A i a b

lemma extend_mem_smooth_range {n : ℕ} (A : Models R n) (z : SmoothTotal R I J X Y n) :
    extend R A X Y (smoothTotalInclusion R I J X Y n z) ∈
      LinearMap.range (smoothTotalInclusion R I J X Y (n+1)) := by
  simp only [extend, LinearMap.sum_apply, LinearMap.comp_apply]
  apply Submodule.sum_mem
  intro i _
  exact component_smooth_tensor R I J X Y A i (z i)

/-- Any table of affine universal chains gives a linear smooth restriction
of its natural extension. The underlying map is exactly `extend`. -/
lemma extend_smooth {n : ℕ} (A : Models R n) :
    ∃ L : SmoothTotal R I J X Y n →ₗ[R] SmoothTotal R I J X Y (n+1),
      (smoothTotalInclusion R I J X Y (n+1)).comp L =
        (extend R A X Y).comp (smoothTotalInclusion R I J X Y n) := by
  refine ⟨(smoothProjection R I J X Y (n+1)).comp
    ((extend R A X Y).comp (smoothTotalInclusion R I J X Y n)), ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨w,hw⟩ := extend_mem_smooth_range R I J X Y A z
  change smoothTotalInclusion R I J X Y (n+1)
    (smoothProjection R I J X Y (n+1)
      (extend R A X Y (smoothTotalInclusion R I J X Y n z))) =
    extend R A X Y (smoothTotalInclusion R I J X Y n z)
  rw [← hw]
  exact congrArg (smoothTotalInclusion R I J X Y (n+1))
    (LinearMap.congr_fun (smoothProjection_inclusion R I J X Y (n+1)) w)

end Smooth
end UniversalExtension
/-- Algebraic assembly once the universal affine chains satisfy the two
ordinary homotopy equations. This lemma is conditional; it is not the
unconditional Eilenberg--Zilber existence theorem. -/
def ofUniversalModels
    (A : ∀ n, UniversalExtension.Models R n)
    (hzero : ∀ (X Y : TopCat.{w}),
      defect R X Y 0 = (totalBoundary R X Y 0).comp (UniversalExtension.extend R (A 0) X Y))
    (hsucc : ∀ (X Y : TopCat.{w}) n,
      defect R X Y (n+1) =
        (totalBoundary R X Y (n+1)).comp (UniversalExtension.extend R (A (n+1)) X Y) +
          (UniversalExtension.extend R (A n) X Y).comp (totalBoundary R X Y n)) :
    P202Specs.EZTensorHomotopy.TensorHomotopy.{u,w} R where
  hom X Y n := UniversalExtension.extend R (A n) X Y
  zero := hzero
  succ := hsucc
  naturality f g n := UniversalExtension.extend_natural R (A n) f g

lemma ofUniversalModels_smooth
    (A : ∀ n, UniversalExtension.Models R n)
    (hzero : ∀ (X Y : TopCat.{w}),
      defect R X Y 0 = (totalBoundary R X Y 0).comp (UniversalExtension.extend R (A 0) X Y))
    (hsucc : ∀ (X Y : TopCat.{w}) n,
      defect R X Y (n+1) =
        (totalBoundary R X Y (n+1)).comp (UniversalExtension.extend R (A (n+1)) X Y) +
          (UniversalExtension.extend R (A n) X Y).comp (totalBoundary R X Y n)) :
    (ofUniversalModels R A hzero hsucc).Smooth.{u,w,vE,vF,vH,vK} R := by
  intro E F H K _ _ _ _ _ _ I J X Y _ _ n
  exact UniversalExtension.extend_smooth R I J X Y (A n)

namespace VertexModel

lemma realizeSimplex_comp {X : TopCat.{w}} {p a b : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (s : Simplex p a) (t : Simplex a b) :
    realizeSimplex (realizeSimplex σ s) t = realizeSimplex σ (t ≫ s) := by
  simp [realizeSimplex, Functor.map_comp]

lemma realizeSimplex_id {X : TopCat.{w}} {p : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) : realizeSimplex σ (𝟙 ⦋p⦌) = σ := by
  simp [realizeSimplex]

/-- Composition of ordered vertex maps within the affine model. -/
def reindex {p a : ℕ} (s : Simplex p a) (n : ℕ) :
    Chains R a n →ₗ[R] Chains R p n :=
  Finsupp.lmapDomain R R (fun t => t ≫ s)

lemma realize_reindex {X : TopCat.{w}} {p a : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (s : Simplex p a) (n : ℕ) :
    (realize R σ n).comp (reindex R s n) = realize R (realizeSimplex σ s) n := by
  apply Finsupp.lhom_ext
  intro t r
  simp only [LinearMap.comp_apply, reindex, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, realize_single, realizeSimplex_comp]

namespace TensorModel

def reindex {p q a b : ℕ} (s : VertexModel.Simplex p a) (t : VertexModel.Simplex q b)
    (n : ℕ) : Total R a b n →ₗ[R] Total R p q n where
  toFun z i := TensorProduct.map (VertexModel.reindex R s i.val.1)
    (VertexModel.reindex R t i.val.2) (z i)
  map_add' := by intros; funext i; exact map_add _ _ _
  map_smul' := by
    intro r z; funext i
    change TensorProduct.map _ _ (r • z i) = r • _
    exact map_smul _ _ _

lemma realize_reindex {X Y : TopCat.{w}} {p q a b : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (s : VertexModel.Simplex p a) (t : VertexModel.Simplex q b) (n : ℕ) :
    (realize R σ τ n).comp (reindex R s t n) =
      realize R (realizeSimplex σ s) (realizeSimplex τ t) n := by
  apply LinearMap.ext
  intro z
  funext i
  change TensorProduct.map _ _ (TensorProduct.map _ _ (z i)) = _
  rw [TensorProduct.map_map, VertexModel.realize_reindex, VertexModel.realize_reindex]
  rfl

lemma realize_single {X Y : TopCat.{w}} {p q n : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (i : Diagonal n) (z : VertexModel.Chains R p i.val.1 ⊗[R] VertexModel.Chains R q i.val.2) :
    realize R σ τ n (Pi.single i z) =
      Pi.single i (TensorProduct.map (VertexModel.realize R σ i.val.1)
        (VertexModel.realize R τ i.val.2) z) := by
  classical
  funext j
  by_cases h : j = i
  · subst j; simp [realize]
  · simp [realize, Pi.single_eq_of_ne h]

end TensorModel
end VertexModel

namespace UniversalExtension
open VertexModel

lemma extend_single {n : ℕ} (A : Models R n) (X Y : TopCat.{w}) (i : Diagonal n)
    (z : Summand R X Y i.val.1 i.val.2) :
    extend R A X Y (Pi.single i z) = component R A X Y i z := by
  classical
  simp only [extend, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji; rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

lemma extend_realize_mem_range {n p q : ℕ} (A : Models R n) {X Y : TopCat.{w}}
    (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (z : TensorModel.Total R p q n) :
    extend R A X Y (TensorModel.realize R σ τ n z) ∈
      LinearMap.range (TensorModel.realize R σ τ (n+1)) := by
  classical
  let S := LinearMap.range (TensorModel.realize R σ τ (n+1))
  have hsingle : ∀ (i : Diagonal n)
      (c : VertexModel.Chains R p i.val.1 ⊗[R] VertexModel.Chains R q i.val.2),
      extend R A X Y (TensorModel.realize R σ τ n (Pi.single i c)) ∈ S := by
    intro i c
    induction c using TensorProduct.inductionOn with
    | add a b ha hb =>
      simpa only [Pi.single_add, map_add] using Submodule.add_mem S ha hb
    | tmul a b =>
      induction a using Finsupp.induction_linear with
      | zero => simp [TensorProduct.zero_tmul, map_zero]
      | add a a' ha ha' =>
        simpa only [TensorProduct.add_tmul, Pi.single_add, map_add] using Submodule.add_mem S ha ha'
      | single s r =>
        induction b using Finsupp.induction_linear with
        | zero => simp [TensorProduct.tmul_zero, map_zero]
        | add b b' hb hb' =>
          simpa only [TensorProduct.tmul_add, Pi.single_add, map_add] using Submodule.add_mem S hb hb'
        | single t v =>
          have hb : extend R A X Y
              (TensorModel.realize R σ τ n
                (Pi.single i (Finsupp.single s 1 ⊗ₜ[R] Finsupp.single t 1))) ∈ S := by
            rw [TensorModel.realize_single, TensorProduct.map_tmul, VertexModel.realize_single,
              VertexModel.realize_single, extend_single, component_basis]
            refine ⟨TensorModel.reindex R s t (n+1) (A i), ?_⟩
            exact LinearMap.congr_fun (TensorModel.realize_reindex R σ τ s t (n+1)) (A i)
          have he : Finsupp.single s r ⊗ₜ[R] Finsupp.single t v =
              (r*v) • (Finsupp.single s 1 ⊗ₜ[R] Finsupp.single t 1) := by
            have hr : Finsupp.single s r = r • Finsupp.single s (1 : R) := by simp
            have hv : Finsupp.single t v = v • Finsupp.single t (1 : R) := by simp
            rw [hr, hv, TensorProduct.smul_tmul_smul]
          rw [he, Pi.single_smul, map_smul, map_smul]
          exact Submodule.smul_mem S _ hb
  have hz : z = ∑ i : Diagonal n, Pi.single i (z i) := by
    funext j
    simp
  rw [hz, map_sum, map_sum]
  exact Submodule.sum_mem S (fun i _ => hsingle i (z i))

end UniversalExtension

namespace AffineClosure
open VertexModel

lemma shuffle_projections {X Y : TopCat.{w}} {p q : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (s : LatticePath p q) :
    postSimplex (firstProjection X Y) (p+q) (shuffleSimplex s σ τ) =
      realizeSimplex σ (SimplexCategory.Hom.mk s.horizontal) ∧
    postSimplex (secondProjection X Y) (p+q) (shuffleSimplex s σ τ) =
      realizeSimplex τ (SimplexCategory.Hom.mk s.vertical) := by
  constructor
  · apply (simplexEquiv X (p+q)).injective
    ext z
    simp only [P202.SingularChains.simplexEquiv_postcomp, realize_continuous]
    change (simplexEquiv (productSpace X Y) (p+q) (shuffleSimplex s σ τ) z).1 = _
    erw [P202.ShuffleChains.simplex_formula]
    rfl
  · apply (simplexEquiv Y (p+q)).injective
    ext z
    simp only [P202.SingularChains.simplexEquiv_postcomp, realize_continuous]
    change (simplexEquiv (productSpace X Y) (p+q) (shuffleSimplex s σ τ) z).2 = _
    erw [P202.ShuffleChains.simplex_formula]
    rfl

/-- Every AW summand of a shuffle is still an ordered affine pullback in
both factors, including the degenerate summands in the unnormalized complex. -/
def awShuffle (p q : ℕ) : TensorModel.Total R p q (p+q) := fun i =>
  ∑ s : LatticePath p q, s.sign •
    (Finsupp.single (intervalInclusion 0 i.val.1 (p+q) (by have := i.property; omega) ≫
      SimplexCategory.Hom.mk s.horizontal) 1 ⊗ₜ[R]
     Finsupp.single (intervalInclusion i.val.1 i.val.2 (p+q) (by have := i.property; omega) ≫
      SimplexCategory.Hom.mk s.vertical) 1)

lemma aw_shuffle_simplex {X Y : TopCat.{w}} {p q : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q)
    (s : LatticePath p q) (i : Diagonal (p+q)) :
    aw R X Y (p+q) (Finsupp.single (shuffleSimplex s σ τ) 1) i =
      TensorProduct.map (VertexModel.realize R σ i.val.1) (VertexModel.realize R τ i.val.2)
        (Finsupp.single (intervalInclusion 0 i.val.1 (p+q) (by have := i.property; omega) ≫
          SimplexCategory.Hom.mk s.horizontal) 1 ⊗ₜ[R]
         Finsupp.single (intervalInclusion i.val.1 i.val.2 (p+q) (by have := i.property; omega) ≫
          SimplexCategory.Hom.mk s.vertical) 1) := by
  rw [P202.AlexanderWhitney.formula]
  simp only [one_smul, awComponent, (shuffle_projections σ τ s).1,
    (shuffle_projections σ τ s).2, TensorProduct.map_tmul, VertexModel.realize_single]
  change Finsupp.single (realizeSimplex (realizeSimplex σ _) _) 1 ⊗ₜ[R]
      Finsupp.single (realizeSimplex (realizeSimplex τ _) _) 1 = _
  rw [realizeSimplex_comp, realizeSimplex_comp]

lemma awShuffle_realize {X Y : TopCat.{w}} {p q : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) (τ : P202Specs.SingularChains.Simplex Y q) :
    TensorModel.realize R σ τ (p+q) (awShuffle R p q) =
      aw R X Y (p+q) (shuffle R X Y (p+q)
        (Pi.single (⟨(p,q),rfl⟩ : Diagonal (p+q))
          (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1))) := by
  rw [P202.ShuffleBoundary.shuffle_single]
  change _ = aw R X Y (p+q) (shuffleComponent R X Y p q _)
  rw [P202.ShuffleChains.component_formula]
  simp only [mul_one, one_smul, map_sum, map_zsmul]
  funext i
  change TensorProduct.map _ _ (∑ s : LatticePath p q, _) = _
  simp only [map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg (fun z => s.sign • z) (aw_shuffle_simplex R σ τ s i).symm

lemma generator_mem_range {X Y : TopCat.{w}} {n : ℕ} (i : Diagonal n)
    (σ : P202Specs.SingularChains.Simplex X i.val.1)
    (τ : P202Specs.SingularChains.Simplex Y i.val.2) :
    Pi.single i (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1) ∈
      LinearMap.range (TensorModel.realize R σ τ n) := by
  refine ⟨Pi.single i (Finsupp.single (𝟙 _) 1 ⊗ₜ[R] Finsupp.single (𝟙 _) 1), ?_⟩
  rw [TensorModel.realize_single, TensorProduct.map_tmul, VertexModel.realize_single,
    VertexModel.realize_single, realizeSimplex_id, realizeSimplex_id]

lemma defect_generator_mem_range {X Y : TopCat.{w}} {n : ℕ} (i : Diagonal n)
    (σ : P202Specs.SingularChains.Simplex X i.val.1)
    (τ : P202Specs.SingularChains.Simplex Y i.val.2) :
    defect R X Y n (Pi.single i (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1)) ∈
      LinearMap.range (TensorModel.realize R σ τ n) := by
  change aw R X Y n (shuffle R X Y n _) - _ ∈ _
  apply Submodule.sub_mem
  · rcases i with ⟨⟨p,q⟩,h⟩
    dsimp at h
    subst n
    exact ⟨awShuffle R p q, awShuffle_realize R σ τ⟩
  · exact generator_mem_range R i σ τ

end AffineClosure

namespace UniversalExtension
open VertexModel

/-- The next obstruction after the lower-degree homotopy has been chosen. -/
def residual {n : ℕ} (A : Models R n) (X Y : TopCat.{w}) :
    P202Specs.AlexanderWhitney.Total R X Y (n+1) →ₗ[R]
      P202Specs.AlexanderWhitney.Total R X Y (n+1) :=
  defect R X Y (n+1) - (extend R A X Y).comp (totalBoundary R X Y n)

lemma residual_natural {n : ℕ} (A : Models R n) {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (totalMap R f g (n+1)).comp (residual R A X Y) =
      (residual R A X' Y').comp (totalMap R f g (n+1)) := by
  simp only [residual, LinearMap.comp_sub, LinearMap.sub_comp]
  rw [defect_natural]
  congr 1
  rw [← LinearMap.comp_assoc, extend_natural, LinearMap.comp_assoc,
    ← P202.AlexanderWhitney.totalMap_boundary, ← LinearMap.comp_assoc]

lemma boundary_extend_natural {n : ℕ} (A : Models R n) {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (totalMap R f g n).comp ((totalBoundary R X Y n).comp (extend R A X Y)) =
      ((totalBoundary R X' Y' n).comp (extend R A X' Y')).comp (totalMap R f g n) := by
  rw [← LinearMap.comp_assoc, ← P202.AlexanderWhitney.totalMap_boundary,
    LinearMap.comp_assoc, extend_natural, ← LinearMap.comp_assoc]

lemma residual_generator_mem_range {n : ℕ} (A : Models R n) {X Y : TopCat.{w}}
    (i : Diagonal (n+1)) (σ : P202Specs.SingularChains.Simplex X i.val.1)
    (τ : P202Specs.SingularChains.Simplex Y i.val.2) :
    residual R A X Y (Pi.single i (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1)) ∈
      LinearMap.range (TensorModel.realize R σ τ (n+1)) := by
  apply Submodule.sub_mem
  · exact AffineClosure.defect_generator_mem_range R i σ τ
  · obtain ⟨z,hz⟩ := AffineClosure.generator_mem_range R i σ τ
    change extend R A X Y (totalBoundary R X Y n _) ∈ _
    rw [← hz]
    have hb := LinearMap.congr_fun (TensorModel.realize_boundary R σ τ n) z
    change totalBoundary R X Y n (TensorModel.realize R σ τ (n+1) z) =
      TensorModel.realize R σ τ n (TensorModel.boundary R i.val.1 i.val.2 n z) at hb
    rw [hb]
    exact extend_realize_mem_range R A σ τ (TensorModel.boundary R i.val.1 i.val.2 n z)

end UniversalExtension

namespace UniversalExtension
lemma residual_cycle_zero {X Y : TopCat.{w}} (A : Models R 0)
    (hA : defect R X Y 0 = (totalBoundary R X Y 0).comp (extend R A X Y))
    (z : P202Specs.AlexanderWhitney.Total R X Y 1) :
    totalBoundary R X Y 0
      (defect R X Y 1 z - extend R A X Y (totalBoundary R X Y 0 z)) = 0 := by
  rw [map_sub]
  have hc := LinearMap.congr_fun (defect_boundary R X Y 0) z
  change totalBoundary R X Y 0 (defect R X Y 1 z) =
    defect R X Y 0 (totalBoundary R X Y 0 z) at hc
  rw [hc, hA]
  simp only [LinearMap.comp_apply, sub_self]

lemma residual_cycle_succ {X Y : TopCat.{w}} (n : ℕ) (A : Models R (n+1)) (B : Models R n)
    (hA : defect R X Y (n+1) =
      (totalBoundary R X Y (n+1)).comp (extend R A X Y) +
        (extend R B X Y).comp (totalBoundary R X Y n))
    (z : P202Specs.AlexanderWhitney.Total R X Y (n+2)) :
    totalBoundary R X Y (n+1)
      (defect R X Y (n+2) z - extend R A X Y (totalBoundary R X Y (n+1) z)) = 0 := by
  rw [map_sub]
  have hc := LinearMap.congr_fun (defect_boundary R X Y (n+1)) z
  change totalBoundary R X Y (n+1) (defect R X Y (n+2) z) =
    defect R X Y (n+1) (totalBoundary R X Y (n+1) z) at hc
  rw [hc, hA]
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  have hz := LinearMap.congr_fun (P202.AlexanderWhitney.totalBoundary_squared R X Y n) z
  change totalBoundary R X Y n (totalBoundary R X Y (n+1) z) = 0 at hz
  rw [hz, map_zero, add_zero, sub_self]


end UniversalExtension
namespace VertexModel

def evaluation {X : TopCat.{w}} {p : ℕ} (σ : P202Specs.SingularChains.Simplex X p) :
    space.{w} p ⟶ X :=
  TopCat.ofHom ((simplexEquiv X p σ).comp ⟨ULift.down, continuous_uliftDown⟩)

lemma post_evaluation_universal {X : TopCat.{w}} {p : ℕ}
    (σ : P202Specs.SingularChains.Simplex X p) :
    postSimplex (evaluation σ) p (universal.{w} p) = σ := by
  apply (simplexEquiv X p).injective
  ext z
  simp [postSimplex, P202.SingularChains.simplexEquiv_postcomp, evaluation, universal]

end VertexModel

/-- The tensor of two singular generators, in its single diagonal component. -/
def totalGenerator {X Y : TopCat.{w}} {n : ℕ} (i : Diagonal n)
    (σ : Simplex X i.val.1) (τ : Simplex Y i.val.2) : Total R X Y n :=
  Pi.single i (Finsupp.single σ 1 ⊗ₜ[R] Finsupp.single τ 1)

lemma totalMap_single {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    {n : ℕ} (i : Diagonal n) (z : Summand R X Y i.val.1 i.val.2) :
    totalMap R f g n (Pi.single i z) =
      Pi.single i (TensorProduct.map (push R f i.val.1) (push R g i.val.2) z) := by
  classical
  funext j
  by_cases h : j = i
  · subst j; simp only [totalMap, push, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same]; rfl
  · simp [totalMap, Pi.single_eq_of_ne h]

lemma totalMap_generator {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    {n : ℕ} (i : Diagonal n) (σ : Simplex X i.val.1) (τ : Simplex Y i.val.2) :
    totalMap R f g n (totalGenerator R i σ τ) =
      totalGenerator R i (postSimplex f i.val.1 σ) (postSimplex g i.val.2 τ) := by
  rw [totalGenerator, totalMap_single]
  rw [TensorProduct.map_tmul]
  change (Pi.single i
    (((chainMap R R f).f i.val.1).hom (Finsupp.single σ 1) ⊗ₜ[R]
      ((chainMap R R g).f i.val.2).hom (Finsupp.single τ 1)) : Total R X' Y' n) = _
  rw [P202.SingularChains.chainMap_single, P202.SingularChains.chainMap_single]
  rfl

namespace UniversalExtension

lemma natural_eq_of_universal {n m : ℕ}
    (D E : ∀ X Y : TopCat.{w}, Total R X Y n →ₗ[R] Total R X Y m)
    (hD : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y'),
      (totalMap R f g m).comp (D X Y) = (D X' Y').comp (totalMap R f g n))
    (hE : ∀ {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y'),
      (totalMap R f g m).comp (E X Y) = (E X' Y').comp (totalMap R f g n))
    (hmodel : ∀ i : Diagonal n,
      D (VertexModel.space i.val.1) (VertexModel.space i.val.2)
          (totalGenerator R i (VertexModel.universal i.val.1) (VertexModel.universal i.val.2)) =
        E (VertexModel.space i.val.1) (VertexModel.space i.val.2)
          (totalGenerator R i (VertexModel.universal i.val.1) (VertexModel.universal i.val.2)))
    (X Y : TopCat.{w}) : D X Y = E X Y := by
  classical
  apply LinearMap.pi_ext
  intro i z
  have hi : (D X Y).comp (LinearMap.single R (fun j : Diagonal n =>
      Summand R X Y j.val.1 j.val.2) i) =
      (E X Y).comp (LinearMap.single R (fun j : Diagonal n =>
        Summand R X Y j.val.1 j.val.2) i) := by
    apply ((Finsupp.basisSingleOne : Module.Basis (Simplex X i.val.1) R
      (Chains R X i.val.1)).tensorProduct
      (Finsupp.basisSingleOne : Module.Basis (Simplex Y i.val.2) R
        (Chains R Y i.val.2))).ext
    intro ⟨σ,τ⟩
    simp only [Module.Basis.tensorProduct_apply, Finsupp.coe_basisSingleOne,
      LinearMap.comp_apply, LinearMap.single_apply]
    change D X Y (totalGenerator R i σ τ) = E X Y (totalGenerator R i σ τ)
    let f := VertexModel.evaluation σ
    let g := VertexModel.evaluation τ
    have hgen : totalMap R f g n
        (totalGenerator R i (VertexModel.universal i.val.1) (VertexModel.universal i.val.2)) =
        totalGenerator R i σ τ := by
      rw [totalMap_generator, VertexModel.post_evaluation_universal,
        VertexModel.post_evaluation_universal]
    have hd := LinearMap.congr_fun (hD f g)
      (totalGenerator R i (VertexModel.universal i.val.1) (VertexModel.universal i.val.2))
    have he := LinearMap.congr_fun (hE f g)
      (totalGenerator R i (VertexModel.universal i.val.1) (VertexModel.universal i.val.2))
    simp only [LinearMap.comp_apply, hgen] at hd he
    exact hd.symm.trans ((congrArg (totalMap R f g m) (hmodel i)).trans he)
  exact LinearMap.congr_fun hi z

end UniversalExtension

namespace UniversalExtension

lemma extend_generator {n : ℕ} (A : Models R n) (X Y : TopCat.{w})
    (i : Diagonal n) (σ : Simplex X i.val.1) (τ : Simplex Y i.val.2) :
    extend R A X Y (totalGenerator R i σ τ) =
      VertexModel.TensorModel.realize R σ τ (n+1) (A i) := by
  rw [totalGenerator, extend_single, component_basis]

lemma step_residual_identity {n : ℕ} (A : Models R n) (B : Models R (n+1))
    (hmodel : ∀ i : Diagonal (n+1),
      totalBoundary R (VertexModel.space.{w} i.val.1) (VertexModel.space i.val.2) (n+1)
        (extend R B (VertexModel.space i.val.1) (VertexModel.space i.val.2)
          (totalGenerator R i (VertexModel.universal i.val.1) (VertexModel.universal i.val.2))) =
      residual R A (VertexModel.space i.val.1) (VertexModel.space i.val.2)
        (totalGenerator R i (VertexModel.universal i.val.1) (VertexModel.universal i.val.2)))
    (X Y : TopCat.{w}) :
    residual R A X Y = (totalBoundary R X Y (n+1)).comp (extend R B X Y) := by
  apply natural_eq_of_universal R
    (fun X Y => residual R A X Y)
    (fun X Y => (totalBoundary R X Y (n+1)).comp (extend R B X Y))
    (fun f g => residual_natural R A f g)
    (fun f g => boundary_extend_natural R B f g)
  intro i
  exact (hmodel i).symm

lemma step_identity {n : ℕ} (A : Models R n) (B : Models R (n+1))
    (hmodel : ∀ i : Diagonal (n+1),
      totalBoundary R (VertexModel.space.{w} i.val.1) (VertexModel.space i.val.2) (n+1)
        (extend R B (VertexModel.space i.val.1) (VertexModel.space i.val.2)
          (totalGenerator R i (VertexModel.universal i.val.1) (VertexModel.universal i.val.2))) =
      residual R A (VertexModel.space i.val.1) (VertexModel.space i.val.2)
        (totalGenerator R i (VertexModel.universal i.val.1) (VertexModel.universal i.val.2)))
    (X Y : TopCat.{w}) :
    defect R X Y (n+1) =
      (totalBoundary R X Y (n+1)).comp (extend R B X Y) +
        (extend R A X Y).comp (totalBoundary R X Y n) := by
  have h := step_residual_identity R A B hmodel X Y
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun h z
  change defect R X Y (n+1) z - extend R A X Y (totalBoundary R X Y n z) =
    totalBoundary R X Y (n+1) (extend R B X Y z) at hz
  exact sub_eq_iff_eq_add.mp hz

end UniversalExtension

namespace UniversalExtension
open VertexModel

/-- Choose the affine preimage on the universal pair, then fill it using the
explicit tensor contraction. No cycle or filling hypothesis is used to define
the table; the inductive invariant below proves that these choices fill it. -/
def stepModels {n : ℕ} (A : Models R n) : Models R (n+1) := fun i =>
  TensorModel.cone R i.val.1 i.val.2 (n+1)
    (Classical.choose (residual_generator_mem_range R A i
      (universal.{w} i.val.1) (universal.{w} i.val.2)))

lemma stepModels_universal {n : ℕ} (A : Models R n)
    (hcycle : ∀ (X Y : TopCat.{w}) (z : P202Specs.AlexanderWhitney.Total R X Y (n+1)),
      totalBoundary R X Y n (residual R A X Y z) = 0)
    (i : Diagonal (n+1)) :
    totalBoundary R (space.{w} i.val.1) (space.{w} i.val.2) (n+1)
      (extend R (stepModels.{u,w} R A) (space i.val.1) (space i.val.2)
        (Pi.single i (Finsupp.single (universal i.val.1) 1 ⊗ₜ[R]
          Finsupp.single (universal i.val.2) 1))) =
      residual R A (space i.val.1) (space i.val.2)
        (Pi.single i (Finsupp.single (universal i.val.1) 1 ⊗ₜ[R]
          Finsupp.single (universal i.val.2) 1)) := by
  let z := Classical.choose (residual_generator_mem_range R A i
      (universal.{w} i.val.1) (universal.{w} i.val.2))
  have hz : TensorModel.realize R (universal.{w} i.val.1) (universal.{w} i.val.2) (n+1) z =
      residual R A (space i.val.1) (space i.val.2)
        (Pi.single i (Finsupp.single (universal i.val.1) 1 ⊗ₜ[R]
          Finsupp.single (universal i.val.2) 1)) :=
    Classical.choose_spec (residual_generator_mem_range R A i
      (universal.{w} i.val.1) (universal.{w} i.val.2))
  have hfill : TensorModel.boundary R i.val.1 i.val.2 (n+1)
      (TensorModel.cone R i.val.1 i.val.2 (n+1) z) = z := by
    apply TensorModel.fill_of_realized_cycle.{u,w}
    rw [hz]
    exact hcycle _ _ _
  rw [extend_single, component_basis]
  have hb := LinearMap.congr_fun (TensorModel.realize_boundary R
    (universal.{w} i.val.1) (universal.{w} i.val.2) (n+1))
      (TensorModel.cone R i.val.1 i.val.2 (n+1) z)
  change totalBoundary R (space i.val.1) (space i.val.2) (n+1)
      (TensorModel.realize R (universal i.val.1) (universal i.val.2) (n+1+1)
        (TensorModel.cone R i.val.1 i.val.2 (n+1) z)) = _
  simp only [LinearMap.comp_apply] at hb
  rw [hb, hfill, hz]

lemma successor_identity {n : ℕ} (A : Models R n)
    (hcycle : ∀ (X Y : TopCat.{w}) (z : P202Specs.AlexanderWhitney.Total R X Y (n+1)),
      totalBoundary R X Y n (residual R A X Y z) = 0)
    (X Y : TopCat.{w}) :
    defect R X Y (n+1) =
      (totalBoundary R X Y (n+1)).comp (extend R (stepModels.{u,w} R A) X Y) +
        (extend R A X Y).comp (totalBoundary R X Y n) := by
  exact step_identity R A (stepModels.{u,w} R A) (stepModels_universal R A hcycle) X Y

/-- A finite stage carries the next cycle assertion, rather than an assumed
filling certificate: the assertion is proved from the preceding identity. -/
def Stages (n : ℕ) := {A : Models R n //
    ∀ (X Y : TopCat.{w}) (z : P202Specs.AlexanderWhitney.Total R X Y (n+1)),
      totalBoundary R X Y n (residual R A X Y z) = 0}

def stages (n : ℕ) : Stages.{u,w} R n := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, ?_⟩
    intro X Y z
    exact residual_cycle_zero R (fun _ => 0) (base_identity R X Y) z
  | succ n A =>
    refine ⟨stepModels.{u,w} R A.val, ?_⟩
    intro X Y z
    exact residual_cycle_succ R n (stepModels.{u,w} R A.val) A.val
      (successor_identity R A.val A.property X Y) z

/-- The recursively constructed affine tables, simultaneously in all degrees. -/
def allModels (n : ℕ) : Models R n := (stages.{u,w} R n).val

lemma allModels_zero (X Y : TopCat.{w}) :
    defect R X Y 0 =
      (totalBoundary R X Y 0).comp (extend R (allModels.{u,w} R 0) X Y) :=
  base_identity R X Y

lemma allModels_succ (X Y : TopCat.{w}) (n : ℕ) :
    defect R X Y (n+1) =
      (totalBoundary R X Y (n+1)).comp (extend R (allModels.{u,w} R (n+1)) X Y) +
        (extend R (allModels.{u,w} R n) X Y).comp (totalBoundary R X Y n) := by
  exact successor_identity R (stages.{u,w} R n).val (stages.{u,w} R n).property X Y

end UniversalExtension

/-- The tensor-side Eilenberg--Zilber homotopy, natural for all continuous
maps and admitting genuine linear lifts on the smooth tensor subcomplex. -/
theorem naturalHomotopy :
    P202Specs.EZTensorHomotopy.naturalHomotopy_type.{u,w,vE,vF,vH,vK} := by
  intro R _
  let A := UniversalExtension.allModels.{u,w} R
  have hzero := UniversalExtension.allModels_zero.{u,w} R
  have hsucc := UniversalExtension.allModels_succ.{u,w} R
  exact ⟨ofUniversalModels R A hzero hsucc, ofUniversalModels_smooth R A hzero hsucc⟩


end P202.EZTensorHomotopy
