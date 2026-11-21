import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.EZProductHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.AlexanderWhitney
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.ShuffleChains
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! The natural product-side Eilenberg–Zilber homotopy (paper.tex,
`thm:p202-ez`). Universal fillings are finite formal vertex lists. Their
faithful affine realizations give the signed boundary equations, and their
affine parametrizations preserve local smooth extensions at corners. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct
namespace P202.EZProductHomotopy
open P202Specs.SingularChains P202Specs.AlexanderWhitney P202Specs.ShuffleModel
universe u v w
variable (R : Type u) [CommRing R]

namespace VertexChains
/-- Formal finite ordered vertex lists, before affine realization. Repeated
vertices are retained, as in unnormalized singular chains. -/
abbrev Chain (V : Type v) (n : ℕ) := (Fin (n+1) → V) →₀ R

def boundary (V : Type v) (n : ℕ) : Chain R V (n+1) →ₗ[R] Chain R V n :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
    Finsupp.lmapDomain R R (fun s => s ∘ i.succAbove)

def cone {V : Type v} (v : V) (n : ℕ) : Chain R V n →ₗ[R] Chain R V (n+1) :=
  Finsupp.lmapDomain R R (fun s : Fin (n+1) → V => Fin.cons v s)

def map {V W : Type v} (f : V → W) (n : ℕ) : Chain R V n →ₗ[R] Chain R W n :=
  Finsupp.lmapDomain R R (fun s => f ∘ s)

@[simp] lemma boundary_single {V : Type v} (n : ℕ) (s : Fin (n+2) → V) (r : R) :
    boundary R V n (Finsupp.single s r) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (s ∘ i.succAbove) r := by
  simp [boundary, LinearMap.sum_apply]

@[simp] lemma cone_single {V : Type v} (v : V) (n : ℕ) (s : Fin (n+1) → V) (r : R) :
    cone R v n (Finsupp.single s r) = Finsupp.single (Fin.cons v s) r := by
  simp [cone]

@[simp] lemma map_single {V W : Type v} (f : V → W) (n : ℕ)
    (s : Fin (n+1) → V) (r : R) :
    map R f n (Finsupp.single s r) = Finsupp.single (f ∘ s) r := by
  simp [map]

lemma remove_cons_zero {V : Type v} (v : V) {n : ℕ} (s : Fin (n+1) → V) :
    Fin.cons v s ∘ (0 : Fin (n+2)).succAbove = s := by
  funext i
  simp

lemma remove_cons_succ {V : Type v} (v : V) {n : ℕ} (s : Fin (n+2) → V)
    (i : Fin (n+2)) :
    Fin.cons v s ∘ i.succ.succAbove = Fin.cons v (s ∘ i.succAbove) := by
  exact Fin.cons_comp_succ_succAbove v s i

/-- The augmented cone formula in positive degrees. -/
theorem boundary_cone {V : Type v} (v : V) (n : ℕ) :
    (boundary R V (n+1)).comp (cone R v (n+1)) +
      (cone R v n).comp (boundary R V n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s r
  simp only [LinearMap.add_apply, LinearMap.comp_apply, cone_single, boundary_single,
    map_sum, map_zsmul, LinearMap.id_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, remove_cons_zero,
    Fin.val_succ, remove_cons_succ, pow_succ, mul_smul, neg_one_zsmul, smul_neg,
    Finset.sum_neg_distrib]
  abel

/-- In degree zero the second term is exactly the augmentation at the apex. -/
theorem boundary_cone_zero {V : Type v} (v : V) (s : Fin 1 → V) (r : R) :
    boundary R V 0 (cone R v 0 (Finsupp.single s r)) =
      Finsupp.single s r - Finsupp.single (fun _ : Fin 1 => v) r := by
  rw [cone_single, boundary_single, Fin.sum_univ_two]
  have h₁ : Fin.cons v s ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 => v := by
    funext i
    fin_cases i
    rfl
  simp [h₁, sub_eq_add_neg]

/-- Every positive-degree cycle has an explicit finite filling. -/
theorem fill_cycle {V : Type v} (v : V) (n : ℕ) (c : Chain R V (n+1))
    (hc : boundary R V n c = 0) :
    boundary R V (n+1) (cone R v (n+1) c) = c := by
  have h := LinearMap.congr_fun (boundary_cone R v n) c
  simpa [hc] using h

/-- A fixed cone commutes with vertex maps carrying its apex to the new apex. -/
theorem map_cone {V W : Type v} (f : V → W) (v : V) (n : ℕ) :
    (map R f (n+1)).comp (cone R v n) =
      (cone R (f v) n).comp (map R f n) := by
  apply Finsupp.lhom_ext
  intro s r
  simp only [LinearMap.comp_apply, cone_single, map_single]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Arbitrary vertex maps commute with signed face deletion. -/
theorem map_boundary {V W : Type v} (f : V → W) (n : ℕ) :
    (map R f n).comp (boundary R V n) =
      (boundary R W n).comp (map R f (n+1)) := by
  apply Finsupp.lhom_ext
  intro s r
  simp only [LinearMap.comp_apply, boundary_single, map_single, map_sum, map_zsmul]
  rfl

end VertexChains

/-- The defect to be filled, using the exact upstream maps. -/
def defect (X Y : TopCat.{w}) (n : ℕ) :
    Chains R (productSpace X Y) n →ₗ[R] Chains R (productSpace X Y) n :=
  (shuffle R X Y n).comp (aw R X Y n) - LinearMap.id

lemma defect_boundary (X Y : TopCat.{w}) (n : ℕ) :
    (boundary R R (productSpace X Y) n).comp (defect R X Y (n+1)) =
      (defect R X Y n).comp (boundary R R (productSpace X Y) n) := by
  simp only [defect, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id,
    LinearMap.id_comp]
  rw [← LinearMap.comp_assoc, P202.ShuffleChains.chain_identity R X Y n,
    LinearMap.comp_assoc, P202.AlexanderWhitney.chain_identity R X Y n,
    LinearMap.comp_assoc]

lemma defect_natural {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (((chainMap R R (productMap f g)).f n).hom).comp (defect R X Y n) =
      (defect R X' Y' n).comp (((chainMap R R (productMap f g)).f n).hom) := by
  simp only [defect, LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_id,
    LinearMap.id_comp]
  rw [← LinearMap.comp_assoc, P202.ShuffleChains.naturality R f g n,
    LinearMap.comp_assoc, P202.AlexanderWhitney.naturality R f g n,
    LinearMap.comp_assoc]

/-- An affine simplex determined by a list of vertices of a product model. -/
def affineSimplex {X Y : TopCat.{w}} {p q k : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q)
    (v : Fin (k+1) → Fin (p+1) × Fin (q+1)) : Simplex (productSpace X Y) k :=
  (simplexEquiv (productSpace X Y) k).symm
    ⟨fun z => (simplexEquiv X p σ (z.map (fun j => (v j).1)),
      simplexEquiv Y q τ (z.map (fun j => (v j).2))),
      ((simplexEquiv X p σ).continuous.comp
        (Convexity.StdSimplex.continuous_map ℝ _)).prodMk
      ((simplexEquiv Y q τ).continuous.comp
        (Convexity.StdSimplex.continuous_map ℝ _))⟩

@[simp] lemma affineSimplex_apply {X Y : TopCat.{w}} {p q k : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q)
    (v : Fin (k+1) → Fin (p+1) × Fin (q+1)) (z : StdSimplex k) :
    simplexEquiv (productSpace X Y) k (affineSimplex σ τ v) z =
      (simplexEquiv X p σ (z.map (fun j => (v j).1)),
        simplexEquiv Y q τ (z.map (fun j => (v j).2))) := by
  simp [affineSimplex]

lemma simplexEquiv_post {X Y : TopCat.{w}} (f : X ⟶ Y) {n : ℕ}
    (σ : Simplex X n) (z : StdSimplex n) :
    simplexEquiv Y n (postSimplex f n σ) z = f (simplexEquiv X n σ z) := rfl

lemma affineSimplex_face {X Y : TopCat.{w}} {p q k : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q)
    (v : Fin (k+2) → Fin (p+1) × Fin (q+1)) (i : Fin (k+2)) :
    face i (affineSimplex σ τ v) = affineSimplex σ τ (v ∘ i.succAbove) := by
  apply (simplexEquiv _ _).injective
  ext z
  rw [P202.SingularChains.simplexEquiv_face]
  simp only [ContinuousMap.comp_apply, affineSimplex_apply]
  change (simplexEquiv X p σ ((z.map i.succAbove).map _),
      simplexEquiv Y q τ ((z.map i.succAbove).map _)) = _
  simp only [Convexity.StdSimplex.map_map, Function.comp_def]

/-- Linear affine realization; it never introduces infinite chains. -/
def realize {X Y : TopCat.{w}} {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q) (k : ℕ) :
    VertexChains.Chain R (Fin (p+1) × Fin (q+1)) k →ₗ[R]
      Chains R (productSpace X Y) k :=
  Finsupp.lmapDomain R R (affineSimplex σ τ)

@[simp] lemma realize_single {X Y : TopCat.{w}} {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) (k : ℕ)
    (v : Fin (k+1) → Fin (p+1) × Fin (q+1)) (r : R) :
    realize R σ τ k (Finsupp.single v r) = Finsupp.single (affineSimplex σ τ v) r := by
  simp [realize]

lemma realize_boundary {X Y : TopCat.{w}} {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) (k : ℕ) :
    (boundary R R (productSpace X Y) k).comp (realize R σ τ (k+1)) =
      (realize R σ τ k).comp (VertexChains.boundary R _ k) := by
  apply Finsupp.lhom_ext
  intro v r
  change boundary R R (productSpace X Y) k
    (realize R σ τ (k+1) (Finsupp.single v r)) =
    realize R σ τ k (VertexChains.boundary R _ k (Finsupp.single v r))
  rw [realize_single, P202.SingularChains.boundary_single,
    VertexChains.boundary_single, map_sum]
  simp only [map_zsmul, realize_single, affineSimplex_face]

lemma affineSimplex_natural {X X' Y Y' : TopCat.{w}} {p q k : ℕ}
    (f : X ⟶ X') (g : Y ⟶ Y') (σ : Simplex X p) (τ : Simplex Y q)
    (v : Fin (k+1) → Fin (p+1) × Fin (q+1)) :
    postSimplex (productMap f g) k (affineSimplex σ τ v) =
      affineSimplex (postSimplex f p σ) (postSimplex g q τ) v := by
  apply (simplexEquiv _ _).injective
  ext z
  simp only [simplexEquiv_post, affineSimplex_apply]
  rfl

lemma realize_natural {X X' Y Y' : TopCat.{w}} {p q : ℕ}
    (f : X ⟶ X') (g : Y ⟶ Y') (σ : Simplex X p) (τ : Simplex Y q) (k : ℕ) :
    (((chainMap R R (productMap f g)).f k).hom).comp (realize R σ τ k) =
      realize R (postSimplex f p σ) (postSimplex g q τ) k := by
  apply Finsupp.lhom_ext
  intro v r
  change ((chainMap R R (productMap f g)).f k).hom
    (realize R σ τ k (Finsupp.single v r)) =
      realize R (postSimplex f p σ) (postSimplex g q τ) k (Finsupp.single v r)
  rw [realize_single, realize_single, P202.SingularChains.chainMap_single]
  change Finsupp.single (postSimplex _ k (affineSimplex σ τ v)) r = _
  rw [affineSimplex_natural]

/-- Vertices of a shuffle after the AW split. -/
def splitVertices {p q : ℕ} (s : LatticePath p q) :
    Fin (p+q+1) → Fin (p+q+1) × Fin (p+q+1) :=
  fun k => (⟨(s.horizontal k).val, by have := (s.horizontal k).isLt; omega⟩,
    ⟨p+(s.vertical k).val, by have := (s.vertical k).isLt; omega⟩)

lemma shuffle_interval {X Y : TopCat.{w}} {p q : ℕ}
    (σ : Simplex X (p+q)) (τ : Simplex Y (p+q)) (s : LatticePath p q) :
    shuffleSimplex s (interval σ 0 p (by omega)) (interval τ p q (by omega)) =
      affineSimplex σ τ (splitVertices s) := by
  apply (simplexEquiv _ _).injective
  ext z
  rw [P202.ShuffleChains.simplex_formula, affineSimplex_apply]
  rw [P202.AlexanderWhitney.interval_continuous, P202.AlexanderWhitney.interval_continuous]
  simp only [ContinuousMap.comp_apply]
  change (simplexEquiv X (p+q) σ ((z.map s.horizontal).map _),
    simplexEquiv Y (p+q) τ ((z.map s.vertical).map _)) = _
  simp only [Convexity.StdSimplex.map_map]
  apply Prod.ext
  · apply congrArg (simplexEquiv X (p+q) σ)
    apply congrArg (fun f : Fin (p+q+1) → Fin (p+q+1) => z.map f)
    funext k
    apply Fin.ext
    change 0 + (s.horizontal k).val = (s.horizontal k).val
    omega
  · rfl

/-- The signed universal sh-AW chain for one split. Only degrees are cast. -/
def splitChain (n p q : ℕ) (h : p+q=n) :
    VertexChains.Chain R (Fin (n+1) × Fin (n+1)) n := by
  subst n
  exact ∑ s : LatticePath p q, s.sign • Finsupp.single (splitVertices s) 1

lemma realize_splitChain {X Y : TopCat.{w}} (n p q : ℕ) (h : p+q=n)
    (σ : Simplex X n) (τ : Simplex Y n) :
    realize R σ τ n (splitChain R n p q h) =
      castChains R h (shuffleComponent R X Y p q
        (Finsupp.single (interval σ 0 p (by omega)) 1 ⊗ₜ[R]
          Finsupp.single (interval τ p q (by omega)) 1)) := by
  subst n
  rw [P202.ShuffleChains.component_formula]
  simp only [one_mul, one_smul, splitChain, map_sum, map_zsmul,
    realize_single, shuffle_interval, castChains, LinearMap.id_apply]

/-- The universal defect, before affine realization. -/
def formalDefect (n : ℕ) : VertexChains.Chain R (Fin (n+1) × Fin (n+1)) n :=
  (∑ i : Diagonal n, splitChain R n i.val.1 i.val.2 i.property) -
    Finsupp.single (fun k => (k,k)) 1

lemma affineSimplex_diagonal {X Y : TopCat.{w}} {n : ℕ}
    (s : Simplex (productSpace X Y) n) :
    affineSimplex (postSimplex (firstProjection X Y) n s)
      (postSimplex (secondProjection X Y) n s) (fun k => (k,k)) = s := by
  apply (simplexEquiv _ _).injective
  ext z
  simp only [affineSimplex_apply, simplexEquiv_post]
  rw [show z.map (fun j => j) = z from Convexity.StdSimplex.map_id z]
  rfl

lemma realize_formalDefect {X Y : TopCat.{w}} (n : ℕ)
    (s : Simplex (productSpace X Y) n) :
    realize R (postSimplex (firstProjection X Y) n s)
      (postSimplex (secondProjection X Y) n s) n (formalDefect R n) =
      defect R X Y n (Finsupp.single s 1) := by
  rw [formalDefect, map_sub, map_sum, realize_single, affineSimplex_diagonal]
  change _ = shuffle R X Y n (aw R X Y n (Finsupp.single s 1)) - Finsupp.single s 1
  simp only [shuffle, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [realize_splitChain, P202.AlexanderWhitney.formula]
  simp only [one_smul, awComponent]

/-- Apply universal affine coefficients to any product singular generator. -/
def onProduct (X Y : TopCat.{w}) (n k : ℕ)
    (c : VertexChains.Chain R (Fin (n+1) × Fin (n+1)) k) :
    Chains R (productSpace X Y) n →ₗ[R] Chains R (productSpace X Y) k :=
  Finsupp.linearCombination R (fun s =>
    realize R (postSimplex (firstProjection X Y) n s)
      (postSimplex (secondProjection X Y) n s) k c)

@[simp] lemma onProduct_single (X Y : TopCat.{w}) (n k : ℕ)
    (c : VertexChains.Chain R (Fin (n+1) × Fin (n+1)) k)
    (s : Simplex (productSpace X Y) n) (r : R) :
    onProduct R X Y n k c (Finsupp.single s r) = r •
      realize R (postSimplex (firstProjection X Y) n s)
        (postSimplex (secondProjection X Y) n s) k c := by
  exact Finsupp.linearCombination_single _ _ _

lemma onProduct_natural {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') (n k : ℕ)
    (c : VertexChains.Chain R (Fin (n+1) × Fin (n+1)) k) :
    (((chainMap R R (productMap f g)).f k).hom).comp (onProduct R X Y n k c) =
      (onProduct R X' Y' n k c).comp (((chainMap R R (productMap f g)).f n).hom) := by
  apply Finsupp.lhom_ext
  intro s r
  change ((chainMap R R (productMap f g)).f k).hom
    (onProduct R X Y n k c (Finsupp.single s r)) =
      onProduct R X' Y' n k c (((chainMap R R (productMap f g)).f n).hom (Finsupp.single s r))
  rw [onProduct_single, P202.SingularChains.chainMap_single, onProduct_single, map_smul]
  change r • Finsupp.mapDomain (postSimplex (productMap f g) k)
    (realize R (postSimplex (firstProjection X Y) n s)
      (postSimplex (secondProjection X Y) n s) k c) = r •
    realize R (postSimplex (firstProjection X' Y') n (postSimplex (productMap f g) n s))
      (postSimplex (secondProjection X' Y') n (postSimplex (productMap f g) n s)) k c
  apply congrArg (fun z : Chains R (productSpace X' Y') k => r • z)
  have h := LinearMap.congr_fun (realize_natural R f g
    (postSimplex (firstProjection X Y) n s)
    (postSimplex (secondProjection X Y) n s) k) c
  change Finsupp.mapDomain (postSimplex (productMap f g) k) _ = _ at h
  exact h.trans (congrArg₂ (fun σ τ => realize R σ τ k c) (by rfl) (by rfl))

/-- Reindex both model coordinates along an ordered face inclusion. -/
def modelFace {n : ℕ} (i : Fin (n+2)) :
    Fin (n+1) × Fin (n+1) → Fin (n+2) × Fin (n+2) :=
  fun v => (i.succAbove v.1, i.succAbove v.2)

def lowerBoundary (n : ℕ)
    (c : VertexChains.Chain R (Fin (n+1) × Fin (n+1)) (n+1)) :
    VertexChains.Chain R (Fin (n+2) × Fin (n+2)) (n+1) :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • VertexChains.map R (modelFace i) (n+1) c

/-- Universal affine fillings. This is an unconditional recursive definition;
its correctness is the homotopy identity to be established. -/
def filling (n : ℕ) : VertexChains.Chain R (Fin (n+1) × Fin (n+1)) (n+1) :=
  match n with
  | 0 => 0
  | n+1 => VertexChains.cone R ((0,0) : Fin (n+2) × Fin (n+2)) (n+1)
      (formalDefect R (n+1) - lowerBoundary R n (filling n))

/-- Candidate family from the fixed universal affine fillings. -/
def hom (X Y : TopCat.{w}) (n : ℕ) :
    Chains R (productSpace X Y) n →ₗ[R] Chains R (productSpace X Y) (n+1) :=
  onProduct R X Y n (n+1) (filling R n)

lemma hom_natural {X X' Y Y' : TopCat.{w}}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    (((chainMap R R (productMap f g)).f (n+1)).hom).comp (hom R X Y n) =
      (hom R X' Y' n).comp (((chainMap R R (productMap f g)).f n).hom) :=
  onProduct_natural R f g n (n+1) _

/-- The identity simplex on the finite real simplex, used only to test formal
coefficients; it adds no restrictions to the spaces of the theorem. -/
def model (n : ℕ) : TopCat.{0} := TopCat.of (StdSimplex n)

def modelSimplex (n : ℕ) : Simplex (model n) n :=
  (simplexEquiv (model n) n).symm (ContinuousMap.id _)

lemma realize_model_injective (p q k : ℕ) :
    Function.Injective (realize R (modelSimplex p) (modelSimplex q) k) := by
  apply Finsupp.mapDomain_injective
  intro v v' h
  funext j
  have hj := congrArg (fun s => simplexEquiv _ k s (Convexity.StdSimplex.single j)) h
  simp only [affineSimplex_apply, Convexity.StdSimplex.map_single] at hj
  change (Convexity.StdSimplex.single (v j).1, Convexity.StdSimplex.single (v j).2) =
    (Convexity.StdSimplex.single (v' j).1, Convexity.StdSimplex.single (v' j).2) at hj
  exact Prod.ext (Convexity.StdSimplex.single_injective (congrArg Prod.fst hj))
    (Convexity.StdSimplex.single_injective (congrArg Prod.snd hj))

lemma affineSimplex_modelFace {X Y : TopCat.{w}} {n k : ℕ}
    (σ : Simplex X (n+1)) (τ : Simplex Y (n+1)) (i : Fin (n+2))
    (v : Fin (k+1) → Fin (n+1) × Fin (n+1)) :
    affineSimplex σ τ (modelFace i ∘ v) = affineSimplex (face i σ) (face i τ) v := by
  apply (simplexEquiv _ _).injective
  ext z
  simp only [affineSimplex_apply]
  rw [P202.SingularChains.simplexEquiv_face, P202.SingularChains.simplexEquiv_face]
  simp only [ContinuousMap.comp_apply]
  change _ = (simplexEquiv X (n+1) σ ((z.map _).map i.succAbove),
    simplexEquiv Y (n+1) τ ((z.map _).map i.succAbove))
  simp only [Convexity.StdSimplex.map_map]
  rfl

lemma realize_modelFace {X Y : TopCat.{w}} {n : ℕ}
    (σ : Simplex X (n+1)) (τ : Simplex Y (n+1)) (i : Fin (n+2)) (k : ℕ) :
    (realize R σ τ k).comp (VertexChains.map R (modelFace i) k) =
      realize R (face i σ) (face i τ) k := by
  apply Finsupp.lhom_ext
  intro v r
  change realize R σ τ k (VertexChains.map R (modelFace i) k (Finsupp.single v r)) = _
  rw [VertexChains.map_single, realize_single, realize_single, affineSimplex_modelFace]

lemma onProduct_boundary (X Y : TopCat.{w}) (n : ℕ)
    (c : VertexChains.Chain R (Fin (n+1) × Fin (n+1)) (n+1))
    (s : Simplex (productSpace X Y) (n+1)) :
    onProduct R X Y n (n+1) c (boundary R R (productSpace X Y) n (Finsupp.single s 1)) =
      realize R (postSimplex (firstProjection X Y) (n+1) s)
        (postSimplex (secondProjection X Y) (n+1) s) (n+1) (lowerBoundary R n c) := by
  rw [P202.SingularChains.boundary_single, map_sum, lowerBoundary, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul, map_zsmul, onProduct_single, one_smul]
  have h := LinearMap.congr_fun (realize_modelFace R
    (postSimplex (firstProjection X Y) (n+1) s)
    (postSimplex (secondProjection X Y) (n+1) s) i (n+1)) c
  simp only [LinearMap.comp_apply] at h
  rw [h]
  rw [P202.AlexanderWhitney.post_face, P202.AlexanderWhitney.post_face]

lemma formalDefect_zero : formalDefect R 0 = 0 := by
  let : Unique (Diagonal 0) :=
    ⟨⟨⟨(0,0), rfl⟩⟩, by
      rintro ⟨⟨p,q⟩,h⟩
      apply Subtype.ext
      apply Prod.ext <;> dsimp at * <;> omega⟩
  let : Unique (LatticePath 0 0) :=
    ⟨⟨zeroLeft 0⟩, fun s => P202.ShuffleModel.zeroLeft_unique 0 s⟩
  simp only [formalDefect, Fintype.sum_unique]
  change splitChain R 0 0 0 rfl - Finsupp.single (fun k => (k,k)) 1 = 0
  simp only [splitChain, Fintype.sum_unique]
  change (zeroLeft 0).sign • Finsupp.single (splitVertices (zeroLeft 0)) (1:R) - _ = 0
  rw [P202.ShuffleModel.zeroLeft_sign, one_smul]
  have h : splitVertices (zeroLeft 0) = fun k : Fin 1 => (k,k) := by
    funext k
    fin_cases k
    rfl
  rw [h, sub_self]

lemma hom_zero (X Y : TopCat.{w}) : hom R X Y 0 = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  change onProduct R X Y 0 1 0 (Finsupp.single s r) = 0
  rw [onProduct_single, map_zero, smul_zero]

lemma defect_zero (X Y : TopCat.{w}) : defect R X Y 0 = 0 := by
  apply Finsupp.lhom_ext
  intro s r
  have h := realize_formalDefect R 0 s
  rw [formalDefect_zero, map_zero] at h
  rw [← Finsupp.smul_single_one s r, map_smul, ← h, smul_zero]
  rfl

/-- The lower term in the ordinary homotopy equation. -/
def previous (X Y : TopCat.{w}) (n : ℕ) :
    Chains R (productSpace X Y) n →ₗ[R] Chains R (productSpace X Y) n :=
  match n with
  | 0 => 0
  | n+1 => (hom R X Y n).comp (P202Specs.EZProductHomotopy.differential R (productSpace X Y) n)

/-- The formal defect remaining after the already chosen lower homotopy. -/
def remainder (n : ℕ) : VertexChains.Chain R (Fin (n+1) × Fin (n+1)) n :=
  match n with
  | 0 => formalDefect R 0
  | n+1 => formalDefect R (n+1) - lowerBoundary R n (filling R n)

lemma realize_remainder (X Y : TopCat.{w}) (n : ℕ)
    (s : Simplex (productSpace X Y) n) :
    realize R (postSimplex (firstProjection X Y) n s)
      (postSimplex (secondProjection X Y) n s) n (remainder R n) =
      defect R X Y n (Finsupp.single s 1) - previous R X Y n (Finsupp.single s 1) := by
  cases n with
  | zero => simpa only [remainder, previous, LinearMap.zero_apply, sub_zero] using
      realize_formalDefect R 0 s
  | succ n =>
    rw [remainder, map_sub, realize_formalDefect]
    congr 1
    exact (onProduct_boundary R X Y n (filling R n) s).symm

lemma identity_of_filling (n : ℕ)
    (h : VertexChains.boundary R _ n (filling R n) = remainder R n)
    (X Y : TopCat.{w}) :
    defect R X Y n =
      (P202Specs.EZProductHomotopy.differential R (productSpace X Y) n).comp (hom R X Y n) +
        previous R X Y n := by
  apply Finsupp.lhom_ext
  intro s r
  suffices hs : defect R X Y n (Finsupp.single s 1) =
      P202Specs.EZProductHomotopy.differential R (productSpace X Y) n (hom R X Y n (Finsupp.single s 1)) +
        previous R X Y n (Finsupp.single s 1) by
    simpa only [← Finsupp.smul_single_one s r, map_smul, smul_add,
      LinearMap.add_apply, LinearMap.comp_apply, P202Specs.EZProductHomotopy.differential]
      using congrArg (fun c : Chains R (productSpace X Y) n => r • c) hs
  have hb := LinearMap.congr_fun (realize_boundary R
    (postSimplex (firstProjection X Y) n s)
    (postSimplex (secondProjection X Y) n s) n) (filling R n)
  change P202Specs.EZProductHomotopy.differential R (productSpace X Y) n
    (realize R (postSimplex (firstProjection X Y) n s)
      (postSimplex (secondProjection X Y) n s) (n+1) (filling R n)) = _ at hb
  have hr := realize_remainder R X Y n s
  have he := hb.trans (congrArg (realize R (postSimplex (firstProjection X Y) n s)
    (postSimplex (secondProjection X Y) n s) n) h)
  have he' := he.trans hr
  change defect R X Y n (Finsupp.single s 1) =
    P202Specs.EZProductHomotopy.differential R (productSpace X Y) n
      (onProduct R X Y n (n+1) (filling R n) (Finsupp.single s 1)) + _
  rw [onProduct_single, one_smul]
  exact (eq_sub_iff_add_eq.mp he').symm

lemma first_affine_diagonal {X Y : TopCat.{w}} {n : ℕ}
    (σ : Simplex X n) (τ : Simplex Y n) :
    postSimplex (firstProjection X Y) n (affineSimplex σ τ (fun k => (k,k))) = σ := by
  apply (simplexEquiv _ _).injective
  ext z
  rw [simplexEquiv_post]
  change (simplexEquiv _ _ (affineSimplex σ τ (fun k => (k,k))) z).1 = _
  rw [affineSimplex_apply]
  change simplexEquiv X n σ (z.map (fun k => k)) = _
  rw [show z.map (fun k => k) = z from Convexity.StdSimplex.map_id z]

lemma second_affine_diagonal {X Y : TopCat.{w}} {n : ℕ}
    (σ : Simplex X n) (τ : Simplex Y n) :
    postSimplex (secondProjection X Y) n (affineSimplex σ τ (fun k => (k,k))) = τ := by
  apply (simplexEquiv _ _).injective
  ext z
  rw [simplexEquiv_post]
  change (simplexEquiv _ _ (affineSimplex σ τ (fun k => (k,k))) z).2 = _
  rw [affineSimplex_apply]
  change simplexEquiv Y n τ (z.map (fun k => k)) = _
  rw [show z.map (fun k => k) = z from Convexity.StdSimplex.map_id z]

open P202Specs.EZProductHomotopy (differential)

lemma previous_boundary (X Y : TopCat.{w}) (n : ℕ)
    (c : Chains R (productSpace X Y) (n+1)) :
    previous R X Y n (differential R (productSpace X Y) n c) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    change hom R X Y n (differential R (productSpace X Y) n
      (differential R (productSpace X Y) (n+1) c)) = 0
    have hd := LinearMap.congr_fun (P202.SingularChains.boundary_squared R R (productSpace X Y) n) c
    change differential R (productSpace X Y) n
      (differential R (productSpace X Y) (n+1) c) = 0 at hd
    rw [hd, map_zero]

lemma correction_cycle (X Y : TopCat.{w}) (n : ℕ)
    (h : defect R X Y n =
      (differential R (productSpace X Y) n).comp (hom R X Y n) + previous R X Y n)
    (c : Chains R (productSpace X Y) (n+1)) :
    differential R (productSpace X Y) n
      (defect R X Y (n+1) c - hom R X Y n (differential R (productSpace X Y) n c)) = 0 := by
  have hd := LinearMap.congr_fun (defect_boundary R X Y n) c
  change differential R (productSpace X Y) n (defect R X Y (n+1) c) =
    defect R X Y n (differential R (productSpace X Y) n c) at hd
  have hh := LinearMap.congr_fun h (differential R (productSpace X Y) n c)
  change defect R X Y n (differential R (productSpace X Y) n c) =
    differential R (productSpace X Y) n (hom R X Y n (differential R (productSpace X Y) n c)) +
      previous R X Y n (differential R (productSpace X Y) n c) at hh
  rw [previous_boundary, add_zero] at hh
  rw [map_sub]
  exact sub_eq_zero.mpr (hd.trans hh)

/-- At each step the affine remainder is a cycle. Faithful affine realization
in the convex model reduces this to the already proved lower identity. -/
lemma remainder_cycle (n : ℕ)
    (h : VertexChains.boundary R _ n (filling R n) = remainder R n) :
    VertexChains.boundary R _ n (remainder R (n+1)) = 0 := by
  let S := modelSimplex (n+1)
  let X := model (n+1)
  let s := affineSimplex S S (fun k => (k,k))
  let c : Chains R (productSpace X X) (n+1) := Finsupp.single s 1
  apply realize_model_injective R (n+1) (n+1) n
  rw [map_zero]
  have hb := LinearMap.congr_fun (realize_boundary R S S n) (remainder R (n+1))
  change differential R (productSpace X X) n (realize R S S (n+1) (remainder R (n+1))) =
    realize R S S n (VertexChains.boundary R _ n (remainder R (n+1))) at hb
  have hr := realize_remainder R X X (n+1) s
  dsimp only [s] at hr
  rw [first_affine_diagonal, second_affine_diagonal] at hr
  change realize R S S (n+1) (remainder R (n+1)) =
    defect R X X (n+1) c - hom R X X n (differential R (productSpace X X) n c) at hr
  exact hb.symm.trans ((congrArg (differential R (productSpace X X) n) hr).trans
    (correction_cycle R X X n (identity_of_filling R n h X X) c))

/-- The universal affine fillings satisfy every signed boundary equation. -/
theorem boundary_filling (n : ℕ) :
    VertexChains.boundary R _ n (filling R n) = remainder R n := by
  induction n with
  | zero => simp only [filling, remainder, formalDefect_zero, map_zero]
  | succ n ih =>
    change VertexChains.boundary R _ (n+1)
      (VertexChains.cone R ((0,0) : Fin (n+2) × Fin (n+2)) (n+1) (remainder R (n+1))) = _
    exact VertexChains.fill_cycle R _ n _ (remainder_cycle R n ih)

/-- Full ordinary chain identity for the constructed family. -/
theorem hom_identity (X Y : TopCat.{w}) (n : ℕ) :
    defect R X Y n =
      (differential R (productSpace X Y) n).comp (hom R X Y n) + previous R X Y n :=
  identity_of_filling R n (boundary_filling R n) X Y

section Smooth
variable {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]

/-- Taking a factor projection preserves the chart-local extension criterion. -/
lemma charts_fst {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N] (I : H → E) (J : K → F) {n : ℕ}
    (f : StdSimplex n → M × N)
    (hf : SmoothInCharts (H := ModelProd H K) (fun z => (I z.1, J z.2)) f) :
    SmoothInCharts I (fun z => (f z).1) := by
  refine ⟨continuous_fst.comp hf.1, ?_⟩
  intro z c hc hcz
  let d := chartAt K (f z).2
  have hcd : c.prod d ∈ atlas (ModelProd H K) (M × N) :=
    Set.mem_image2_of_mem hc (chart_mem_atlas K (f z).2)
  obtain ⟨U, hU, hz, G, hG, heq⟩ := hf.2 z (c.prod d) hcd
    ⟨hcz, mem_chart_source K (f z).2⟩
  refine ⟨U, hU, hz, fun a => (G a).1, hG.fst, ?_⟩
  intro x hx
  obtain ⟨hfx, hEq⟩ := heq x hx
  exact ⟨hfx.1, congrArg Prod.fst hEq⟩

lemma charts_snd {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N] (I : H → E) (J : K → F) {n : ℕ}
    (f : StdSimplex n → M × N)
    (hf : SmoothInCharts (H := ModelProd H K) (fun z => (I z.1, J z.2)) f) :
    SmoothInCharts J (fun z => (f z).2) := by
  refine ⟨continuous_snd.comp hf.1, ?_⟩
  intro z d hd hdz
  let c := chartAt H (f z).1
  have hcd : c.prod d ∈ atlas (ModelProd H K) (M × N) :=
    Set.mem_image2_of_mem (chart_mem_atlas H (f z).1) hd
  obtain ⟨U, hU, hz, G, hG, heq⟩ := hf.2 z (c.prod d) hcd
    ⟨mem_chart_source H (f z).1, hdz⟩
  refine ⟨U, hU, hz, fun a => (G a).2, hG.snd, ?_⟩
  intro x hx
  obtain ⟨hfx, hEq⟩ := heq x hx
  exact ⟨hfx.2, congrArg Prod.snd hEq⟩

lemma smooth_affineSimplex (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] {p q k : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q)
    (hσ : SmoothSimplex I X σ) (hτ : SmoothSimplex J Y τ)
    (v : Fin (k+1) → Fin (p+1) × Fin (q+1)) :
    SmoothSimplex (H := ModelProd H K) (fun z => (I z.1, J z.2))
      (productSpace X Y) (affineSimplex σ τ v) := by
  change SmoothInCharts _ _
  have he : (simplexEquiv _ k (affineSimplex σ τ v) : StdSimplex k → X × Y) =
      fun z => (simplexEquiv X p σ (z.map (fun j => (v j).1)),
        simplexEquiv Y q τ (z.map (fun j => (v j).2))) := by
    funext z
    exact affineSimplex_apply σ τ v z
  rw [he]
  exact P202.ShuffleModel.charts_pair I J _ _
    (P202.ShuffleChains.charts_pullback I _ hσ _)
    (P202.ShuffleChains.charts_pullback J _ hτ _)

lemma smooth_realize (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] {p q k : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q)
    (hσ : SmoothSimplex I X σ) (hτ : SmoothSimplex J Y τ)
    (c : VertexChains.Chain R (Fin (p+1) × Fin (q+1)) k) :
    realize R σ τ k c ∈ smoothChains R (H := ModelProd H K)
      (fun z => (I z.1, J z.2)) (productSpace X Y) k := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (smoothChains R _ _ k).add_mem hc hd
  | single v r =>
    rw [realize_single]
    exact Finsupp.single_mem_supported R r (smooth_affineSimplex I J X Y σ τ hσ hτ v)

lemma smooth_onProduct (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] (n k : ℕ)
    (a : VertexChains.Chain R (Fin (n+1) × Fin (n+1)) k)
    (c : Chains R (productSpace X Y) n)
    (hc : c ∈ smoothChains R (H := ModelProd H K)
      (fun z => (I z.1, J z.2)) (productSpace X Y) n) :
    onProduct R X Y n k a c ∈ smoothChains R (H := ModelProd H K)
      (fun z => (I z.1, J z.2)) (productSpace X Y) k := by
  apply P202.ShuffleModel.map_smoothChains R _ _ _ _ ?_ c hc
  intro σ hσ
  rw [onProduct_single, one_smul]
  exact smooth_realize R I J X Y
    (postSimplex (firstProjection X Y) n σ) (postSimplex (secondProjection X Y) n σ)
    (charts_fst I J _ hσ) (charts_snd I J _ hσ) a

lemma hom_smooth (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] (n : ℕ)
    (c : Chains R (productSpace X Y) n)
    (hc : c ∈ smoothChains R (H := ModelProd H K)
      (fun z => (I z.1, J z.2)) (productSpace X Y) n) :
    hom R X Y n c ∈ smoothChains R (H := ModelProd H K)
      (fun z => (I z.1, J z.2)) (productSpace X Y) (n+1) :=
  smooth_onProduct R I J X Y n (n+1) _ c hc

end Smooth
/-- The constructed natural family, with both ordinary endpoint identities. -/
def productHomotopy : P202Specs.EZProductHomotopy.ProductHomotopy.{u,w} R where
  hom := hom R
  zero X Y := by
    simpa only [defect, previous, add_zero] using hom_identity R X Y 0
  succ X Y n := by
    simpa only [defect, previous] using hom_identity R X Y (n+1)
  naturality := hom_natural R

/-- The same universal affine choices preserve chart-local smoothness. -/
theorem productHomotopy_smooth : (productHomotopy.{u,w} R).Smooth R := by
  intro E F H K _ _ _ _ _ _ I J X Y _ _ n c hc
  exact hom_smooth R I J X Y n c hc

/-- Product-side Eilenberg–Zilber, natural for arbitrary continuous maps and
with the very same homotopy preserving smooth singular chains. -/
theorem naturalHomotopy : P202Specs.EZProductHomotopy.naturalHomotopy_type.{u,w} := by
  intro R _
  exact ⟨productHomotopy R, productHomotopy_smooth R⟩

end P202.EZProductHomotopy
