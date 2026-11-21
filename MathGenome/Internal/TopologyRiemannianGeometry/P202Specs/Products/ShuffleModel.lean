import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.AlexanderWhitney
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! The explicit, finite, oriented shuffle construction on the shared singular
chains. A path is recorded by its two monotone vertex coordinates; their sum
is the vertex number. Thus every edge is one horizontal or vertical step. -/
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct ContDiff
namespace P202Specs.ShuffleModel
open P202Specs.SingularChains P202Specs.AlexanderWhitney
universe u w

abbrev LatticePath (p q : ℕ) :=
  {f : (Fin (p+q+1) →o Fin (p+1)) × (Fin (p+q+1) →o Fin (q+1)) //
    ∀ k, (f.1 k).val + (f.2 k).val = k.val}

namespace LatticePath
variable {p q : ℕ}
instance : Finite (LatticePath p q) :=
  Finite.of_injective (fun s : LatticePath p q =>
    ((fun k => s.val.1 k), (fun k => s.val.2 k))) (by
      intro s t h
      apply Subtype.ext
      exact Prod.ext (DFunLike.ext' (congrArg Prod.fst h))
        (DFunLike.ext' (congrArg Prod.snd h)))
noncomputable instance : Fintype (LatticePath p q) := Fintype.ofFinite _
abbrev horizontal (s : LatticePath p q) := s.val.1
abbrev vertical (s : LatticePath p q) := s.val.2

lemma rank (s : LatticePath p q) (k : Fin (p+q+1)) :
    (s.horizontal k).val + (s.vertical k).val = k.val := s.property k

lemma step (s : LatticePath p q) (k : Fin (p+q)) :
    ((s.horizontal k.succ).val = (s.horizontal k.castSucc).val + 1 ∧
      s.vertical k.succ = s.vertical k.castSucc) ∨
    (s.horizontal k.succ = s.horizontal k.castSucc ∧
      (s.vertical k.succ).val = (s.vertical k.castSucc).val + 1) := by
  have h₀ := s.rank k.castSucc
  have h₁ := s.rank k.succ
  have hx := s.horizontal.monotone k.castSucc_le_succ
  have hy := s.vertical.monotone k.castSucc_le_succ
  simp only [Fin.le_def] at hx hy
  simp only [Fin.val_castSucc, Fin.val_succ] at h₀ h₁
  by_cases h : (s.horizontal k.succ).val = (s.horizontal k.castSucc).val + 1
  · exact Or.inl ⟨h, Fin.ext (by omega)⟩
  · exact Or.inr ⟨Fin.ext (by omega), by omega⟩

/-- The label of a step in the reference ordering H₀,…,Hₚ₋₁,V₀,…,V_q₋₁. -/
def stepLabel (s : LatticePath p q) (k : Fin (p+q)) : Fin (p+q) :=
  if h : (s.horizontal k.succ).val = (s.horizontal k.castSucc).val + 1 then
    ⟨(s.horizontal k.castSucc).val, by have := (s.horizontal k.succ).isLt; omega⟩
  else
    ⟨p + (s.vertical k.castSucc).val, by
      have hs := s.step k
      have := (s.vertical k.succ).isLt
      rcases hs with hs | hs <;> omega⟩

lemma stepLabel_injective (s : LatticePath p q) : Function.Injective s.stepLabel := by
  intro i j hij
  wlog h : i ≤ j generalizing i j
  · exact (this hij.symm (le_of_not_ge h)).symm
  by_contra hne
  have hlt : i < j := lt_of_le_of_ne h hne
  have hle : i.succ ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    have : i.val < j.val := hlt
    omega
  have hx := s.horizontal.monotone hle
  have hy := s.vertical.monotone hle
  have hi := s.step i
  have hj := s.step j
  have hxi := (s.horizontal i.succ).isLt
  have hxj := (s.horizontal j.succ).isLt
  simp only [Fin.le_def] at hx hy
  have he := congrArg Fin.val hij
  simp only [stepLabel] at he
  split at he <;> split at he <;> simp only [Fin.val_mk] at he
  all_goals rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp only [Fin.ext_iff] at hi hj <;> omega

/-- The actual permutation of reference step labels, read in path order. -/
def permutation (s : LatticePath p q) : Equiv.Perm (Fin (p+q)) :=
  Equiv.ofBijective s.stepLabel ((Finite.injective_iff_bijective).mp s.stepLabel_injective)

/-- Permutation sign relative to all horizontal steps followed by all vertical steps. -/
def sign (s : LatticePath p q) : ℤ := (Equiv.Perm.sign s.permutation : ℤˣ)

end LatticePath

abbrev StdSimplex (n : ℕ) := Convexity.StdSimplex ℝ (Fin (n+1))

/-- Affine parametrization whose ordered vertices are exactly the path vertices. -/
def parametrization {p q : ℕ} (s : LatticePath p q) :
    C(StdSimplex (p+q), StdSimplex p × StdSimplex q) :=
  ⟨fun z => (z.map s.horizontal, z.map s.vertical),
    (Convexity.StdSimplex.continuous_map ℝ s.horizontal).prodMk
      (Convexity.StdSimplex.continuous_map ℝ s.vertical)⟩

/-- Push the affine path simplex forward by the two given singular simplices. -/
def shuffleSimplex {X Y : TopCat.{w}} {p q : ℕ} (s : LatticePath p q)
    (σ : Simplex X p) (τ : Simplex Y q) : Simplex (productSpace X Y) (p+q) :=
  (simplexEquiv (productSpace X Y) (p+q)).symm
    ⟨fun z => (simplexEquiv X p σ (parametrization s z).1,
      simplexEquiv Y q τ (parametrization s z).2),
      ((simplexEquiv X p σ).continuous.comp
        (continuous_fst.comp (parametrization s).continuous)).prodMk
      ((simplexEquiv Y q τ).continuous.comp
        (continuous_snd.comp (parametrization s).continuous))⟩

/-- The unique path when the first factor has dimension zero. -/
def zeroLeft (q : ℕ) : LatticePath 0 q :=
  ⟨(⟨fun _ => 0, by intro i j h; rfl⟩,
      ⟨fun k => ⟨k.val, by omega⟩, by intro i j h; exact h⟩), by intro k; change 0 + k.val = k.val; omega⟩

/-- The unique path when the second factor has dimension zero. -/
def zeroRight (p : ℕ) : LatticePath p 0 :=
  ⟨(⟨fun k => ⟨k.val, by omega⟩, by intro i j h; exact h⟩,
      ⟨fun _ => 0, by intro i j h; rfl⟩), by intro k; change k.val + 0 = k.val; omega⟩

abbrev Ambient (n : ℕ) := Fin (n+1) → ℝ

def weights {n : ℕ} (z : StdSimplex n) : Ambient n := z.weights

/-- A linear extension of barycentric pushforward, defined on the entire ambient
vector space. Thus it is available across every boundary face and corner. -/
def ambientMap {m n : ℕ} (f : Fin (m+1) → Fin (n+1)) (a : Ambient m) : Ambient n :=
  fun i => ∑ k with f k = i, a k

def ambientParametrization {p q : ℕ} (s : LatticePath p q)
    (a : Ambient (p+q)) : Ambient p × Ambient q :=
  (ambientMap s.horizontal a, ambientMap s.vertical a)

/-- Local ambient smooth extensions, including all boundary faces and corners.
Applied in a manifold chart this is the smooth-singular-simplex criterion. -/
def SmoothAtCorners {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : StdSimplex n → E) : Prop :=
  ∀ z, ∃ (U : Set (Ambient n)), IsOpen U ∧ weights z ∈ U ∧
    ∃ F : Ambient n → E, ContDiffOn ℝ ∞ F U ∧
      ∀ x : StdSimplex n, weights x ∈ U → F (weights x) = f x

/-- Ambient coordinates of the affine path cell. -/
def cell {p q : ℕ} (s : LatticePath p q) : Set (Ambient p × Ambient q) :=
  Set.range (fun z : StdSimplex (p+q) =>
    (weights (parametrization s z).1, weights (parametrization s z).2))

/-- Ordered vertices of the ambient path cell. -/
def vertex {p q : ℕ} (s : LatticePath p q) (k : Fin (p+q+1)) :
    Ambient p × Ambient q :=
  (weights (Convexity.StdSimplex.single (s.horizontal k)),
    weights (Convexity.StdSimplex.single (s.vertical k)))

/-- Shared product vertices, the canonical face data for two path cells. -/
def commonVertices {p q : ℕ} (s t : LatticePath p q) : Set (Ambient p × Ambient q) :=
  Set.range (vertex s) ∩ Set.range (vertex t)

/-- Product orientation coordinates: the successive edges of the first standard
simplex followed by those of the second. Tail sums send these edges to the
positively ordered coordinate vectors. -/
def productCoordinates (p q : ℕ) (a : Ambient p × Ambient q) : Fin (p+q) → ℝ :=
  fun k => if k.val < p then ∑ j : Fin (p+1) with k.val < j.val, a.1 j
    else ∑ j : Fin (q+1) with k.val-p < j.val, a.2 j

/-- Columns from the initial product vertex to each subsequent path vertex. -/
def orientationMatrix {p q : ℕ} (s : LatticePath p q) :
    Matrix (Fin (p+q)) (Fin (p+q)) ℝ :=
  fun i j => productCoordinates p q (vertex s j.succ) i -
    productCoordinates p q (vertex s 0) i

variable (R : Type u) [CommRing R]

/-- Signed finite chain on a pair of basis simplices. -/
def shuffleGenerator {X Y : TopCat.{w}} {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) : Chains R (productSpace X Y) (p+q) :=
  ∑ s : LatticePath p q, s.sign • Finsupp.single (shuffleSimplex s σ τ) 1

/-- Linear extension using the actual tensor product of the singular bases. -/
def shuffleComponent (X Y : TopCat.{w}) (p q : ℕ) :
    Summand R X Y p q →ₗ[R] Chains R (productSpace X Y) (p+q) :=
  ((Finsupp.basisSingleOne : Module.Basis (Simplex X p) R (Chains R X p)).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (Simplex Y q) R (Chains R Y q))).constr R
    (fun st => shuffleGenerator R st.1 st.2)

/-- Transport only the grading, without changing a coefficient or simplex. -/
def castChains {X : TopCat.{w}} {n m : ℕ} (h : n=m) : Chains R X n →ₗ[R] Chains R X m :=
  by subst m; exact LinearMap.id

/-- Sum over the finite grading diagonal of the ordinary total tensor complex. -/
def shuffle (X Y : TopCat.{w}) (n : ℕ) :
    Total R X Y n →ₗ[R] Chains R (productSpace X Y) n :=
  ∑ i : Diagonal n, (castChains R i.property).comp
    ((shuffleComponent R X Y i.val.1 i.val.2).comp (LinearMap.proj i))


/-- Local extensions in every target chart containing the image point. `I`
gives the model's Euclidean coordinates (use `id` for an ordinary smooth
manifold, or its model-with-corners inclusion). Neighborhoods and extensions
can vary with both the point and the chart; the simplex need not fit in one
chart. This statement also applies to finite-dimensional smooth manifolds. -/
def SmoothInCharts {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    (I : H → E) {n : ℕ} (f : StdSimplex n → M) : Prop :=
  Continuous f ∧ ∀ z, ∀ c ∈ atlas H M, f z ∈ c.source →
    ∃ (U : Set (Ambient n)), IsOpen U ∧ weights z ∈ U ∧
      ∃ F : Ambient n → E, ContDiffOn ℝ ∞ F U ∧
        ∀ x : StdSimplex n, weights x ∈ U →
          f x ∈ c.source ∧ F (weights x) = I (c (f x))

/-- Expose the ordinary product chart structure through the shared `TopCat`
product wrapper, without changing its topology or its charts. -/
instance productSpaceChartedSpace {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y] :
    ChartedSpace (ModelProd H K) (productSpace X Y) :=
  inferInstanceAs (ChartedSpace (ModelProd H K) (X × Y))

/-- The chart-local corner criterion on the shared continuous simplex. -/
def SmoothSimplex {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : H → E) (X : TopCat.{w}) [ChartedSpace H X]
    {n : ℕ} (σ : Simplex X n) : Prop :=
  SmoothInCharts I (simplexEquiv X n σ)

/-- This is a submodule of the original finite chains, with precisely the
smooth simplices in its support. It introduces no locally finite chains. -/
def smoothChains {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : H → E) (X : TopCat.{w}) [ChartedSpace H X]
    (n : ℕ) : Submodule R (Chains R X n) :=
  Finsupp.supported R R {σ | SmoothSimplex I X σ}

/-- The finite diagonal tensor module on the finite smooth-chain submodules. -/
abbrev SmoothTotal {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F) (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    (n : ℕ) :=
  (i : Diagonal n) → smoothChains R I X i.val.1 ⊗[R] smoothChains R J Y i.val.2

def smoothTotalInclusion {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F) (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    (n : ℕ) : SmoothTotal R I J X Y n →ₗ[R] Total R X Y n where
  toFun z i := TensorProduct.map (smoothChains R I X i.val.1).subtype
    (smoothChains R J Y i.val.2).subtype (z i)
  map_add' z z' := by ext i; exact map_add _ _ _
  map_smul' r z := by
    ext i
    change TensorProduct.map _ _ (r • z i) = r • _
    exact map_smul _ _ _

/-! Full independent expected types and canonical values. These are definitions
of propositions, without assumed boundary or triangulation certificates. -/

def shuffleComponent_type := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (p q : ℕ),
    Summand R X Y p q →ₗ[R] Chains R (productSpace X Y) (p+q)

abbrev shuffleComponent_value := @shuffleComponent

def shuffle_type := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (n : ℕ),
    Total R X Y n →ₗ[R] Chains R (productSpace X Y) n

abbrev shuffle_value := @shuffle

def path_initial_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q),
  s.horizontal 0 = 0 ∧ s.vertical 0 = 0

def path_terminal_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q),
  s.horizontal (Fin.last (p+q)) = Fin.last p ∧
      s.vertical (Fin.last (p+q)) = Fin.last q

def path_step_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q) (k : Fin (p+q)),
  ((s.horizontal k.succ).val = (s.horizontal k.castSucc).val + 1 ∧
      s.vertical k.succ = s.vertical k.castSucc) ∨
    (s.horizontal k.succ = s.horizontal k.castSucc ∧
      (s.vertical k.succ).val = (s.vertical k.castSucc).val + 1)

def parametrization_vertex_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q) (k : Fin (p+q+1)),
  parametrization s (Convexity.StdSimplex.single k) =
      (Convexity.StdSimplex.single (s.horizontal k),
        Convexity.StdSimplex.single (s.vertical k))

def parametrization_weights_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q) (z : StdSimplex (p+q)),
  (parametrization s z).1.weights = z.weights.mapDomain s.horizontal ∧
      (parametrization s z).2.weights = z.weights.mapDomain s.vertical

def simplex_formula_type : Prop := ∀ {X Y : TopCat.{w}} {p q : ℕ} (s : LatticePath p q)
    (σ : Simplex X p) (τ : Simplex Y q) (z : StdSimplex (p+q)),
  simplexEquiv (productSpace X Y) (p+q) (shuffleSimplex s σ τ) z =
      (simplexEquiv X p σ (z.map s.horizontal),
        simplexEquiv Y q τ (z.map s.vertical))

def component_formula_type : Prop := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (p q : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) (r t : R),
  shuffleComponent R X Y p q (Finsupp.single σ r ⊗ₜ[R] Finsupp.single τ t) =
      (r*t) • ∑ s : LatticePath p q, s.sign • Finsupp.single (shuffleSimplex s σ τ) 1

def component_natural_type : Prop := ∀ (R : Type u) [CommRing R] {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p q : ℕ),
  (((chainMap R R (productMap f g)).f (p+q)).hom).comp
      (shuffleComponent R X Y p q) =
    (shuffleComponent R X' Y' p q).comp
      (TensorProduct.map ((chainMap R R f).f p).hom ((chainMap R R g).f q).hom)

def naturality_type : Prop := ∀ (R : Type u) [CommRing R] {X X' Y Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ),
  (((chainMap R R (productMap f g)).f n).hom).comp (shuffle R X Y n) =
      (shuffle R X' Y' n).comp (totalMap R f g n)

def component_zero_left_type : Prop := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (q : ℕ)
    (σ : Simplex X 0) (τ : Simplex Y q),
  shuffleComponent R X Y 0 q (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)) =
      Finsupp.single (shuffleSimplex (zeroLeft q) σ τ) 1

def component_zero_right_type : Prop := ∀ (R : Type u) [CommRing R] (X Y : TopCat.{w}) (p : ℕ)
    (σ : Simplex X p) (τ : Simplex Y 0),
  shuffleComponent R X Y p 0 (Finsupp.single σ (1:R) ⊗ₜ[R] Finsupp.single τ (1:R)) =
      Finsupp.single (shuffleSimplex (zeroRight p) σ τ) 1

def ambientParametrization_smooth_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q),
  ContDiff ℝ ∞ (ambientParametrization s)

def ambientParametrization_weights_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q)
    (z : StdSimplex (p+q)),
  ambientParametrization s (weights z) =
      (weights (parametrization s z).1, weights (parametrization s z).2)

def smooth_pullback_type : Prop := ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m n : ℕ} (f : StdSimplex n → E) (hf : SmoothAtCorners f)
    (θ : Fin (m+1) → Fin (n+1)),
  SmoothAtCorners (fun z : StdSimplex m => f (z.map θ))

def smooth_shuffle_type : Prop := ∀ {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p q : ℕ}
    (f : StdSimplex p → E) (g : StdSimplex q → F)
    (hf : SmoothAtCorners f) (hg : SmoothAtCorners g) (s : LatticePath p q),
  SmoothAtCorners (fun z : StdSimplex (p+q) =>
      (f (parametrization s z).1, g (parametrization s z).2))


def total_formula_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (n : ℕ) (z : Total R X Y n),
  shuffle R X Y n z = ∑ i : Diagonal n, castChains R i.property
    (shuffleComponent R X Y i.val.1 i.val.2 (z i))

def permutation_sign_type : Prop := ∀ {p q : ℕ} (s : LatticePath p q),
  (∀ k, s.permutation k = s.stepLabel k) ∧
    s.sign = ((Equiv.Perm.sign s.permutation : ℤˣ) : ℤ)

def zeroLeft_unique_type : Prop := ∀ (q : ℕ) (s : LatticePath 0 q), s = zeroLeft q

def zeroRight_unique_type : Prop := ∀ (p : ℕ) (s : LatticePath p 0), s = zeroRight p

def zeroLeft_sign_type : Prop := ∀ q : ℕ, (zeroLeft q).sign = 1

def zeroRight_sign_type : Prop := ∀ p : ℕ, (zeroRight p).sign = 1

def ambientMap_smooth_type : Prop := ∀ {m n : ℕ} (f : Fin (m+1) → Fin (n+1)),
  ContDiff ℝ ∞ (ambientMap f)

def face_ambient_extension_type : Prop := ∀ {n : ℕ} (i : Fin (n+2)),
  ContDiff ℝ ∞ (ambientMap i.succAbove) ∧
    ∀ z : StdSimplex n, ambientMap i.succAbove (weights z) = weights (faceInclusion i z)

section ChartTypes

/-- Pullback is local in the target charts and valid at all corners. -/
def charts_pullback_type : Prop := ∀ {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (I : H → E) {m n : ℕ} (f : StdSimplex n → M) (hf : SmoothInCharts I f)
    (θ : Fin (m+1) → Fin (n+1)),
  SmoothInCharts I (fun z : StdSimplex m => f (z.map θ))

def charts_shuffle_type : Prop := ∀ {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace K N] (I : H → E) (J : K → F) {p q : ℕ}
    (f : StdSimplex p → M) (g : StdSimplex q → N)
    (hf : SmoothInCharts I f) (hg : SmoothInCharts J g) (s : LatticePath p q),
  SmoothInCharts (H := ModelProd H K) (fun h => (I h.1, J h.2))
    (fun z : StdSimplex (p+q) => (f (parametrization s z).1, g (parametrization s z).2))

def smooth_face_type : Prop := ∀ {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : H → E) (X : TopCat.{w}) [ChartedSpace H X]
    {n : ℕ} (σ : Simplex X (n+1)) (hσ : SmoothSimplex I X σ) (i : Fin (n+2)),
  SmoothSimplex I X (face i σ)

def smooth_boundary_type : Prop := ∀ (R : Type u) [CommRing R] {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : H → E) (X : TopCat.{w}) [ChartedSpace H X] (n : ℕ)
    (c : Chains R X (n+1)) (hc : c ∈ smoothChains R I X (n+1)),
  boundary R R X n c ∈ smoothChains R I X n

def smooth_simplex_type : Prop := ∀ {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F)
    (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    {p q : ℕ} (σ : Simplex X p) (τ : Simplex Y q)
    (hσ : SmoothSimplex I X σ) (hτ : SmoothSimplex J Y τ) (s : LatticePath p q),
  SmoothSimplex (H := ModelProd H K) (fun h => (I h.1, J h.2))
    (productSpace X Y) (shuffleSimplex s σ τ)

def smooth_component_type : Prop := ∀ (R : Type u) [CommRing R] {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F) (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    (p q : ℕ) (a : smoothChains R I X p) (b : smoothChains R J Y q),
  shuffleComponent R X Y p q (a.val ⊗ₜ[R] b.val) ∈
    smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2)) (productSpace X Y) (p+q)
/-- Existence of the actual restriction of the prescribed tensor map. -/
def smooth_restriction_type : Prop := ∀ (R : Type u) [CommRing R] {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F) (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    (p q : ℕ),
  ∃ L : (smoothChains R I X p ⊗[R] smoothChains R J Y q) →ₗ[R]
      smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2)) (productSpace X Y) (p+q),
    (smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2))
      (productSpace X Y) (p+q)).subtype.comp L =
    (shuffleComponent R X Y p q).comp
      (TensorProduct.map (smoothChains R I X p).subtype (smoothChains R J Y q).subtype)

/-- The full finite-diagonal map restricts as well, with the identical
underlying continuous singular chain. -/
def smooth_total_restriction_type : Prop := ∀ (R : Type u) [CommRing R] {E F H K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
    (I : H → E) (J : K → F) (X Y : TopCat.{w}) [ChartedSpace H X] [ChartedSpace K Y]
    (n : ℕ),
  ∃ L : SmoothTotal R I J X Y n →ₗ[R]
      smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2)) (productSpace X Y) n,
    (smoothChains R (H := ModelProd H K) (fun h => (I h.1, J h.2))
      (productSpace X Y) n).subtype.comp L =
    (shuffle R X Y n).comp (smoothTotalInclusion R I J X Y n)

end ChartTypes

end P202Specs.ShuffleModel
