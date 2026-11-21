import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleTriangulation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.ShuffleBoundary

/-! Independent specification of the external product. All objects are the
canonical finite singular-chain shuffle model shared by the boundary and
geometry results. No boundary or triangulation certificate is assumed here. -/
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial TensorProduct ContDiff
namespace P202Specs.ShuffleChains
open P202Specs.SingularChains P202Specs.AlexanderWhitney
universe u w

export P202Specs.ShuffleModel (LatticePath StdSimplex parametrization
  shuffleSimplex zeroLeft zeroRight Ambient weights ambientMap
  ambientParametrization SmoothAtCorners cell vertex commonVertices
  productCoordinates orientationMatrix shuffleGenerator shuffleComponent
  castChains shuffle SmoothInCharts SmoothSimplex smoothChains SmoothTotal
  smoothTotalInclusion)

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


/-- This is the tensor boundary identity on the ordinary complex in every
positive total degree. No augmentation is inserted at degree zero. -/
def chain_identity_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}) (n : ℕ),
  (boundary R R (productSpace X Y) n).comp (shuffle R X Y (n+1)) =
    (shuffle R X Y n).comp (totalBoundary R X Y n)

/-- Geometric triangulation, including the full common-face property. -/
def triangulation_type : Prop := ∀ (p q : ℕ),
  (∀ s : LatticePath p q, Function.Injective (parametrization s)) ∧
  (∀ z : StdSimplex p × StdSimplex q,
    ∃ (s : LatticePath p q) (x : StdSimplex (p+q)), parametrization s x = z) ∧
  (∀ s t : LatticePath p q,
    cell s ∩ cell t = convexHull ℝ (Set.range (vertex s) ∩ Set.range (vertex t)))

/-- The ordered path simplex has precisely the stipulated product orientation. -/
def orientation_type : Prop := ∀ (p q : ℕ) (s : LatticePath p q),
  Matrix.det (orientationMatrix s) = (s.sign : ℝ)

/-- Packaging the specified linear maps into the genuine external product
chain map from the accepted tensor complex to the shared singular complex. -/
def chain_map_realization_type : Prop := ∀ (R : Type u) [CommRing R]
    (X Y : TopCat.{w}),
  ∃ F : tensorComplex R X Y ⟶ complex R R (productSpace X Y),
    ∀ n, F.f n = ModuleCat.ofHom (shuffle R X Y n)


/-- The corner criterion is local in target charts, and the finite smooth
chains form a boundary-stable submodule. The restricted shuffle has the exact
same underlying continuous singular chain. -/
abbrev permutation_sign_type := P202Specs.ShuffleModel.permutation_sign_type

abbrev face_ambient_extension_type := P202Specs.ShuffleModel.face_ambient_extension_type

abbrev charts_pullback_type.{v0, v1, v2} := P202Specs.ShuffleModel.charts_pullback_type.{v0, v1, v2}

abbrev charts_shuffle_type.{v0, v1, v2, v3, v4, v5} := P202Specs.ShuffleModel.charts_shuffle_type.{v0, v1, v2, v3, v4, v5}

abbrev smooth_face_type.{v0, v1, v2} := P202Specs.ShuffleModel.smooth_face_type.{v0, v1, v2}

abbrev smooth_boundary_type.{v0, v1, v2, v3} := P202Specs.ShuffleModel.smooth_boundary_type.{v0, v1, v2, v3}

abbrev smooth_simplex_type.{v0, v1, v2, v3, v4} := P202Specs.ShuffleModel.smooth_simplex_type.{v0, v1, v2, v3, v4}

abbrev smooth_restriction_type.{v0, v1, v2, v3, v4, v5} := P202Specs.ShuffleModel.smooth_restriction_type.{v0, v1, v2, v3, v4, v5}

abbrev smooth_total_restriction_type.{v0, v1, v2, v3, v4, v5} := P202Specs.ShuffleModel.smooth_total_restriction_type.{v0, v1, v2, v3, v4, v5}

/-- Orientation also measured directly in the usual ordered product basis. -/
abbrev standard_orientation_type := P202Specs.ShuffleTriangulation.standard_orientation_type

/-- The tail coordinates preserve the standard product orientation. -/
abbrev standard_basis_orientation_type :=
  P202Specs.ShuffleTriangulation.standard_basis_orientation_type

/-- Degree zero is ordinary, without an augmentation term. -/
abbrev ordinary_boundary_zero_type.{v0, v1} := P202Specs.ShuffleBoundary.ordinary_boundary_zero_type.{v0, v1}

end P202Specs.ShuffleChains
