import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.HurewiczOne
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.FundamentalGroupoid
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory
open scoped Simplicial
namespace P202.HurewiczOne
open P202Specs.SingularChains P202Specs.Topology P202Specs.HurewiczOne
universe u
variable {X : TopCat.{u}}

@[simp] theorem simplexEquiv_point (x : X) :
    simplexEquiv X 0 (pointSimplex x) = ContinuousMap.const _ x :=
  (simplexEquiv X 0).apply_symm_apply _

@[simp] theorem simplexEquiv_path {x y : X} (a : Path x y) :
    simplexEquiv X 1 (pathSimplex a) =
      a.toContinuousMap.comp ⟨Convexity.StdSimplex.homeomorphI, Convexity.StdSimplex.homeomorphI.continuous⟩ :=
  (simplexEquiv X 1).apply_symm_apply _

@[simp] theorem pathSimplex_simplexPath (s : Simplex X 1) :
    pathSimplex (simplexPath s) = s := by
  apply (simplexEquiv X 1).injective
  ext t
  simp [simplexPath]

@[simp] theorem face_path_zero {x y : X} (a : Path x y) :
    face 0 (pathSimplex a) = pointSimplex y := by
  apply (simplexEquiv X 0).injective
  rw [P202.SingularChains.simplexEquiv_face, simplexEquiv_path, simplexEquiv_point]
  ext t
  have ht : t = .single 0 := (inferInstance : Subsingleton (Convexity.StdSimplex ℝ (Fin 1))).elim _ _
  subst t
  simp [ContinuousMap.comp_apply, P202.SingularChains.faceInclusion_vertex]

@[simp] theorem face_path_one {x y : X} (a : Path x y) :
    face 1 (pathSimplex a) = pointSimplex x := by
  apply (simplexEquiv X 0).injective
  rw [P202.SingularChains.simplexEquiv_face, simplexEquiv_path, simplexEquiv_point]
  ext t
  have ht : t = .single 0 := (inferInstance : Subsingleton (Convexity.StdSimplex ℝ (Fin 1))).elim _ _
  subst t
  simp [ContinuousMap.comp_apply, P202.SingularChains.faceInclusion_vertex]

theorem pathBoundary : Expected.pathBoundary.{u} := by
  intro X x y a
  rw [pathChain, P202.SingularChains.boundary_single]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

theorem loop_is_cycle (x : X) (a : Path x x) :
    boundary ℤ ℤ X 0 (pathChain a) = 0 := by
  rw [pathBoundary, sub_self]

/-- The affine collapse sends ordered vertices to 0, 1/2 and 1. -/
def triangleParameter : C(Convexity.StdSimplex ℝ (Fin 3), unitInterval) where
  toFun w := ⟨w.weights 1 / 2 + w.weights 2, by
    have h := w.total_of_fintype
    rw [Fin.sum_univ_three] at h
    have h0 := w.weights_nonneg 0
    have h1 := w.weights_nonneg 1
    have h2 := w.weights_nonneg 2
    constructor <;> linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((Convexity.StdSimplex.continuous_weights_apply ℝ 1).div_const 2).add
      (Convexity.StdSimplex.continuous_weights_apply ℝ 2)

lemma faceInclusion_weight (i : Fin 3) (t : Convexity.StdSimplex ℝ (Fin 2))
    (j : Fin 3) :
    (faceInclusion i t).weights j =
      (if i.succAbove 0 = j then t.weights 0 else 0) +
      (if i.succAbove 1 = j then t.weights 1 else 0) := by
  rw [P202.SingularChains.faceInclusion_weights, Finsupp.mapDomain_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_two, Finsupp.single_apply]

lemma triangleParameter_face_zero (t : Convexity.StdSimplex ℝ (Fin 2)) :
    (triangleParameter (faceInclusion 0 t) : ℝ) =
      (1 + (Convexity.StdSimplex.homeomorphI t : ℝ)) / 2 := by
  change (faceInclusion 0 t).weights 1 / 2 + (faceInclusion 0 t).weights 2 = _
  rw [faceInclusion_weight, faceInclusion_weight]
  norm_num [Fin.succAbove] at *
  have h := t.total_fin_two
  change t.weights 0 / 2 + t.weights 1 = (1 + t.weights 1) / 2
  linarith

lemma triangleParameter_face_one (t : Convexity.StdSimplex ℝ (Fin 2)) :
    triangleParameter (faceInclusion 1 t) = Convexity.StdSimplex.homeomorphI t := by
  apply Subtype.ext
  change (faceInclusion 1 t).weights 1 / 2 + (faceInclusion 1 t).weights 2 = _
  rw [faceInclusion_weight, faceInclusion_weight]
  norm_num [Fin.succAbove]
  rfl

lemma triangleParameter_face_two (t : Convexity.StdSimplex ℝ (Fin 2)) :
    (triangleParameter (faceInclusion 2 t) : ℝ) =
      (Convexity.StdSimplex.homeomorphI t : ℝ) / 2 := by
  change (faceInclusion 2 t).weights 1 / 2 + (faceInclusion 2 t).weights 2 = _
  rw [faceInclusion_weight, faceInclusion_weight]
  norm_num [Fin.succAbove]
  rfl

def concatenationSimplex {x y z : X} (a : Path x y) (b : Path y z) : Simplex X 2 :=
  (simplexEquiv X 2).symm ((a.trans b).toContinuousMap.comp triangleParameter)

@[simp] theorem concatenationSimplex_face_zero {x y z : X} (a : Path x y) (b : Path y z) :
    face 0 (concatenationSimplex a b) = pathSimplex b := by
  apply (simplexEquiv X 1).injective
  rw [P202.SingularChains.simplexEquiv_face, simplexEquiv_path]
  ext t
  change (a.trans b) (triangleParameter (faceInclusion 0 t)) = b _
  rw [← Path.extend_apply (a.trans b), Path.extend_trans_of_half_le]
  · rw [triangleParameter_face_zero]
    convert Path.extend_apply b (Convexity.StdSimplex.homeomorphI t).property using 1; congr 1; ring
  · rw [triangleParameter_face_zero]
    have h := (Convexity.StdSimplex.homeomorphI t).property.1
    linarith

@[simp] theorem concatenationSimplex_face_one {x y z : X} (a : Path x y) (b : Path y z) :
    face 1 (concatenationSimplex a b) = pathSimplex (a.trans b) := by
  apply (simplexEquiv X 1).injective
  rw [P202.SingularChains.simplexEquiv_face, simplexEquiv_path]
  ext t
  change (a.trans b) (triangleParameter (faceInclusion 1 t)) = (a.trans b) _
  rw [triangleParameter_face_one]
  rfl

@[simp] theorem concatenationSimplex_face_two {x y z : X} (a : Path x y) (b : Path y z) :
    face 2 (concatenationSimplex a b) = pathSimplex a := by
  apply (simplexEquiv X 1).injective
  rw [P202.SingularChains.simplexEquiv_face, simplexEquiv_path]
  ext t
  change (a.trans b) (triangleParameter (faceInclusion 2 t)) = a _
  rw [← Path.extend_apply (a.trans b), Path.extend_trans_of_le_half]
  · rw [triangleParameter_face_two]
    convert Path.extend_apply a (Convexity.StdSimplex.homeomorphI t).property using 1; congr 1; ring
  · rw [triangleParameter_face_two]
    have h := (Convexity.StdSimplex.homeomorphI t).property.2
    linarith

theorem concatenationBoundary : Expected.concatenationBoundary.{u} := by
  intro X x y z a b
  refine ⟨concatenationSimplex a b, ?_⟩
  rw [P202.SingularChains.boundary_single]
  change (∑ i : Fin 3, (-1 : ℤ) ^ i.val • Finsupp.single
    (face i (concatenationSimplex a b)) 1) = _
  simp [Fin.sum_univ_three, pathChain]
  abel

/-- Straight interpolation of two paths in a finite standard simplex fixes endpoints. -/
def simplexPathHomotopy {n : ℕ} {x y : Convexity.StdSimplex ℝ (Fin (n+1))}
    (p q : Path x y) : p.Homotopy q where
  toFun z := Convexity.convexCombPair (R := ℝ) (1 - (z.1 : ℝ)) (z.1 : ℝ)
    (sub_nonneg.mpr z.1.property.2) z.1.property.1 (by ring) (p z.2) (q z.2)
  continuous_toFun := by
    rw [(Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).continuous_iff]
    apply continuous_pi
    intro i
    simp only [Function.comp_def, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  map_zero_left := by intro t; simp
  map_one_left := by intro t; simp
  prop' := by
    intro t s hs
    rcases hs with hs | hs
    · subst s; simp
    · have hs : s = 1 := hs
      subst s; simp

/-- The oriented affine edge joining two vertices. -/
def vertexPath {n : ℕ} (i j : Fin (n+1)) :
    Path (Convexity.StdSimplex.single (R := ℝ) i) (.single j) where
  toFun t := Convexity.StdSimplex.map ![i, j] (Convexity.StdSimplex.homeomorphI.symm t)
  continuous_toFun := (Convexity.StdSimplex.continuous_map ℝ ![i, j]).comp
    Convexity.StdSimplex.homeomorphI.symm.continuous
  source' := by simp
  target' := by simp

lemma vertexPath_face (s : Simplex X 2) (i : Fin 3) :
    pathSimplex ((vertexPath (i.succAbove 0) (i.succAbove 1)).map
      (simplexEquiv X 2 s).continuous) = face i s := by
  apply (simplexEquiv X 1).injective
  rw [simplexEquiv_path, P202.SingularChains.simplexEquiv_face]
  ext t
  change (simplexEquiv X 2 s)
    (Convexity.StdSimplex.map ![i.succAbove 0, i.succAbove 1]
      (Convexity.StdSimplex.homeomorphI.symm (Convexity.StdSimplex.homeomorphI t))) = _
  rw [Homeomorph.symm_apply_apply]
  apply congrArg (simplexEquiv X 2 s)
  change Convexity.StdSimplex.map _ t = Convexity.StdSimplex.map i.succAbove t
  congr 1
  funext j
  fin_cases j <;> rfl

theorem nullTriangle : Expected.nullTriangle.{u} := by
  intro X s
  let F := simplexEquiv X 2 s
  refine ⟨(vertexPath (0 : Fin 3) 1).map F.continuous,
    (vertexPath (1 : Fin 3) 2).map F.continuous,
    (vertexPath (0 : Fin 3) 2).map F.continuous, ?_, ?_, ?_, ?_⟩
  · exact vertexPath_face s 2
  · exact vertexPath_face s 0
  · exact vertexPath_face s 1
  · rw [← Path.map_trans]
    exact ⟨(simplexPathHomotopy ((vertexPath (0 : Fin 3) 1).trans (vertexPath 1 2))
      (vertexPath 0 2)).map F⟩

/-- One-chains modulo all two-boundaries; individual paths need not be cycles. -/
abbrev EdgeQuotient (X : TopCat.{u}) := Chains ℤ X 1 ⧸ LinearMap.range (boundary ℤ ℤ X 1)

def edgeProjection (X : TopCat.{u}) : Chains ℤ X 1 →ₗ[ℤ] EdgeQuotient X :=
  (LinearMap.range (boundary ℤ ℤ X 1)).mkQ

def edgeClass {x y : X} (a : Path x y) : EdgeQuotient X := edgeProjection X (pathChain a)

lemma edgeProjection_boundary (c : Chains ℤ X 2) :
    edgeProjection X (boundary ℤ ℤ X 1 c) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨c, rfl⟩

lemma edgeClass_trans {x y z : X} (a : Path x y) (b : Path y z) :
    edgeClass (a.trans b) = edgeClass a + edgeClass b := by
  obtain ⟨s, hs⟩ := concatenationBoundary X x y z a b
  have h := edgeProjection_boundary (X := X) (Finsupp.single s 1)
  rw [hs, map_sub, map_add] at h
  exact (sub_eq_zero.mp h).symm

lemma constantSimplex_face (x : X) (n : ℕ) (i : Fin (n+2)) :
    face i ((simplexEquiv X (n+1)).symm (ContinuousMap.const _ x)) =
      (simplexEquiv X n).symm (ContinuousMap.const _ x) := by
  apply (simplexEquiv X n).injective
  rw [P202.SingularChains.simplexEquiv_face]
  simp

lemma constantSimplex_boundary (x : X) :
    boundary ℤ ℤ X 1 (Finsupp.single
      ((simplexEquiv X 2).symm (ContinuousMap.const _ x)) 1) = pathChain (Path.refl x) := by
  rw [P202.SingularChains.boundary_single]
  change (∑ i : Fin 3, (-1 : ℤ) ^ i.val • Finsupp.single
    (face i ((simplexEquiv X 2).symm (ContinuousMap.const _ x))) 1) = _
  simp [Fin.sum_univ_three, constantSimplex_face, pathChain, pathSimplex]
  rfl

lemma edgeClass_refl (x : X) : edgeClass (Path.refl x) = 0 := by
  rw [edgeClass, ← constantSimplex_boundary]
  exact edgeProjection_boundary _

/-- Affine coordinates for the two triangles of a homotopy square. -/
def squareLast : C(Convexity.StdSimplex ℝ (Fin 3), unitInterval) where
  toFun w := ⟨w.weights 2, w.weights_nonneg 2, w.weights_apply_le_one 2⟩
  continuous_toFun := (Convexity.StdSimplex.continuous_weights_apply ℝ 2).subtype_mk _

def squareSum : C(Convexity.StdSimplex ℝ (Fin 3), unitInterval) where
  toFun w := ⟨w.weights 1 + w.weights 2, by
    have h := w.total_of_fintype
    rw [Fin.sum_univ_three] at h
    have h0 := w.weights_nonneg 0
    have h1 := w.weights_nonneg 1
    have h2 := w.weights_nonneg 2
    constructor <;> linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ 1).add
      (Convexity.StdSimplex.continuous_weights_apply ℝ 2)

lemma squareLast_faces (w : Convexity.StdSimplex ℝ (Fin 2)) :
    squareLast (faceInclusion 0 w) = Convexity.StdSimplex.homeomorphI w ∧
    squareLast (faceInclusion 1 w) = Convexity.StdSimplex.homeomorphI w ∧
    squareLast (faceInclusion 2 w) = 0 := by
  constructor
  · apply Subtype.ext
    change (faceInclusion 0 w).weights 2 = w.weights 1
    rw [faceInclusion_weight]
    norm_num [Fin.succAbove]
  constructor
  · apply Subtype.ext
    change (faceInclusion 1 w).weights 2 = w.weights 1
    rw [faceInclusion_weight]
    norm_num [Fin.succAbove]
  · apply Subtype.ext
    change (faceInclusion 2 w).weights 2 = 0
    rw [faceInclusion_weight]
    norm_num [Fin.succAbove]

lemma squareSum_faces (w : Convexity.StdSimplex ℝ (Fin 2)) :
    squareSum (faceInclusion 0 w) = 1 ∧
    squareSum (faceInclusion 1 w) = Convexity.StdSimplex.homeomorphI w ∧
    squareSum (faceInclusion 2 w) = Convexity.StdSimplex.homeomorphI w := by
  constructor
  · apply Subtype.ext
    change (faceInclusion 0 w).weights 1 + (faceInclusion 0 w).weights 2 = 1
    rw [faceInclusion_weight, faceInclusion_weight]
    norm_num [Fin.succAbove]
  constructor
  · apply Subtype.ext
    change (faceInclusion 1 w).weights 1 + (faceInclusion 1 w).weights 2 = w.weights 1
    rw [faceInclusion_weight, faceInclusion_weight]
    norm_num [Fin.succAbove]
  · apply Subtype.ext
    change (faceInclusion 2 w).weights 1 + (faceInclusion 2 w).weights 2 = w.weights 1
    rw [faceInclusion_weight, faceInclusion_weight]
    norm_num [Fin.succAbove]

def homotopyUpper {x y : X} {a b : Path x y} (H : a.Homotopy b) : Simplex X 2 :=
  (simplexEquiv X 2).symm ⟨fun w => H (squareLast w, squareSum w),
    H.continuous.comp (squareLast.continuous.prodMk squareSum.continuous)⟩

def homotopyLower {x y : X} {a b : Path x y} (H : a.Homotopy b) : Simplex X 2 :=
  (simplexEquiv X 2).symm ⟨fun w => H (squareSum w, squareLast w),
    H.continuous.comp (squareSum.continuous.prodMk squareLast.continuous)⟩

lemma homotopyUpper_faces {x y : X} {a b : Path x y} (H : a.Homotopy b) :
    face 0 (homotopyUpper H) = pathSimplex (Path.refl y) ∧
    face 2 (homotopyUpper H) = pathSimplex a := by
  constructor <;> apply (simplexEquiv X 1).injective <;>
    rw [P202.SingularChains.simplexEquiv_face, simplexEquiv_path]
  · ext w
    change H (squareLast (faceInclusion 0 w), squareSum (faceInclusion 0 w)) = y
    rw [(squareLast_faces w).1, (squareSum_faces w).1]
    exact H.target _
  · ext w
    change H (squareLast (faceInclusion 2 w), squareSum (faceInclusion 2 w)) = a _
    rw [(squareLast_faces w).2.2, (squareSum_faces w).2.2]
    exact H.apply_zero _

lemma homotopyLower_faces {x y : X} {a b : Path x y} (H : a.Homotopy b) :
    face 0 (homotopyLower H) = pathSimplex b ∧
    face 2 (homotopyLower H) = pathSimplex (Path.refl x) := by
  constructor <;> apply (simplexEquiv X 1).injective <;>
    rw [P202.SingularChains.simplexEquiv_face, simplexEquiv_path]
  · ext w
    change H (squareSum (faceInclusion 0 w), squareLast (faceInclusion 0 w)) = b _
    rw [(squareSum_faces w).1, (squareLast_faces w).1]
    exact H.apply_one _
  · ext w
    change H (squareSum (faceInclusion 2 w), squareLast (faceInclusion 2 w)) = x
    rw [(squareSum_faces w).2.2, (squareLast_faces w).2.2]
    exact H.source _

lemma homotopy_diagonal {x y : X} {a b : Path x y} (H : a.Homotopy b) :
    face 1 (homotopyUpper H) = face 1 (homotopyLower H) := by
  apply (simplexEquiv X 1).injective
  rw [P202.SingularChains.simplexEquiv_face, P202.SingularChains.simplexEquiv_face]
  ext w
  change H (squareLast (faceInclusion 1 w), squareSum (faceInclusion 1 w)) =
    H (squareSum (faceInclusion 1 w), squareLast (faceInclusion 1 w))
  rw [(squareLast_faces w).2.1, (squareSum_faces w).2.1]

lemma edgeProjection_triangle (s : Simplex X 2) :
    edgeProjection X (Finsupp.single (face 0 s) 1) -
      edgeProjection X (Finsupp.single (face 1 s) 1) +
      edgeProjection X (Finsupp.single (face 2 s) 1) = 0 := by
  have h := edgeProjection_boundary (X := X) (Finsupp.single s 1)
  rw [P202.SingularChains.boundary_single] at h
  change edgeProjection X (∑ i : Fin 3, (-1 : ℤ) ^ i.val •
    Finsupp.single (face i s) 1) = 0 at h
  simpa [Fin.sum_univ_three, sub_eq_add_neg] using h

lemma edgeClass_homotopy {x y : X} {a b : Path x y} (H : a.Homotopy b) :
    edgeClass a = edgeClass b := by
  have hu := edgeProjection_triangle (homotopyUpper H)
  have hl := edgeProjection_triangle (homotopyLower H)
  rw [(homotopyUpper_faces H).1, (homotopyUpper_faces H).2, homotopy_diagonal H] at hu
  rw [(homotopyLower_faces H).1, (homotopyLower_faces H).2] at hl
  change edgeClass (Path.refl y) - _ + edgeClass a = 0 at hu
  change edgeClass b - _ + edgeClass (Path.refl x) = 0 at hl
  rw [edgeClass_refl, zero_sub] at hu
  rw [edgeClass_refl, add_zero] at hl
  have he := sub_eq_zero.mp hl
  rw [← he] at hu
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using hu)

def cycleToEdge (X : TopCat.{u}) : FirstHomologyQuotient X →ₗ[ℤ] EdgeQuotient X :=
  (LinearMap.range (boundaryToCycles X)).liftQ
    ((edgeProjection X).comp (OneCycles X).subtype) (by
      rintro _ ⟨c, rfl⟩
      exact edgeProjection_boundary c)

lemma cycleToEdge_injective (X : TopCat.{u}) : Function.Injective (cycleToEdge X) := by
  apply (injective_iff_map_eq_zero (cycleToEdge X)).mpr
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    intro hz
    change edgeProjection X z.val = 0 at hz
    have hz' : z.val ∈ LinearMap.range (boundary ℤ ℤ X 1) :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨c, hc⟩ := hz'
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨c, Subtype.ext hc⟩

def homologyToEdge (X : TopCat.{u}) : homology ℤ ℤ X 1 →ₗ[ℤ] EdgeQuotient X :=
  (cycleToEdge X).comp (homologyQuotientEquiv X).toLinearMap

lemma homologyToEdge_injective (X : TopCat.{u}) : Function.Injective (homologyToEdge X) :=
  (cycleToEdge_injective X).comp (homologyQuotientEquiv X).injective

@[simp] lemma homologyToEdge_cycleClass (c : Chains ℤ X 1) (hc) :
    homologyToEdge X (cycleClass X c hc) = edgeProjection X c := by
  simp [homologyToEdge, cycleClass, cycleToEdge]
  rfl

/-- Descend the singular cycle of a loop through endpoint-fixed path homotopy. -/
def hurewiczFunction (x : X) (g : Pi1 X x) : homology ℤ ℤ X 1 :=
  Quotient.liftOn (pathClass g)
    (fun a => cycleClass X (pathChain a) (loop_is_cycle x a)) (by
      intro a b hab
      apply homologyToEdge_injective X
      simp only [homologyToEdge_cycleClass]
      exact edgeClass_homotopy hab.some)

@[simp] lemma hurewiczFunction_loop (x : X) (a : Path x x) :
    hurewiczFunction x (loopClass a) = cycleClass X (pathChain a) (loop_is_cycle x a) := rfl

def hurewiczHom (x : X) : Pi1 X x →* Multiplicative (homology ℤ ℤ X 1) where
  toFun g := Multiplicative.ofAdd (hurewiczFunction x g)
  map_one' := by
    change hurewiczFunction x (loopClass (Path.refl x)) = 0
    apply homologyToEdge_injective X
    simp only [hurewiczFunction_loop, homologyToEdge_cycleClass, map_zero]
    exact edgeClass_refl x
  map_mul' a b := by
    obtain ⟨a, rfl⟩ := P202.Topology.loopClass_surjective a
    obtain ⟨b, rfl⟩ := P202.Topology.loopClass_surjective b
    change hurewiczFunction x (loopClass (a.trans b)) =
      hurewiczFunction x (loopClass a) + hurewiczFunction x (loopClass b)
    apply homologyToEdge_injective X
    simp only [hurewiczFunction_loop, homologyToEdge_cycleClass, map_add]
    exact edgeClass_trans a b

theorem hurewiczMap : Expected.hurewiczMap.{u} := by
  intro X x
  exact ⟨hurewiczHom x, fun a => ⟨loop_is_cycle x a, rfl⟩⟩

abbrev AbelianPi1 (X : TopCat.{u}) (x : X) := Additive (Abelianization (Pi1 X x))

def connectorClass {x : X} (l : ∀ y : X, Path x y) {y z : X} (a : Path y z) :
    AbelianPi1 X x :=
  Additive.ofMul (Abelianization.of (loopClass (((l y).trans a).trans (l z).symm)))

lemma connectorClass_congr {x : X} (l : ∀ y : X, Path x y)
    {y z y' z' : X} (a : Path y z) (b : Path y' z') (h : ∀ t, a t = b t) :
    connectorClass l a = connectorClass l b := by
  have hy : y = y' := by simpa using h 0
  have hz : z = z' := by simpa using h 1
  subst y'; subst z'
  have hab : a = b := Path.ext (funext h)
  rw [hab]

lemma connectorClass_trans {x : X} (l : ∀ y : X, Path x y)
    {y z w : X} (a : Path y z) (b : Path z w) :
    connectorClass l (a.trans b) = connectorClass l a + connectorClass l b := by
  change Additive.ofMul (Abelianization.of (loopClass _)) =
    Additive.ofMul (Abelianization.of (loopClass _) * Abelianization.of (loopClass _))
  rw [← map_mul]
  apply congrArg Additive.ofMul
  apply congrArg Abelianization.of
  apply P202.Topology.pathClass_injective
  simp only [P202.Topology.pathClass_loopClass, P202.Topology.pathClass_mul,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, P202.Topology.class_symm_trans_cancel]

lemma connectorClass_homotopy {x : X} (l : ∀ y : X, Path x y)
    {y z : X} {a b : Path y z} (h : a.Homotopic b) :
    connectorClass l a = connectorClass l b := by
  apply congrArg Additive.ofMul
  apply congrArg Abelianization.of
  apply P202.Topology.pathClass_injective
  simp only [P202.Topology.pathClass_loopClass, Path.Homotopic.Quotient.mk_trans]
  rw [Path.Homotopic.Quotient.eq.mpr h]

lemma connectorClass_loop {x : X} (l : ∀ y : X, Path x y) (a : Path x x) :
    connectorClass l a = Additive.ofMul (Abelianization.of (loopClass a)) := by
  change Additive.ofMul (Abelianization.of
    (loopClass (l x) * loopClass a * (loopClass (l x))⁻¹)) = _
  simp [map_mul, mul_comm]

def connectorChain {x : X} (l : ∀ y : X, Path x y) :
    Chains ℤ X 1 →ₗ[ℤ] AbelianPi1 X x :=
  Finsupp.linearCombination ℤ (fun s => connectorClass l (simplexPath s))

@[simp] lemma connectorChain_pathChain {x : X} (l : ∀ y : X, Path x y)
    {y z : X} (a : Path y z) :
    connectorChain l (pathChain a) = connectorClass l a := by
  simp only [connectorChain, pathChain, Finsupp.linearCombination_single, one_smul]
  apply connectorClass_congr
  intro t
  simp [simplexPath]

lemma connectorChain_boundary {x : X} (l : ∀ y : X, Path x y) :
    (connectorChain l).comp (boundary ℤ ℤ X 1) = 0 := by
  apply Finsupp.lhom_ext
  intro s n
  have hs : connectorChain l (boundary ℤ ℤ X 1 (Finsupp.single s 1)) = 0 := by
    obtain ⟨a, b, c, ha, hb, hc, h⟩ := nullTriangle X s
    rw [P202.SingularChains.boundary_single]
    change connectorChain l (∑ i : Fin 3, (-1 : ℤ) ^ i.val •
      Finsupp.single (face i s) 1) = 0
    simp only [Fin.sum_univ_three]
    norm_num only [Fin.val_zero, Fin.val_one, Fin.reduceFinMk, pow_zero, pow_one, neg_one_sq,
      one_zsmul, neg_smul, one_smul]
    have he : ((-1 : ℤ) ^ (2 : Fin 3).val) = 1 := by norm_num
    rw [he, one_smul]
    rw [← ha, ← hb, ← hc]
    change connectorChain l (pathChain b + -pathChain c + pathChain a) = 0
    rw [map_add, map_add, map_neg, connectorChain_pathChain, connectorChain_pathChain,
      connectorChain_pathChain, ← connectorClass_homotopy l h, connectorClass_trans]
    abel
  have hn : Finsupp.single s n = n • Finsupp.single s (1 : ℤ) := by simp
  change connectorChain l (boundary ℤ ℤ X 1 (Finsupp.single s n)) = 0
  rw [hn, map_zsmul, map_zsmul, hs, smul_zero]

def inverseOnHomology {x : X} (l : ∀ y : X, Path x y) :
    homology ℤ ℤ X 1 →ₗ[ℤ] AbelianPi1 X x :=
  ((LinearMap.range (boundaryToCycles X)).liftQ
    ((connectorChain l).comp (OneCycles X).subtype) (by
      rintro _ ⟨c, rfl⟩
      exact LinearMap.congr_fun (connectorChain_boundary l) c)).comp
    (homologyQuotientEquiv X).toLinearMap

@[simp] lemma inverseOnHomology_cycleClass {x : X} (l : ∀ y : X, Path x y)
    (c : Chains ℤ X 1) (hc) :
    inverseOnHomology l (cycleClass X c hc) = connectorChain l c := by
  simp [inverseOnHomology, cycleClass]
  rfl

def abelianizedHurewicz (x : X) : AbelianPi1 X x →+ homology ℤ ℤ X 1 :=
  (Abelianization.lift (hurewiczHom x)).toAdditiveLeft

@[simp] lemma abelianizedHurewicz_loop (x : X) (a : Path x x) :
    abelianizedHurewicz x (Additive.ofMul (Abelianization.of (loopClass a))) =
      cycleClass X (pathChain a) (loop_is_cycle x a) := rfl

lemma inverse_left {x : X} (l : ∀ y : X, Path x y) (z : AbelianPi1 X x) :
    inverseOnHomology l (abelianizedHurewicz x z) = z := by
  induction z using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨a, rfl⟩ := P202.Topology.loopClass_surjective g
    change inverseOnHomology l (abelianizedHurewicz x
      (Additive.ofMul (Abelianization.of (loopClass a)))) =
      Additive.ofMul (Abelianization.of (loopClass a))
    rw [abelianizedHurewicz_loop, inverseOnHomology_cycleClass, connectorChain_pathChain,
      connectorClass_loop]

lemma edgeClass_symm {y z : X} (a : Path y z) : edgeClass a.symm = -edgeClass a := by
  have h := edgeClass_homotopy (Path.Homotopic.trans_symm a).some
  rw [edgeClass_trans, edgeClass_refl] at h
  exact eq_neg_of_add_eq_zero_right h

lemma forward_connector_edge {x : X} (l : ∀ y : X, Path x y) {y z : X} (a : Path y z) :
    homologyToEdge X (abelianizedHurewicz x (connectorClass l a)) =
      edgeClass a + edgeClass (l y) - edgeClass (l z) := by
  simp only [connectorClass, abelianizedHurewicz_loop, homologyToEdge_cycleClass]
  change edgeClass (((l y).trans a).trans (l z).symm) = _
  rw [edgeClass_trans, edgeClass_trans, edgeClass_symm]
  abel

/-- The connector correction factors through the boundary of a one-chain. -/
def vertexConnectorChain {x : X} (l : ∀ y : X, Path x y) :
    Chains ℤ X 0 →ₗ[ℤ] EdgeQuotient X :=
  Finsupp.linearCombination ℤ (fun s => edgeClass (l (simplexEquiv X 0 s (.single 0))))

@[simp] lemma vertexConnectorChain_point {x : X} (l : ∀ y : X, Path x y) (y : X) :
    vertexConnectorChain l (Finsupp.single (pointSimplex y) 1) = edgeClass (l y) := by
  simp only [vertexConnectorChain, Finsupp.linearCombination_single, one_smul]
  rw [simplexEquiv_point]
  rfl

lemma vertexConnector_boundary_path {x : X} (l : ∀ y : X, Path x y)
    {y z : X} (a : Path y z) :
    vertexConnectorChain l (boundary ℤ ℤ X 0 (pathChain a)) =
      edgeClass (l z) - edgeClass (l y) := by
  rw [pathBoundary, map_sub, vertexConnectorChain_point, vertexConnectorChain_point]

lemma connector_chain_identity {x : X} (l : ∀ y : X, Path x y) (c : Chains ℤ X 1) :
    homologyToEdge X (abelianizedHurewicz x (connectorChain l c)) =
      edgeProjection X c - vertexConnectorChain l (boundary ℤ ℤ X 0 c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, hc, hd]
    abel
  | single s n =>
    have hs : Finsupp.single s n = n • pathChain (simplexPath s) := by
      simp [pathChain]
    rw [hs]
    simp only [map_zsmul]
    rw [← smul_sub]
    congr 1
    rw [connectorChain_pathChain, forward_connector_edge, vertexConnector_boundary_path]
    change edgeClass (simplexPath s) + _ - _ = edgeClass (simplexPath s) - (_ - _)
    abel

lemma cycleClass_surjective (X : TopCat.{u}) :
    Function.Surjective (fun c : OneCycles X => cycleClass X c.val c.property) := by
  intro h
  obtain ⟨c, hc⟩ := (Submodule.mkQ_surjective (LinearMap.range (boundaryToCycles X)))
    ((homologyQuotientEquiv X) h)
  refine ⟨c, ?_⟩
  apply (homologyQuotientEquiv X).injective
  simpa [cycleClass] using hc

lemma inverse_right {x : X} (l : ∀ y : X, Path x y) (h : homology ℤ ℤ X 1) :
    abelianizedHurewicz x (inverseOnHomology l h) = h := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective X h
  rw [inverseOnHomology_cycleClass]
  apply homologyToEdge_injective X
  rw [homologyToEdge_cycleClass]
  have hi := connector_chain_identity l c.val
  change homologyToEdge X (abelianizedHurewicz x (connectorChain l c.val)) =
    edgeProjection X c.val - vertexConnectorChain l (boundary ℤ ℤ X 0 c.val) at hi
  rw [c.property, map_zero, sub_zero] at hi
  exact hi

/-- The source-convention degree-one Hurewicz isomorphism for arbitrary
path-connected spaces, with its action on every based loop. -/
theorem hurewiczOne : Expected.hurewiczOne.{u} := by
  intro X _ x
  let l : ∀ y : X, Path x y := fun y => PathConnectedSpace.somePath x y
  refine ⟨{
    toFun := abelianizedHurewicz x
    invFun := inverseOnHomology l
    left_inv := inverse_left l
    right_inv := inverse_right l
    map_add' := (abelianizedHurewicz x).map_add }, ?_⟩
  intro a
  exact ⟨loop_is_cycle x a, rfl⟩

end P202.HurewiczOne
