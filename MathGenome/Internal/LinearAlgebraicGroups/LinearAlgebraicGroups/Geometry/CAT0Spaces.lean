import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Geometry.CAT0Spaces
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Geodesic spaces, CAT(0) comparison, and geometric actions. -/

open Set unitInterval

open scoped ENNReal

universe u v

namespace LinearAlgebraicGroups.Geometry

variable {X : Type*} [MetricSpace X]

/-- A path on the unit interval has constant metric speed equal to the distance of its endpoints. -/
def IsGeodesicSegment {x y : X} (p : Path x y) : Prop :=
  ∀ s t : I, dist (p s) (p t) = dist s t * dist x y

/-- A constant-speed geodesic segment from `x` to `y`, parametrized on `[0, 1]`. -/
abbrev GeodesicSegment (x y : X) :=
  {p : Path x y // IsGeodesicSegment p}

/-- A geodesic space is nonempty and any two points can be joined by a segment. -/
def IsGeodesicSpace (X : Type*) [MetricSpace X] : Prop :=
  Nonempty X ∧ ∀ x y : X, Nonempty (GeodesicSegment x y)

/-- The nonempty spaces in which each pair of endpoints specifies a unique segment. -/
def IsUniquelyGeodesic (X : Type*) [MetricSpace X] : Prop :=
  IsGeodesicSpace X ∧ ∀ x y : X, Subsingleton (GeodesicSegment x y)

/-- The subset contains every segment between any two of its points. In a uniquely
geodesic space this tests the unique segment. -/
def GeodesicConvex (C : Set X) : Prop :=
  ∀ ⦃x y : X⦄, x ∈ C → y ∈ C → ∀ (p : GeodesicSegment x y) (t : I), p.val t ∈ C

/-- The comparison plane with the Euclidean metric. -/
abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-- The product of metric spaces equipped with the Euclidean product metric. -/
abbrev EuclideanProduct (X : Type u) (Y : Type v) := WithLp 2 (X × Y)

theorem euclideanProduct_dist {Y : Type*} [MetricSpace Y] (x y : EuclideanProduct X Y) :
    dist x y = Real.sqrt (dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2) := by
  rw [WithLp.prod_dist_eq_add (by simp : 0 < (2 : ℝ≥0∞).toReal), Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

/-- The Euclidean vertices have the same pairwise distances as the original vertices. -/
def IsComparisonTriangle (v : Fin 3 → X) (w : Fin 3 → EuclideanPlane) : Prop :=
  ∀ i j, dist (w i) (w j) = dist (v i) (v j)

private abbrev planePoint (a b : ℝ) : EuclideanPlane :=
  WithLp.toLp 2 ![a, b]

private theorem planePoint_dist_sq (a b c d : ℝ) :
    dist (planePoint a b) (planePoint c d) ^ 2 = (a - c) ^ 2 + (b - d) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp [Real.dist_eq]

private theorem exists_planar_distances (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≤ b + c) (hbc : b ≤ a + c) (hca : c ≤ a + b) :
    ∃ p q r : EuclideanPlane, dist p q = a ∧ dist p r = b ∧ dist q r = c := by
  by_cases ha0 : a = 0
  · have hbc' : b = c := by linarith
    refine ⟨planePoint 0 0, planePoint 0 0, planePoint b 0, ?_, ?_, ?_⟩
    · simp [ha0]
    · apply (sq_eq_sq₀ dist_nonneg hb).mp
      rw [planePoint_dist_sq]
      ring
    · rw [← hbc']
      apply (sq_eq_sq₀ dist_nonneg hb).mp
      rw [planePoint_dist_sq]
      ring
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hdenom : 0 < 2 * a := mul_pos two_pos ha'
    let m := (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a)
    have hdiff : (a - b) ^ 2 ≤ c ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hc, abs_le]
      constructor <;> linarith
    have hsum : c ^ 2 ≤ (a + b) ^ 2 :=
      (sq_le_sq₀ hc (add_nonneg ha hb)).mpr hca
    have hmlo : -b ≤ m := by
      apply (le_div_iff₀ hdenom).mpr
      nlinarith only [hsum]
    have hmhi : m ≤ b := by
      apply (div_le_iff₀ hdenom).mpr
      nlinarith only [hdiff]
    have hmsq : m ^ 2 ≤ b ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hb]
      exact abs_le.mpr ⟨hmlo, hmhi⟩
    let n := Real.sqrt (b ^ 2 - m ^ 2)
    have hnsq : n ^ 2 = b ^ 2 - m ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hmsq)
    have hm : m * (2 * a) = a ^ 2 + b ^ 2 - c ^ 2 :=
      div_mul_cancel₀ _ hdenom.ne'
    refine ⟨planePoint 0 0, planePoint a 0, planePoint m n, ?_, ?_, ?_⟩
    · apply (sq_eq_sq₀ dist_nonneg ha).mp
      rw [planePoint_dist_sq]
      ring
    · apply (sq_eq_sq₀ dist_nonneg hb).mp
      rw [planePoint_dist_sq]
      linear_combination hnsq
    · apply (sq_eq_sq₀ dist_nonneg hc).mp
      rw [planePoint_dist_sq]
      linear_combination hnsq - hm

/-- Every metric triangle has a comparison triangle, including triangles with zero sides
or equality in a triangle inequality. -/
theorem exists_comparisonTriangle (v : Fin 3 → X) :
    ∃ w : Fin 3 → EuclideanPlane, IsComparisonTriangle v w := by
  obtain ⟨p, q, r, hpq, hpr, hqr⟩ :=
    exists_planar_distances (dist (v 0) (v 1)) (dist (v 0) (v 2)) (dist (v 1) (v 2))
      dist_nonneg dist_nonneg dist_nonneg (dist_triangle_right (v 0) (v 1) (v 2))
      (dist_triangle (v 0) (v 1) (v 2)) (dist_triangle_left (v 1) (v 2) (v 0))
  refine ⟨![p, q, r], ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hpq
    | exact hpr
    | exact hqr
    | exact (dist_comm _ _).trans (hpq.trans (dist_comm _ _))
    | exact (dist_comm _ _).trans (hpr.trans (dist_comm _ _))
    | exact (dist_comm _ _).trans (hqr.trans (dist_comm _ _))
    | simp only [dist_self]

/-- Comparison triangles for the same metric triangle are congruent by an isometry of
the whole Euclidean plane, including when their vertices are collinear or coincide. -/
theorem comparisonTriangle_congruent {v : Fin 3 → X} {w w' : Fin 3 → EuclideanPlane}
    (hw : IsComparisonTriangle v w) (hw' : IsComparisonTriangle v w') :
    ∃ e : EuclideanPlane ≃ᵢ EuclideanPlane, ∀ i, e (w i) = w' i := by
  have hdist (i j : Fin 3) : dist (w i) (w j) = dist (w' i) (w' j) :=
    (hw i j).trans (hw' i j).symm
  have hgram (i j : Fin 3) :
      inner ℝ (w i - w 0) (w j - w 0) = inner ℝ (w' i - w' 0) (w' j - w' 0) := by
    simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm, hdist]
  let f := Finsupp.linearCombination ℝ (fun i => w i - w 0)
  let g := Finsupp.linearCombination ℝ (fun i => w' i - w' 0)
  have hnorm (c : Fin 3 →₀ ℝ) : ‖f c‖ = ‖g c‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [← real_inner_self_eq_norm_sq, f, g, Finsupp.linearCombination_apply,
      Finsupp.sum_inner, Finsupp.inner_sum, real_inner_smul_left, inner_smul_right, hgram]
  -- Equal norms make the map on vertex differences well-defined on their span.
  have hker : LinearMap.ker f.rangeRestrict ≤ LinearMap.ker g := by
    intro c hc
    have hfc : f c = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hc)
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp ((hnorm c).symm.trans (by simp [hfc])))
  let L := f.rangeRestrict.liftOfSurjective f.surjective_rangeRestrict ⟨g, hker⟩
  have hL (c : Fin 3 →₀ ℝ) : L (f.rangeRestrict c) = g c :=
    LinearMap.equivOfSurjective_apply _ _
  let A : LinearMap.range f →ₗᵢ[ℝ] EuclideanPlane :=
    { toLinearMap := L
      norm_map' := by
        intro x
        obtain ⟨c, rfl⟩ := f.surjective_rangeRestrict x
        rw [hL]
        exact (hnorm c).symm }
  have hsurj : Function.Surjective A.extend :=
    LinearMap.injective_iff_surjective.mp A.extend.injective
  let e := (LinearIsometryEquiv.ofSurjective A.extend hsurj).toIsometryEquiv
  refine ⟨(IsometryEquiv.subRight (w 0)).trans (e.trans (IsometryEquiv.addRight (w' 0))), ?_⟩
  intro i
  have hf : f (Finsupp.single i 1) = w i - w 0 := by
    simp [f, Finsupp.linearCombination_single]
  have hg : g (Finsupp.single i 1) = w' i - w' 0 := by
    simp [g, Finsupp.linearCombination_single]
  have he : e (w i - w 0) = w' i - w' 0 := by
    rw [← hf]
    change A.extend (f.rangeRestrict (Finsupp.single i 1) : LinearMap.range f) = _
    rw [LinearIsometry.extend_apply]
    exact (hL _).trans hg
  simp [he]

/-- A geodesic space is CAT(0) if distances between points on triangle sides are bounded
by the corresponding Euclidean distances. The cyclic side indexing includes repeated
vertices, collinear comparison vertices and pairs of points on the same side. -/
def CAT0 (X : Type*) [MetricSpace X] : Prop :=
  IsGeodesicSpace X ∧
    ∀ (v : Fin 3 → X) (side : ∀ i : Fin 3, GeodesicSegment (v i) (v (i + 1)))
      (w : Fin 3 → EuclideanPlane), IsComparisonTriangle v w →
        ∀ (i j : Fin 3) (s t : I), dist ((side i).val s) ((side j).val t) ≤
          dist ((1 - (s : ℝ)) • w i + (s : ℝ) • w (i + 1))
               ((1 - (t : ℝ)) • w j + (t : ℝ) • w (j + 1))

section Actions

variable (G X : Type*) [Group G] [MetricSpace X] [MulAction G X]

/-- Properness of a discrete group action in the compact-set formulation. -/
def IsProperAction : Prop :=
  ∀ K : Set X, IsCompact K → {g : G | ∃ x ∈ K, g • x ∈ K}.Finite

/-- The translates of one compact set cover the space. -/
def IsCocompactAction : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ (g : G) (k : X), k ∈ K ∧ g • k = x

/-- A discrete group action is geometric if it is isometric, proper and cocompact. -/
def IsGeometricAction : Prop :=
  IsIsometricSMul G X ∧ IsProperAction G X ∧ IsCocompactAction G X

end Actions

/-- The infimum of the displacement of an isometry. -/
noncomputable def translationLength (g : X ≃ᵢ X) : ℝ :=
  ⨅ x : X, dist x (g x)

/-- The points at which an isometry attains its displacement infimum. -/
def minset (g : X ≃ᵢ X) : Set X :=
  {x | dist x (g x) = translationLength g}

/-- An isometry is semisimple when its translation length is attained. -/
def IsSemisimple (g : X ≃ᵢ X) : Prop :=
  (minset g).Nonempty

/-- The intersection of the minsets of a family of isometries. -/
def commonMinset {ι : Type*} (f : ι → X ≃ᵢ X) : Set X :=
  ⋂ i, minset (f i)

/-- The intersection of the minsets over the elements of an isometrically acting group. -/
def actionMinset (G X : Type*) [Group G] [MetricSpace X]
    [MulAction G X] [IsIsometricSMul G X] : Set X :=
  commonMinset (fun g : G => (IsometryEquiv.constSMul g : X ≃ᵢ X))

end LinearAlgebraicGroups.Geometry
