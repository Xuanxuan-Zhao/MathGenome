import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndices
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerAlcoveSymmetries
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerUniformizerTranslations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerWeylDirections
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndexParabolic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Geometry.Circumcenter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Geometry.FlatTorus
import Mathlib.Topology.Baire.Lemmas
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndices

open Specs.ExceptionalInnerIndices
open Specs.ExceptionalInnerWeylDirections (reflectValues reflectWord)
open Specs.ExceptionalAffineRootSystems (exceptionalCartan)
open Specs.ExceptionalInnerAlcoveSymmetries
  (e6Highest e7Highest e6Rotate e7Reverse directionalValues invariantDirections)

private theorem e6Orbit_surjective : Function.Surjective e6Orbit := by
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨4, rfl⟩

private theorem e7Orbit_surjective : Function.Surjective e7Orbit := by
  intro i
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

private theorem e6Orbit_iff (i j : Fin 7) :
    e6Orbit i = e6Orbit j ↔ ∃ k : Fin 3, (e6Rotate ^ (k : ℕ)) i = j := by
  revert i j
  decide

private theorem e7Orbit_iff (i j : Fin 8) :
    e7Orbit i = e7Orbit j ↔ ∃ k : Fin 2, (e7Reverse ^ (k : ℕ)) i = j := by
  revert i j
  decide

private theorem e6InvariantValues (r : Fin 6 → ℚ)
    (hr : r ∈ invariantDirections e6Highest e6Rotate) :
    ∃ a b : ℚ, r = ![-2*a-b, a, a, b, a, -2*a-b] := by
  change ∀ i, directionalValues e6Highest r (e6Rotate i) = directionalValues e6Highest r i at hr
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  change r 0 = -(∑ i, (e6Highest i : ℚ) * r i) at h0
  change r 5 = r 0 at h1
  change r 2 = r 1 at h2
  change r 4 = r 2 at h3
  norm_num [e6Highest, Fin.sum_univ_succ] at h0
  refine ⟨r 1, r 3, ?_⟩
  ext i
  fin_cases i <;> simp <;> linarith

private theorem e7InvariantValues (r : Fin 7 → ℚ)
    (hr : r ∈ invariantDirections e7Highest e7Reverse) :
    ∃ a b c d : ℚ, r = ![a, d, b, c, b, a, -2*a-3*b-2*c-d] := by
  change ∀ i, directionalValues e7Highest r (e7Reverse i) = directionalValues e7Highest r i at hr
  have h0 := hr 0
  have h1 := hr 1
  have h3 := hr 3
  change r 6 = -(∑ i, (e7Highest i : ℚ) * r i) at h0
  change r 5 = r 0 at h1
  change r 4 = r 2 at h3
  norm_num [e7Highest, Fin.sum_univ_succ] at h0
  refine ⟨r 0, r 2, r 3, r 1, ?_⟩
  ext i
  fin_cases i <;> simp <;> linarith

private theorem e6Cartan_entries (i j : Fin 6) :
    exceptionalCartan 6 i j =
      (!![2, 0, -1, 0, 0, 0;
        0, 2, 0, -1, 0, 0;
        -1, 0, 2, -1, 0, 0;
        0, -1, -1, 2, -1, 0;
        0, 0, 0, -1, 2, -1;
        0, 0, 0, 0, -1, 2] : Matrix (Fin 6) (Fin 6) ℤ) i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem e6InvariantValues_reflect (a b : ℚ) :
    ![-2*a-b, a, a, b, a, -2*a-b] ∈ invariantDirections e6Highest e6Rotate ∧
    reflectWord e6Word ![-2*a-b, a, a, b, a, -2*a-b] = ![0, b, 0, a, 0, 0] := by
  constructor
  · intro i
    fin_cases i <;> try rfl
    · change -2*a-b = -(∑ j, (e6Highest j : ℚ) * (![-2*a-b, a, a, b, a, -2*a-b] : Fin 6 → ℚ) j)
      norm_num [e6Highest, Fin.sum_univ_succ]; ring
    · change -(∑ j, (e6Highest j : ℚ) * (![-2*a-b, a, a, b, a, -2*a-b] : Fin 6 → ℚ) j) = -2*a-b
      norm_num [e6Highest, Fin.sum_univ_succ]; ring
  · ext i
    fin_cases i <;>
      norm_num [reflectWord, e6Word, reflectValues, e6Cartan_entries] <;> ring

private theorem e7Cartan_entries (i j : Fin 7) :
    exceptionalCartan 7 i j =
      (!![2, 0, -1, 0, 0, 0, 0;
        0, 2, 0, -1, 0, 0, 0;
        -1, 0, 2, -1, 0, 0, 0;
        0, -1, -1, 2, -1, 0, 0;
        0, 0, 0, -1, 2, -1, 0;
        0, 0, 0, 0, -1, 2, -1;
        0, 0, 0, 0, 0, -1, 2] : Matrix (Fin 7) (Fin 7) ℤ) i j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem e7InvariantValues_reflect (a b c d : ℚ) :
    ![a, d, b, c, b, a, -2*a-3*b-2*c-d] ∈ invariantDirections e7Highest e7Reverse ∧
    reflectWord e7Word ![a, d, b, c, b, a, -2*a-3*b-2*c-d] = ![d, 0, c, b, 0, a, 0] := by
  constructor
  · intro i
    fin_cases i <;> try rfl
    · change -2*a-3*b-2*c-d = -(∑ j, (e7Highest j : ℚ) * (![a, d, b, c, b, a, -2*a-3*b-2*c-d] : Fin 7 → ℚ) j)
      norm_num [e7Highest, Fin.sum_univ_succ]; ring
    · change -(∑ j, (e7Highest j : ℚ) * (![a, d, b, c, b, a, -2*a-3*b-2*c-d] : Fin 7 → ℚ) j) = -2*a-3*b-2*c-d
      norm_num [e7Highest, Fin.sum_univ_succ]; ring
  · ext i
    fin_cases i <;>
      norm_num [reflectWord, e7Word, reflectValues, e7Cartan_entries] <;> ring

theorem e6IndexCalculation : E6IndexCalculation := by
  refine ⟨e6Orbit_surjective, e6Orbit_iff, e6InvariantValues, e6InvariantValues_reflect, ?_⟩
  ext i
  constructor
  · intro h
    have hv := h _ ⟨_, (e6InvariantValues_reflect 1 1).1, rfl⟩
    rw [(e6InvariantValues_reflect 1 1).2] at hv
    fin_cases i <;> simp_all [e6Black]
  · rintro h _ ⟨r, hr, rfl⟩
    obtain ⟨a, b, rfl⟩ := e6InvariantValues r hr
    rw [(e6InvariantValues_reflect a b).2]
    fin_cases i <;> simp_all [e6Black]

theorem e7IndexCalculation : E7IndexCalculation := by
  refine ⟨e7Orbit_surjective, e7Orbit_iff, e7InvariantValues, e7InvariantValues_reflect, ?_⟩
  ext i
  constructor
  · intro h
    have hv := h _ ⟨_, (e7InvariantValues_reflect 1 1 1 1).1, rfl⟩
    rw [(e7InvariantValues_reflect 1 1 1 1).2] at hv
    fin_cases i <;> simp_all [e7Black]
  · rintro h _ ⟨r, hr, rfl⟩
    obtain ⟨a, b, c, d, rfl⟩ := e7InvariantValues r hr
    rw [(e7InvariantValues_reflect a b c d).2]
    fin_cases i <;> simp_all [e7Black]


open Set
open LinearAlgebraicGroups.Geometry

/-- An isometric flat covered by countably many isometric Euclidean images
cannot have larger dimension than all the covering spaces. -/
theorem dimension_le_of_euclidean_cover {X ι E : Type*} [MetricSpace X] [Countable ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {r : ℕ} (f : EuclideanSpace ℝ (Fin r) → X) (hf : Isometry f)
    (g : ι → E → X) (hg : ∀ i, Isometry (g i))
    (hcover : range f ⊆ ⋃ i, range (g i)) : r ≤ Module.finrank ℝ E := by
  classical
  let A (i : ι) := f ⁻¹' range (g i)
  have hA i : IsClosed (A i) :=
    (hg i).isUniformEmbedding.isClosedEmbedding.isClosed_range.preimage hf.continuous
  have hUnion : ⋃ i, A i = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_range_self x))
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hA hUnion
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hA_ball : Metric.ball x ε ⊆ A i := hball.trans interior_subset
  let b := EuclideanSpace.basisFun (Fin r) ℝ
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let y (k : Fin r) := δ • b k + x
  have hy (k : Fin r) : y k ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hb : ‖b k‖ = 1 := b.orthonormal.norm_eq_one k
    simp only [y, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hb, mul_one]
    exact half_lt_self hε
  have hx' : x ∈ A i := interior_subset hx
  obtain ⟨u, hu⟩ := hx'
  choose v hv using fun k => hA_ball (hy k)
  have hd₁ (k) : dist (v k) u = dist (y k) x := by
    rw [← (hg i).dist_eq, hv k, hu, hf.dist_eq]
  have hd₂ (k l) : dist (v k) (v l) = dist (y k) (y l) := by
    rw [← (hg i).dist_eq, hv k, hv l, hf.dist_eq]
  let w (k : Fin r) := δ⁻¹ • (v k - u)
  have hgram (k l) : inner ℝ (v k - u) (v l - u) = inner ℝ (y k - x) (y l - x) := by
    simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm, hd₁, hd₂]
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro k l
    have hscale (k : Fin r) : δ⁻¹ • (δ • b k) = b k := by
      rw [smul_smul, inv_mul_cancel₀ hδ.ne', one_smul]
    calc
      inner ℝ (w k) (w l)
          = inner ℝ (δ⁻¹ • (δ • b k)) (δ⁻¹ • (δ • b l)) := by
            simp only [w, real_inner_smul_left, inner_smul_right, hgram, y, add_sub_cancel_right]
            ring
      _ = inner ℝ (b k) (b l) := by rw [hscale, hscale]
      _ = if k = l then 1 else 0 := (orthonormal_iff_ite.mp b.orthonormal) k l
  simpa using hw.linearIndependent.fintype_card_le_finrank


universe u v

open Specs.ExceptionalAffineBuilding (Chamber Realization Weights)
open Specs.ExceptionalAffineBruhat (leftCosets)
open Specs.ExceptionalAffineRootSystems (ApartmentRoots)

/-- Finite Bruhat cells in the chamber quotient, indexed by the ordinary
Coxeter group on finitely many simple walls, give countably many chambers. -/
theorem chamber_countable {G B W : Type*} [Group G] [Group W] [Finite B]
    {m : CoxeterMatrix B} (cs : CoxeterSystem m W) (I G₀ : Subgroup G) (lift : W → G)
    (hcover : (⋃ w, DoubleCoset.doubleCoset (lift w) I I) = (G₀ : Set G))
    (hfinite : ∀ w, (leftCosets I (lift w)).Finite) : Countable (Chamber I G₀) := by
  let : Countable W := cs.wordProd_surjective.countable
  apply Set.countable_coe_iff.mpr
  refine (Set.countable_iUnion fun w => (hfinite w).countable).mono ?_
  rintro _ ⟨g, rfl⟩
  have hg : (g : G) ∈ ⋃ w, DoubleCoset.doubleCoset (lift w) I I := hcover ▸ g.property
  obtain ⟨w, hw⟩ := mem_iUnion.mp hg
  exact mem_iUnion.mpr ⟨w, mem_image_of_mem _ hw⟩

/-- A fixed point of a type-permuting action has weights constant on vertex
orbits in any chamber containing the point. -/
theorem weights_fixed_of_place_fixed
    {G V : Type u} {J : Type v} [Group G] [AddCommGroup V] [Module ℚ V]
    {A : ApartmentRoots ℚ V J} {p : V} {m : CoxeterMatrix (A.SimpleWall p)}
    {cs : CoxeterSystem m A.affineWeylGroup} {I G₀ : Subgroup G}
    {lift : A.affineWeylGroup → G} (X : Realization cs I G₀ lift)
    (a : X.Point → X.Point) (σ : Equiv.Perm (A.SimpleWall p))
    (ha : ∀ g t, ∃ h s, a (X.place g t) = X.place h s ∧ ∀ i, s.val (σ i) = t.val i)
    (g : G₀) (t : Weights (A.SimpleWall p)) (ht : a (X.place g t) = X.place g t) :
    ∀ i, t.val (σ i) = t.val i := by
  obtain ⟨h, s, hs, hweights⟩ := ha g t
  have hst : s = t := ((X.place_eq h g s t).mp (hs.symm.trans ht)).1
  simpa only [hst] using hweights


open private minset_iff_minimizes isometry_euclideanSlice from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Geometry.FlatTorus

/-- An isometry translating a Euclidean apartment attains its minimum
displacement everywhere on the apartment. -/
theorem apartmentPoint_mem_minset {A X E : Type*} [Group A] [MetricSpace X]
    [MulAction A X] [IsIsometricSMul A X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → X) (hf : Isometry f) (a : A) (v : E)
    (htrans : ∀ x, a • f x = f (x + v)) (x : E) :
    f x ∈ minset (IsometryEquiv.constSMul a : X ≃ᵢ X) := by
  apply minset_iff_minimizes.mpr
  intro y
  have hp (n : ℕ) : (a ^ n) • f x = f (x + n • v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, ih, htrans, succ_nsmul, ← add_assoc]
  have hdist (n : ℕ) : dist ((a ^ n) • f x) (f x) = (n : ℝ) * ‖v‖ := by
    rw [hp, hf.dist_eq, dist_eq_norm, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul ℝ,
      norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
  have hstep (n : ℕ) : dist ((a ^ n) • y) y ≤ (n : ℝ) * dist (a • y) y := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        dist ((a ^ (n + 1)) • y) y
            ≤ dist ((a ^ (n + 1)) • y) ((a ^ n) • y) + dist ((a ^ n) • y) y :=
          dist_triangle _ _ _
        _ ≤ dist (a • y) y + (n : ℝ) * dist (a • y) y := by
          rw [pow_succ, mul_smul, dist_smul]
          exact add_le_add (le_refl _) ih
        _ = ((n + 1 : ℕ) : ℝ) * dist (a • y) y := by push_cast; ring
  have hbound (n : ℕ) : (n : ℝ) * ‖v‖ ≤ 2 * dist (f x) y + n * dist (a • y) y := by
    calc
      (n : ℝ) * ‖v‖ = dist ((a ^ n) • f x) (f x) := (hdist n).symm
      _ ≤ dist ((a ^ n) • f x) ((a ^ n) • y) + dist ((a ^ n) • y) y + dist y (f x) :=
        dist_triangle4 _ _ _ _
      _ ≤ 2 * dist (f x) y + n * dist (a • y) y := by
        rw [dist_smul, dist_comm y (f x)]
        linarith only [hstep n]
  have hmin : ‖v‖ ≤ dist (a • y) y := by
    by_contra! h
    have hgap : 0 < ‖v‖ - dist (a • y) y := sub_pos.mpr h
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * dist (f x) y / (‖v‖ - dist (a • y) y))
    have hlo := (div_lt_iff₀ hgap).mp hn
    linarith only [hlo, hbound n]
  change dist (f x) (a • f x) ≤ dist y (a • y)
  rw [dist_comm (f x), dist_comm y]
  have hone : dist (a • f x) (f x) = ‖v‖ := by simpa using hdist 1
  exact hone.trans_le hmin

/-- Commuting finite isometries preserve a flat of the lattice rank in their
fixed locus when the lattice acts by proper translations on an apartment. -/
theorem exists_flat_of_commuting_translations
    {X E Γ A : Type*} [MetricSpace X] [CompleteSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Group Γ] [Finite Γ] [MulAction Γ X] [IsIsometricSMul Γ X]
    [Group A] [MulAction A X] [IsIsometricSMul A X]
    (hX : CAT0 X) (f : E → X) (hf : Isometry f) (v : A → E)
    (htrans : ∀ a x, a • f x = f (x + v a))
    (hproper : ∀ b : ℝ, {a : A | ‖v a‖ ≤ b}.Finite)
    (hcomm : ∀ (γ : Γ) (a : A) (x : X), γ • (a • x) = a • (γ • x))
    (r : ℕ) (hr : Nonempty (A ≃* Multiplicative (Fin r → ℤ))) :
    ∃ e : EuclideanSpace ℝ (Fin r) → X, Isometry e ∧
      range e ⊆ MulAction.fixedPoints Γ X := by
  let Z := MulAction.fixedPoints Γ X
  let smulZ (a : A) (x : Z) : Z := ⟨a • (x : X), by
    intro γ
    rw [hcomm, x.property γ]⟩
  let : MulAction A Z :=
    { smul := smulZ
      one_smul x := Subtype.ext (one_smul A (x : X))
      mul_smul a b x := Subtype.ext (mul_smul a b (x : X)) }
  let : IsIsometricSMul A Z := ⟨fun a => Isometry.of_dist_eq fun x y =>
    dist_smul a (x : X) (y : X)⟩
  let g (a : A) : X ≃ᵢ X := IsometryEquiv.constSMul a
  have hmin (a : A) : f 0 ∈ minset (g a) :=
    apartmentPoint_mem_minset f hf a (v a) (htrans a) 0
  have horbit : MulAction.orbit Γ (f 0) ⊆ commonMinset g := by
    rintro _ ⟨γ, rfl⟩
    refine mem_iInter.mpr fun a => minset_iff_minimizes.mpr fun y => ?_
    change dist (γ • f 0) (a • (γ • f 0)) ≤ dist y (a • y)
    rw [← hcomm, dist_smul]
    have h := minset_iff_minimizes.mp (hmin a) (γ⁻¹ • y)
    change dist (f 0) (a • f 0) ≤ dist (γ⁻¹ • y) (a • (γ⁻¹ • y)) at h
    rwa [← hcomm, dist_smul] at h
  let c := circumcenter (MulAction.orbit Γ (f 0)) (MulAction.nonempty_orbit (f 0))
  have hc : c ∈ Z ∩ commonMinset g :=
    hX.finiteOrbit_circumcenter_mem (Finite.finite_mulAction_orbit (M := Γ) (f 0)) g horbit
  let z : Z := ⟨c, hc.1⟩
  obtain ⟨_, _, hZ, hComplete⟩ := hX.closedConvex_fixedPoints (G := Γ) ⟨c, hc.1⟩
  let : CompleteSpace Z := hComplete
  have hzmin (a : A) : ∀ y : Z, dist z (a • z) ≤ dist y (a • y) :=
    fun y => minset_iff_minimizes.mp (mem_iInter.mp hc.2 a) (y : X)
  have hzdist (a : A) : dist z (a • z) = ‖v a‖ := by
    change dist c (g a c) = ‖v a‖
    have hd : dist c (g a c) = dist (f 0) (g a (f 0)) := by
      exact (show c ∈ minset (g a) from mem_iInter.mp hc.2 a).trans (hmin a).symm
    rw [hd]
    change dist (f 0) (a • f 0) = _
    rw [htrans, zero_add, hf.dist_eq, dist_zero_left]
  have hproperZ : IsProperAction A Z := by
    intro K hK
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall z).mp hK.isBounded
    refine (hproper (2 * R)).subset ?_
    rintro a ⟨x, hx, hax⟩
    change ‖v a‖ ≤ 2 * R
    rw [← hzdist]
    have hx' := Metric.mem_closedBall.mp (hR hx)
    have hax' := Metric.mem_closedBall.mp (hR hax)
    calc
      dist z (a • z) ≤ dist z (a • x) + dist (a • x) (a • z) := dist_triangle _ _ _
      _ ≤ 2 * R := by
        rw [dist_smul, dist_comm z (a • x)]
        linarith
  have hss (a : A) : IsSemisimple (IsometryEquiv.constSMul a : Z ≃ᵢ Z) :=
    ⟨z, minset_iff_minimizes.mpr (hzmin a)⟩
  obtain ⟨_, Y, _, hY, _, e, _⟩ := CAT0.flatTorus r hr hZ hproperZ hss
  obtain ⟨y⟩ := hY.1.1
  refine ⟨fun x => ((e (WithLp.toLp 2 (y, x)) : Z) : X), ?_, ?_⟩
  · exact isometry_subtype_coe.comp (isometry_euclideanSlice _ e y)
  · rintro _ ⟨x, rfl⟩
    exact Subtype.property (e (WithLp.toLp 2 (y, x)) : Z)


open Specs.ExceptionalAffineBuilding (EuclideanApartment realAffine rationalPoint
  simplexPoint faceSubgroup cotype)

/-- In the marked complex, a flat whose points have weights constant on
the fibres of a partition into `d + 1` classes has dimension at most `d`. -/
theorem flat_dimension_le_of_orbit_weights
    {G V : Type u} {J : Type v} [Group G] [AddCommGroup V] [Module ℚ V]
    {A : ApartmentRoots ℚ V J} {p : V} {m : CoxeterMatrix (A.SimpleWall p)}
    {cs : CoxeterSystem m A.affineWeylGroup} {I G₀ : Subgroup G}
    {lift : A.affineWeylGroup → G} (X : Realization cs I G₀ lift) [Countable (Chamber I G₀)]
    {r d : ℕ} (o : A.SimpleWall p → Fin (d + 1)) (ho : Function.Surjective o)
    (f : EuclideanSpace ℝ (Fin r) → X.Point) (hf : Isometry f)
    (hw : ∀ x, ∃ g t, X.place g t = f x ∧ ∀ i j, o i = o j → t.val i = t.val j) :
    r ≤ d := by
  classical
  let B := A.SimpleWall p
  let : Fintype B := @Fintype.ofFinite B X.finite_types
  let W := Fin (d + 1) → ℝ
  let mass : W →ₗ[ℝ] ℝ := ∑ i : B, LinearMap.proj (o i)
  let pos : W →ₗ[ℝ] EuclideanApartment V :=
    ∑ i : B, (LinearMap.proj (o i)).smulRight (rationalPoint X.coordinates (X.vertex i))
  have hmass (x : W) : mass x = ∑ i : B, x (o i) := by
    simp only [mass, LinearMap.sum_apply]
    rfl
  have hpos (x : W) : pos x = ∑ i : B, x (o i) • rationalPoint X.coordinates (X.vertex i) := by
    simp only [pos, LinearMap.sum_apply, LinearMap.smulRight_apply]
    rfl
  have hB : Nonempty B := ⟨(ho 0).choose⟩
  let x₀ : W := fun _ => (Fintype.card B : ℝ)⁻¹
  have hx₀ : mass x₀ = 1 := by
    rw [hmass]
    simp [x₀, nsmul_eq_mul, (Nat.ne_of_gt (@Fintype.card_pos B _ hB))]
  have hmass_range : LinearMap.range mass = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro x
    exact ⟨x • x₀, by simp [hx₀]⟩
  have hker : Module.finrank ℝ (LinearMap.ker mass) = d := by
    have h := mass.finrank_range_add_finrank_ker
    rw [hmass_range, finrank_top, Module.finrank_self] at h
    have hW : Module.finrank ℝ W = d + 1 := by simp [W]
    omega
  let L := pos.comp mass.ker.subtype
  let S := LinearMap.range L
  have hS : Module.finrank ℝ S ≤ d := by
    rw [← hker]
    exact L.finrank_range_le
  let repr (g : Chamber I G₀) : G₀ := g.property.choose
  let w₁ : G₀ := ⟨lift 1, X.lift_mem 1⟩
  let chart (g : Chamber I G₀) (y : S) := X.chart (repr g * w₁⁻¹) (pos x₀ + y)
  have hchart (g : Chamber I G₀) : Isometry (chart g) := by
    exact (X.chart_isometry _).comp ((IsometryEquiv.addLeft (pos x₀)).isometry.comp
      isometry_subtype_coe)
  refine (dimension_le_of_euclidean_cover f hf chart hchart ?_).trans hS
  rintro _ ⟨x, rfl⟩
  obtain ⟨g, t, ht, hinv⟩ := hw x
  let g₁ : Chamber I G₀ := ⟨QuotientGroup.mk (g : G), g, rfl⟩
  have hg₁ : QuotientGroup.mk (repr g₁ : G) = (QuotientGroup.mk (g : G) : G ⧸ I) :=
    g₁.property.choose_spec
  have hre : X.place (repr g₁) t = X.place g t := by
    refine (X.place_eq _ _ _ _).mpr ⟨rfl, Subgroup.subset_closure (Or.inl ?_)⟩
    exact QuotientGroup.eq.mp hg₁
  let c : W := fun i => t.val (ho i).choose
  have hc (i : B) : c (o i) = t.val i := hinv _ _ (ho _).choose_spec
  have hmass_c : mass c = 1 := by
    rw [hmass]
    simpa only [hc, finsum_eq_sum_of_fintype] using t.property.2
  have hpos_c : pos c = simplexPoint X.coordinates X.vertex t := by
    change pos c = ∑ᶠ i, t.val i • rationalPoint X.coordinates (X.vertex i)
    rw [hpos, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr (by ext i; simp) (fun i _ => by rw [hc])
  let y : mass.ker := ⟨c - x₀, by simp [LinearMap.mem_ker, hmass_c, hx₀]⟩
  have hy : (pos x₀ + L y) = simplexPoint X.coordinates X.vertex t := by
    change pos x₀ + pos (c - x₀) = _
    rw [map_sub, add_sub_left_comm, sub_self, add_zero, hpos_c]
  apply mem_iUnion.mpr
  refine ⟨g₁, ⟨⟨L y, LinearMap.mem_range_self L y⟩, ?_⟩⟩
  change X.chart (repr g₁ * w₁⁻¹) (pos x₀ + L y) = f x
  rw [hy, ← ht, ← hre]
  have hplace := X.chart_place (repr g₁ * w₁⁻¹) 1 t
  change X.chart (repr g₁ * w₁⁻¹)
      (realAffine X.coordinates X.coordinates 1 (simplexPoint X.coordinates X.vertex t)) =
    X.place (repr g₁ * w₁⁻¹ * w₁) t at hplace
  have hlin : (AffineEquiv.linear (1 : V ≃ᵃ[ℚ] V)).toLinearMap = LinearMap.id := rfl
  simpa [Specs.ExceptionalRealAlcove.realAffine, hlin, LinearMap.baseChange_id] using hplace


/-- The rank bound in a marked realization. The finite action and the
translation lattice must act on this same metric complex. -/
theorem translation_rank_le_of_vertex_orbits
    {G V : Type u} {J : Type v} [Group G] [AddCommGroup V] [Module ℚ V]
    {A : ApartmentRoots ℚ V J} {p : V} {m : CoxeterMatrix (A.SimpleWall p)}
    {cs : CoxeterSystem m A.affineWeylGroup} {I G₀ : Subgroup G}
    {lift : A.affineWeylGroup → G} (X : Realization cs I G₀ lift)
    (hcover : (⋃ w, DoubleCoset.doubleCoset (lift w) I I) = (G₀ : Set G))
    (hfinite : ∀ w, (leftCosets I (lift w)).Finite)
    {Γ Λ : Type*} [Group Γ] [Finite Γ] [Group Λ]
    [MulAction Γ X.Point] [IsIsometricSMul Γ X.Point]
    [MulAction Λ X.Point] [IsIsometricSMul Λ X.Point]
    (γ : Γ) (σ : Equiv.Perm (A.SimpleWall p))
    (hg : ∀ g t, ∃ h s, γ • X.place g t = X.place h s ∧
      ∀ i, s.val (σ i) = t.val i)
    {r d : ℕ} (o : A.SimpleWall p → Fin (d + 1)) (ho : Function.Surjective o)
    (horbit : ∀ i j, o i = o j → ∃ n : ℕ, (σ ^ n) i = j)
    (a : G₀) (v : Λ → EuclideanApartment V)
    (htrans : ∀ l x, l • X.chart a x = X.chart a (x + v l))
    (hproper : ∀ b : ℝ, {l : Λ | ‖v l‖ ≤ b}.Finite)
    (hcomm : ∀ (γ' : Γ) (l : Λ) (x : X.Point), γ' • (l • x) = l • (γ' • x))
    (hr : Nonempty (Λ ≃* Multiplicative (Fin r → ℤ))) : r ≤ d := by
  let : Finite (A.SimpleWall p) := X.finite_types
  let : Countable (Chamber I G₀) := chamber_countable cs I G₀ lift hcover hfinite
  obtain ⟨f, hf, hfix⟩ := exists_flat_of_commuting_translations X.cat0 (X.chart a)
    (X.chart_isometry a) v htrans hproper hcomm r hr
  refine flat_dimension_le_of_orbit_weights X o ho f hf fun x => ?_
  obtain ⟨g, t, ht⟩ := X.place_surjective (f x)
  have hfγ : γ • X.place g t = X.place g t := ht ▸ hfix (mem_range_self x) γ
  have hweights := weights_fixed_of_place_fixed X (γ • ·) σ hg g t hfγ
  refine ⟨g, t, ht, fun i j hij => ?_⟩
  obtain ⟨n, rfl⟩ := horbit i j hij
  clear hij
  symm
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hweights, ih]


open Specs.ExceptionalAffineBruhat (FieldPoints LocalComparison)
open Specs.ExceptionalAffineBuilding (Building lengthZeroNormalizer typeChange)
open Specs.ExceptionalAffineRootSystems (alcoveStabilizer)
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra)
open scoped CategoryTheory.MonObj TensorProduct
attribute [local instance] integerAlgebra

section LengthZero

variable {K G Wf V : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
    {J : Type v} {D : BasedRootDatum.{u}} {M : Model D}
    {j : G →* FieldPoints M K} {A : ApartmentRoots ℚ V J} {p : V}
    {C : LocalComparison (j := j) (Wf := Wf) A p}

/-- For an actual length-zero normalizer point the type class acts on the
apartment by its actual affine normalizer value. -/
theorem affine_typeChange_of_lengthZero (B : Building C) (Q : C.TypeQuotient)
    (n : C.N) (hn : (n : G) ∈ lengthZeroNormalizer C) :
    (typeChange Q (n : G)).val.val = C.affine n := by
  let := Q.normal
  obtain ⟨n', hn', heq⟩ := hn
  have hnn' : n' = n := Subtype.ext heq
  subst n'
  obtain ⟨w, hw, hω⟩ := hn'
  let ω : alcoveStabilizer A (A.alcove p) := ⟨w, hw⟩
  have hω₀ : C.affine (Q.lift ω) = C.affine n :=
    (Q.affine_lift ω).trans hω
  let d := (Q.lift ω)⁻¹ * n
  have hd : d ∈ C.affine.ker := by
    change C.affine d = 1
    simp [d, hω₀]
  have hd₀ : (d : G) ∈ C.T₀ := by
    change (d : G) ∈ (Specs.ExceptionalIwahoriImageComparison.integralUnitTorus (K := K) M).comap j
    rw [← C.kernel]
    exact Subgroup.mem_map_of_mem _ hd
  have hdI : (d : G) ∈ C.I := (show (d : G) ∈ C.I ⊓ C.N from
    B.iwahori_inter_normalizer.symm ▸ hd₀).1
  have hdG : (d : G) ∈ C.G₀ := B.realization.iwahori_mem hdI
  have hdType : typeChange Q (d : G) = 1 := by
    change Q.quotient (QuotientGroup.mk (d : G)) = 1
    rw [(QuotientGroup.eq_one_iff (d : G)).mpr hdG, map_one]
  have hType : typeChange Q (n : G) = ω := by
    have hprod : (n : G) = (Q.lift ω : G) * (d : G) := by
      simp [d]
    rw [hprod, map_mul, hdType, mul_one]
    exact Q.quotient_lift ω
  rw [hType]
  exact hω

end LengthZero


open Specs.ExceptionalAffineRootSystems (IsRootCoordinate simpleReflection simpleRootValues)
open RootPairing

private theorem coordinates_of_reflection_word {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (word : List (Fin n)) {r : Fin n → ℤ} (h : IsRootCoordinate C r) :
    IsRootCoordinate C (word.foldl (fun v i => simpleReflection C i v) r) := by
  induction word generalizing r with
  | nil => exact h
  | cons j word ih => exact ih (h.reflect j)

/-- The candidate highest root of the pinned (E_6) base is in the
simple reflection orbit of a simple root. -/
theorem e6Highest_isRootCoordinate : IsRootCoordinate (exceptionalCartan 6) e6Highest := by
  let word : List (Fin 6) := [2, 3, 1, 4, 3, 2, 5, 4, 3, 1]
  convert coordinates_of_reflection_word word (IsRootCoordinate.simple (0 : Fin 6)) using 1
  funext i
  fin_cases i <;> decide

/-- The candidate highest root of the pinned (E_7) base is in the
simple reflection orbit of a simple root. -/
theorem e7Highest_isRootCoordinate : IsRootCoordinate (exceptionalCartan 7) e7Highest := by
  let word : List (Fin 7) := [2, 3, 1, 4, 3, 2, 5, 4, 3, 1, 6, 5, 4, 3, 2, 0]
  convert coordinates_of_reflection_word word (IsRootCoordinate.simple (0 : Fin 7)) using 1
  funext i
  fin_cases i <;> decide

private theorem root_sum_reflection
    {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {n : ℕ}
    (P : RootPairing J ℤ X Y) (b : Fin n → J)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : ∀ i j, C i j = P.pairing (b j) (b i))
    (r : Fin n → ℤ) (j : Fin n) :
    (∑ i, simpleReflection C j r i • P.root (b i)) =
      P.reflection (b j) (∑ i, r i • P.root (b i)) := by
  classical
  have hpair : C.mulVec r j = P.coroot' (b j) (∑ i, r i • P.root (b i)) := by
    simp only [Matrix.mulVec, dotProduct, hC, map_sum, map_zsmul,
      root_coroot'_eq_pairing, smul_eq_mul]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [P.reflection_apply, ← hpair]
  simp only [simpleReflection, Pi.sub_apply, Pi.smul_apply, sub_smul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

/-- Reflection coordinates lift to actual roots of a datum with the
specified Cartan entries. -/
theorem exists_root_of_isRootCoordinate
    {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {n : ℕ}
    (P : RootPairing J ℤ X Y) (b : Fin n → J)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : ∀ i j, C i j = P.pairing (b j) (b i))
    {r : Fin n → ℤ} (h : IsRootCoordinate C r) :
    ∃ a, P.root a = ∑ i, r i • P.root (b i) := by
  classical
  induction h with
  | simple i =>
    refine ⟨b i, ?_⟩
    symm
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  | reflect _ j ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨P.reflectionPerm (b j) a, by rw [root_sum_reflection P b hC, ← ha, root_reflectionPerm]⟩

private theorem exceptionalCartan_comm (n : ℕ) (i j : Fin n) :
    exceptionalCartan n i j = exceptionalCartan n j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp only [exceptionalCartan, ite_eq_right h, ite_eq_right (Ne.symm h)]
    rw [Finset.pair_comm i.val j.val]

/-- The actual simple reflection on the cocharacter apartment acts on
simple-root values by the Cartan row formula of the index calculation. -/
theorem simpleRootValues_reflection
    {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {n : ℕ}
    (P : RootPairing J ℤ X Y) (B : P.Base) (b : Fin n ≃ B.support)
    (hC : ∀ i j, P.pairing (b i) (b j) = exceptionalCartan n i j)
    (j : Fin n) (x : ℚ ⊗[ℤ] Y) :
    simpleRootValues P B b ℚ ((ApartmentRoots.split P ℚ).linearReflection (b j) x) =
      reflectValues j (simpleRootValues P B b ℚ x) := by
  let A := ApartmentRoots.split P ℚ
  ext i
  change A.root (b i) (x - (A.root (b j) x) • A.coroot (b j)) =
    A.root (b i) x - (exceptionalCartan n j i : ℚ) * A.root (b j) x
  have hpair : A.root (b i) (A.coroot (b j)) = (exceptionalCartan n j i : ℚ) := by
    change RootData.extendFunctional ℚ (P.root' (b i)) (1 ⊗ₜ[ℤ] P.coroot (b j)) = _
    simp [hC, exceptionalCartan_comm n i j]
  simp [map_sub, map_smul, hpair, mul_comm]


private theorem isRootCoordinate_neg {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    (hdiag : ∀ i, C i i = 2) {r : Fin n → ℤ} (hr : IsRootCoordinate C r) :
    IsRootCoordinate C (-r) := by
  classical
  induction hr with
  | simple i =>
    have he : simpleReflection C i (Pi.single i 1) = -Pi.single i (1 : ℤ) := by
      rw [simpleReflection, Matrix.mulVec_single_one, Matrix.col_apply, hdiag]
      ext j
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    rw [← he]
    exact (IsRootCoordinate.simple i).reflect i
  | @reflect r _ i ih =>
    have he : simpleReflection C i (-r) = -simpleReflection C i r := by
      simp only [simpleReflection, Matrix.mulVec_neg, Pi.neg_apply, neg_smul]
      abel
    rw [← he]
    exact ih.reflect i

/-- The actual roots of a finite based integral root datum have coordinates in
the orbit of the simple roots under the marked simple reflections. -/
theorem exists_isRootCoordinate_of_root
    {J X Y : Type*} [Finite J] [AddCommGroup X] [AddCommGroup Y] {n : ℕ}
    (P : RootPairing J ℤ X Y) [P.IsReduced] (B : P.Base) (b : Fin n ≃ B.support)
    {C : Matrix (Fin n) (Fin n) ℤ} (hC : ∀ i j, C i j = P.pairing (b j) (b i)) (a : J) :
    ∃ r : Fin n → ℤ, IsRootCoordinate C r ∧ P.root a = ∑ i, r i • P.root (b i) := by
  classical
  refine B.induction_reflect (p := fun j =>
    ∃ r : Fin n → ℤ, IsRootCoordinate C r ∧ P.root j = ∑ i, r i • P.root (b i)) a ?_ ?_ ?_
  · rintro i ⟨r, hr, he⟩
    have hdiag (j : Fin n) : C j j = 2 := (hC j j).trans (P.pairing_same _)
    refine ⟨-r, isRootCoordinate_neg hdiag hr, ?_⟩
    rw [P.root_reflectionPerm, P.reflection_apply_self, he]
    simp [neg_smul, Finset.sum_neg_distrib]
  · intro i hi
    let k := b.symm ⟨i, hi⟩
    have hk : (b k : J) = i := congrArg Subtype.val (b.apply_symm_apply ⟨i, hi⟩)
    refine ⟨Pi.single k 1, IsRootCoordinate.simple k, ?_⟩
    symm
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  · rintro i j ⟨r, hr, he⟩ hj
    let k := b.symm ⟨j, hj⟩
    have hk : (b k : J) = j := congrArg Subtype.val (b.apply_symm_apply ⟨j, hj⟩)
    refine ⟨simpleReflection C k r, hr.reflect k, ?_⟩
    rw [root_sum_reflection P (fun l => (b l : J)) hC, ← he, hk, P.root_reflectionPerm]

/-- Successive marked simple reflections on cocharacters induce the same
word on the simple-root values. -/
theorem simpleRootValues_reflectionWord
    {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {n : ℕ}
    (P : RootPairing J ℤ X Y) (B : P.Base) (b : Fin n ≃ B.support)
    (hC : ∀ i j, P.pairing (b i) (b j) = exceptionalCartan n i j)
    (word : List (Fin n)) (x : ℚ ⊗[ℤ] Y) :
    simpleRootValues P B b ℚ
      (word.foldl (fun z j => (ApartmentRoots.split P ℚ).linearReflection (b j) z) x) =
      reflectWord word (simpleRootValues P B b ℚ x) := by
  induction word generalizing x with
  | nil => rfl
  | cons j word ih =>
    rw [List.foldl_cons, ih, simpleRootValues_reflection P B b hC]
    rfl


/-- An injective real-linear realization of the integer lattice has finitely
many translation vectors in each bounded ball. -/
theorem finite_bounded_integer_translations
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {r : ℕ} (e : (Fin r → ℝ) →ₗ[ℝ] E) (he : Function.Injective e) (R : ℝ) :
    {z : Fin r → ℤ | ‖e (fun i => (z i : ℝ))‖ ≤ R}.Finite := by
  let q := LinearEquiv.ofInjective e he
  let b := (Pi.basisFun ℝ (Fin r)).map q
  let j (z : Fin r → ℤ) : e.range := q (fun i => (z i : ℝ))
  have hj : Function.Injective j := by
    intro z w h
    have h' := q.injective h
    funext i
    exact Int.cast_injective (α := ℝ) (congrFun h' i)
  have hz (z : Fin r → ℤ) : j z ∈ Submodule.span ℤ (range b) := by
    rw [b.mem_span_iff_repr_mem ℤ]
    intro i
    exact ⟨z i, by simp [j, b]⟩
  have hf := ZSpan.setFinite_inter b
    (Metric.isBounded_closedBall (x := (0 : e.range)) (r := R))
  refine (hf.preimage (f := j) hj.injOn).subset ?_
  intro z hzR
  exact ⟨by simpa [Metric.mem_closedBall, j, q, dist_zero_right] using hzR, hz z⟩

open Specs.ExceptionalAffineBruhat (residue)

/-- Finiteness of the residue field makes each individual Bruhat cell finite
in the chamber quotient. -/
theorem finite_bruhat_cells
    {K G Wf V : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Group G] [Group Wf] [AddCommGroup V] [Module ℚ V]
    {J : Type v} {D : BasedRootDatum.{u}} {M : Model D}
    {j : G →* FieldPoints M K} {A : ApartmentRoots ℚ V J} {p : V}
    {C : LocalComparison (j := j) (Wf := Wf) A p}
    (data : C.Bruhat (Nat.card (residue K))) (w : A.affineWeylGroup) :
    (leftCosets C.I (C.lift w : G)).Finite := by
  apply Set.finite_coe_iff.mp
  apply Nat.finite_of_card_ne_zero
  rw [data.coset_count]
  let : Finite (residue K) := (LinearAlgebraicGroups.Arithmetic.localField_properties K).2.1
  exact pow_ne_zero _ (Nat.card_pos (α := residue K)).ne'


/-- Invariance under the inverse permutation gives the same subspace. -/
theorem invariantRootValues_symm {n : ℕ} (highest : Fin n → ℤ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    invariantDirections highest σ.symm = invariantDirections highest σ := by
  ext r
  change (∀ i, directionalValues highest r (σ.symm i) = directionalValues highest r i) ↔
    (∀ i, directionalValues highest r (σ i) = directionalValues highest r i)
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using (h (σ i)).symm
  · intro h i
    simpa only [Equiv.apply_symm_apply] using (h (σ.symm i)).symm

/-- The invariant directions of a nontrivial E₆ rotation have dimension two. -/
theorem e6InvariantRootValues_finrank :
    Module.finrank ℚ (invariantDirections e6Highest e6Rotate) = 2 := by
  let U := invariantDirections e6Highest e6Rotate
  let f : U →ₗ[ℚ] (Fin 2 → ℚ) :=
    LinearMap.pi fun i => (LinearMap.proj (![1, 3] i)).comp U.subtype
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have h₁ : (x : Fin 6 → ℚ) 1 = (y : Fin 6 → ℚ) 1 := congrFun h 0
      have h₂ : (x : Fin 6 → ℚ) 3 = (y : Fin 6 → ℚ) 3 := congrFun h 1
      obtain ⟨a, b, hx⟩ := e6InvariantValues x.val x.property
      obtain ⟨a', b', hy⟩ := e6InvariantValues y.val y.property
      rw [hx, hy] at h₁ h₂
      change a = a' at h₁
      change b = b' at h₂
      exact Subtype.ext (hx.trans (h₁ ▸ h₂ ▸ hy.symm))
    · intro z
      refine ⟨⟨![-2*z 0-z 1, z 0, z 0, z 1, z 0, -2*z 0-z 1],
        (e6InvariantValues_reflect (z 0) (z 1)).1⟩, ?_⟩
      funext i
      fin_cases i <;> rfl
  simpa using (LinearEquiv.ofBijective f hf).finrank_eq

/-- The invariant directions of the E₇ reversal have dimension four. -/
theorem e7InvariantRootValues_finrank :
    Module.finrank ℚ (invariantDirections e7Highest e7Reverse) = 4 := by
  let U := invariantDirections e7Highest e7Reverse
  let f : U →ₗ[ℚ] (Fin 4 → ℚ) :=
    LinearMap.pi fun i => (LinearMap.proj (![0, 2, 3, 1] i)).comp U.subtype
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have h₁ : (x : Fin 7 → ℚ) 0 = (y : Fin 7 → ℚ) 0 := congrFun h 0
      have h₂ : (x : Fin 7 → ℚ) 2 = (y : Fin 7 → ℚ) 2 := congrFun h 1
      have h₃ : (x : Fin 7 → ℚ) 3 = (y : Fin 7 → ℚ) 3 := congrFun h 2
      have h₄ : (x : Fin 7 → ℚ) 1 = (y : Fin 7 → ℚ) 1 := congrFun h 3
      obtain ⟨a, b, c, d, hx⟩ := e7InvariantValues x.val x.property
      obtain ⟨a', b', c', d', hy⟩ := e7InvariantValues y.val y.property
      rw [hx, hy] at h₁ h₂ h₃ h₄
      change a = a' at h₁
      change b = b' at h₂
      change c = c' at h₃
      change d = d' at h₄
      exact Subtype.ext (hx.trans (h₁ ▸ h₂ ▸ h₃ ▸ h₄ ▸ hy.symm))
    · intro z
      refine ⟨⟨![z 0, z 3, z 1, z 2, z 1, z 0, -2*z 0-3*z 1-2*z 2-z 3],
        (e7InvariantValues_reflect (z 0) (z 1) (z 2) (z 3)).1⟩, ?_⟩
      funext i
      fin_cases i <;> rfl
  simpa using (LinearEquiv.ofBijective f hf).finrank_eq

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped WithZero

open Specs.ExceptionalAffineBruhat (ExceptionalNumbering IsUnramifiedLocalExtension SplitLevel)
open Specs.ExceptionalAffineBuilding (SplitBuildingLevel)
open Specs.ExceptionalStableAlcoveRepresentatives (IsArithmeticFrobenius)
open Specs.ExceptionalTwistedTraceComparison (PointCocycle Twist)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover markedGroundPoint)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.AutomorphismSequence (AdjointQuotient)
open Specs.IntegralSemisimpleModel (fibre forgetFibrePoint)

open private exists_normalized_uniformizer
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves

private abbrev isometryAction {L X : Type*} [Monoid L] [MetricSpace X]
    (action : L →* (X ≃ᵢ X)) : MulAction L X where
  smul g x := action g x
  one_smul x := by
    change action 1 x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    change action (g * h) x = action g (action h x)
    rw [map_mul]
    rfl

section FiniteInnerTwist

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {Y : SplitLevel K c p p' e}

set_option backward.isDefEq.respectTransparency false in
private theorem splitRank_le_of_typeOrbits
    (hFK : IsUnramifiedLocalExtension F K) (B : SplitBuildingLevel Y)
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    (iG : G.val ≅ (fibre F).obj M.group) (iQ : Q.quotient.val ≅ (fibre F).obj M'.group)
    (hQ : Q.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map c.map)
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a) (σ : Gal(K/F))
    (hσ : IsArithmeticFrobenius σ) {d : ℕ}
    (o : (ApartmentRoots.split E.datum ℚ).SimpleWall p' → Fin (d + 1))
    (ho : Function.Surjective o)
    (horbit : ∀ i j, o i = o j → ∃ m : ℕ,
      (Y.typeQuotient.wallPerm (typeChange Y.typeQuotient
          (forgetFibrePoint M'.group (CommAlgCat.of F K) (a.val σ ≫ iQ.hom.hom.hom))) ^ m) i = j) :
    ∀ (S : ClosedSubgroup T.group.val) (r : ℕ), IsSplitOfRank S.group r → r ≤ d := by
  obtain ⟨_, _, twist, _, _, hweights, htranslations⟩ :=
    ExceptionalInnerUniformizerTranslations.uniformizerTranslations F K hFK c Y B G Q iG iQ hQ a T
  obtain ⟨π, hπ⟩ := exists_normalized_uniformizer F
  intro S r hS
  obtain ⟨s⟩ := hS
  obtain ⟨_, _, lattice, g, v, _, _, hinj, hcomm, htranslate⟩ := htranslations S r s.symm π hπ
  let act := B.adjoint.action.comp lattice
  let X := B.ad.realization
  let : MulAction (Gal(K/F)) X.Point := isometryAction twist
  let : IsIsometricSMul (Gal(K/F)) X.Point := ⟨fun τ => (twist τ).isometry⟩
  let : MulAction (Multiplicative (Fin r → ℤ)) X.Point := isometryAction act
  let : IsIsometricSMul (Multiplicative (Fin r → ℤ)) X.Point := ⟨fun z => (act z).isometry⟩
  refine translation_rank_le_of_vertex_orbits X Y.ad_bruhat.cover
    (finite_bruhat_cells Y.ad_bruhat) σ _ (hweights σ hσ) o ho horbit g
    (fun z => v (fun i => (z.toAdd i : ℝ))) ?_ ?_ ?_ ⟨MulEquiv.refl _⟩
  · exact fun z x => htranslate z.toAdd x
  · intro R
    exact (finite_bounded_integer_translations v hinj R).preimage Multiplicative.toAdd.injective.injOn
  · exact fun τ z x => (hcomm z τ x).symm

end FiniteInnerTwist

open Specs.ExceptionalInnerAlcoveSymmetries (MarkedAlcoveSymmetriesFor fixedDirections)
open Specs.ExceptionalInnerStandardTorusDescent (markedCocharacterMap)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
private theorem innerIndex_of_markedAlcove {n r : ℕ} {highest : Fin n → ℤ}
    {permutations : Set (Equiv.Perm (Fin (n + 1)))} {black : Set (Fin n)}
    (hn : n = 6 ∨ n = 7) (alcoves : MarkedAlcoveSymmetriesFor.{u} n r highest permutations)
    (orbit : Fin (n + 1) → Fin (r + 1)) (ho : Function.Surjective orbit)
    (hcycles : ∀ τ ∈ permutations, ∀ i j, orbit i = orbit j → ∃ m : ℕ, (τ ^ m) i = j)
    (word : List (Fin n))
    (hblack : ∀ τ ∈ permutations,
      VanishingNodes (reflectWord word '' invariantDirections highest τ) = black)
    (hpositive : ∀ τ ∈ permutations,
      ∃ v ∈ reflectWord word '' invariantDirections highest τ, ∀ i ∉ black, 0 < v i) :
    InnerIndex.{u} n r highest permutations black := by
  unfold InnerIndex
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ hFK D E M M' c b b' hb hb' hsc had p p' e Y B A hp
    G Q iG iQ hQ a T σ hσ t ht hne
  let v : Y.ad.N := ⟨t, (Subgroup.mem_map.mp ht).choose_spec.2 ▸
    (Subgroup.mem_map.mp ht).choose.property⟩
  let L := (Y.ad.affine v).linear
  let perm := Y.typeQuotient.wallPerm (typeChange Y.typeQuotient t)
  obtain ⟨l, coord, hcoord, _, _, hwall, haction⟩ :=
    alcoves F K hFK c b b' hb hb' hsc had Y B hp
  obtain ⟨_, _, τ, hτ, hl, _, _, hrank⟩ := haction v ht hne
  have hpower (m : ℕ) (i : Fin (n + 1)) : (perm ^ m) (l i) = l ((τ ^ m) i) := by
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply, ih]
      exact hl _
  let o := orbit ∘ l.symm
  have horbit (i j : A.SimpleWall p') (h : o i = o j) : ∃ m : ℕ, (perm ^ m) i = j := by
    obtain ⟨m, hm⟩ := hcycles τ hτ (l.symm i) (l.symm j) h
    refine ⟨m, ?_⟩
    simpa only [Equiv.apply_symm_apply] using (hpower m (l.symm i)).trans (congrArg l hm)
  have hbound := splitRank_le_of_typeOrbits hFK B iG iQ hQ T σ hσ o
    (ho.comp l.symm.surjective) horbit
  refine ⟨⟨l, ?_, τ, hτ, hl⟩, ?_⟩
  · intro i x
    have hx : coord x = simpleRootValues E.datum E.base b' ℚ x := DFunLike.congr_fun hcoord x
    simpa only [hx] using hwall i x
  obtain ⟨j, f, hj, hf, hstd⟩ := ExceptionalInnerStandardTorusDescent.descendedStandardTorus
    F K hFK c n b b' hn hb hb' hsc had Y B hp G Q iG iQ hQ a T σ hσ ht
  obtain ⟨bAd, hbAd, _, _, g, hg, _, hweyl⟩ :=
    ExceptionalInnerWeylDirections.markedWeylDirections K c Y b hn hb hb'.1 word
  obtain ⟨_, coordAd, hcoordAd, _, _, _, hactionAd⟩ :=
    alcoves F K hFK c b bAd hb hbAd hsc had Y B hp
  obtain ⟨_, _, ρ, hρ, _, _, hfixed, _⟩ := hactionAd v ht hne
  have hvalues : simpleRootValues E.datum E.base bAd ℚ ''
      (LinearMap.ker (L.toLinearMap - LinearMap.id) : Set _) =
        (invariantDirections highest ρ : Set _) := by
    change simpleRootValues E.datum E.base bAd ℚ '' (fixedDirections L : Set _) = _
    rw [← Submodule.map_coe, ← hcoordAd, hfixed]
  have hadapt := ExceptionalInnerIndexParabolic.adaptedIndexParabolic c Y.sc_fibre f Y.sc.N L
    hstd r hbound hrank b black g hg
  obtain ⟨U, S, uK, hU, hS, hrS, hSU, hu, J, sK, jK, hJ, hSJ, hconj, hB, hchars⟩ :=
    hadapt (by
      intro H _ s hs d hd
      have himage := hweyl d hd s
      dsimp only at himage
      rw [hs, hvalues] at himage
      constructor
      · intro i hi y hy
        have hz := Set.mem_image_of_mem (simpleRootValues D.datum D.base b ℚ) hy
        rw [himage] at hz
        have hi' : i ∈ VanishingNodes (reflectWord word '' invariantDirections highest ρ) := by
          rwa [hblack ρ hρ]
        exact hi' _ hz
      · obtain ⟨q, hq, hqpos⟩ := hpositive ρ hρ
        rw [← himage] at hq
        obtain ⟨y, hy, hval⟩ := hq
        refine ⟨y, hy, fun i hi => ?_⟩
        change 0 < simpleRootValues D.datum D.base b ℚ y i
        rw [hval]
        exact hqpos i hi)
  exact ⟨j, f, hj, hf, hbound, U, S, uK, hU, hS, hrS, hSU, hu,
    g, J, sK, jK, hg, hJ, hSJ, hconj, hB, hchars⟩

private theorem e6InverseOrbit_iff (i j : Fin 7) :
    e6Orbit i = e6Orbit j ↔ ∃ k : Fin 3, (e6Rotate.symm ^ (k : ℕ)) i = j := by
  revert i j
  decide

private theorem e6_orbit_of_rotation (τ : Equiv.Perm (Fin 7))
    (hτ : τ ∈ ({e6Rotate, e6Rotate.symm} : Set (Equiv.Perm (Fin 7))))
    (i j : Fin 7) (h : e6Orbit i = e6Orbit j) : ∃ k : ℕ, (τ ^ k) i = j := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
  rcases hτ with rfl | rfl
  · obtain ⟨k, hk⟩ := (e6Orbit_iff i j).mp h
    exact ⟨k, hk⟩
  · obtain ⟨k, hk⟩ := (e6InverseOrbit_iff i j).mp h
    exact ⟨k, hk⟩

private theorem e6_invariantDirections_of_rotation (τ : Equiv.Perm (Fin 7))
    (hτ : τ ∈ ({e6Rotate, e6Rotate.symm} : Set (Equiv.Perm (Fin 7)))) :
    invariantDirections e6Highest τ = invariantDirections e6Highest e6Rotate := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hτ
  rcases hτ with rfl | rfl
  · rfl
  · exact invariantRootValues_symm e6Highest e6Rotate

private theorem e6_positive_direction :
    ∃ v ∈ reflectWord e6Word '' invariantDirections e6Highest e6Rotate,
      ∀ i ∉ e6Black, 0 < v i := by
  have h := e6InvariantValues_reflect 1 1
  refine ⟨![0, 1, 0, 1, 0, 0], ⟨_, h.1, h.2⟩, ?_⟩
  intro i hi
  fin_cases i <;> simp_all [e6Black]

private theorem e7_positive_direction :
    ∃ v ∈ reflectWord e7Word '' invariantDirections e7Highest e7Reverse,
      ∀ i ∉ e7Black, 0 < v i := by
  have h := e7InvariantValues_reflect 1 1 1 1
  refine ⟨![1, 0, 1, 1, 0, 1, 0], ⟨_, h.1, h.2⟩, ?_⟩
  intro i hi
  fin_cases i <;> simp_all [e7Black]

/-- The inner exceptional forms represented by nontrivial alcove symmetries
have split ranks two and four with the indicated absolute black nodes. -/
theorem exceptionalInnerTitsIndices : ExceptionalInnerTitsIndices.{u} := by
  refine ⟨e6IndexCalculation, e7IndexCalculation, ?_, ?_⟩
  · refine innerIndex_of_markedAlcove (Or.inl rfl)
      ExceptionalInnerAlcoveSymmetries.markedAlcoveSymmetries.{u}.1 e6Orbit e6Orbit_surjective
      e6_orbit_of_rotation e6Word ?_ ?_
    · intro τ hτ
      rw [e6_invariantDirections_of_rotation τ hτ]
      exact e6IndexCalculation.2.2.2.2
    · intro τ hτ
      rw [e6_invariantDirections_of_rotation τ hτ]
      exact e6_positive_direction
  · refine innerIndex_of_markedAlcove (Or.inr rfl)
      ExceptionalInnerAlcoveSymmetries.markedAlcoveSymmetries.{u}.2 e7Orbit e7Orbit_surjective
      ?_ e7Word ?_ ?_
    · intro τ hτ i j hij
      have h : τ = e7Reverse := Set.mem_singleton_iff.mp hτ
      subst τ
      obtain ⟨k, hk⟩ := (e7Orbit_iff i j).mp hij
      exact ⟨k, hk⟩
    · intro τ hτ
      rw [Set.mem_singleton_iff.mp hτ]
      exact e7IndexCalculation.2.2.2.2
    · intro τ hτ
      rw [Set.mem_singleton_iff.mp hτ]
      exact e7_positive_direction

end LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndices
