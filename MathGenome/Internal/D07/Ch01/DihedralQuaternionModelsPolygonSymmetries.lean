import MathGenome.Internal.Specs.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Geometric dihedral groups (paper.tex:363–369).

We first prove that arbitrary preserving isometries fix the centroid; only
then do we apply the classification of real-linear isometries of ℂ.
This proves that the explicit action is exhaustive on the whole plane.
Conjugation by a similarity covers every center, size and initial vertex.
-/
noncomputable section
namespace D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
open Specs.D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
open Complex
open scoped ComplexConjugate

lemma primitive_root (n : ℕ) [NeZero n] : IsPrimitiveRoot (root n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

lemma vertex_injective (n : ℕ) [NeZero n] :
    Function.Injective (fun i : Fin n => root n ^ i.val) := by
  intro i j h
  exact Fin.ext ((primitive_root n).pow_inj i.isLt j.isLt h)

lemma mem_vertices_iff (n : ℕ) [NeZero n] (z : ℂ) :
    z ∈ vertices n 0 1 ↔ z ^ n = 1 := by
  simp only [vertices, Set.mem_range, one_mul, zero_add]
  constructor
  · rintro ⟨i, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, (primitive_root n).pow_eq_one, one_pow]
  · intro hz
    obtain ⟨i, hi, he⟩ := (primitive_root n).eq_pow_of_pow_eq_one hz
    exact ⟨⟨i, hi⟩, he⟩

lemma turn_apply (n : ℕ) (z : ℂ) : turn n z = root n * z := by
  simp only [turn, LinearIsometryEquiv.coe_toIsometryEquiv, rotation_apply, root,
    Circle.coe_exp, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  congr 2
  ring

lemma mirror_apply (z : ℂ) : mirror z = conj z := rfl

/-- The centroid of the canonical polygon is zero. -/
lemma vertex_sum (n : ℕ) [NeZero n] (hn : 1 < n) :
    ∑ i : Fin n, root n ^ i.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  exact (primitive_root n).geom_sum_eq_zero hn

/-- A symmetry permutes the vertices, so it preserves their unweighted sum. -/
lemma sum_images (n : ℕ) [NeZero n]
    (f : symmetryGroup (vertices n 0 1)) :
    ∑ i : Fin n, f.val (root n ^ i.val) = ∑ i : Fin n, root n ^ i.val := by
  classical
  have hmem (i : Fin n) : f.val (root n ^ i.val) ∈ vertices n 0 1 :=
    (f.property _).2 (by exact ⟨i, by simp⟩)
  have hex (i : Fin n) : ∃ j : Fin n, root n ^ j.val = f.val (root n ^ i.val) := by
    simpa only [vertices, Set.mem_range, one_mul, zero_add] using hmem i
  choose σ hσ using hex
  have hinj : Function.Injective σ := by
    intro i j hij
    apply vertex_injective n
    apply f.val.injective
    rw [← hσ i, ← hσ j, hij]
  exact Fintype.sum_bijective σ ((Finite.injective_iff_bijective).mp hinj)
    _ _ (fun i => (hσ i).symm)

/-- No unproved assumption that the center is fixed is built into the group.
It follows from its centroid and Mazur–Ulam's theorem. -/
lemma fixes_center (n : ℕ) [NeZero n] (hn : 1 < n)
    (f : symmetryGroup (vertices n 0 1)) : f.val 0 = 0 := by
  have hsum := map_sum (f.val.toRealLinearIsometryEquiv).toLinearEquiv.toLinearMap
    (fun i : Fin n => root n ^ i.val) Finset.univ
  change f.val.toRealLinearIsometryEquiv (∑ i : Fin n, root n ^ i.val) =
    ∑ i : Fin n, (f.val (root n ^ i.val) - f.val 0) at hsum
  rw [vertex_sum n hn, map_zero, Finset.sum_sub_distrib, sum_images,
    vertex_sum n hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
  have hz : n • f.val 0 = 0 := by simpa using hsum.symm
  exact (smul_eq_zero.mp hz).resolve_left (NeZero.ne n)

/-- The primitive root regarded as an actual unit-length complex scalar. -/
def rootCircle (n : ℕ) [NeZero n] : Circle :=
  ⟨root n, by
    change root n ∈ Metric.sphere 0 1
    exact mem_sphere_zero_iff_norm.mpr ((primitive_root n).norm'_eq_one (NeZero.ne n))⟩

lemma primitive_circle (n : ℕ) [NeZero n] : IsPrimitiveRoot (rootCircle n) n where
  pow_eq_one := Circle.ext (by exact (primitive_root n).pow_eq_one)
  dvd_of_pow_eq_one k hk := (primitive_root n).dvd_of_pow_eq_one k
    (congrArg (fun z : Circle => (z : ℂ)) hk)

def phase (n : ℕ) [NeZero n] (i : ZMod n) : Circle := rootCircle n ^ i.val

lemma phase_coe (n : ℕ) [NeZero n] (i : ZMod n) :
    (phase n i : ℂ) = root n ^ i.val := rfl

@[simp] lemma phase_zero (n : ℕ) [NeZero n] : phase n 0 = 1 := by
  simp [phase]

lemma phase_add (n : ℕ) [NeZero n] (i j : ZMod n) :
    phase n (i + j) = phase n i * phase n j := by
  dsimp [phase]
  rw [ZMod.val_add]
  have hmod := pow_mod_orderOf (rootCircle n) (i.val + j.val)
  rw [← (primitive_circle n).eq_orderOf] at hmod
  exact hmod.trans (pow_add _ _ _)

@[simp] lemma phase_neg (n : ℕ) [NeZero n] (i : ZMod n) :
    phase n (-i) = (phase n i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← phase_add, neg_add_cancel, phase_zero]

lemma phase_sub (n : ℕ) [NeZero n] (i j : ZMod n) :
    phase n (i - j) = phase n i * (phase n j)⁻¹ := by
  rw [sub_eq_add_neg, phase_add, phase_neg]

lemma phase_injective (n : ℕ) [NeZero n] : Function.Injective (phase n) := by
  intro i j h
  have hval := (primitive_root n).pow_inj (ZMod.val_lt i) (ZMod.val_lt j)
    (congrArg (fun z : Circle => (z : ℂ)) h)
  exact ZMod.val_injective n hval

/-- The abstract dihedral model acts by genuine isometries of the entire plane. -/
def geometricAction (n : ℕ) [NeZero n] : DihedralGroup n →* (ℂ ≃ᵢ ℂ) where
  toFun
    | .r i => (rotation (phase n i)).toIsometryEquiv
    | .sr i => ((rotation (phase n i)).trans conjLIE).toIsometryEquiv
  map_one' := by
    apply IsometryEquiv.ext
    intro z
    change rotation (phase n 0) z = z
    simp
  map_mul' := by
    rintro (i | i) (j | j) <;> apply IsometryEquiv.ext <;> intro z
    · change (phase n (i + j) : ℂ) * z = (phase n i : ℂ) * ((phase n j : ℂ) * z)
      simp [phase_add, mul_assoc]
    · change conj ((phase n (j - i) : ℂ) * z) =
        (phase n i : ℂ) * conj ((phase n j : ℂ) * z)
      simp [phase_sub, map_mul, ← Circle.coe_inv_eq_conj, mul_assoc, mul_comm]
    · change conj ((phase n (i + j) : ℂ) * z) =
        conj ((phase n i : ℂ) * ((phase n j : ℂ) * z))
      simp [phase_add, mul_assoc]
    · change (phase n (j - i) : ℂ) * z =
        conj ((phase n i : ℂ) * conj ((phase n j : ℂ) * z))
      simp [phase_sub, map_mul, ← Circle.coe_inv_eq_conj, mul_comm, mul_left_comm]

@[simp] lemma geometricAction_r (n : ℕ) [NeZero n] (i : ZMod n) (z : ℂ) :
    geometricAction n (.r i) z = (phase n i : ℂ) * z := rfl

@[simp] lemma geometricAction_sr (n : ℕ) [NeZero n] (i : ZMod n) (z : ℂ) :
    geometricAction n (.sr i) z = conj ((phase n i : ℂ) * z) := rfl

lemma phase_pow (n : ℕ) [NeZero n] (i : ZMod n) : (phase n i : ℂ) ^ n = 1 := by
  rw [phase_coe, ← pow_mul, mul_comm, pow_mul, (primitive_root n).pow_eq_one, one_pow]

lemma action_preserves (n : ℕ) [NeZero n] (d : DihedralGroup n) :
    geometricAction n d ∈ symmetryGroup (vertices n 0 1) := by
  intro z
  rw [mem_vertices_iff, mem_vertices_iff]
  cases d with
  | r i => simp [mul_pow, phase_pow]
  | sr i =>
      simp only [geometricAction_sr, ← map_pow, mul_pow, phase_pow, one_mul]
      constructor
      · intro h
        simpa using congrArg conj h
      · intro h
        rw [h, map_one]

/-- The homomorphism into the complete geometric symmetry group. -/
def geometricHom (n : ℕ) [NeZero n] :
    DihedralGroup n →* symmetryGroup (vertices n 0 1) :=
  (geometricAction n).codRestrict _ (action_preserves n)

lemma phase_natCast (n : ℕ) [NeZero n] (k : ℕ) :
    phase n (k : ZMod n) = rootCircle n ^ k := by
  dsimp [phase]
  rw [ZMod.val_natCast]
  have hmod := pow_mod_orderOf (rootCircle n) k
  rwa [← (primitive_circle n).eq_orderOf] at hmod

lemma geometricHom_injective (n : ℕ) [NeZero n] :
    Function.Injective (geometricHom n) := by
  apply (injective_iff_map_eq_one _).2
  intro d hd
  have h1 := congrArg (fun f : symmetryGroup (vertices n 0 1) => f.val 1) hd
  have hI := congrArg (fun f : symmetryGroup (vertices n 0 1) => f.val I) hd
  cases d with
  | r i =>
      change (phase n i : ℂ) * 1 = 1 at h1
      have hi : i = 0 := phase_injective n (Circle.ext (by simpa using h1))
      simp [hi]
  | sr i =>
      change conj ((phase n i : ℂ) * 1) = 1 at h1
      have hc : (phase n i : ℂ) = 1 := by
        simpa using congrArg conj h1
      change conj ((phase n i : ℂ) * I) = I at hI
      have him := congrArg Complex.im hI
      norm_num [hc] at him

/-- Exhaustion of all preserving isometries, not just of generated words. -/
lemma geometricHom_surjective (n : ℕ) [NeZero n] (hn : 1 < n) :
    Function.Surjective (geometricHom n) := by
  intro f
  let g := f.val.toRealLinearIsometryEquivOfMapZero (fixes_center n hn f)
  have hg (z : ℂ) : g z = f.val z := rfl
  have hmem : f.val 1 ∈ vertices n 0 1 :=
    (f.property 1).2 ((mem_vertices_iff n 1).2 (one_pow n))
  obtain ⟨j, hj⟩ : ∃ j : Fin n, root n ^ j.val = f.val 1 := by
    simpa only [vertices, Set.mem_range, one_mul, zero_add] using hmem
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex g
  · have hf (z : ℂ) : f.val z = (a : ℂ) * z := by
      rw [← hg z, ha]; rfl
    have haj : (a : ℂ) = root n ^ j.val := by simpa only [hf, mul_one] using hj.symm
    refine ⟨.r (j.val : ZMod n), ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    change (phase n (j.val : ZMod n) : ℂ) * z = f.val z
    rw [phase_natCast, Circle.coe_pow]
    rw [hf, haj]
    rfl
  · have hf (z : ℂ) : f.val z = (a : ℂ) * conj z := by
      rw [← hg z, ha]; rfl
    have haj : (a : ℂ) = root n ^ j.val := by simpa only [hf, map_one, mul_one] using hj.symm
    refine ⟨.sr (-(j.val : ZMod n)), ?_⟩
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    change conj ((phase n (-(j.val : ZMod n)) : ℂ) * z) = f.val z
    rw [phase_neg, Circle.coe_inv_eq_conj, map_mul, conj_conj, phase_natCast, Circle.coe_pow]
    rw [hf, haj]
    rfl

/-- The actual identification with the abstract group, obtained from a
faithful and exhaustive action. -/
def geometricEquiv (n : ℕ) [NeZero n] (hn : 1 < n) :
    DihedralGroup n ≃* symmetryGroup (vertices n 0 1) :=
  MulEquiv.ofBijective (geometricHom n)
    ⟨geometricHom_injective n, geometricHom_surjective n hn⟩

lemma action_rotation (n : ℕ) [NeZero n] : geometricAction n (.r 1) = turn n := by
  apply IsometryEquiv.ext
  intro z
  rw [geometricAction_r, turn_apply]
  rw [show phase n 1 = rootCircle n by simpa using phase_natCast n 1]
  rfl

lemma action_reflection (n : ℕ) [NeZero n] : geometricAction n (.sr 0) = mirror := by
  apply IsometryEquiv.ext
  intro z
  simp [mirror_apply]

theorem canonical_identification : CanonicalIdentification := by
  intro n hn
  let : NeZero n := ⟨by omega⟩
  exact ⟨geometricEquiv n (by omega), action_rotation n, action_reflection n⟩

theorem generator_relations : GeneratorRelations := by
  intro n hn
  let : NeZero n := ⟨by omega⟩
  have hr : (DihedralGroup.r 1 : DihedralGroup n) ^ n = 1 := by
    simp
  have hs : (DihedralGroup.sr 0 : DihedralGroup n) ^ 2 = 1 := by
    simp [pow_two]
  have hsr : (DihedralGroup.sr 0 : DihedralGroup n) * .r 1 * .sr 0 = (.r 1)⁻¹ := by
    simp
  refine ⟨?_, ?_, ?_⟩
  · simpa only [map_pow, map_one, action_rotation] using congrArg (geometricAction n) hr
  · simpa only [map_pow, map_one, action_reflection] using congrArg (geometricAction n) hs
  · simpa only [map_mul, map_inv, action_rotation, action_reflection] using
      congrArg (geometricAction n) hsr

/-- Exponent and choice of family, with the source's `r^i * s` convention. -/
def normalFormEquiv (n : ℕ) [NeZero n] : Fin n × Bool ≃ DihedralGroup n where
  toFun p := if p.2 then .sr (-(p.1.val : ZMod n)) else .r (p.1.val : ZMod n)
  invFun
    | .r i => (⟨i.val, ZMod.val_lt i⟩, false)
    | .sr i => (⟨(-i).val, ZMod.val_lt (-i)⟩, true)
  left_inv := by
    rintro ⟨i, b⟩
    cases b <;> simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  right_inv := by
    rintro (i | i) <;> simp

lemma normalFormEquiv_eq (n : ℕ) [NeZero n] (p : Fin n × Bool) :
    normalFormEquiv n p = if p.2 then
      (DihedralGroup.r 1 : DihedralGroup n) ^ p.1.val * .sr 0
    else (DihedralGroup.r 1 : DihedralGroup n) ^ p.1.val := by
  rcases p with ⟨i, b⟩
  cases b <;> simp [normalFormEquiv]

lemma normalForm_action (n : ℕ) [NeZero n] (p : Fin n × Bool) :
    geometricAction n (normalFormEquiv n p) =
      if p.2 then turn n ^ p.1.val * mirror else turn n ^ p.1.val := by
  rw [normalFormEquiv_eq]
  split <;> simp only [map_mul, map_pow, action_rotation, action_reflection]

theorem unique_normal_forms : UniqueNormalForms := by
  intro n hn
  let : NeZero n := ⟨by omega⟩
  intro f
  let E : Fin n × Bool ≃ symmetryGroup (vertices n 0 1) :=
    (normalFormEquiv n).trans (geometricEquiv n (by omega)).toEquiv
  have hE (p : Fin n × Bool) : (E p : ℂ ≃ᵢ ℂ) =
      if p.2 then turn n ^ p.1.val * mirror else turn n ^ p.1.val :=
    normalForm_action n p
  refine ⟨E.symm f, ?_, ?_⟩
  · dsimp only
    rw [← hE (E.symm f), E.apply_symm_apply]
  · intro p hp
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    exact (hE p).trans hp.symm

/-- Conjugating an isometry by a similarity is still an isometry: the scale
factor cancels. This permits changes in size as well as rigid coordinates. -/
def similarityConjugate (T : ℂ ≃ ℂ) (k : ℝ)
    (hT : ∀ x y, dist (T x) (T y) = k * dist x y) (f : ℂ ≃ᵢ ℂ) : ℂ ≃ᵢ ℂ where
  toEquiv := T.permCongr f.toEquiv
  isometry_toFun := Isometry.of_dist_eq (fun x y => by
    change dist (T (f (T.symm x))) (T (f (T.symm y))) = dist x y
    rw [hT, f.dist_eq]
    exact (by simpa using (hT (T.symm x) (T.symm y)).symm))

lemma inverse_similarity (T : ℂ ≃ ℂ) (k : ℝ) (hk : k ≠ 0)
    (hT : ∀ x y, dist (T x) (T y) = k * dist x y) :
    ∀ x y, dist (T.symm x) (T.symm y) = k⁻¹ * dist x y := by
  intro x y
  have h := hT (T.symm x) (T.symm y)
  simp only [T.apply_symm_apply] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

/-- The complete symmetry groups of similar vertex sets are isomorphic. -/
def similaritySymmetryEquiv (P Q : Set ℂ) (T : ℂ ≃ ℂ) (k : ℝ) (hk : k ≠ 0)
    (hT : ∀ x y, dist (T x) (T y) = k * dist x y)
    (hP : ∀ x, T x ∈ Q ↔ x ∈ P) : symmetryGroup P ≃* symmetryGroup Q where
  toFun f := ⟨similarityConjugate T k hT f.val, by
    intro z
    change T (f.val (T.symm z)) ∈ Q ↔ z ∈ Q
    rw [hP, f.property]
    exact (hP (T.symm z)).symm.trans (by rw [T.apply_symm_apply])⟩
  invFun f := ⟨similarityConjugate T.symm k⁻¹ (inverse_similarity T k hk hT) f.val, by
    intro z
    change T.symm (f.val (T z)) ∈ P ↔ z ∈ P
    rw [← hP, T.apply_symm_apply, f.property, hP]⟩
  left_inv f := by
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    change T.symm (T (f.val (T.symm (T z)))) = f.val z
    simp
  right_inv f := by
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    change T (T.symm (f.val (T (T.symm z)))) = f.val z
    simp
  map_mul' f g := by
    apply Subtype.ext
    apply IsometryEquiv.ext
    intro z
    change T (f.val (g.val (T.symm z))) = T (f.val (T.symm (T (g.val (T.symm z)))))
    rw [T.symm_apply_apply]

/-- The explicit coordinate normalization of an arbitrary regular polygon. -/
def polygonSimilarity (c a : ℂ) (ha : a ≠ 0) : ℂ ≃ ℂ where
  toFun z := c + a * z
  invFun z := (z - c) / a
  left_inv z := by field_simp; ring
  right_inv z := by field_simp; ring

lemma polygonSimilarity_dist (c a : ℂ) (ha : a ≠ 0) (x y : ℂ) :
    dist (polygonSimilarity c a ha x) (polygonSimilarity c a ha y) = ‖a‖ * dist x y := by
  change dist (c + a * x) (c + a * y) = _
  rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← mul_sub, norm_mul]

lemma polygonSimilarity_vertices (n : ℕ) (c a : ℂ) (ha : a ≠ 0) (z : ℂ) :
    polygonSimilarity c a ha z ∈ vertices n c a ↔ z ∈ vertices n 0 1 := by
  simp only [vertices, Set.mem_range, one_mul, zero_add]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (polygonSimilarity c a ha).injective hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- Transport to arbitrary center, size, and initial vertex. -/
def polygonSymmetryEquiv (n : ℕ) (c a : ℂ) (ha : a ≠ 0) :
    symmetryGroup (vertices n 0 1) ≃* symmetryGroup (vertices n c a) :=
  similaritySymmetryEquiv _ _ (polygonSimilarity c a ha) ‖a‖ (norm_ne_zero_iff.mpr ha)
    (polygonSimilarity_dist c a ha) (polygonSimilarity_vertices n c a ha)

theorem general_identification : GeneralIdentification := by
  intro n P hn hP
  rcases hP with ⟨c, a, ha, rfl⟩
  let : NeZero n := ⟨by omega⟩
  exact ⟨(geometricEquiv n (by omega)).trans (polygonSymmetryEquiv n c a ha)⟩

theorem geometric_order : GeometricOrder := by
  intro n P hn hP
  obtain ⟨e⟩ := general_identification n P hn hP
  let : NeZero n := ⟨by omega⟩
  have hfin : Finite (symmetryGroup P) := Finite.of_equiv (DihedralGroup n) e.toEquiv
  exact ⟨hfin, (Nat.card_congr e.toEquiv.symm).trans DihedralGroup.nat_card⟩

/-- Normal forms can be transported through any faithful identification. -/
lemma normal_forms_of_equiv (n : ℕ) [NeZero n] {G : Type*} [Group G]
    (e : DihedralGroup n ≃* G) (f : G) :
    ∃! p : Fin n × Bool, f = if p.2 then
      e (.r 1) ^ p.1.val * e (.sr 0) else e (.r 1) ^ p.1.val := by
  let E := (normalFormEquiv n).trans e.toEquiv
  have hE (p : Fin n × Bool) : E p = if p.2 then
      e (.r 1) ^ p.1.val * e (.sr 0) else e (.r 1) ^ p.1.val := by
    change e (normalFormEquiv n p) = _
    rw [normalFormEquiv_eq]
    split <;> simp only [map_mul, map_pow]
  refine ⟨E.symm f, ?_, ?_⟩
  · dsimp only
    rw [← hE (E.symm f), E.apply_symm_apply]
  · intro p hp
    apply E.injective
    rw [E.apply_symm_apply]
    exact (hE p).trans hp.symm

theorem full_geometric_model : FullGeometricModel := by
  intro n c a hn ha
  let : NeZero n := ⟨by omega⟩
  let e : DihedralGroup n ≃* symmetryGroup (vertices n c a) :=
    (geometricEquiv n (by omega)).trans (polygonSymmetryEquiv n c a ha)
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, normal_forms_of_equiv n e⟩
  · intro z
    change c + a * (geometricAction n (.r 1) ((z - c) / a)) = _
    rw [action_rotation, turn_apply]
    field_simp
  · intro z
    change c + a * (geometricAction n (.sr 0) ((z - c) / a)) = _
    rw [action_reflection, mirror_apply]
  · rw [← map_pow]
    simp
  · rw [← map_pow]
    simp [pow_two]
  · rw [← map_mul, ← map_mul, ← map_inv]
    congr 1
    simp

end D07.Ch01.DihedralQuaternionModelsPolygonSymmetries
