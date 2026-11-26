import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RealLatticeReduction
import Mathlib.Algebra.Order.Round
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

open Module MeasureTheory
open scoped Matrix

namespace LinearAlgebraicGroups.Arithmetic.RealLatticeReduction

private theorem length_sq {n : ℕ} (x : Fin n → ℝ) :
    euclideanLength x ^ 2 = ∑ i, x i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

private theorem length_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ euclideanLength x := norm_nonneg _

private theorem abs_apply_le_length {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    |x i| ≤ euclideanLength x := by
  rw [← sq_le_sq₀ (abs_nonneg _) (length_nonneg _), sq_abs, length_sq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

private theorem length_le_of_abs_le {n : ℕ} (x : Fin n → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ i, |x i| ≤ R) : euclideanLength x ≤ (n + 1 : ℝ) * R := by
  rw [← sq_le_sq₀ (length_nonneg _) (by positivity), length_sq]
  calc
    ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, R ^ 2 := Finset.sum_le_sum fun i _ => by
      rw [← sq_abs (x i)]
      exact (sq_le_sq₀ (abs_nonneg _) hR).mpr (h i)
    _ = (n : ℝ) * R ^ 2 := by simp
    _ ≤ ((n + 1 : ℝ) * R) ^ 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      nlinarith [sq_nonneg R, mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg R),
        mul_nonneg hn (sq_nonneg R)]

private theorem length_sq_tail {n : ℕ} (x : Fin (n + 1) → ℝ) :
    euclideanLength x ^ 2 = x 0 ^ 2 + euclideanLength (Fin.tail x) ^ 2 := by
  rw [length_sq, length_sq, Fin.sum_univ_succ]
  rfl

private theorem covolume_eq_abs_det {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis (Fin n) ℤ L) :
    ZLattice.covolume L = |(basisMatrix b).det| := by
  rw [ZLattice.covolume_eq_det L b, ← Matrix.det_transpose]
  rfl

private theorem exists_short_vector (n : ℕ) (D : ℝ) (hD : 0 < D)
    (L : Submodule ℤ (Fin (n + 1) → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hvol : ZLattice.covolume L ≤ D) :
    ∃ x ∈ L, x ≠ 0 ∧ euclideanLength x ≤ (n + 2 : ℝ) * (D + 1) := by
  let b : Basis (Fin (n + 1)) ℤ L := IsZLattice.basis L
  let F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L)
  have hF : IsAddFundamentalDomain L F volume := ZLattice.isAddFundamentalDomain b volume
  have hFvol : volume F = ENNReal.ofReal (ZLattice.covolume L) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume hF, measureReal_def,
      ENNReal.ofReal_toReal]
    exact (ZSpan.fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ L)).measure_lt_top.ne
  let R := D + 1
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have hball : volume F * 2 ^ finrank ℝ (Fin (n + 1) → ℝ) <
      volume (Metric.closedBall (0 : Fin (n + 1) → ℝ) R) := by
    rw [hFvol, Real.volume_pi_closedBall _ hR, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)),
      ← ENNReal.ofReal_mul (ZLattice.covolume_pos L volume).le, mul_pow]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
    rw [mul_comm (2 ^ (n + 1) : ℝ)]
    apply mul_lt_mul_of_pos_right _ (by positivity)
    refine hvol.trans_lt ?_
    calc
      D < R := by dsimp [R]; linarith
      _ ≤ R ^ (n + 1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_left hR (one_le_pow₀ (by dsimp [R]; linarith))
  let : Countable L.toAddSubgroup := inferInstanceAs (Countable L)
  obtain ⟨x, hx, hmem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := L.toAddSubgroup) hF
    (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
    (convex_closedBall (0 : Fin (n + 1) → ℝ) R) hball
  refine ⟨x, x.property, fun h => hx (Subtype.ext h), ?_⟩
  convert length_le_of_abs_le (x : Fin (n + 1) → ℝ) hR (fun i => ?_) using 1
  · push_cast
    ring
  · have hnorm : ‖(x : Fin (n + 1) → ℝ)‖ ≤ R := by simpa using hmem
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm (x : Fin (n + 1) → ℝ) i).trans hnorm

private theorem exists_shortest {n : ℕ} (L : Submodule ℤ (Fin n → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] {x : Fin n → ℝ} (hx : x ∈ L) (hx0 : x ≠ 0) :
    ∃ b ∈ L, b ≠ 0 ∧ euclideanLength b ≤ euclideanLength x ∧
      ∀ y ∈ L, y ≠ 0 → euclideanLength b ≤ euclideanLength y := by
  let S : Set (Fin n → ℝ) := {y | y ∈ L ∧ y ≠ 0 ∧ euclideanLength y ≤ euclideanLength x}
  have hbounded : Bornology.IsBounded {y : Fin n → ℝ | euclideanLength y ≤ euclideanLength x} := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := euclideanLength x)).subset ?_
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (length_nonneg x)]
    exact fun i => (by simpa [Real.norm_eq_abs] using (abs_apply_le_length y i).trans hy)
  let b₀ : Basis (Fin n) ℤ L := IsZLattice.basis L
  have hfinite : S.Finite := by
    refine (ZSpan.setFinite_inter (b₀.ofZLatticeBasis ℝ L) hbounded).subset ?_
    rw [b₀.ofZLatticeBasis_span ℝ]
    exact fun y hy => ⟨hy.2.2, hy.1⟩
  obtain ⟨b, hb, hmin⟩ := Set.exists_min_image S euclideanLength hfinite ⟨x, hx, hx0, le_rfl⟩
  refine ⟨b, hb.1, hb.2.1, hb.2.2, fun y hy hy0 => ?_⟩
  by_cases h : euclideanLength y ≤ euclideanLength x
  · exact hmin y ⟨hy, hy0, h⟩
  · exact hb.2.2.trans (le_of_not_ge h)

/-- An orthogonal change of coordinates placing a given nonzero vector on the first axis. -/
private theorem exists_axis_coordinates {n : ℕ} {x : Fin (n + 1) → ℝ} (hx : x ≠ 0) :
    ∃ e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ),
      MeasurePreserving e ∧ (∀ y, euclideanLength (e y) = euclideanLength y) ∧
        e (Pi.single 0 (euclideanLength x)) = x := by
  let X : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 x
  have hX : 0 < ‖X‖ := norm_pos_iff.mpr (fun h => hx ((WithLp.equiv 2 _).symm.injective h))
  let v : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) := fun _ => ‖X‖⁻¹ • X
  have hv : Orthonormal ℝ (({0} : Set (Fin (n + 1))).domRestrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    change ‖‖X‖⁻¹ • X‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hX),
      inv_mul_cancel₀ hX.ne']
  obtain ⟨q, hq⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp)
  let u := EuclideanSpace.equiv (Fin (n + 1)) ℝ
  let e := u.symm.trans (q.repr.symm.toContinuousLinearEquiv.trans u)
  refine ⟨e, ?_, ?_, ?_⟩
  · have hu : MeasurePreserving u := PiLp.volume_preserving_ofLp _
    have hu' : MeasurePreserving u.symm := PiLp.volume_preserving_toLp _
    exact (hu.comp q.measurePreserving_repr_symm).comp hu'
  · intro y
    exact q.repr.symm.norm_map (WithLp.toLp 2 y)
  · apply u.symm.injective
    change u.symm (u (q.repr.symm (WithLp.toLp 2 (Pi.single 0 (euclideanLength x))))) = X
    rw [u.symm_apply_apply]
    have hs : (WithLp.toLp 2 (Pi.single 0 (euclideanLength x)) :
        EuclideanSpace ℝ (Fin (n + 1))) = ‖X‖ • EuclideanSpace.single 0 1 := by
      ext i
      by_cases hi : i = 0 <;> simp [EuclideanSpace.single, hi, Pi.single_apply, X, euclideanLength]
    rw [hs, map_smul, q.repr_symm_single, hq 0 (Set.mem_singleton 0)]
    change ‖X‖ • (‖X‖⁻¹ • X) = X
    rw [smul_smul, mul_inv_cancel₀ hX.ne', one_smul]

private def tailLinear (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := Fin.tail
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem projected_full {n : ℕ} (L : Submodule ℤ (Fin (n + 1) → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology (L.map ((tailLinear n).restrictScalars ℤ))] :
    IsZLattice ℝ (L.map ((tailLinear n).restrictScalars ℤ)) := by
  constructor
  change Submodule.span ℝ ((tailLinear n) '' (L : Set (Fin (n + 1) → ℝ))) = ⊤
  rw [← Submodule.map_span, IsZLattice.span_top, Submodule.map_top, LinearMap.range_eq_top]
  intro y
  exact ⟨Fin.cons 0 y, by ext i; rfl⟩

/-- Reduce the first coordinate of a lift by a nearest integer multiple of the axis vector. -/
private theorem reduce_lift {n : ℕ} (L : Submodule ℤ (Fin (n + 1) → ℝ)) {r : ℝ}
    (hr : 0 < r) (hb : Pi.single 0 r ∈ L) {x : Fin (n + 1) → ℝ} (hx : x ∈ L) :
    ∃ k : ℤ, let y := x - k • Pi.single 0 r
      y ∈ L ∧ Fin.tail y = Fin.tail x ∧ |y 0| ≤ r / 2 := by
  refine ⟨round (x 0 / r), L.sub_mem hx (L.smul_mem _ hb), ?_, ?_⟩
  · ext i
    simp [Fin.tail, Fin.succ_ne_zero]
  · change |x 0 - (_ : ℤ) • (Pi.single 0 r : Fin (n + 1) → ℝ) 0| ≤ r / 2
    simp only [Pi.single_eq_same, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
    have ht : x 0 - (↑(round (x 0 / r)) : ℝ) * r =
        (x 0 / r - ↑(round (x 0 / r))) * r := by
      rw [sub_mul, div_mul_cancel₀ _ hr.ne']
    rw [ht, abs_mul, abs_of_pos hr, show r / 2 = 1 / 2 * r by ring]
    exact mul_le_mul_of_nonneg_right (abs_sub_round _) hr.le

private theorem projected_lower_bound {n : ℕ} (L : Submodule ℤ (Fin (n + 1) → ℝ)) {r : ℝ}
    (hr : 0 < r) (hb : Pi.single 0 r ∈ L)
    (hmin : ∀ x ∈ L, x ≠ 0 → r ≤ euclideanLength x)
    {v : Fin n → ℝ} (hv : v ∈ L.map ((tailLinear n).restrictScalars ℤ)) (hv0 : v ≠ 0) :
    r / 2 ≤ euclideanLength v := by
  obtain ⟨x, hx, hxv⟩ := Submodule.mem_map.mp hv
  change Fin.tail x = v at hxv
  obtain ⟨k, hy, htail, hhead⟩ := reduce_lift L hr hb hx
  let y := x - k • Pi.single 0 r
  change y ∈ L at hy
  change Fin.tail y = Fin.tail x at htail
  change |y 0| ≤ r / 2 at hhead
  have hyv : Fin.tail y = v := htail.trans hxv
  have hy0 : y ≠ 0 := fun h => hv0 (hyv.symm.trans (h ▸ rfl))
  have h1 := (sq_le_sq₀ hr.le (length_nonneg y)).mpr (hmin y hy hy0)
  rw [length_sq_tail, hyv] at h1
  have h2 := (sq_le_sq₀ (abs_nonneg (y 0)) (show 0 ≤ r / 2 by positivity)).mpr hhead
  rw [sq_abs] at h2
  apply (sq_le_sq₀ (by positivity) (length_nonneg v)).1
  nlinarith [sq_nonneg r]

private theorem projected_discrete {n : ℕ} (P : Submodule ℤ (Fin n → ℝ)) {r : ℝ}
    (hr : 0 < r) (hP : ∀ v ∈ P, v ≠ 0 → r / 2 ≤ euclideanLength v) : DiscreteTopology P := by
  apply DiscreteTopology.of_forall_le_dist (r := r / 2 / (n + 1 : ℝ)) (by positivity)
  intro x y hxy
  rw [Subtype.dist_eq, dist_eq_norm, div_le_iff₀ (by positivity : (0 : ℝ) < n + 1), mul_comm]
  let z := (x : Fin n → ℝ) - y
  exact (hP z (P.sub_mem x.property y.property) (fun hz => hxy (Subtype.ext (sub_eq_zero.mp hz)))).trans
    (length_le_of_abs_le z (norm_nonneg z) (fun i => by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm z i))

private theorem axis_kernel {n : ℕ} (L : Submodule ℤ (Fin (n + 1) → ℝ)) {r : ℝ}
    (hr : 0 < r) (hb : Pi.single 0 r ∈ L)
    (hmin : ∀ x ∈ L, x ≠ 0 → r ≤ euclideanLength x)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ L) (hxt : Fin.tail x = 0) :
    ∃ k : ℤ, x = k • Pi.single 0 r := by
  obtain ⟨k, hy, htail, hhead⟩ := reduce_lift L hr hb hx
  let y := x - k • Pi.single 0 r
  change y ∈ L at hy
  change Fin.tail y = Fin.tail x at htail
  change |y 0| ≤ r / 2 at hhead
  have hy0 : y = 0 := by
    by_contra h
    have h1 := (sq_le_sq₀ hr.le (length_nonneg y)).mpr (hmin y hy h)
    rw [length_sq_tail, htail, hxt] at h1
    have h2 := (sq_le_sq₀ (abs_nonneg (y 0)) (show 0 ≤ r / 2 by positivity)).mpr hhead
    rw [sq_abs] at h2
    have hz : euclideanLength (0 : Fin n → ℝ) = 0 := by simp [euclideanLength]
    rw [hz] at h1
    nlinarith [sq_pos_of_pos hr]
  exact ⟨k, sub_eq_zero.mp hy0⟩

/-- A basis of the projection lifts to an integral basis together with the axis vector.
Each lift can be taken with first coordinate of absolute value at most half the axis length. -/
private theorem lift_basis {n : ℕ} (L : Submodule ℤ (Fin (n + 1) → ℝ)) {r : ℝ}
    (hr : 0 < r) (hb : Pi.single 0 r ∈ L)
    (hmin : ∀ x ∈ L, x ≠ 0 → r ≤ euclideanLength x)
    (b : Basis (Fin n) ℤ (L.map ((tailLinear n).restrictScalars ℤ))) :
    ∃ b' : Basis (Fin (n + 1)) ℤ L,
      (b' 0 : Fin (n + 1) → ℝ) = Pi.single 0 r ∧
        ∀ i : Fin n, Fin.tail (b' i.succ : Fin (n + 1) → ℝ) = (b i : Fin n → ℝ) ∧
          |(b' i.succ : Fin (n + 1) → ℝ) 0| ≤ r / 2 := by
  classical
  let P := L.map ((tailLinear n).restrictScalars ℤ)
  let p : L →ₗ[ℤ] P := LinearMap.codRestrict P
    (((tailLinear n).restrictScalars ℤ).domRestrict L)
    (fun x => Submodule.mem_map.mpr ⟨x, x.property, rfl⟩)
  let a : L := ⟨Pi.single 0 r, hb⟩
  have hpa : p a = 0 := by
    apply Subtype.ext
    ext i
    change (Pi.single 0 r : Fin (n + 1) → ℝ) i.succ = 0
    simp [Fin.succ_ne_zero]
  have lifts (i : Fin n) : ∃ y : L, p y = b i ∧ |(y : Fin (n + 1) → ℝ) 0| ≤ r / 2 := by
    obtain ⟨x, hx, hxp⟩ := Submodule.mem_map.mp (b i).property
    obtain ⟨k, hy, htail, hhead⟩ := reduce_lift L hr hb hx
    let y := x - k • Pi.single 0 r
    refine ⟨⟨y, hy⟩, Subtype.ext ?_, hhead⟩
    exact htail.trans hxp
  choose v hpv hv using lifts
  let w : Fin (n + 1) → L := Fin.cons a v
  let f := Fintype.linearCombination ℤ w
  have hf (z : Fin (n + 1) → ℤ) : f z = z 0 • a + ∑ i : Fin n, z i.succ • v i := by
    rw [Fintype.linearCombination_apply, Fin.sum_univ_succ]
    rfl
  have hpf (z : Fin (n + 1) → ℤ) : p (f z) = b.equivFun.symm (Fin.tail z) := by
    rw [hf, map_add, map_smul, hpa, smul_zero, zero_add, map_sum, Basis.equivFun_symm_apply]
    simp [hpv, Fin.tail]
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).2
    intro z hz
    have htz : Fin.tail z = 0 := by
      apply b.equivFun.symm.injective
      rw [← hpf z, hz, map_zero, map_zero]
    have hs : ∀ i : Fin n, z i.succ = 0 := fun i => congrFun htz i
    rw [hf, Finset.sum_eq_zero (fun i _ => by rw [hs, zero_smul]), add_zero] at hz
    have hz0 : z 0 = 0 := by
      have h := congrFun (congrArg Subtype.val hz) (0 : Fin (n + 1))
      change (z 0 • (Pi.single 0 r : Fin (n + 1) → ℝ)) 0 = 0 at h
      simpa [Pi.smul_apply, Pi.single_eq_same, ← Int.cast_smul_eq_zsmul ℝ,
        smul_eq_mul, hr.ne'] using h
    exact funext (Fin.cases hz0 hs)
  have hsurj : Function.Surjective f := by
    intro x
    let c := b.equivFun (p x)
    let y := x - f (Fin.cons 0 c)
    have hy : p y = 0 := by
      rw [map_sub, hpf, Fin.tail_cons, b.equivFun.symm_apply_apply, sub_self]
    have hyt : Fin.tail (y : Fin (n + 1) → ℝ) = 0 := congrArg Subtype.val hy
    obtain ⟨k, hk⟩ := axis_kernel L hr hb hmin y.property hyt
    have hyk : y = k • a := Subtype.ext hk
    refine ⟨Fin.cons k c, ?_⟩
    have heq : f (Fin.cons k c) = k • a + f (Fin.cons 0 c) := by simp [hf]
    rw [heq, ← hyk, sub_add_cancel]
  let b' := Basis.mk ((linearIndependent_iff_injective_fintypeLinearCombination).2 hinj)
    (by rw [← Fintype.range_linearCombination, top_le_iff, LinearMap.range_eq_top]; exact hsurj)
  have hb' (i : Fin (n + 1)) : b' i = w i := Basis.mk_apply _ _ _
  refine ⟨b', ?_, fun i => ?_⟩
  · rw [hb']
    rfl
  · rw [hb']
    exact ⟨congrArg Subtype.val (hpv i), hv i⟩

private theorem covolume_projection {n : ℕ} (L : Submodule ℤ (Fin (n + 1) → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] {r : ℝ} (hr : 0 < r) (hb : Pi.single 0 r ∈ L)
    (hmin : ∀ x ∈ L, x ≠ 0 → r ≤ euclideanLength x)
    [DiscreteTopology (L.map ((tailLinear n).restrictScalars ℤ))]
    [IsZLattice ℝ (L.map ((tailLinear n).restrictScalars ℤ))] :
    ZLattice.covolume L = r * ZLattice.covolume (L.map ((tailLinear n).restrictScalars ℤ)) := by
  let b := IsZLattice.basis (L.map ((tailLinear n).restrictScalars ℤ))
  obtain ⟨b', hb', htail⟩ := lift_basis L hr hb hmin b
  have hsub : (basisMatrix b').submatrix Fin.succ Fin.succ = basisMatrix b := by
    ext i j
    exact congrFun (htail j).1 i
  have hzero (i : Fin n) : basisMatrix b' i.succ 0 = 0 := by
    change (b' 0 : Fin (n + 1) → ℝ) i.succ = 0
    simp [hb', Fin.succ_ne_zero]
  have hfirst : basisMatrix b' 0 0 = r := by
    change (b' 0 : Fin (n + 1) → ℝ) 0 = r
    simp [hb']
  rw [covolume_eq_abs_det L b', covolume_eq_abs_det _ b, Matrix.det_succ_column_zero,
    Fin.sum_univ_succ, Finset.sum_eq_zero (fun i _ => by simp [hzero])]
  simp [hfirst, hsub, abs_mul, abs_of_pos hr]

private theorem length_single_zero {n : ℕ} (r : ℝ) :
    euclideanLength (Pi.single 0 r : Fin (n + 1) → ℝ) = |r| := by
  apply (sq_eq_sq₀ (length_nonneg _) (abs_nonneg _)).1
  rw [length_sq, sq_abs, Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

private theorem length_of_lift_le {n : ℕ} (x : Fin (n + 1) → ℝ) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (h₁ : |x 0| ≤ a) (h₂ : euclideanLength (Fin.tail x) ≤ c) :
    euclideanLength x ≤ a + c := by
  apply (sq_le_sq₀ (length_nonneg _) (add_nonneg ha hc)).1
  rw [length_sq_tail]
  have h₁' := (sq_le_sq₀ (abs_nonneg _) ha).2 h₁
  rw [sq_abs] at h₁'
  have h₂' := (sq_le_sq₀ (length_nonneg _) hc).2 h₂
  nlinarith [mul_nonneg ha hc]

/-- The bound for a basis depends only on dimension, a lower length bound and
an upper covolume bound. The latter changes under projection. -/
private theorem bounded_basis_aux (n : ℕ) :
    ∀ (ε D : ℝ), 0 < ε → 0 < D →
      ∃ C : ℝ, 0 < C ∧
        ∀ (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
          ZLattice.covolume L ≤ D →
          (∀ x ∈ L, x ≠ 0 → ε ≤ euclideanLength x) →
          ∃ b : Basis (Fin n) ℤ L, ∀ i, euclideanLength (b i : Fin n → ℝ) ≤ C := by
  induction n with
  | zero =>
    intro ε D hε hD
    refine ⟨1, one_pos, ?_⟩
    intro L _ _ _ _
    exact ⟨IsZLattice.basis L, fun i => i.elim0⟩
  | succ n ih =>
    intro ε D hε hD
    obtain ⟨C, hC, hCbound⟩ := ih (ε / 2) (D / ε) (by positivity) (by positivity)
    let R : ℝ := (n + 2 : ℝ) * (D + 1)
    have hR : 0 < R := by dsimp [R]; positivity
    refine ⟨R + C, by positivity, ?_⟩
    intro L _ _ hvol hlower
    obtain ⟨x, hx, hx0, hxlen⟩ := exists_short_vector n D hD L hvol
    obtain ⟨v, hv, hv0, hvlen, hvmin⟩ := exists_shortest L hx hx0
    let r := euclideanLength v
    have hεr : ε ≤ r := hlower v hv hv0
    have hr : 0 < r := hε.trans_le hεr
    have hrR : r ≤ R := hvlen.trans hxlen
    obtain ⟨e, hem, he, hev⟩ := exists_axis_coordinates hv0
    let L' := ZLattice.comap ℝ L e.toLinearMap
    have hb : Pi.single 0 r ∈ L' := by change e (Pi.single 0 r) ∈ L; rwa [hev]
    have hmin : ∀ y ∈ L', y ≠ 0 → r ≤ euclideanLength y := by
      intro y hy hy0
      rw [← he y]
      exact hvmin (e y) hy (fun h => hy0 (e.injective (h.trans e.map_zero.symm)))
    let P := L'.map ((tailLinear n).restrictScalars ℤ)
    have hP := fun y hy hy0 => projected_lower_bound L' hr hb hmin (v := y) hy hy0
    let : DiscreteTopology P := projected_discrete P hr hP
    let : IsZLattice ℝ P := projected_full L'
    have hvolL' : ZLattice.covolume L' ≤ D := (ZLattice.covolume_comap L _ _ hem).trans_le hvol
    have hvolP : ZLattice.covolume P ≤ D / ε := by
      apply (le_div_iff₀ hε).2
      rw [mul_comm]
      calc
        ε * ZLattice.covolume P ≤ r * ZLattice.covolume P :=
          mul_le_mul_of_nonneg_right hεr (ZLattice.covolume_pos P volume).le
        _ = ZLattice.covolume L' := (covolume_projection L' hr hb hmin).symm
        _ ≤ D := hvolL'
    obtain ⟨bP, hbP⟩ := hCbound P hvolP (fun y hy hy0 => by
      exact (div_le_div_of_nonneg_right hεr (by norm_num)).trans (hP y hy hy0))
    obtain ⟨b', hb', htail⟩ := lift_basis L' hr hb hmin bP
    let b := b'.map (ZLattice.comap_equiv ℝ L e.toLinearEquiv).symm
    refine ⟨b, fun i => ?_⟩
    have hbi : (b i : Fin (n + 1) → ℝ) = e (b' i : Fin (n + 1) → ℝ) := by
      change ((ZLattice.comap_equiv ℝ L e.toLinearEquiv).symm (b' i) : Fin (n + 1) → ℝ) = _
      have h := congrArg Subtype.val ((ZLattice.comap_equiv ℝ L e.toLinearEquiv).apply_symm_apply (b' i))
      exact e.symm.injective (h.trans (e.symm_apply_apply _).symm)
    rw [hbi, he]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hb', length_single_zero, abs_of_pos hr]
      linarith
    · have hh := (htail j).2
      have ht : euclideanLength (Fin.tail (b' j.succ : Fin (n + 1) → ℝ)) ≤ C := by
        rw [(htail j).1]
        exact hbP j
      exact (length_of_lift_le _ (by positivity) hC.le hh ht).trans (by linarith)

/-- Reorient by negating one column, preserving each of the entry bounds. -/
private theorem orient_basis {n : ℕ} {L : Submodule ℤ (Fin n → ℝ)}
    (b : Basis (Fin n) ℤ L) {C : ℝ} (hb : entriesBounded C (basisMatrix b))
    (hdet : |(basisMatrix b).det| = 1) :
    ∃ b' : Basis (Fin n) ℤ L, (basisMatrix b').det = 1 ∧ entriesBounded C (basisMatrix b') := by
  cases n with
  | zero => exact ⟨b, Matrix.det_isEmpty, hb⟩
  | succ n =>
    rcases abs_eq_abs.mp (hdet.trans (abs_one : |(1 : ℝ)| = 1).symm) with hp | hn
    · exact ⟨b, hp, hb⟩
    · let u : Fin (n + 1) → ℤˣ := fun i => if i = 0 then -1 else 1
      let d : Fin (n + 1) → ℝ := fun i => if i = 0 then -1 else 1
      let b' := b.unitsSMul u
      have hmat : basisMatrix b' = basisMatrix b * Matrix.diagonal d := by
        ext i j
        rw [Matrix.mul_diagonal]
        change ((b.unitsSMul u j : L) : Fin (n + 1) → ℝ) i = (b j : Fin (n + 1) → ℝ) i * d j
        rw [Basis.unitsSMul_apply]
        by_cases hj : j = 0 <;> simp [u, d, hj, Units.smul_def]
      refine ⟨b', ?_, fun i j => ?_⟩
      · have hd : (Matrix.diagonal d).det = -1 := by
          rw [Matrix.det_diagonal, Fin.prod_univ_succ]
          simp [d, Fin.succ_ne_zero]
        rw [hmat, Matrix.det_mul, hn, hd]
        norm_num
      · rw [hmat, Matrix.mul_diagonal, abs_mul]
        have hd : |d j| = 1 := by by_cases hj : j = 0 <;> simp [d, hj]
        simpa [hd] using hb i j

private theorem abs_det_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {C : ℝ}
    (hA : entriesBounded C A) :
    |A.det| ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * C ^ n := by
  classical
  rw [Matrix.det_apply]
  calc
    |∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i| ≤
        ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), C ^ n := by
      apply Finset.sum_le_sum
      intro σ _
      have hprod : |∏ i, A (σ i) i| ≤ C ^ n := by
        rw [Finset.abs_prod]
        calc
          ∏ i, |A (σ i) i| ≤ ∏ _i : Fin n, C :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
          _ = C ^ n := by simp
      rcases Int.isUnit_iff.mp (Equiv.Perm.sign σ).isUnit with hs | hs
      all_goals simpa [Units.smul_def, hs] using hprod
    _ = _ := by simp

private theorem inverse_entries_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {C : ℝ}
    (hC : 1 ≤ C) (hA : entriesBounded C A) (hdet : A.det = 1) :
    entriesBounded ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * C ^ n) A⁻¹ := by
  classical
  have hinv : A⁻¹ = A.adjugate := by rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  intro i j
  rw [hinv, Matrix.adjugate_apply]
  apply abs_det_le
  intro k l
  by_cases hk : k = j
  · subst k
    rw [Matrix.updateRow_self]
    by_cases hl : l = i <;> simp [hl, zero_le_one.trans hC, hC]
  · rw [Matrix.updateRow_ne hk]
    exact hA k l

theorem boundedRealLatticeBasis : Specs.RealLatticeReduction.boundedRealLatticeBasis := by
  intro n ε hε
  obtain ⟨C, hC, hbound⟩ := bounded_basis_aux n ε 1 hε one_pos
  let B := max C 1
  let D := (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * B ^ n
  refine ⟨max B D, hC.trans_le ((le_max_left C 1).trans (le_max_left B D)), ?_⟩
  intro L _ _ hvol hlower
  obtain ⟨b, hb⟩ := hbound L hvol.le hlower
  have he : entriesBounded B (basisMatrix b) :=
    fun i j => (abs_apply_le_length _ i).trans ((hb j).trans (le_max_left C 1))
  obtain ⟨b', hdet, he'⟩ := orient_basis b he ((covolume_eq_abs_det L b).symm.trans hvol)
  have hi := inverse_entries_le (basisMatrix b') (le_max_right C 1) he' hdet
  exact ⟨b', hdet, fun i j => (he' i j).trans (le_max_left B D),
    fun i j => (hi i j).trans (le_max_right B D)⟩

theorem boundedRealMatrixBasis : Specs.RealLatticeReduction.boundedRealMatrixBasis := by
  intro n ε hε
  obtain ⟨C, hC, hbound⟩ := boundedRealLatticeBasis n ε hε
  refine ⟨C, hC, ?_⟩
  intro g hg hshort
  let b : Basis (Fin n) ℝ (Fin n → ℝ) :=
    (Pi.basisFun ℝ (Fin n)).map (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  let L := Submodule.span ℤ (Set.range b)
  let b₀ := b.restrictScalars ℤ
  have hcol (i j : Fin n) : b j i = g.val i j := by
    simp [b, Basis.map_apply, Pi.basisFun_apply, Matrix.col_apply]
  have hmat : basisMatrix b₀ = g.val := by
    ext i j
    change ((b.restrictScalars ℤ j : L) : Fin n → ℝ) i = _
    rw [Basis.restrictScalars_apply]
    exact hcol i j
  have hvol : ZLattice.covolume L = 1 := by
    rw [covolume_eq_abs_det L b₀, hmat, hg]
  have hL (x : Fin n → ℝ) (hx : x ∈ L) (hx0 : x ≠ 0) : ε ≤ euclideanLength x := by
    let z : Fin n → ℤ := b₀.equivFun ⟨x, hx⟩
    have hz : z ≠ 0 := by
      intro he
      have he' : (⟨x, hx⟩ : L) = 0 := b₀.equivFun.injective (he.trans b₀.equivFun.map_zero.symm)
      exact hx0 (congrArg Subtype.val he')
    have hmul : g.val.mulVec (fun i => (z i : ℝ)) = x := by
      have hs := congrArg (fun y : L => (y : Fin n → ℝ)) (b₀.sum_repr ⟨x, hx⟩)
      ext i
      have hsi := congrFun hs i
      change (L.subtype (∑ j, z j • b₀ j)) i = x i at hsi
      rw [map_sum] at hsi
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
        at hsi
      simp only [b₀, Submodule.subtype_apply, Basis.restrictScalars_apply] at hsi
      simp only [Matrix.mulVec, dotProduct, ← hcol]
      exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans hsi
    simpa only [hmul] using hshort z hz
  obtain ⟨b₁, hb₁, he, hi⟩ := hbound L hvol hL
  let γ : Matrix.GeneralLinearGroup (Fin n) ℤ :=
    ⟨b₀.toMatrix b₁, b₁.toMatrix b₀, b₀.toMatrix_mul_toMatrix_flip b₁,
      b₁.toMatrix_mul_toMatrix_flip b₀⟩
  refine ⟨γ, ?_⟩
  let h := g * Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ
  change h.val.det = 1 ∧ entriesBounded C h.val ∧ entriesBounded C h⁻¹.val
  have heq : h.val = basisMatrix b₁ := by
    change g.val * (Int.castRingHom ℝ).mapMatrix (b₀.toMatrix b₁) = _
    have hg' : g.val = (Pi.basisFun ℝ (Fin n)).toMatrix b := by
      ext i j
      exact (hcol i j).symm
    rw [hg', show (Int.castRingHom ℝ).mapMatrix (b₀.toMatrix b₁) =
      b.toMatrix (fun i => (b₁ i : Fin n → ℝ)) from b.restrictScalars_toMatrix ℤ b₁,
      Basis.toMatrix_mul_toMatrix]
    rfl
  have hinv : h⁻¹.val = (basisMatrix b₁)⁻¹ := by
    rw [Matrix.GeneralLinearGroup.coe_inv h, heq]
  exact ⟨heq ▸ hb₁, heq ▸ he, hinv ▸ hi⟩

end LinearAlgebraicGroups.Arithmetic.RealLatticeReduction
