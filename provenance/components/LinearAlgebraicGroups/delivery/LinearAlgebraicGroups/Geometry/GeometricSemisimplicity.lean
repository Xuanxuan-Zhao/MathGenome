import LinearAlgebraicGroups.Geometry.CAT0Comparison
import Mathlib.Topology.MetricSpace.Thickening

/-! Metric properness and semisimplicity of geometric actions on CAT(0) spaces. -/

open Set Metric Filter unitInterval
open scoped Topology

namespace LinearAlgebraicGroups.Geometry

variable {G X : Type*} [Group G] [MetricSpace X] [MulAction G X]

private theorem weaklyLocallyCompactSpace_of_properAction [IsIsometricSMul G X]
    (hp : IsProperAction G X) {K : Set X} (hK : IsCompact K)
    (hcover : ∀ x : X, ∃ (a : G) (k : X), k ∈ K ∧ a • k = x) :
    WeaklyLocallyCompactSpace X := by
  classical
  let T (a : G) : Set X := (a • ·) '' K
  have hT (a : G) : IsCompact (T a) := hK.image (isometry_smul X a).continuous
  -- A convergent sequence can meet only finitely many translates of the compact set.
  have closedUnion (A : Set G) : IsClosed (⋃ a ∈ A, T a) := by
    refine IsSeqClosed.isClosed ?_
    intro u y hu hy
    let C := K ∪ insert y (range u)
    have hC : IsCompact C := hK.union ((Nat.cofinite_eq_atTop ▸ hy).isCompact_insert_range_of_cofinite)
    let B := {a : G | ∃ k ∈ C, a • k ∈ C}
    have hB : B.Finite := hp C hC
    have hu' (n : ℕ) : u n ∈ ⋃ a ∈ A ∩ B, T a := by
      obtain ⟨a, ha, hta⟩ := mem_iUnion₂.mp (hu n)
      obtain ⟨k, hk, heq⟩ := hta
      refine mem_iUnion₂.mpr ⟨a, ⟨ha, k, Or.inl hk, ?_⟩, k, hk, heq⟩
      change a • k = u n at heq
      rw [heq]
      exact Or.inr (mem_insert_of_mem _ (mem_range_self n))
    have hy' := ((hB.subset inter_subset_right).isCompact_biUnion
      (fun a _ => hT a)).isClosed.mem_of_tendsto hy (Eventually.of_forall hu')
    obtain ⟨a, ha, hyT⟩ := mem_iUnion₂.mp hy'
    exact mem_iUnion₂.mpr ⟨a, ha.1, hyT⟩
  refine ⟨fun x => ?_⟩
  let A := {a : G | x ∈ T a}
  have hA : A.Finite := by
    refine (hp (insert x K) (hK.insert x)).subset ?_
    rintro a ⟨k, hk, rfl⟩
    exact ⟨k, mem_insert_of_mem _ hk, mem_insert _ _⟩
  refine ⟨⋃ a ∈ A, T a, hA.isCompact_biUnion (fun a _ => hT a), ?_⟩
  have hx : x ∈ (⋃ a ∈ Aᶜ, T a)ᶜ := by
    intro hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hx
    exact ha hxa
  refine Filter.mem_of_superset ((closedUnion Aᶜ).isOpen_compl.mem_nhds hx) ?_
  intro y hy
  obtain ⟨a, k, hk, rfl⟩ := hcover y
  have hyT : a • k ∈ T a := ⟨k, hk, rfl⟩
  have ha : a ∈ A := by
    by_contra ha
    exact hy (mem_iUnion₂.mpr ⟨a, ha, hyT⟩)
  exact mem_iUnion₂.mpr ⟨a, ha, hyT⟩

private theorem properSpace_of_uniform_compact_balls (hg : IsGeodesicSpace X)
    {δ : ℝ} (hδ : 0 < δ) (hball : ∀ x : X, IsCompact (closedBall x δ)) :
    ProperSpace X := by
  -- A finite net in the smaller ball covers the larger ball by compact balls.
  have extend {x : X} {r : ℝ} (hr : 0 ≤ r) (hcompact : IsCompact (closedBall x r)) :
      IsCompact (closedBall x (r + δ / 2)) := by
    obtain ⟨S, _, hS, hcover⟩ := hcompact.finite_cover_balls (half_pos hδ)
    refine (hS.isCompact_biUnion fun z _ => hball z).of_isClosed_subset isClosed_closedBall ?_
    intro y hy
    have hy' : dist x y ≤ r + δ / 2 := by simpa only [mem_closedBall, dist_comm y x] using hy
    have hnear : ∃ z ∈ closedBall x r, dist y z ≤ δ / 2 := by
      by_cases hry : dist x y ≤ r
      · exact ⟨y, by simpa [dist_comm] using hry, by simpa using (half_pos hδ).le⟩
      · have hd : 0 < dist x y := lt_of_le_of_lt hr (lt_of_not_ge hry)
        obtain ⟨p⟩ := hg.2 x y
        let t : I := ⟨r / dist x y, div_nonneg hr hd.le,
          (div_le_one hd).mpr (lt_of_not_ge hry).le⟩
        have ht : (t : ℝ) * dist x y = r := div_mul_cancel₀ r hd.ne'
        refine ⟨p.val t, ?_, ?_⟩
        · rw [mem_closedBall, dist_comm, p.dist_source, ht]
        · rw [dist_comm, p.dist_target, sub_mul, one_mul, ht]
          exact sub_le_iff_le_add'.2 hy'
    obtain ⟨z, hz, hyz⟩ := hnear
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hcover hz)
    exact mem_iUnion₂.mpr ⟨w, hw, (dist_triangle y z w).trans (by
      change dist z w < δ / 2 at hzw
      linarith)⟩
  have hcompact (x : X) (n : ℕ) : IsCompact (closedBall x (n * (δ / 2))) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, add_mul, one_mul]
        exact extend (mul_nonneg (Nat.cast_nonneg n) (half_pos hδ).le) ih
  refine ⟨fun x r => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (r / (δ / 2))
  exact (hcompact x n).of_isClosed_subset isClosed_closedBall
    (closedBall_subset_closedBall ((div_lt_iff₀ (half_pos hδ)).mp hn).le)

/-- A CAT(0) space admitting a geometric action has compact closed balls. -/
theorem IsGeometricAction.properSpace (h : IsGeometricAction G X) (hX : CAT0 X) :
    ProperSpace X := by
  let := h.1
  obtain ⟨K, hK, hcover⟩ := h.2.2
  let := weaklyLocallyCompactSpace_of_properAction h.2.1 hK hcover
  obtain ⟨δ, hδ, hcompact⟩ := hK.exists_isCompact_cthickening
  refine properSpace_of_uniform_compact_balls hX.1 hδ fun x => ?_
  obtain ⟨a, k, hk, rfl⟩ := hcover x
  have hkball := hcompact.of_isClosed_subset isClosed_closedBall
    (closedBall_subset_cthickening hk δ)
  rw [← Metric.smul_closedBall]
  exact hkball.image (isometry_smul X a).continuous

/-- Completeness follows from the geometric action and CAT(0) hypotheses. -/
theorem IsGeometricAction.completeSpace (h : IsGeometricAction G X) (hX : CAT0 X) :
    CompleteSpace X := by
  let := h.properSpace hX
  infer_instance

/-- Each group element in a geometric action on a CAT(0) space attains its displacement infimum. -/
theorem IsGeometricAction.isSemisimple (h : IsGeometricAction G X) (hX : CAT0 X) (g : G) :
    letI : IsIsometricSMul G X := h.1
    IsSemisimple (IsometryEquiv.constSMul g : X ≃ᵢ X) := by
  let := h.1
  let := h.properSpace hX
  let := hX.1.1
  obtain ⟨x₀⟩ := hX.1.1
  obtain ⟨K, hK, hcover⟩ := h.2.2
  let displacement (x : X) := dist x (g • x)
  let D := displacement x₀
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall x₀
  let C := K ∪ closedBall x₀ (R + D)
  let conjugate (a : G) := a⁻¹ * g * a
  let B := {b : G | ∃ k ∈ C, b • k ∈ C} ∩ range conjugate
  have hB : B.Finite := (h.2.1 C (hK.union (isCompact_closedBall _ _))).subset inter_subset_left
  have hconjugate (a : G) (k : X) :
      dist k (conjugate a • k) = displacement (a • k) := calc
    _ = dist (a • k) (a • (conjugate a • k)) := (dist_smul a _ _).symm
    _ = _ := by simp [conjugate, displacement, mul_smul]
  -- The displacements at most D are represented in a finite union of compact images.
  let L := ⋃ b ∈ B, (fun k : X => dist k (b • k)) '' K
  have hL : IsCompact L := hB.isCompact_biUnion fun b _ =>
    hK.image (continuous_id.dist (isometry_smul X b).continuous)
  have hmem (x : X) (hx : displacement x ≤ D) : displacement x ∈ L := by
    obtain ⟨a, k, hk, rfl⟩ := hcover x
    have hbk : conjugate a • k ∈ closedBall x₀ (R + D) := by
      rw [mem_closedBall]
      calc
        dist (conjugate a • k) x₀ ≤ dist (conjugate a • k) k + dist k x₀ :=
          dist_triangle _ _ _
        _ ≤ R + D := by
          rw [dist_comm (conjugate a • k) k, hconjugate]
          exact (add_le_add hx (hR hk)).trans_eq (add_comm D R)
    exact mem_iUnion₂.mpr ⟨conjugate a, ⟨⟨k, Or.inl hk, Or.inr hbk⟩, mem_range_self a⟩,
      k, hk, hconjugate a k⟩
  obtain ⟨d, hd, hmin⟩ := hL.exists_isMinOn ⟨D, hmem x₀ le_rfl⟩ continuous_id.continuousOn
  obtain ⟨b, hb, k, _, rfl⟩ := mem_iUnion₂.mp hd
  obtain ⟨a, rfl⟩ := hb.2
  refine ⟨a • k, ?_⟩
  change displacement (a • k) = ⨅ x : X, displacement x
  refine le_antisymm (le_ciInf fun x => ?_) (ciInf_le ⟨0, by
    rintro _ ⟨x, rfl⟩
    exact dist_nonneg⟩ _)
  rw [← hconjugate a k]
  by_cases hx : displacement x ≤ D
  · exact hmin (hmem x hx)
  · exact (hmin (hmem x₀ le_rfl)).trans (le_of_not_ge hx)

end LinearAlgebraicGroups.Geometry
