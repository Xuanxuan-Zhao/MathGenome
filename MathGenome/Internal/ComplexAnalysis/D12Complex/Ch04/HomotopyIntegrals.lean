import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.HomotopyIntegrals
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskPrimitives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import Mathlib.Tactic.LinearCombination

/-! Homotopy invariance by a finite grid of local primitives. No derivative
of the homotopy, or integral on its intermediate continuous paths, is used. -/
noncomputable section
open Set Metric MeasureTheory
open scoped unitInterval BigOperators

namespace D12Complex.HomotopyIntegrals

theorem continuousOn_of_holomorphic {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) : ContinuousOn f Ω :=
  fun z hz => (hf.2 z hz).continuousAt.continuousWithinAt

theorem holomorphicOn_ball {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) {c : ℂ} {r : ℝ} (hB : ball c r ⊆ Ω) :
    HolomorphicOn (ball c r) f :=
  ⟨isOpen_ball, fun z hz => hf.2 z (hB hz)⟩

/-- A chord in a primitive disk has the same endpoint increment. -/
theorem segmentIntegral_endpoint {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) {c : ℂ} {r : ℝ} (_hr : 0 < r)
    (hB : ball c r ⊆ Ω) {F : ℂ → ℂ} (hF : Primitives.IsPrimitive (ball c r) f F)
    {z w : ℂ} (hz : z ∈ ball c r) (hw : w ∈ ball c r) :
    segmentIntegral f z w = F w - F z := by
  have htrace : (segmentPath z w).trace ⊆ ball c r :=
    by
      rw [segmentPath_trace]
      exact (convex_ball c r).segment_subset hz hw
  simpa only [segmentIntegral, segmentPath, PiecewiseC1Path.path, ComplexPath.source, ComplexPath.target,
      AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
    using Primitives.piecewise_endpoint (ball c r) f F
      (continuousOn_of_holomorphic (holomorphicOn_ball hf hB)) hF (segmentPath z w) htrace

/-- A cell's four chord integrals cancel, by a primitive in its image disk. -/
theorem cell_integrals {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : ball c r ⊆ Ω) {a b d e : ℂ}
    (ha : a ∈ ball c r) (hb : b ∈ ball c r)
    (hd : d ∈ ball c r) (he : e ∈ ball c r) :
    segmentIntegral f a b + segmentIntegral f b e =
      segmentIntegral f a d + segmentIntegral f d e := by
  obtain ⟨F, hF⟩ := DiskPrimitives.disk_exists_primitive c r f hr (holomorphicOn_ball hf hB)
  rw [segmentIntegral_endpoint hf hr hB hF ha hb,
    segmentIntegral_endpoint hf hr hB hF hb he,
    segmentIntegral_endpoint hf hr hB hF ha hd,
    segmentIntegral_endpoint hf hr hB hF hd he]
  abel

/-- Arbitrary finite subdivisions, allowing repeated nodes, may be replaced
by chords whenever each entire subpath lies in a primitive disk. -/
theorem integral_eq_chord_sum {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω)
    {n : ℕ} (v : Fin (n + 1) → ℝ) (hv : Monotone v)
    (hfirst : v 0 = γ.path.a) (hlast : v (Fin.last n) = γ.path.b)
    (hlocal : ∀ i : Fin n, ∃ (c : ℂ) (r : ℝ), 0 < r ∧ ball c r ⊆ Ω ∧
      ∀ t ∈ Icc (v i.castSucc) (v i.succ), γ t ∈ ball c r) :
    γ.integral f = ∑ i : Fin n, segmentIntegral f (γ (v i.castSucc)) (γ (v i.succ)) := by
  have hfγ := (continuousOn_of_holomorphic hf).mono hγ
  have hwhole := C1Partition.parameter_integrable γ.path γ.partition f hfγ
  have hlo (i : Fin (n + 1)) : γ.path.a ≤ v i := by
    rw [← hfirst]; exact hv (Fin.zero_le i)
  have hhi (i : Fin (n + 1)) : v i ≤ γ.path.b := by
    rw [← hlast]; exact hv (Fin.le_last i)
  have hint (i : Fin n) : IntervalIntegrable (fun t => f (γ t) * deriv γ t)
      volume (v i.castSucc) (v i.succ) := by
    exact hwhole.mono_set (by
      rw [uIcc_of_le (hv i.castSucc_lt_succ.le), uIcc_of_le γ.path.ordered]
      exact Icc_subset_Icc (hlo _) (hhi _))
  have heq (i : Fin n) :
      (∫ t in v i.castSucc..v i.succ, f (γ t) * deriv γ t) =
        segmentIntegral f (γ (v i.castSucc)) (γ (v i.succ)) := by
    obtain ⟨c, r, hr, hB, hsub⟩ := hlocal i
    obtain ⟨η, ha, hb, hη⟩ := γ.exists_restriction (v i.castSucc) (v i.succ)
      (hlo _) (hv i.castSucc_lt_succ.le) (hhi _)
    have hηtrace : η.trace ⊆ ball c r := by
      rintro z ⟨t, ht, rfl⟩
      rw [ha, hb] at ht
      rw [hη ht]
      exact hsub t ht
    have hfη := (continuousOn_of_holomorphic (holomorphicOn_ball hf hB)).mono hηtrace
    have hrep := η.integral_congr_representative γ f hfη (by simpa [ha, hb] using hη)
    rw [ha, hb] at hrep
    obtain ⟨F, hF⟩ := DiskPrimitives.disk_exists_primitive c r f hr (holomorphicOn_ball hf hB)
    rw [← hrep, Primitives.piecewise_endpoint (ball c r) f F
      (continuousOn_of_holomorphic (holomorphicOn_ball hf hB)) hF η hηtrace,
      segmentIntegral_endpoint hf hr hB hF
        (hsub _ ⟨le_rfl, hv i.castSucc_lt_succ.le⟩) (hsub _ ⟨hv i.castSucc_lt_succ.le, le_rfl⟩)]
    simp only [ComplexPath.target, ComplexPath.source, ha, hb]
    rw [hη ⟨hv i.castSucc_lt_succ.le, le_rfl⟩, hη ⟨le_rfl, hv i.castSucc_lt_succ.le⟩]
  rw [PiecewiseC1Path.integral, C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hfγ,
    ← hfirst, ← hlast, ← (intervalIntegral_fin_partition v _ hint).2]
  exact Finset.sum_congr rfl (fun i _ => heq i)

/-- Compactness of the parameter square gives a common finite grid subordinate
    to the inverse images of disks contained in Ω. -/
theorem exists_disk_grid {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (H : C(I × I, ℂ)) (hH : ∀ p, H p ∈ Ω) :
    ∃ (t : ℕ → I) (n : ℕ), t 0 = 0 ∧ Monotone t ∧ t n = 1 ∧
      ∀ i j : ℕ, ∃ (c : ℂ) (r : ℝ), 0 < r ∧ ball c r ⊆ Ω ∧
        ∀ s ∈ Icc (t i) (t (i + 1)), ∀ u ∈ Icc (t j) (t (j + 1)),
          H (s, u) ∈ ball c r := by
  let B := {p : ℂ × ℝ // 0 < p.2 ∧ ball p.1 p.2 ⊆ Ω}
  let cover : B → Set (I × I) := fun p => H ⁻¹' ball p.val.1 p.val.2
  have hopen (p : B) : IsOpen (cover p) := isOpen_ball.preimage H.continuous
  have hcover : univ ⊆ ⋃ p : B, cover p := by
    intro q _
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ (H q) (hH q)
    exact mem_iUnion.mpr ⟨⟨(H q, r), hr, hsub⟩, mem_ball_self hr⟩
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hgrid⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hopen hcover
  refine ⟨t, n, ht0, hmono, hn n le_rfl, ?_⟩
  intro i j
  obtain ⟨p, hp⟩ := hgrid i j
  exact ⟨p.val.1, p.val.2, p.property.1, p.property.2,
    fun s hs u hu => hp ⟨hs, hu⟩⟩

theorem segmentIntegral_self (f : ℂ → ℂ) (z : ℂ) : segmentIntegral f z z = 0 := by
  apply PiecewiseC1Path.integral_of_constant (segmentPath z z) z
  intro t _
  simp [segmentPath, PiecewiseC1Path.path]

/-- Pure finite cancellation: the four edges of each cell imply equality
of the two horizontal polygonal rows when the side increments agree. -/
theorem grid_rows_equal {f : ℂ → ℂ} {n : ℕ} (v : ℕ → ℕ → ℂ)
    (hcell : ∀ i j, i < n → j < n →
      segmentIntegral f (v i j) (v i (j + 1)) +
        segmentIntegral f (v i (j + 1)) (v (i + 1) (j + 1)) =
      segmentIntegral f (v i j) (v (i + 1) j) +
        segmentIntegral f (v (i + 1) j) (v (i + 1) (j + 1)))
    (hside : ∀ i, i < n →
      segmentIntegral f (v i 0) (v (i + 1) 0) =
        segmentIntegral f (v i n) (v (i + 1) n)) :
    (∑ j : Fin n, segmentIntegral f (v 0 j) (v 0 (j + 1))) =
      ∑ j : Fin n, segmentIntegral f (v n j) (v n (j + 1)) := by
  let row (i : ℕ) := ∑ j : Fin n, segmentIntegral f (v i j) (v i (j + 1))
  have hstep (i : ℕ) (hi : i < n) : row i = row (i + 1) := by
    have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun (j : Fin n) _ => hcell i j hi j.isLt)
    simp only [Finset.sum_add_distrib] at h
    have htel := (Fin.sum_univ_succ
      (fun j : Fin (n + 1) => segmentIntegral f (v i j) (v (i + 1) j))).symm.trans
      (Fin.sum_univ_castSucc (fun j : Fin (n + 1) =>
        segmentIntegral f (v i j) (v (i + 1) j)))
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last] at htel
    dsimp [row]
    linear_combination h - htel + hside i hi
  have hall : ∀ k, k ≤ n → row 0 = row k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      exact (ih (Nat.le_of_succ_le hk)).trans (hstep k (Nat.lt_of_succ_le hk))
  exact hall n le_rfl

/-- The chord representation on an affine unit-interval traversal. The
intermediate value theorem also handles a zero-length original interval. -/
theorem normalized_integral_eq_chord_sum {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (γ : PiecewiseC1Path) (hγ : γ.trace ⊆ Ω)
    (t : ℕ → I) (n : ℕ) (ht0 : t 0 = 0) (htn : t n = 1) (hmono : Monotone t)
    (row : I → ℂ)
    (hrow : ∀ u : I, row u = γ (γ.path.a + (γ.path.b - γ.path.a) * (u : ℝ)))
    (hlocal : ∀ j, j < n → ∃ (c : ℂ) (r : ℝ), 0 < r ∧ ball c r ⊆ Ω ∧
      ∀ u ∈ Icc (t j) (t (j + 1)), row u ∈ ball c r) :
    γ.integral f = ∑ j : Fin n, segmentIntegral f (row (t j)) (row (t (j + 1))) := by
  let v : Fin (n + 1) → ℝ := fun i =>
    γ.path.a + (γ.path.b - γ.path.a) * (t i : ℝ)
  have hv : Monotone v := by
    intro i j hij
    change γ.path.a + (γ.path.b - γ.path.a) * (t i : ℝ) ≤
      γ.path.a + (γ.path.b - γ.path.a) * (t j : ℝ)
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left
    · exact hmono (Fin.val_le_of_le hij)
    · exact sub_nonneg.mpr γ.path.ordered
  have hfirst : v 0 = γ.path.a := by simp [v, ht0]
  have hlast : v (Fin.last n) = γ.path.b := by simp [v, htn]
  have hpieces (i : Fin n) : ∃ (c : ℂ) (r : ℝ), 0 < r ∧ ball c r ⊆ Ω ∧
      ∀ x ∈ Icc (v i.castSucc) (v i.succ), γ x ∈ ball c r := by
    obtain ⟨c, r, hr, hB, hsub⟩ := hlocal i i.isLt
    refine ⟨c, r, hr, hB, ?_⟩
    intro x hx
    have hab : (t i : ℝ) ≤ (t (i + 1) : ℝ) := hmono (Nat.le_succ i)
    obtain ⟨q, hq, hqx⟩ := intermediate_value_Icc hab
      ((continuous_const.add (continuous_const.mul continuous_id)).continuousOn :
        ContinuousOn (fun u : ℝ => γ.path.a + (γ.path.b - γ.path.a) * u)
          (Icc (t i : ℝ) (t (i + 1) : ℝ))) hx
    have hqI : q ∈ Icc (0 : ℝ) 1 :=
      ⟨(t i).property.1.trans hq.1, hq.2.trans (t (i + 1)).property.2⟩
    change γ.path.a + (γ.path.b - γ.path.a) * q = x at hqx
    rw [← hqx, ← hrow ⟨q, hqI⟩]
    exact hsub _ hq
  rw [integral_eq_chord_sum hf γ hγ v hv hfirst hlast hpieces]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [v]
  rw [← hrow (t j), ← hrow (t (j + 1))]

/-- Homotopy invariance with the exact side-increment condition needed for
finite cancellation. Fixed sides and matching sides both satisfy it. -/
theorem integral_eq_of_homotopy {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (γ₀ γ₁ : PiecewiseC1Path)
    (hγ₀ : γ₀.trace ⊆ Ω) (hγ₁ : γ₁.trace ⊆ Ω)
    (H : C(I × I, ℂ)) (hH : ∀ p, H p ∈ Ω)
    (hbottom : ∀ u : I, H (0, u) = γ₀ (γ₀.path.a + (γ₀.path.b - γ₀.path.a) * (u : ℝ)))
    (htop : ∀ u : I, H (1, u) = γ₁ (γ₁.path.a + (γ₁.path.b - γ₁.path.a) * (u : ℝ)))
    (hside : ∀ s u : I, segmentIntegral f (H (s, 0)) (H (u, 0)) =
      segmentIntegral f (H (s, 1)) (H (u, 1))) :
    γ₀.integral f = γ₁.integral f := by
  obtain ⟨t, n, ht0, hmono, htn, hgrid⟩ := exists_disk_grid hf.1 H hH
  let v (i j : ℕ) : ℂ := H (t i, t j)
  have hedge (k : ℕ) : ∀ j, j < n → ∃ (c : ℂ) (r : ℝ),
      0 < r ∧ ball c r ⊆ Ω ∧
        ∀ u ∈ Icc (t j) (t (j + 1)), H (t k, u) ∈ ball c r := by
    intro j _
    obtain ⟨c, r, hr, hB, hsub⟩ := hgrid k j
    exact ⟨c, r, hr, hB, fun u hu =>
      hsub _ ⟨le_rfl, hmono (Nat.le_succ k)⟩ u hu⟩
  have hb := normalized_integral_eq_chord_sum hf γ₀ hγ₀ t n ht0 htn hmono
    (fun u => H (0, u)) hbottom (by simpa [ht0] using hedge 0)
  have ht := normalized_integral_eq_chord_sum hf γ₁ hγ₁ t n ht0 htn hmono
    (fun u => H (1, u)) htop (by simpa [htn] using hedge n)
  rw [hb, ht]
  have hc (i j : ℕ) (_hi : i < n) (_hj : j < n) :
      segmentIntegral f (v i j) (v i (j + 1)) +
        segmentIntegral f (v i (j + 1)) (v (i + 1) (j + 1)) =
      segmentIntegral f (v i j) (v (i + 1) j) +
        segmentIntegral f (v (i + 1) j) (v (i + 1) (j + 1)) := by
    obtain ⟨c, r, hr, hB, hsub⟩ := hgrid i j
    have hi := hmono (Nat.le_succ i)
    have hj := hmono (Nat.le_succ j)
    exact cell_integrals hf hr hB
      (hsub _ ⟨le_rfl, hi⟩ _ ⟨le_rfl, hj⟩)
      (hsub _ ⟨le_rfl, hi⟩ _ ⟨hj, le_rfl⟩)
      (hsub _ ⟨hi, le_rfl⟩ _ ⟨le_rfl, hj⟩)
      (hsub _ ⟨hi, le_rfl⟩ _ ⟨hj, le_rfl⟩)
  have hs (i : ℕ) (_hi : i < n) :
      segmentIntegral f (v i 0) (v (i + 1) 0) =
        segmentIntegral f (v i n) (v (i + 1) n) := by
    simpa [v, ht0, htn] using hside (t i) (t (i + 1))
  simpa [v, ht0, htn] using grid_rows_equal v hc hs

theorem fixed_endpoint_integral :
    Specs.D12Complex.Ch04.HomotopyIntegrals.fixed_endpoint_integral_type := by
  intro Ω f hf γ₀ γ₁ hγ₀ hγ₁ H hH hb ht hs he
  apply integral_eq_of_homotopy hf γ₀ γ₁ hγ₀ hγ₁ H hH hb ht
  intro s u
  rw [hs s, hs u, he s, he u, segmentIntegral_self, segmentIntegral_self]

theorem free_loop_integral :
    Specs.D12Complex.Ch04.HomotopyIntegrals.free_loop_integral_type := by
  intro Ω f hf γ₀ γ₁ hγ₀ hγ₁ _hclosed₀ _hclosed₁ H hH hb ht hs
  apply integral_eq_of_homotopy hf γ₀ γ₁ hγ₀ hγ₁ H hH hb ht
  intro s u
  rw [hs s, hs u]

theorem null_homotopic_integral :
    Specs.D12Complex.Ch04.HomotopyIntegrals.null_homotopic_integral_type := by
  intro Ω f hf γ hγ hclosed ⟨z, H, hH, hb, ht, hs⟩
  let η := PiecewiseC1Path.const 0 1 zero_le_one z
  have hη : η.trace ⊆ Ω := by
    rintro w ⟨u, hu, rfl⟩
    change z ∈ Ω
    rw [← ht 0]
    exact hH (1, 0)
  have heq := free_loop_integral Ω f hf γ η hγ hη hclosed
    (PiecewiseC1Path.const_closed 0 1 zero_le_one z) H hH hb
    (by simpa [η, PiecewiseC1Path.const, PiecewiseC1Path.path, ComplexPath.const] using ht) hs
  exact heq.trans (PiecewiseC1Path.const_integral 0 1 zero_le_one z f)

end D12Complex.HomotopyIntegrals
