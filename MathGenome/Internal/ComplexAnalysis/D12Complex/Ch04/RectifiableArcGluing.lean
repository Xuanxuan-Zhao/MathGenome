import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.RectifiableArcGluing
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.ArclengthFactorization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathsChains
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! Finite-length continuous gluing, D12.04.08 (paper.tex:1196–1237).
Arclength gives uniform disk covers. Rectangular grid incidence, exact edge
cancellation and uniform continuity prove removal. The final locality step
handles arbitrary locally finite families, including intersecting traces.
-/

noncomputable section
open Set Metric
open scoped BigOperators

namespace D12Complex.ArcGluing

/-- A uniform linear bound on the number of equal-radius covering disks.
This is geometric data about E, not a removability certificate. -/
def HasLinearCoverBound (E : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
    ∃ (n : ℕ) (c : Fin n → ℂ),
      (n : ℝ) * h ≤ C ∧ E ⊆ ⋃ j, closedBall (c j) h

/-- Every point of Ω has an open neighborhood meeting only finitely many traces.
The family may have arbitrary intersections and arbitrary index type. -/
def LocallyFiniteTracesOn {ι : Type*} (Ω : Set ℂ) (γ : ι → ComplexPath) : Prop :=
  ∀ z ∈ Ω, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
    {i | ((γ i).trace ∩ U).Nonempty}.Finite

theorem lipschitz_interval_cover :
    Specs.D12Complex.Ch04.RectifiableArcGluing.lipschitz_interval_cover_type := by
  intro L h hL hh σ hσ
  let n := ⌊L / h⌋₊ + 1
  let c : Fin n → ℂ := fun j => σ ((j : ℕ) * h)
  have hfloor : (⌊L / h⌋₊ : ℝ) * h ≤ L :=
    (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hL hh.le))
  refine ⟨n, c, ?_, ?_⟩
  · dsimp only [n]
    push_cast
    nlinarith
  · rintro z ⟨v, hv, rfl⟩
    let j : Fin n := ⟨⌊v / h⌋₊,
      Nat.lt_succ_of_le (Nat.floor_mono ((div_le_div_iff_of_pos_right hh).mpr hv.2))⟩
    have hj0 : 0 ≤ ((j : ℕ) : ℝ) * h := by positivity
    have hjv : ((j : ℕ) : ℝ) * h ≤ v :=
      (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hv.1 hh.le))
    have hvj : v < (((j : ℕ) : ℝ) + 1) * h :=
      (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (v / h))
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    change dist (σ v) (σ (((j : ℕ) : ℝ) * h)) ≤ h
    have hd := hσ.dist_le_mul v hv _ (show ((j : ℕ) : ℝ) * h ∈ Icc 0 L from
      ⟨hj0, hjv.trans hv.2⟩)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hjv)] at hd
    exact hd.trans (by linarith)

theorem rectifiable_trace_cover :
    Specs.D12Complex.Ch04.RectifiableArcGluing.rectifiable_trace_cover_type := by
  intro γ hγ
  obtain ⟨σ, hσ, _, htrace, _⟩ := Arclength.lipschitz_factor γ hγ
  let L := (Stieltjes.polygonalLength γ).toReal
  refine ⟨L + 1, by dsimp [L]; positivity, ?_⟩
  intro h hh hh1
  obtain ⟨n, c, hnc, hcov⟩ := lipschitz_interval_cover L h ENNReal.toReal_nonneg hh σ hσ
  exact ⟨n, c, hnc.trans (by linarith), htrace ▸ hcov⟩

/-- Uniform equal-radius disk covering bounds are stable under finite unions. -/
theorem HasLinearCoverBound.union {E F : Set ℂ}
    (hE : HasLinearCoverBound E) (hF : HasLinearCoverBound F) :
    HasLinearCoverBound (E ∪ F) := by
  obtain ⟨C, hC, hE⟩ := hE
  obtain ⟨D, hD, hF⟩ := hF
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  intro h hh hh1
  obtain ⟨n, c, hnc, hc⟩ := hE h hh hh1
  obtain ⟨m, d, hmd, hd⟩ := hF h hh hh1
  refine ⟨n + m, Fin.addCases c d, ?_, ?_⟩
  · push_cast
    nlinarith
  · intro z hz
    rcases hz with hz | hz
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hc hz)
      exact mem_iUnion.mpr ⟨Fin.castAdd m j, by simpa using hj⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hd hz)
      exact mem_iUnion.mpr ⟨Fin.natAdd n j, by simpa using hj⟩

theorem hasLinearCoverBound_empty : HasLinearCoverBound (∅ : Set ℂ) := by
  refine ⟨0, le_rfl, ?_⟩
  intro h hh hh1
  exact ⟨0, Fin.elim0, by simp, empty_subset _⟩

theorem hasLinearCoverBound_biUnion {ι : Type*} (s : Finset ι) (E : ι → Set ℂ)
    (hE : ∀ i ∈ s, HasLinearCoverBound (E i)) :
    HasLinearCoverBound (⋃ i ∈ s, E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasLinearCoverBound_empty
  | @insert i s hi ih =>
    have hu := (hE i (Finset.mem_insert_self _ _)).union
      (ih (fun j hj => hE j (Finset.mem_insert_of_mem hj)))
    simpa using hu

theorem finite_rectifiable_traces_cover :
    Specs.D12Complex.Ch04.RectifiableArcGluing.finite_rectifiable_traces_cover_type := by
  intro n γ hγ
  change HasLinearCoverBound (⋃ i, (γ i).trace)
  simpa using hasLinearCoverBound_biUnion Finset.univ (fun i => (γ i).trace)
    (fun i _ => rectifiable_trace_cover (γ i) (hγ i))

/-- Once the compact-set analytic removal lemma is proved, the finite-family
case follows from the actual covering and compactness theorems. -/
theorem finite_gluing_of_linear_cover_gluing
    (hremove : Specs.D12Complex.Ch04.RectifiableArcGluing.linear_cover_gluing_type) :
    Specs.D12Complex.Ch04.RectifiableArcGluing.finite_rectifiable_arc_gluing_type := by
  intro n γ Ω f hγ hΩ hf hd
  exact hremove Ω (⋃ i, (γ i).trace) f hΩ
    (isCompact_iUnion (fun i => ComplexPath.trace_compact (γ i)))
    (finite_rectifiable_traces_cover n γ hγ) hf hd

/-- The local-finiteness step is independent of any geometric property of the
arcs. It reduces the original obligation to removal of finite families. -/
theorem locally_finite_gluing_of_finite_gluing.{u}
    (hfinite : Specs.D12Complex.Ch04.RectifiableArcGluing.finite_rectifiable_arc_gluing_type) :
    Specs.D12Complex.Ch04.RectifiableArcGluing.rectifiable_arc_gluing_type.{u} := by
  intro ι γ Ω f hγ htr hΩ hlf hf hd
  classical
  refine ⟨hΩ, ?_⟩
  intro z hz
  obtain ⟨U, hU, hzU, hs⟩ := hlf z hz
  let s : Finset ι := hs.toFinset
  let n := Fintype.card {i // i ∈ s}
  let e : Fin n ≃ {i // i ∈ s} := (Fintype.equivFin _).symm
  let η : Fin n → ComplexPath := fun j => γ (e j).val
  have hsub : (Ω ∩ U) \ (⋃ j, (η j).trace) ⊆ Ω \ (⋃ i, (γ i).trace) := by
    intro w hw
    refine ⟨hw.1.1, ?_⟩
    intro hwi
    obtain ⟨i, hi⟩ := mem_iUnion.mp hwi
    have his : i ∈ s := by
      change i ∈ hs.toFinset
      exact hs.mem_toFinset.mpr ⟨w, hi, hw.1.2⟩
    have he : η (e.symm ⟨i, his⟩) = γ i := by simp [η]
    exact hw.2 (mem_iUnion.mpr ⟨e.symm ⟨i, his⟩, he.symm ▸ hi⟩)
  have hlocal : HolomorphicOn (Ω ∩ U) f :=
    hfinite n η (Ω ∩ U) f (fun j => hγ _) (hΩ.inter hU)
      (hf.mono inter_subset_left)
      ⟨(hΩ.inter hU).sdiff
        (isCompact_iUnion (fun j => ComplexPath.trace_compact (η j))).isClosed,
        fun w hw => hd.2 w (hsub hw)⟩
  exact hlocal.2 z ⟨hz, hzU⟩

end D12Complex.ArcGluing

namespace D12Complex.ArcGluing

attribute [local instance] Classical.propDecidable

/-- Closed cells of an axis-parallel rectangular lattice. Boundaries are
included, so the incidence estimates also count tangencies and grid vertices. -/
def gridCell (a : ℂ) (dx dy : ℝ) (k : ℤ × ℤ) : Set ℂ :=
  {z | z.re ∈ Icc (a.re + k.1 * dx) (a.re + (k.1 + 1) * dx) ∧
    z.im ∈ Icc (a.im + k.2 * dy) (a.im + (k.2 + 1) * dy)}

theorem grid_interval_indices {a c z d r : ℝ} {i : ℤ}
    (hd : 0 < d) (hrd : r ≤ d)
    (hz : z ∈ Icc (a + i * d) (a + (i + 1) * d))
    (hc : |z - c| ≤ r) :
    i ∈ Finset.Icc (⌊(c - a) / d⌋ - 2) (⌊(c - a) / d⌋ + 1) := by
  have hc₀ : (⌊(c - a) / d⌋ : ℝ) * d ≤ c - a :=
    (le_div_iff₀ hd).mp (Int.floor_le _)
  have hc₁ : c - a < ((⌊(c - a) / d⌋ : ℝ) + 1) * d :=
    (div_lt_iff₀ hd).mp (Int.lt_floor_add_one _)
  have hc' := abs_le.mp hc
  have hlow : (⌊(c - a) / d⌋ : ℝ) - 2 ≤ (i : ℝ) := by
    nlinarith [hz.2]
  have hhigh : (i : ℝ) < (⌊(c - a) / d⌋ : ℝ) + 2 := by
    nlinarith [hz.1]
  simp only [Finset.mem_Icc]
  constructor
  · exact_mod_cast hlow
  · have : i < ⌊(c - a) / d⌋ + 2 := by exact_mod_cast hhigh
    omega

/-- The sixteen possible cell indices for a disk no larger than either
lattice spacing. This finite set is independent of the selected grid patch. -/
def diskGridIndices (a c : ℂ) (dx dy : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (⌊(c.re - a.re) / dx⌋ - 2) (⌊(c.re - a.re) / dx⌋ + 1)).product
    (Finset.Icc (⌊(c.im - a.im) / dy⌋ - 2) (⌊(c.im - a.im) / dy⌋ + 1))

theorem diskGridIndices_card (a c : ℂ) (dx dy : ℝ) :
    (diskGridIndices a c dx dy).card = 16 := by
  have h (q : ℤ) : q + 1 + 1 - (q - 2) = 4 := by omega
  simp [diskGridIndices, Finset.card_product, Int.card_Icc, h]

theorem gridCell_disk_index {a c : ℂ} {dx dy r : ℝ} {k : ℤ × ℤ}
    (hdx : 0 < dx) (hdy : 0 < dy) (hrx : r ≤ dx) (hry : r ≤ dy)
    (hk : (gridCell a dx dy k ∩ closedBall c r).Nonempty) :
    k ∈ diskGridIndices a c dx dy := by
  obtain ⟨z, hz, hzc⟩ := hk
  have hn : ‖z - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hzc
  have hre : |z.re - c.re| ≤ r := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z - c)).trans hn
  have him : |z.im - c.im| ≤ r := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - c)).trans hn
  exact Finset.mem_product.mpr
    ⟨grid_interval_indices hdx hrx hz.1 hre, grid_interval_indices hdy hry hz.2 him⟩

/-- A disk meets at most sixteen cells in any finite patch of the lattice. -/
theorem gridCell_disk_card (s : Finset (ℤ × ℤ)) (a c : ℂ) (dx dy r : ℝ)
    (hdx : 0 < dx) (hdy : 0 < dy) (hrx : r ≤ dx) (hry : r ≤ dy) :
    (s.filter (fun k => (gridCell a dx dy k ∩ closedBall c r).Nonempty)).card ≤ 16 := by
  classical
  calc
    _ ≤ (diskGridIndices a c dx dy).card := Finset.card_le_card (by
      intro k hk
      exact gridCell_disk_index hdx hdy hrx hry (Finset.mem_filter.mp hk).2)
    _ = 16 := diskGridIndices_card a c dx dy

/-- Any finite disk cover controls the number of exceptional cells, without
requiring disjoint disks or any separation of the exceptional traces. -/
theorem gridCell_cover_card (s : Finset (ℤ × ℤ)) (a : ℂ) (dx dy r : ℝ)
    (hdx : 0 < dx) (hdy : 0 < dy) (hrx : r ≤ dx) (hry : r ≤ dy)
    (E : Set ℂ) (n : ℕ) (c : Fin n → ℂ)
    (hcover : E ⊆ ⋃ j, closedBall (c j) r) :
    (s.filter (fun k => (gridCell a dx dy k ∩ E).Nonempty)).card ≤ 16 * n := by
  classical
  let disks : Fin n → Finset (ℤ × ℤ) := fun j =>
    s.filter (fun k => (gridCell a dx dy k ∩ closedBall (c j) r).Nonempty)
  have hsub : s.filter (fun k => (gridCell a dx dy k ∩ E).Nonempty) ⊆
      Finset.univ.biUnion disks := by
    intro k hk
    obtain ⟨z, hzk, hzE⟩ := (Finset.mem_filter.mp hk).2
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hzE)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, z, hzk, hj⟩⟩
  calc
    _ ≤ (Finset.univ.biUnion disks).card := Finset.card_le_card hsub
    _ ≤ ∑ j : Fin n, (disks j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin n, 16 := Finset.sum_le_sum fun j _ =>
      gridCell_disk_card s a (c j) dx dy r hdx hdy hrx hry
    _ = 16 * n := by simp [Nat.mul_comm]

/-- Quantitative perimeter control for the grid cells meeting a linearly
coverable set. The bound has no dependence on the number of grid cells. -/
theorem gridCell_bad_perimeter_bound {E : Set ℂ} (hE : HasLinearCoverBound E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset (ℤ × ℤ)) (a : ℂ) (dx dy r : ℝ),
      0 < dx → 0 < dy → 0 < r → r ≤ 1 → r ≤ dx → r ≤ dy →
      (s.filter (fun k => (gridCell a dx dy k ∩ E).Nonempty)).card *
        (2 * (dx + dy)) ≤ C * ((dx + dy) / r) := by
  obtain ⟨C, hC, hcover⟩ := hE
  refine ⟨32 * C, by positivity, ?_⟩
  intro s a dx dy r hdx hdy hr hr1 hrx hry
  obtain ⟨n, c, hn, hc⟩ := hcover r hr hr1
  have hcard := gridCell_cover_card s a dx dy r hdx hdy hrx hry E n c hc
  have hcard' :
      ((s.filter (fun k => (gridCell a dx dy k ∩ E).Nonempty)).card : ℝ) ≤
        16 * (n : ℝ) := by exact_mod_cast hcard
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hr).mpr
  calc
    _ = ((s.filter (fun k => (gridCell a dx dy k ∩ E).Nonempty)).card : ℝ) *
        r * (2 * (dx + dy)) := by ring
    _ ≤ (16 * C) * (2 * (dx + dy)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith
    _ = _ := by ring

/-- Exact cancellation of internal directed edges on a rectangular grid.
No regularity or analytic assertion is hidden in this algebraic identity. -/
theorem grid_edge_cancellation (H V : ℕ → ℕ → ℂ) (m n : ℕ) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
      (H i j + V (i + 1) j - H i (j + 1) - V i j)) =
    (∑ i ∈ Finset.range m, (H i 0 - H i n)) +
      ∑ j ∈ Finset.range n, (V m j - V 0 j) := by
  have htel (F : ℕ → ℂ) (k : ℕ) :
      (∑ i ∈ Finset.range k, (F (i + 1) - F i)) = F k - F 0 := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; abel
  calc
    _ = (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (H i j - H i (j + 1))) +
        ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (V (i + 1) j - V i j) := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      abel
    _ = _ := by
      have hrev (F : ℕ → ℂ) :
          (∑ j ∈ Finset.range n, (F j - F (j + 1))) = F 0 - F n := by
        simpa only [← Finset.sum_neg_distrib, neg_sub] using congrArg Neg.neg (htel F n)
      simp_rw [hrev]
      rw [Finset.sum_comm (s := Finset.range m) (t := Finset.range n)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact htel (fun i => V i j) m

/-- The boundary integral of an axis-parallel rectangle, in the real-coordinate
presentation used by Mathlib's Cauchy and Morera theorems. -/
def rectangleIntegral (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) : ℂ :=
  (∫ x in x₀..x₁, f (x + y₀ * Complex.I)) -
    (∫ x in x₀..x₁, f (x + y₁ * Complex.I)) +
    Complex.I * (∫ y in y₀..y₁, f (x₁ + y * Complex.I)) -
    Complex.I * (∫ y in y₀..y₁, f (x₀ + y * Complex.I))

/-- Subdivision with complete interior cancellation, for arbitrary increasing
coordinate partitions, including degenerate sides and zero-size grids. -/
theorem rectangleIntegral_grid_sum (f : ℂ → ℂ) (x y : ℕ → ℝ) (m n : ℕ)
    (hx : Monotone x) (hy : Monotone y)
    (hf : ContinuousOn f (Icc (x 0) (x m) ×ℂ Icc (y 0) (y n))) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
      rectangleIntegral f (x i) (x (i + 1)) (y j) (y (j + 1))) =
      rectangleIntegral f (x 0) (x m) (y 0) (y n) := by
  have hhor (j : ℕ) (hj : j ≤ n) :
      (∑ i ∈ Finset.range m, ∫ t in x i..x (i + 1), f (t + y j * Complex.I)) =
        ∫ t in x 0..x m, f (t + y j * Complex.I) := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro i hi
    apply ContinuousOn.intervalIntegrable_of_Icc (hx (Nat.le_add_right _ _))
    exact hf.comp (by fun_prop) (by
      intro t ht
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, zero_add, Complex.add_im,
        Complex.mul_im, mul_one]
      exact ⟨⟨(hx (Nat.zero_le i)).trans ht.1,
        ht.2.trans (hx (Nat.succ_le_of_lt hi))⟩, ⟨hy (Nat.zero_le j), hy hj⟩⟩)
  have hvert (i : ℕ) (hi : i ≤ m) :
      (∑ j ∈ Finset.range n, ∫ t in y j..y (j + 1), f (x i + t * Complex.I)) =
        ∫ t in y 0..y n, f (x i + t * Complex.I) := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro j hj
    apply ContinuousOn.intervalIntegrable_of_Icc (hy (Nat.le_add_right _ _))
    exact hf.comp (by fun_prop) (by
      intro t ht
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, zero_add, Complex.add_im,
        Complex.mul_im, mul_one]
      exact ⟨⟨hx (Nat.zero_le i), hx hi⟩,
        (hy (Nat.zero_le j)).trans ht.1, ht.2.trans (hy (Nat.succ_le_of_lt hj))⟩)
  have hc := grid_edge_cancellation
    (fun i j => ∫ t in x i..x (i + 1), f (t + y j * Complex.I))
    (fun i j => Complex.I * ∫ t in y j..y (j + 1), f (x i + t * Complex.I)) m n
  have heq (i j : ℕ) :
      rectangleIntegral f (x i) (x (i + 1)) (y j) (y (j + 1)) =
        (∫ t in x i..x (i + 1), f (t + y j * Complex.I)) +
          Complex.I * (∫ t in y j..y (j + 1), f (x (i + 1) + t * Complex.I)) -
        (∫ t in x i..x (i + 1), f (t + y (j + 1) * Complex.I)) -
          Complex.I * (∫ t in y j..y (j + 1), f (x i + t * Complex.I)) := by
    unfold rectangleIntegral
    abel
  simp_rw [heq]
  rw [hc]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hhor 0 (Nat.zero_le _), hhor n le_rfl, hvert m le_rfl, hvert 0 (Nat.zero_le _)]
  unfold rectangleIntegral
  abel

theorem rectangle_horizontal_continuous {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ y : ℝ}
    (hf : ContinuousOn f (Icc x₀ x₁ ×ℂ Icc y₀ y₁)) (hy : y ∈ Icc y₀ y₁) :
    ContinuousOn (fun x : ℝ => f (x + y * Complex.I)) (Icc x₀ x₁) :=
  hf.comp (by fun_prop) (by intro t ht; simpa [Complex.mem_reProdIm] using And.intro ht hy)

theorem rectangle_vertical_continuous {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ x : ℝ}
    (hf : ContinuousOn f (Icc x₀ x₁ ×ℂ Icc y₀ y₁)) (hx : x ∈ Icc x₀ x₁) :
    ContinuousOn (fun y : ℝ => f (x + y * Complex.I)) (Icc y₀ y₁) :=
  hf.comp (by fun_prop) (by intro t ht; simpa [Complex.mem_reProdIm] using And.intro hx ht)

/-- Pairing opposite edges gives an ML estimate by the oscillation on the
cell. This is the constant-subtraction estimate with the paired constants
already cancelled. -/
theorem rectangleIntegral_norm_le_of_oscillation {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ ε : ℝ}
    (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (Icc x₀ x₁ ×ℂ Icc y₀ y₁))
    (hosc : ∀ z ∈ Icc x₀ x₁ ×ℂ Icc y₀ y₁,
      ∀ w ∈ Icc x₀ x₁ ×ℂ Icc y₀ y₁, ‖f z - f w‖ ≤ ε) :
    ‖rectangleIntegral f x₀ x₁ y₀ y₁‖ ≤ ε * ((x₁ - x₀) + (y₁ - y₀)) := by
  have h₀ := rectangle_horizontal_continuous hf (left_mem_Icc.mpr hy)
  have h₁ := rectangle_horizontal_continuous hf (right_mem_Icc.mpr hy)
  have v₀ := rectangle_vertical_continuous hf (left_mem_Icc.mpr hx)
  have v₁ := rectangle_vertical_continuous hf (right_mem_Icc.mpr hx)
  have hh : ‖∫ t in x₀..x₁, (f (t + y₀ * Complex.I) - f (t + y₁ * Complex.I))‖ ≤
      ε * (x₁ - x₀) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε) ?_).trans_eq
      (by rw [abs_of_nonneg (sub_nonneg.mpr hx)])
    intro t ht
    have ht' : t ∈ Icc x₀ x₁ := ⟨(uIoc_of_le hx ▸ ht).1.le, (uIoc_of_le hx ▸ ht).2⟩
    exact hosc _ (by simpa [Complex.mem_reProdIm] using And.intro ht' (left_mem_Icc.mpr hy))
      _ (by simpa [Complex.mem_reProdIm] using And.intro ht' (right_mem_Icc.mpr hy))
  have hv : ‖∫ t in y₀..y₁, (f (x₁ + t * Complex.I) - f (x₀ + t * Complex.I))‖ ≤
      ε * (y₁ - y₀) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε) ?_).trans_eq
      (by rw [abs_of_nonneg (sub_nonneg.mpr hy)])
    intro t ht
    have ht' : t ∈ Icc y₀ y₁ := ⟨(uIoc_of_le hy ▸ ht).1.le, (uIoc_of_le hy ▸ ht).2⟩
    exact hosc _ (by simpa [Complex.mem_reProdIm] using And.intro (right_mem_Icc.mpr hx) ht')
      _ (by simpa [Complex.mem_reProdIm] using And.intro (left_mem_Icc.mpr hx) ht')
  have heq : rectangleIntegral f x₀ x₁ y₀ y₁ =
      (∫ t in x₀..x₁, (f (t + y₀ * Complex.I) - f (t + y₁ * Complex.I))) +
        Complex.I * (∫ t in y₀..y₁, (f (x₁ + t * Complex.I) - f (x₀ + t * Complex.I))) := by
    rw [intervalIntegral.integral_sub (h₀.intervalIntegrable_of_Icc hx)
      (h₁.intervalIntegrable_of_Icc hx),
      intervalIntegral.integral_sub (v₁.intervalIntegrable_of_Icc hy)
      (v₀.intervalIntegrable_of_Icc hy)]
    unfold rectangleIntegral
    ring
  rw [heq]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ ε * (x₁ - x₀) + ε * (y₁ - y₀) := by
      simpa only [norm_mul, Complex.norm_I, one_mul] using add_le_add hh hv
    _ = _ := by ring

/-- The diameter estimate uses the sum norm on coordinates, so it applies
uniformly even to very thin rectangles. -/
theorem rectangle_dist_le {x₀ x₁ y₀ y₁ : ℝ} {z w : ℂ}
    (hz : z ∈ Icc x₀ x₁ ×ℂ Icc y₀ y₁)
    (hw : w ∈ Icc x₀ x₁ ×ℂ Icc y₀ y₁) :
    dist z w ≤ (x₁ - x₀) + (y₁ - y₀) := by
  have hre : |(z - w).re| ≤ x₁ - x₀ := by
    rw [Complex.sub_re, abs_le]
    constructor <;> linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2]
  have him : |(z - w).im| ≤ y₁ - y₀ := by
    rw [Complex.sub_im, abs_le]
    constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]
  simpa only [dist_eq_norm] using
    (Complex.norm_le_abs_re_add_abs_im (z - w)).trans (add_le_add hre him)

/-- Transfer the incidence estimate to any injectively indexed finite grid. -/
theorem gridCell_cover_card_of_injective {ι : Type*} (s : Finset ι)
    (k : ι → ℤ × ℤ) (hk : Function.Injective k)
    (a : ℂ) (dx dy r : ℝ) (hdx : 0 < dx) (hdy : 0 < dy)
    (hrx : r ≤ dx) (hry : r ≤ dy) (E : Set ℂ) (n : ℕ) (c : Fin n → ℂ)
    (hcover : E ⊆ ⋃ j, closedBall (c j) r) :
    (s.filter (fun i => (gridCell a dx dy (k i) ∩ E).Nonempty)).card ≤ 16 * n := by
  classical
  calc
    _ ≤ ((s.image k).filter (fun j => (gridCell a dx dy j ∩ E).Nonempty)).card := by
      apply Finset.card_le_card_of_injOn k
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
          ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩, (Finset.mem_filter.mp hi).2⟩
      · exact hk.injOn
    _ ≤ 16 * n := gridCell_cover_card _ a dx dy r hdx hdy hrx hry E n c hcover

/-- Good cells vanish by Cauchy-Goursat. This only uses differentiability
at the actual points of the cell, and does not add a neighborhood hypothesis. -/
theorem rectangleIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ}
    (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hd : DifferentiableOn ℂ f (Icc x₀ x₁ ×ℂ Icc y₀ y₁)) :
    rectangleIntegral f x₀ x₁ y₀ y₁ = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (x₀ + y₀ * Complex.I) (x₁ + y₁ * Complex.I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, mul_one, zero_add, uIcc_of_le hx, uIcc_of_le hy] at h
  simpa only [smul_eq_mul, rectangleIntegral] using h hd

/-- Finite-length removal on a single ordered rectangle. The proof uses
only continuity on that rectangle and differentiability at its points off E. -/
theorem rectangleIntegral_zero_of_linear_cover {E : Set ℂ} (hE : HasLinearCoverBound E)
    {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (Icc x₀ x₁ ×ℂ Icc y₀ y₁))
    (hd : ∀ z ∈ (Icc x₀ x₁ ×ℂ Icc y₀ y₁) \ E, DifferentiableAt ℂ f z) :
    rectangleIntegral f x₀ x₁ y₀ y₁ = 0 := by
  classical
  by_cases heqx : x₀ = x₁
  · subst x₁; simp [rectangleIntegral]
  by_cases heqy : y₀ = y₁
  · subst y₁; simp [rectangleIntegral]
  have hw : 0 < x₁ - x₀ := sub_pos.mpr (lt_of_le_of_ne hx heqx)
  have hh : 0 < y₁ - y₀ := sub_pos.mpr (lt_of_le_of_ne hy heqy)
  obtain ⟨C, hC, hcover⟩ := hE
  let w := x₁ - x₀
  let h := y₁ - y₀
  let q := min w h
  have hq : 0 < q := lt_min hw hh
  let K := (w + h) / q
  have hK : 0 ≤ K := div_nonneg (add_nonneg hw.le hh.le) hq.le
  let B := 16 * C * K
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply norm_le_zero_iff.mp
  apply le_of_forall_pos_le_add
  intro ε hε
  let τ := ε / (B + 1)
  have hτ : 0 < τ := div_pos hε (by positivity)
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc.reProdIm isCompact_Icc).uniformContinuousOn_of_continuous hf) τ hτ
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((w + h) / δ) q + 1)
  have hNpos : 0 < (N : ℝ) := lt_trans (by positivity) hN
  have hN₁ : (w + h) / δ < (N : ℝ) := by
    linarith [le_max_left ((w + h) / δ) q]
  have hN₂ : q < (N : ℝ) := by linarith [le_max_right ((w + h) / δ) q]
  let dx := w / (N : ℝ)
  let dy := h / (N : ℝ)
  let r := q / (N : ℝ)
  have hdx : 0 < dx := div_pos hw hNpos
  have hdy : 0 < dy := div_pos hh hNpos
  have hr : 0 < r := div_pos hq hNpos
  have hr1 : r ≤ 1 := (div_le_one hNpos).mpr hN₂.le
  have hrx : r ≤ dx := div_le_div_of_nonneg_right (min_le_left w h) hNpos.le
  have hry : r ≤ dy := div_le_div_of_nonneg_right (min_le_right w h) hNpos.le
  have hsmall : dx + dy < δ := by
    dsimp only [dx, dy]
    rw [← add_div]
    apply (div_lt_iff₀ hNpos).mpr
    exact (div_lt_iff₀ hδ).mp hN₁ |>.trans_eq (mul_comm _ _)
  let x : ℕ → ℝ := fun i => x₀ + i * dx
  let y : ℕ → ℝ := fun j => y₀ + j * dy
  have hxmono : Monotone x := by
    intro i j hij
    dsimp only [x]
    exact add_le_add_right (mul_le_mul_of_nonneg_right
      (show (i : ℝ) ≤ (j : ℝ) from by exact_mod_cast hij) hdx.le) _
  have hymono : Monotone y := by
    intro i j hij
    dsimp only [y]
    exact add_le_add_right (mul_le_mul_of_nonneg_right
      (show (i : ℝ) ≤ (j : ℝ) from by exact_mod_cast hij) hdy.le) _
  have hx0 : x 0 = x₀ := by simp [x]
  have hy0 : y 0 = y₀ := by simp [y]
  have hxN : x N = x₁ := by dsimp [x, dx, w]; field_simp [ne_of_gt hNpos]; ring
  have hyN : y N = y₁ := by dsimp [y, dy, h]; field_simp [ne_of_gt hNpos]; ring
  let S : Finset (ℕ × ℕ) := (Finset.range N).product (Finset.range N)
  let k : ℕ × ℕ → ℤ × ℤ := fun p => (p.1, p.2)
  have hk : Function.Injective k := by
    intro i j hij
    have hi := congrArg Prod.fst hij
    have hj := congrArg Prod.snd hij
    dsimp only [k] at hi hj
    exact Prod.ext (by exact_mod_cast hi) (by exact_mod_cast hj)
  let a : ℂ := x₀ + y₀ * Complex.I
  have hcell (p : ℕ × ℕ) : gridCell a dx dy (k p) =
      Icc (x p.1) (x (p.1 + 1)) ×ℂ Icc (y p.2) (y (p.2 + 1)) := by
    ext z
    simp [gridCell, a, k, x, y, Complex.mem_reProdIm, Nat.cast_add, Nat.cast_one]
  have hsub (p : ℕ × ℕ) (hp : p ∈ S) :
      (Icc (x p.1) (x (p.1 + 1)) ×ℂ Icc (y p.2) (y (p.2 + 1))) ⊆
        Icc x₀ x₁ ×ℂ Icc y₀ y₁ := by
    have hi := Finset.mem_product.mp hp
    have hip : p.1 + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hi.1)
    have hjp : p.2 + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hi.2)
    intro z hz
    exact ⟨⟨(hx0 ▸ hxmono (Nat.zero_le p.1)).trans hz.1.1,
      hz.1.2.trans (hxN ▸ hxmono hip)⟩,
      (hy0 ▸ hymono (Nat.zero_le p.2)).trans hz.2.1,
      hz.2.2.trans (hyN ▸ hymono hjp)⟩
  let bad := S.filter (fun p => (gridCell a dx dy (k p) ∩ E).Nonempty)
  let F : ℕ × ℕ → ℂ := fun p =>
    rectangleIntegral f (x p.1) (x (p.1 + 1)) (y p.2) (y (p.2 + 1))
  have hgood (p : ℕ × ℕ) (hp : p ∈ S) (hbad : p ∉ bad) : F p = 0 := by
    apply rectangleIntegral_eq_zero_of_differentiableOn
      (hxmono (Nat.le_add_right _ _)) (hymono (Nat.le_add_right _ _))
    intro z hz
    apply (hd z ⟨hsub p hp hz, ?_⟩).differentiableWithinAt
    intro hzE
    apply hbad
    exact Finset.mem_filter.mpr ⟨hp, z, (hcell p).symm ▸ hz, hzE⟩
  have hgrid := rectangleIntegral_grid_sum f x y N N hxmono hymono
    (by simpa only [hx0, hy0, hxN, hyN] using hf)
  simp only [hx0, hy0, hxN, hyN] at hgrid
  have hsum : rectangleIntegral f x₀ x₁ y₀ y₁ = ∑ p ∈ bad, F p := by
    calc
      _ = ∑ p ∈ S, F p := by
        rw [← hgrid]
        exact (Finset.sum_product (Finset.range N) (Finset.range N) F).symm
      _ = _ := (Finset.sum_subset (Finset.filter_subset _ _) hgood).symm
  have hosc (p : ℕ × ℕ) (hp : p ∈ S) : ‖F p‖ ≤ τ * (dx + dy) := by
    have he : (x (p.1 + 1) - x p.1) + (y (p.2 + 1) - y p.2) = dx + dy := by
      dsimp [x, y]; push_cast; ring
    apply (rectangleIntegral_norm_le_of_oscillation
      (hxmono (Nat.le_add_right _ _)) (hymono (Nat.le_add_right _ _))
      (hf.mono (hsub p hp)) ?_).trans_eq (congrArg (τ * ·) he)
    intro z hz w hw
    exact (by simpa only [dist_eq_norm] using
      (huc z (hsub p hp hz) w (hsub p hp hw)
        ((rectangle_dist_le hz hw).trans_lt (he ▸ hsmall))).le)
  obtain ⟨n, c, hn, hc⟩ := hcover r hr hr1
  have hcard : bad.card ≤ 16 * n :=
    gridCell_cover_card_of_injective S k hk a dx dy r hdx hdy hrx hry E n c hc
  have hb : (bad.card : ℝ) * r ≤ 16 * C := by
    have hcard' : (bad.card : ℝ) ≤ 16 * (n : ℝ) := by exact_mod_cast hcard
    nlinarith
  have hratio : dx + dy = K * r := by
    dsimp [dx, dy, K, r]
    field_simp [ne_of_gt hq, ne_of_gt hNpos]
  have hbound : (bad.card : ℝ) * (dx + dy) ≤ B := by
    dsimp only [B]
    rw [hratio]
    nlinarith [mul_le_mul_of_nonneg_right hb hK]
  have hτB : τ * B ≤ ε := by
    have ht : τ * (B + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  calc
    ‖rectangleIntegral f x₀ x₁ y₀ y₁‖ = ‖∑ p ∈ bad, F p‖ := congrArg norm hsum
    _ ≤ ∑ p ∈ bad, ‖F p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ bad, τ * (dx + dy) := Finset.sum_le_sum fun p hp =>
      hosc p (Finset.mem_filter.mp hp).1
    _ = τ * ((bad.card : ℝ) * (dx + dy)) := by simp; ring
    _ ≤ τ * B := mul_le_mul_of_nonneg_left hbound hτ.le
    _ ≤ 0 + ε := by simpa using hτB

theorem rectangleIntegral_swap_x (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) :
    rectangleIntegral f x₀ x₁ y₀ y₁ = -rectangleIntegral f x₁ x₀ y₀ y₁ := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_symm x₁ x₀]
  abel

theorem rectangleIntegral_swap_y (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) :
    rectangleIntegral f x₀ x₁ y₀ y₁ = -rectangleIntegral f x₀ x₁ y₁ y₀ := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_symm y₁ y₀, mul_neg]
  abel

/-- The orientation-free version needed by the rectangle formulation of Morera. -/
theorem rectangleIntegral_zero_of_linear_cover_unordered {E : Set ℂ}
    (hE : HasLinearCoverBound E) {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ}
    (hf : ContinuousOn f (uIcc x₀ x₁ ×ℂ uIcc y₀ y₁))
    (hd : ∀ z ∈ (uIcc x₀ x₁ ×ℂ uIcc y₀ y₁) \ E, DifferentiableAt ℂ f z) :
    rectangleIntegral f x₀ x₁ y₀ y₁ = 0 := by
  rcases le_total x₀ x₁ with hx | hx <;> rcases le_total y₀ y₁ with hy | hy
  · simp only [uIcc_of_le hx, uIcc_of_le hy] at hf hd
    exact rectangleIntegral_zero_of_linear_cover hE hx hy hf hd
  · simp only [uIcc_of_le hx, uIcc_of_ge hy] at hf hd
    rw [rectangleIntegral_swap_y, rectangleIntegral_zero_of_linear_cover hE hx hy hf hd, neg_zero]
  · simp only [uIcc_of_ge hx, uIcc_of_le hy] at hf hd
    rw [rectangleIntegral_swap_x, rectangleIntegral_zero_of_linear_cover hE hx hy hf hd, neg_zero]
  · simp only [uIcc_of_ge hx, uIcc_of_ge hy] at hf hd
    rw [rectangleIntegral_swap_x, rectangleIntegral_swap_y f x₁ x₀,
      rectangleIntegral_zero_of_linear_cover hE hx hy hf hd, neg_zero, neg_zero]

/-- Compact sets with a linear disk-cover bound are removable for continuous
holomorphic functions. The rectangle argument above in fact needs no
compactness of E. -/
theorem linear_cover_gluing :
    Specs.D12Complex.Ch04.RectifiableArcGluing.linear_cover_gluing_type := by
  intro Ω E f hΩ _hcompact hE hf hd
  have hcon : Complex.IsConservativeOn f Ω := by
    intro z w hrect
    rw [← add_eq_zero_iff_eq_neg, Complex.wedgeIntegral_add_wedgeIntegral_eq]
    change rectangleIntegral f z.re w.re z.im w.im = 0
    apply rectangleIntegral_zero_of_linear_cover_unordered hE (hf.mono hrect)
    intro p hp
    exact hd.2 p ⟨hrect hp.1, hp.2⟩
  have hdiff : DifferentiableOn ℂ f Ω :=
    (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hΩ).mp ⟨hcon, hf⟩
  exact ⟨hΩ, fun z hz => (hdiff z hz).differentiableAt (hΩ.mem_nhds hz)⟩

theorem finite_rectifiable_arc_gluing :
    Specs.D12Complex.Ch04.RectifiableArcGluing.finite_rectifiable_arc_gluing_type :=
  finite_gluing_of_linear_cover_gluing linear_cover_gluing

/-- Continuous gluing across an arbitrary locally finite family of compact
rectifiable path traces, and hence across the rectifiable arcs of D12.04.08. -/
theorem rectifiable_arc_gluing.{u} :
    Specs.D12Complex.Ch04.RectifiableArcGluing.rectifiable_arc_gluing_type.{u} :=
  locally_finite_gluing_of_finite_gluing finite_rectifiable_arc_gluing

end D12Complex.ArcGluing
