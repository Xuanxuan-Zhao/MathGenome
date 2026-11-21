import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathsChains
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PC1MonotoneChainRule
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PC1MonotoneSubstitution
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PathOperations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Order.Fin.Tuple
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace D12Complex

/-- Repeated nodes can be removed without making any new smoothness assertion. -/
private theorem strictify_partition (f : ℝ → ℂ) :
    ∀ (n : ℕ) (node : Fin (n + 1) → ℝ), Monotone node →
      (∀ i : Fin n, ContDiffOn ℝ 1 f (Icc (node i.castSucc) (node i.succ))) →
      ∃ (m : ℕ) (v : Fin (m + 1) → ℝ), StrictMono v ∧
        v 0 = node 0 ∧ v (Fin.last m) = node (Fin.last n) ∧
        ∀ i : Fin m, ContDiffOn ℝ 1 f (Icc (v i.castSucc) (v i.succ)) := by
  intro n
  induction n with
  | zero =>
    intro node _ _
    exact ⟨0, node, by intro i j h; exact (by omega : False).elim, rfl, rfl,
      fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro node hm hC1
    obtain ⟨m, v, hv, h0, hlast, hs⟩ := ih (fun i => node i.succ)
      (fun _ _ h => hm (by simpa using h)) (fun i => by
        simpa only [Fin.succ_castSucc] using hC1 i.succ)
    have hle : node 0 ≤ v 0 := by rw [h0]; exact hm (Fin.zero_le _)
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact ⟨m, v, hv, heq.symm, hlast, hs⟩
    · refine ⟨m + 1, Fin.cons (node 0) v, Fin.strictMono_cons.mpr ⟨?_, hv⟩,
        rfl, ?_, ?_⟩
      · intro j
        exact hlt.trans_le (hv.monotone (Fin.zero_le j))
      · simpa using hlast
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [h0] using hC1 0
        · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hs j

private theorem monotone_cons {n : ℕ} {v : Fin (n + 1) → ℝ} {a : ℝ}
    (hm : Monotone v) (ha : a ≤ v 0) : Monotone (Fin.cons a v) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using ha
  · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using
      hm (Fin.castSucc_le_succ j)

/-- Append two finite lists of smooth pieces with a common joining node. -/
private theorem append_partitions (f : ℝ → ℂ) :
    ∀ (n : ℕ) (v : Fin (n + 1) → ℝ), Monotone v →
      (∀ i : Fin n, ContDiffOn ℝ 1 f (Icc (v i.castSucc) (v i.succ))) →
      ∀ (m : ℕ) (w : Fin (m + 1) → ℝ), Monotone w →
        v (Fin.last n) = w 0 →
        (∀ i : Fin m, ContDiffOn ℝ 1 f (Icc (w i.castSucc) (w i.succ))) →
        ∃ (k : ℕ) (u : Fin (k + 1) → ℝ), Monotone u ∧
          u 0 = v 0 ∧ u (Fin.last k) = w (Fin.last m) ∧
          ∀ i : Fin k, ContDiffOn ℝ 1 f (Icc (u i.castSucc) (u i.succ)) := by
  intro n
  induction n with
  | zero =>
    intro v _ _ m w hm heq hs
    exact ⟨m, w, hm, heq.symm, rfl, hs⟩
  | succ n ih =>
    intro v hv hvs m w hw heq hws
    obtain ⟨k, u, hu, h0, hl, hs⟩ := ih (fun i => v i.succ)
      (fun _ _ h => hv (by simpa using h))
      (fun i => by simpa only [Fin.succ_castSucc] using hvs i.succ)
      m w hw heq hws
    refine ⟨k + 1, Fin.cons (v 0) u, monotone_cons hu ?_, rfl, ?_, ?_⟩
    · rw [h0]; exact hv (Fin.zero_le _)
    · simpa using hl
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [h0] using hvs 0
      · simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hs j

/-- A nonstrict finite partition is sufficient; empty and repeated pieces are harmless. -/
theorem isPiecewiseC1_of_monotone_partition (γ : ComplexPath) (n : ℕ)
    (node : Fin (n + 1) → ℝ) (hm : Monotone node)
    (h0 : node 0 = γ.a) (hlast : node (Fin.last n) = γ.b)
    (hs : ∀ i : Fin n, ContDiffOn ℝ 1 γ (Icc (node i.castSucc) (node i.succ))) :
    IsPiecewiseC1 γ := by
  obtain ⟨m, v, hv, hv0, hvl, hvs⟩ := strictify_partition γ n node hm hs
  exact ⟨⟨m, v, hv, hv0.trans h0, hvl.trans hlast, hvs⟩⟩

private theorem contDiffOn_Icc_self (f : ℝ → ℂ) (a : ℝ) :
    ContDiffOn ℝ 1 f (Icc a a) := by
  apply contDiffOn_const.congr
  intro t ht
  have : t = a := le_antisymm ht.2 ht.1
  subst t
  rfl

/-- Finite additivity, keeping the integrability conclusion for later use. -/
theorem intervalIntegral_fin_partition {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {n : ℕ} (node : Fin (n + 1) → ℝ)
    (g : ℝ → E)
    (h : ∀ i : Fin n, IntervalIntegrable g volume (node i.castSucc) (node i.succ)) :
    IntervalIntegrable g volume (node 0) (node (Fin.last n)) ∧
      (∑ i : Fin n, ∫ t in node i.castSucc..node i.succ, g t) =
        ∫ t in node 0..node (Fin.last n), g t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := ih (fun i => node i.succ) (fun i => h i.succ)
    refine ⟨(h 0).trans ht.1, ?_⟩
    rw [Fin.sum_univ_succ]
    simp_rw [← Fin.succ_castSucc]
    rw [ht.2]
    exact intervalIntegral.integral_add_adjacent_intervals (h 0) ht.1

namespace C1Partition

theorem piece_integrable_deriv {γ : ComplexPath} (P : C1Partition γ)
    (f : ℂ → ℂ) (hf : ContinuousOn f γ.trace) (i : Fin P.count) :
    IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume
      (P.node i.castSucc) (P.node i.succ) := by
  apply (P.piece_integrable f hf i).congr_uIoo
  rw [uIoo_of_le (P.piece_lt i).le]
  intro t ht
  simp only [pieceSet, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

theorem integral_eq_intervalIntegral :
    Specs.D12Complex.Ch03.PathOperations.partition_integral_eq_intervalIntegral_type := by
  intro γ P f hf
  unfold integral
  have h := intervalIntegral_fin_partition P.node (fun t => f (γ t) * deriv γ t)
    (P.piece_integrable_deriv f hf)
  rw [← P.first, ← P.last]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h.2
  apply intervalIntegral.integral_congr_Ioo_of_le (P.piece_lt i).le
  intro t ht
  simp only [pieceSet, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

theorem parameter_integrable :
    Specs.D12Complex.Ch03.PathOperations.parameter_integrable_type := by
  intro γ P f hf
  have h := (intervalIntegral_fin_partition P.node (fun t => f (γ t) * deriv γ t)
    (P.piece_integrable_deriv f hf)).1
  simpa only [P.first, P.last] using h

theorem integral_independent :
    Specs.D12Complex.Ch03.PathOperations.partition_independent_type := by
  intro γ P Q f hf
  rw [integral_eq_intervalIntegral γ P f hf, integral_eq_intervalIntegral γ Q f hf]

/-- Project a parameter integral after verifying the scalar integrand on the
interiors of the smooth pieces. This avoids choosing derivatives at corners. -/
theorem integral_coordinate {γ : ComplexPath} (P : C1Partition γ)
    (f : ℂ → ℂ) (hf : ContinuousOn f γ.trace) (L : ℂ →L[ℝ] ℝ) (g : ℝ → ℝ)
    (hg : ∀ i : Fin P.count, ∀ t ∈ Ioo (P.node i.castSucc) (P.node i.succ),
      g t = L (f (γ t) * deriv γ t)) :
    (∫ t in γ.a..γ.b, g t) = L (P.integral f) := by
  have hint (i : Fin P.count) : IntervalIntegrable g volume
      (P.node i.castSucc) (P.node i.succ) := by
    have hi := P.piece_integrable_deriv f hf i
    have hL : IntervalIntegrable (fun t => L (f (γ t) * deriv γ t)) volume
        (P.node i.castSucc) (P.node i.succ) :=
      ⟨L.integrable_comp hi.1, L.integrable_comp hi.2⟩
    apply hL.congr_uIoo
    rw [uIoo_of_le (P.piece_lt i).le]
    intro t ht
    exact (hg i t ht).symm
  have heq (i : Fin P.count) :
      (∫ t in P.node i.castSucc..P.node i.succ, g t) =
        L (∫ t in P.node i.castSucc..P.node i.succ, f (γ t) * deriv γ t) := by
    rw [← L.intervalIntegral_comp_comm (P.piece_integrable_deriv f hf i)]
    exact intervalIntegral.integral_congr_Ioo_of_le (P.piece_lt i).le (hg i)
  have hs := (intervalIntegral_fin_partition P.node g hint).2
  rw [P.first, P.last] at hs
  rw [← hs, integral_eq_intervalIntegral γ P f hf]
  simp_rw [heq]
  rw [← map_sum]
  congr 1
  exact (intervalIntegral_fin_partition P.node (fun t => f (γ t) * deriv γ t)
    (P.piece_integrable_deriv f hf)).2.trans (by rw [P.first, P.last])

/-- Ordinary derivatives exist in each open piece, with no assertion at corners. -/
theorem differentiableAt_piece {γ : ComplexPath} (P : C1Partition γ)
    (i : Fin P.count) {t : ℝ} (ht : t ∈ Ioo (P.node i.castSucc) (P.node i.succ)) :
    DifferentiableAt ℝ γ t :=
  ((P.smooth i).differentiableOn one_ne_zero t ⟨ht.1.le, ht.2.le⟩).differentiableAt
    (Icc_mem_nhds ht.1 ht.2)

end C1Partition
namespace PiecewiseC1Path

/-- Restrict a finite C1 partition by clamping its nodes, then remove repetitions. -/
theorem exists_restriction (γ : PiecewiseC1Path) (c d : ℝ)
    (hac : γ.path.a ≤ c) (hcd : c ≤ d) (hdb : d ≤ γ.path.b) :
    ∃ η : PiecewiseC1Path, η.path.a = c ∧ η.path.b = d ∧
      EqOn η γ (Icc c d) := by
  let δ : ComplexPath := ⟨c, d, hcd, γ, γ.path.continuousOn.mono (Icc_subset_Icc hac hdb)⟩
  let P := γ.partition
  let v : Fin (P.count + 1) → ℝ := fun i => max c (min d (P.node i))
  have hpc : IsPiecewiseC1 δ := by
    apply isPiecewiseC1_of_monotone_partition δ P.count v
    · intro i j hij
      exact max_le_max_left c (min_le_min_left d (P.strictMono.monotone hij))
    · simp [δ, v, P.first, min_eq_right (hac.trans hcd), max_eq_left hac]
    · simp [δ, v, P.last, min_eq_left hdb, max_eq_right hcd]
    · intro i
      by_cases hx : d < P.node i.castSucc
      · have hy : d ≤ P.node i.succ := (hx.trans (P.piece_lt i)).le
        simpa [v, min_eq_left hx.le, min_eq_left hy, max_eq_right hcd] using
          contDiffOn_Icc_self (γ : ℝ → ℂ) d
      · by_cases hy : P.node i.succ < c
        · have hx' : P.node i.castSucc ≤ c := ((P.piece_lt i).trans hy).le
          have hy' : P.node i.succ ≤ d := hy.le.trans hcd
          simpa [v, min_eq_right (hx'.trans hcd), min_eq_right hy',
            max_eq_left hx', max_eq_left hy.le] using
              contDiffOn_Icc_self (γ : ℝ → ℂ) c
        · apply (P.smooth i).mono
          apply Icc_subset_Icc
          · exact le_max_of_le_right (by rw [min_eq_right (le_of_not_gt hx)])
          · exact max_le (le_of_not_gt hy) (min_le_right _ _)
  exact ⟨⟨δ, hpc⟩, rfl, rfl, fun _ _ => rfl⟩

/-- The reversed traversal has a finite C1 partition on the same interval. -/
theorem exists_reversal (γ : PiecewiseC1Path) :
    ∃ η : PiecewiseC1Path, η.path.a = γ.path.a ∧ η.path.b = γ.path.b ∧
      EqOn η (fun t => γ (γ.path.a + γ.path.b - t)) (Icc γ.path.a γ.path.b) := by
  let r : ℝ → ℝ := fun t => γ.path.a + γ.path.b - t
  have hr : MapsTo r (Icc γ.path.a γ.path.b) (Icc γ.path.a γ.path.b) := by
    intro t ht
    constructor <;> dsimp [r] <;> linarith [ht.1, ht.2]
  have hrc : ContDiff ℝ 1 r := by exact contDiff_const.sub contDiff_id
  let δ : ComplexPath := ⟨γ.path.a, γ.path.b, γ.path.ordered, γ ∘ r,
    γ.path.continuousOn.comp hrc.continuous.continuousOn hr⟩
  let P := γ.partition
  let v : Fin (P.count + 1) → ℝ := fun i => r (P.node i.rev)
  have hpc : IsPiecewiseC1 δ := by
    apply isPiecewiseC1_of_monotone_partition δ P.count v
    · intro i j hij
      have h := P.strictMono.monotone (Fin.rev_le_rev.mpr hij)
      dsimp [v, r]
      linarith
    · simp [δ, v, r, P.last]
    · simp [δ, v, r, P.first]
    · intro i
      apply (P.smooth i.rev).comp hrc.contDiffOn
      intro t ht
      simp only [v, Fin.rev_castSucc, Fin.rev_succ, mem_Icc] at ht
      constructor <;> dsimp [r] at * <;> linarith [ht.1, ht.2]
  exact ⟨⟨δ, hpc⟩, rfl, rfl, fun _ _ => rfl⟩

/-- An affine traversal on any interval is piecewise C1, including zero speed. -/
private theorem affine_piecewise (γ : PiecewiseC1Path) (p q c d : ℝ)
    (hcd : c ≤ d) (hq : 0 ≤ q) (ha : p + q * c = γ.path.a)
    (hb : p + q * d = γ.path.b) :
    ∃ η : PiecewiseC1Path, η.path.a = c ∧ η.path.b = d ∧
      EqOn η (fun t => γ (p + q * t)) (Icc c d) := by
  by_cases hq0 : q = 0
  · subst q
    exact ⟨const c d hcd (γ p), rfl, rfl, by intro t _; change γ p = γ (p + 0 * t); simp⟩
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  let r : ℝ → ℝ := fun t => p + q * t
  have hrc : ContDiff ℝ 1 r := by exact contDiff_const.add (contDiff_const.mul contDiff_id)
  have hr : MapsTo r (Icc c d) (Icc γ.path.a γ.path.b) := by
    intro t ht
    constructor
    · rw [← ha]; dsimp [r]; nlinarith [ht.1]
    · rw [← hb]; dsimp [r]; nlinarith [ht.2]
  let δ : ComplexPath := ⟨c, d, hcd, γ ∘ r,
    γ.path.continuousOn.comp hrc.continuous.continuousOn hr⟩
  let P := γ.partition
  let v : Fin (P.count + 1) → ℝ := fun i => (P.node i - p) / q
  have hpc : IsPiecewiseC1 δ := by
    apply isPiecewiseC1_of_monotone_partition δ P.count v
    · intro i j hij
      exact div_le_div_of_nonneg_right (sub_le_sub_right (P.strictMono.monotone hij) p) hq
    · dsimp [v, δ]; rw [P.first, ← ha]; field_simp; ring
    · dsimp [v, δ]; rw [P.last, ← hb]; field_simp; ring
    · intro i
      apply (P.smooth i).comp hrc.contDiffOn
      intro t ht
      change (P.node i.castSucc - p) / q ≤ t ∧ t ≤ (P.node i.succ - p) / q at ht
      have hl := (div_le_iff₀ hqpos).mp ht.1
      have hu := (le_div_iff₀ hqpos).mp ht.2
      constructor <;> dsimp [r] <;> linarith
  exact ⟨⟨δ, hpc⟩, rfl, rfl, fun _ _ => rfl⟩

/-- Glue two paths whose parameter intervals touch, keeping their actual traversals. -/
private theorem glue_piecewise (γ₁ γ₂ : PiecewiseC1Path)
    (hjoin : γ₁.path.b = γ₂.path.a) (hvalue : γ₁.path.target = γ₂.path.source) :
    ∃ η : PiecewiseC1Path, η.path.a = γ₁.path.a ∧ η.path.b = γ₂.path.b ∧
      EqOn η γ₁ (Icc γ₁.path.a γ₁.path.b) ∧
      EqOn η γ₂ (Icc γ₂.path.a γ₂.path.b) := by
  classical
  let F : ℝ → ℂ := fun t => if t ≤ γ₁.path.b then γ₁ t else γ₂ t
  have hF₁ : EqOn F γ₁ (Icc γ₁.path.a γ₁.path.b) := by
    intro t ht; simp [F, ht.2]
  have hF₂ : EqOn F γ₂ (Icc γ₂.path.a γ₂.path.b) := by
    intro t ht
    dsimp [F]
    split_ifs with h
    · have heq : t = γ₁.path.b := le_antisymm h (hjoin.trans_le ht.1)
      subst t
      simpa only [ComplexPath.target, ComplexPath.source, ← hjoin] using hvalue
    · rfl
  have hc₁ : ContinuousOn F (Icc γ₁.path.a γ₁.path.b) :=
    γ₁.path.continuousOn.congr hF₁
  have hc₂ : ContinuousOn F (Icc γ₂.path.a γ₂.path.b) :=
    γ₂.path.continuousOn.congr hF₂
  have hc : ContinuousOn F (Icc γ₁.path.a γ₂.path.b) := by
    have h := hc₁.union_of_isClosed hc₂ isClosed_Icc isClosed_Icc
    rwa [← hjoin, Icc_union_Icc_eq_Icc γ₁.path.ordered
      (by simpa only [hjoin] using γ₂.path.ordered)] at h
  let δ : ComplexPath := ⟨γ₁.path.a, γ₂.path.b,
    γ₁.path.ordered.trans (hjoin.trans_le γ₂.path.ordered), F, hc⟩
  let P := γ₁.partition
  let Q := γ₂.partition
  obtain ⟨k, v, hv, h0, hl, hs⟩ := append_partitions F P.count P.node P.strictMono.monotone
    (fun i => (P.smooth i).congr (fun t ht => hF₁ (P.piece_subset i ht)))
    Q.count Q.node Q.strictMono.monotone (by rw [P.last, Q.first, hjoin])
    (fun i => (Q.smooth i).congr (fun t ht => hF₂ (Q.piece_subset i ht)))
  have hpc : IsPiecewiseC1 δ :=
    isPiecewiseC1_of_monotone_partition δ k v hv (h0.trans P.first) (hl.trans Q.last) hs
  exact ⟨⟨δ, hpc⟩, rfl, rfl, hF₁, hF₂⟩

/-- Compatible paths always have a piecewise C1 concatenation on [0,2].
The two traversals occupy [0,1] and [1,2], even for constant or degenerate inputs. -/
theorem exists_concatenation (γ₁ γ₂ : PiecewiseC1Path)
    (hcompat : γ₁.path.target = γ₂.path.source) :
    ∃ η : PiecewiseC1Path, η.path.a = 0 ∧ η.path.b = 2 ∧
      EqOn η (fun t => γ₁ (γ₁.path.a + (γ₁.path.b - γ₁.path.a) * t)) (Icc 0 1) ∧
      EqOn η (fun t => γ₂ (γ₂.path.a + (γ₂.path.b - γ₂.path.a) * (t - 1))) (Icc 1 2) := by
  obtain ⟨δ₁, ha₁, hb₁, hδ₁⟩ := affine_piecewise γ₁ γ₁.path.a
    (γ₁.path.b - γ₁.path.a) 0 1 (by norm_num) (sub_nonneg.mpr γ₁.path.ordered)
    (by ring) (by ring)
  obtain ⟨δ₂, ha₂, hb₂, hδ₂⟩ := affine_piecewise γ₂
    (γ₂.path.a - (γ₂.path.b - γ₂.path.a)) (γ₂.path.b - γ₂.path.a) 1 2
    (by norm_num) (sub_nonneg.mpr γ₂.path.ordered) (by ring) (by ring)
  have hjoin : δ₁.path.b = δ₂.path.a := hb₁.trans ha₂.symm
  have hval : δ₁.path.target = δ₂.path.source := by
    change δ₁ δ₁.path.b = δ₂ δ₂.path.a
    rw [hb₁, ha₂, hδ₁ (by norm_num), hδ₂ (by norm_num)]
    change γ₁ γ₁.path.b = γ₂ γ₂.path.a at hcompat
    simpa only [mul_one, add_sub_cancel, sub_add_cancel] using hcompat
  obtain ⟨η, ha, hb, hη₁, hη₂⟩ := glue_piecewise δ₁ δ₂ hjoin hval
  refine ⟨η, ha.trans ha₁, hb.trans hb₂, ?_, ?_⟩
  · intro t ht
    exact (hη₁ (by simpa only [ha₁, hb₁] using ht)).trans (hδ₁ ht)
  · intro t ht
    rw [hη₂ (by simpa only [ha₂, hb₂] using ht), hδ₂ ht]
    exact congrArg (γ₂ : ℝ → ℂ) (by ring)

theorem integral_eq_partition :
    Specs.D12Complex.Ch03.PathOperations.contour_integral_eq_partition_type := by
  intro γ P f hf
  exact C1Partition.integral_independent γ.path γ.partition P f hf


theorem integral_coordinates :
    Specs.D12Complex.Ch03.PathOperations.contour_integral_coordinates_type := by
  intro γ f hf
  have hx (i : Fin γ.partition.count) (t : ℝ)
      (ht : t ∈ Ioo (γ.partition.node i.castSucc) (γ.partition.node i.succ)) :
      deriv (fun s => (γ s).re) t = (deriv γ t).re := by
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      (γ.partition.differentiableAt_piece i ht).hasDerivAt).deriv
  have hy (i : Fin γ.partition.count) (t : ℝ)
      (ht : t ∈ Ioo (γ.partition.node i.castSucc) (γ.partition.node i.succ)) :
      deriv (fun s => (γ s).im) t = (deriv γ t).im := by
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      (γ.partition.differentiableAt_piece i ht).hasDerivAt).deriv
  have hr := γ.partition.integral_coordinate f hf Complex.reCLM
    (fun t => (f (γ t)).re * deriv (fun s => (γ s).re) t -
      (f (γ t)).im * deriv (fun s => (γ s).im) t)
    (fun i t ht => by rw [hx i t ht, hy i t ht]; rfl)
  have hi := γ.partition.integral_coordinate f hf Complex.imCLM
    (fun t => (f (γ t)).im * deriv (fun s => (γ s).re) t +
      (f (γ t)).re * deriv (fun s => (γ s).im) t)
    (fun i t ht => by rw [hx i t ht, hy i t ht]; simp [Complex.mul_im, add_comm])
  change γ.integral f = _
  rw [hr, hi]
  simpa only [integral, Complex.reCLM_apply, Complex.imCLM_apply, mul_comm] using
    (Complex.re_add_im (γ.partition.integral f)).symm


theorem integral_congr_representative :
    Specs.D12Complex.Ch03.PathOperations.contour_integral_congr_representative_type := by
  intro γ g f hf hEq
  rw [integral, C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hf]
  apply intervalIntegral.integral_congr_Ioo_of_le γ.path.ordered
  intro t ht
  change f (γ t) * deriv γ t = f (g t) * deriv g t
  rw [hEq ⟨ht.1.le, ht.2.le⟩,
    (hEq.mono Ioo_subset_Icc_self).deriv isOpen_Ioo ht]

/-- Continuity on a larger trace restricts to any interval representative. -/
theorem continuousOn_trace_of_restriction (γ δ : PiecewiseC1Path) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace)
    (ha : γ.path.a ≤ δ.path.a) (hb : δ.path.b ≤ γ.path.b)
    (hEq : EqOn δ γ (Icc δ.path.a δ.path.b)) : ContinuousOn f δ.trace := by
  apply hf.mono
  rintro z ⟨t, ht, rfl⟩
  exact ⟨t, ⟨ha.trans ht.1, ht.2.trans hb⟩, (hEq ht).symm⟩

theorem integral_subdivision :
    Specs.D12Complex.Ch03.PathOperations.contour_integral_subdivision_type := by
  intro γ γ₁ γ₂ c f hc ha₁ hb₁ ha₂ hb₂ h₁ h₂ hf
  have hf₁ := continuousOn_trace_of_restriction γ γ₁ f hf
    (by rw [ha₁]) (by rw [hb₁]; exact hc.2) h₁
  have hf₂ := continuousOn_trace_of_restriction γ γ₂ f hf
    (by rw [ha₂]; exact hc.1) (by rw [hb₂]) h₂
  rw [integral_congr_representative γ₁ γ f hf₁ h₁,
    integral_congr_representative γ₂ γ f hf₂ h₂, ha₁, hb₁, ha₂, hb₂,
    integral, C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hf]
  symm
  have hint := C1Partition.parameter_integrable γ.path γ.partition f hf
  apply intervalIntegral.integral_add_adjacent_intervals
  · apply hint.mono_set
    rw [uIcc_of_le hc.1, uIcc_of_le γ.path.ordered]
    exact Icc_subset_Icc le_rfl hc.2
  · apply hint.mono_set
    rw [uIcc_of_le hc.2, uIcc_of_le γ.path.ordered]
    exact Icc_subset_Icc hc.1 le_rfl


theorem integral_reversal :
    Specs.D12Complex.Ch03.PathOperations.contour_integral_reversal_type := by
  intro γ η f ha hb hEq hf
  have hfη : ContinuousOn f η.trace := by
    apply hf.mono
    rintro z ⟨t, ht, rfl⟩
    refine ⟨γ.path.a + γ.path.b - t, ?_, (hEq ht).symm⟩
    rw [ha, hb] at ht
    constructor <;> linarith [ht.1, ht.2]
  rw [integral_congr_representative η _ f hfη hEq]
  simp_rw [deriv_comp_const_sub, mul_neg]
  rw [intervalIntegral.integral_neg, ha, hb,
    intervalIntegral.integral_comp_sub_left (fun t => f (γ t) * deriv γ t) (γ.path.a + γ.path.b)]
  have he₁ : γ.path.a + γ.path.b - γ.path.b = γ.path.a := by ring
  have he₂ : γ.path.a + γ.path.b - γ.path.a = γ.path.b := by ring
  rw [he₁, he₂, integral, C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hf]

/-- Affine substitution on just one interval, including a zero slope. -/
theorem integral_affine_piece (g : ℝ → ℂ) (γ : PiecewiseC1Path)
    (p q c d : ℝ) (hcd : c ≤ d) (f : ℂ → ℂ)
    (ha : p + q * c = γ.path.a) (hb : p + q * d = γ.path.b)
    (hEq : EqOn g (fun t => γ (p + q * t)) (Icc c d))
    (hf : ContinuousOn f γ.trace) :
    (∫ t in c..d, f (g t) * deriv g t) = γ.integral f := by
  have heq : (∫ t in c..d, f (g t) * deriv g t) =
      ∫ t in c..d, f (γ (p + q * t)) * deriv (fun s => γ (p + q * s)) t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hcd
    intro t ht
    change f (g t) * deriv g t = _
    rw [hEq ⟨ht.1.le, ht.2.le⟩,
      (hEq.mono Ioo_subset_Icc_self).deriv isOpen_Ioo ht]
  rw [heq]
  have hd (t : ℝ) : deriv (fun s => γ (p + q * s)) t =
      q • deriv γ (p + q * t) := by
    simpa only [deriv_comp_const_add] using
      (deriv_comp_mul_left q (fun x => γ (p + x)) t)
  simp_rw [hd, mul_smul_comm]
  rw [intervalIntegral.integral_smul,
    intervalIntegral.smul_integral_comp_add_mul (fun t => f (γ t) * deriv γ t) q p,
    ha, hb, integral, C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hf]

theorem integral_affine_parameter :
    Specs.D12Complex.Ch03.PathOperations.contour_integral_affine_parameter_type := by
  intro γ η p q f hq ha hb hEq hf
  have hfη : ContinuousOn f η.trace := by
    apply hf.mono
    rintro z ⟨t, ht, rfl⟩
    refine ⟨p + q * t, ⟨?_, ?_⟩, (hEq ht).symm⟩
    · rw [← ha]; linarith [mul_le_mul_of_nonneg_left ht.1 hq.le]
    · rw [← hb]; linarith [mul_le_mul_of_nonneg_left ht.2 hq.le]
  rw [integral, C1Partition.integral_eq_intervalIntegral η.path η.partition f hfη]
  exact integral_affine_piece η γ p q η.path.a η.path.b η.path.ordered f ha hb hEq hf


theorem integral_concatenation :
    Specs.D12Complex.Ch03.PathOperations.contour_integral_concatenation_type := by
  intro γ₁ γ₂ η c p₁ q₁ p₂ q₂ f hc hq₁ hq₂ _hcompat ha₁ hb₁ ha₂ hb₂ h₁ h₂ hf₁ hf₂
  have hfη : ContinuousOn f η.trace := by
    apply (hf₁.union_of_isClosed hf₂ γ₁.path.trace_compact.isClosed
      γ₂.path.trace_compact.isClosed).mono
    rintro z ⟨t, ht, rfl⟩
    rcases le_total t c with htc | hct
    · left
      refine ⟨p₁ + q₁ * t, ⟨?_, ?_⟩, (h₁ ⟨ht.1, htc⟩).symm⟩
      · rw [← ha₁]; linarith [mul_le_mul_of_nonneg_left ht.1 hq₁]
      · rw [← hb₁]; linarith [mul_le_mul_of_nonneg_left htc hq₁]
    · right
      refine ⟨p₂ + q₂ * t, ⟨?_, ?_⟩, (h₂ ⟨hct, ht.2⟩).symm⟩
      · rw [← ha₂]; linarith [mul_le_mul_of_nonneg_left hct hq₂]
      · rw [← hb₂]; linarith [mul_le_mul_of_nonneg_left ht.2 hq₂]
  rw [integral, C1Partition.integral_eq_intervalIntegral η.path η.partition f hfη]
  have hint := C1Partition.parameter_integrable η.path η.partition f hfη
  have hint₁ : IntervalIntegrable (fun t => f (η t) * deriv η t) volume η.path.a c := by
    apply hint.mono_set
    rw [uIcc_of_le hc.1, uIcc_of_le η.path.ordered]
    exact Icc_subset_Icc le_rfl hc.2
  have hint₂ : IntervalIntegrable (fun t => f (η t) * deriv η t) volume c η.path.b := by
    apply hint.mono_set
    rw [uIcc_of_le hc.2, uIcc_of_le η.path.ordered]
    exact Icc_subset_Icc hc.1 le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂,
    integral_affine_piece η γ₁ p₁ q₁ η.path.a c hc.1 f ha₁ hb₁ h₁ hf₁,
    integral_affine_piece η γ₂ p₂ q₂ c η.path.b hc.2 f ha₂ hb₂ h₂ hf₂]

/-- Change of parameter permits flat pieces, including fibers over corners. -/
theorem integral_monotone_parameter :
    Specs.D12Complex.Ch03.PathOperations.contour_integral_monotone_parameter_type := by
  intro γ η φ f hc hm hmaps hsurj hpieces hη hf
  obtain ⟨n, node, hs, hfirst, hlast, hC1⟩ := hpieces
  have ha : φ η.path.a = γ.path.a := by
    obtain ⟨t, ht, heq⟩ := hsurj (left_mem_Icc.mpr γ.path.ordered)
    exact le_antisymm ((hm (left_mem_Icc.mpr η.path.ordered) ht ht.1).trans_eq heq)
      (hmaps (left_mem_Icc.mpr η.path.ordered)).1
  have hb : φ η.path.b = γ.path.b := by
    obtain ⟨t, ht, heq⟩ := hsurj (right_mem_Icc.mpr γ.path.ordered)
    exact le_antisymm (hmaps (right_mem_Icc.mpr η.path.ordered)).2
      (heq.symm.trans_le (hm ht (right_mem_Icc.mpr η.path.ordered) ht.2))
  have hfη : ContinuousOn f η.trace := by
    apply hf.mono
    rintro z ⟨t, ht, rfl⟩
    exact ⟨φ t, hmaps ht, (hη ht).symm⟩
  have hint := C1Partition.parameter_integrable γ.path γ.partition f hf
  have hsub := Ch03.PC1MonotoneSubstitution.weighted_substitution φ η.path.a η.path.b
    n node η.path.ordered hc hm hs hfirst hlast hC1
    (fun t => f (γ t) * deriv γ t) (by simpa only [ha, hb] using hint)
  have hchain := ae_deriv_monotone_comp γ η φ hc hm hmaps hsurj
    n node hs hfirst hlast hC1 (fun t ht => hη ht)
  rw [integral, C1Partition.integral_eq_intervalIntegral η.path η.partition f hfη,
    integral, C1Partition.integral_eq_intervalIntegral γ.path γ.partition f hf]
  calc
    _ = ∫ t in η.path.a..η.path.b, deriv φ t • (f (γ (φ t)) * deriv γ (φ t)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_imp_of_ae_restrict hchain] with t ht hmem
      rw [uIoc_of_le η.path.ordered] at hmem
      have htI : t ∈ Icc η.path.a η.path.b := ⟨hmem.1.le, hmem.2⟩
      rw [hη htI, ht htI, mul_smul_comm]
    _ = _ := by simpa only [ha, hb] using hsub.2

/-- Subdivision for arbitrary input paths; the restrictions are constructed here. -/
theorem subdivision :
    Specs.D12Complex.Ch03.PathOperations.contour_subdivision_exists_type := by
  intro γ c f hc hf
  obtain ⟨γ₁, ha₁, hb₁, h₁⟩ := exists_restriction γ γ.path.a c le_rfl hc.1 hc.2
  obtain ⟨γ₂, ha₂, hb₂, h₂⟩ := exists_restriction γ c γ.path.b hc.1 hc.2 le_rfl
  refine ⟨γ₁, γ₂, ha₁, hb₁, ha₂, hb₂, h₁, h₂, ?_⟩
  exact integral_subdivision γ γ₁ γ₂ c f hc ha₁ hb₁ ha₂ hb₂
    (by simpa only [ha₁, hb₁] using h₁) (by simpa only [ha₂, hb₂] using h₂) hf

/-- Reversal for arbitrary input paths. -/
theorem reversal :
    Specs.D12Complex.Ch03.PathOperations.contour_reversal_exists_type := by
  intro γ f hf
  obtain ⟨η, ha, hb, hη⟩ := exists_reversal γ
  exact ⟨η, ha, hb, hη, integral_reversal γ η f ha hb
    (by simpa only [ha, hb] using hη) hf⟩

/-- Concatenation for arbitrary compatible input paths. -/
theorem concatenation :
    Specs.D12Complex.Ch03.PathOperations.contour_concatenation_exists_type := by
  intro γ₁ γ₂ f hcompat hf₁ hf₂
  obtain ⟨η, ha, hb, h₁, h₂⟩ := exists_concatenation γ₁ γ₂ hcompat
  refine ⟨η, ha, hb, h₁, h₂, ?_⟩
  apply integral_concatenation γ₁ γ₂ η 1 γ₁.path.a (γ₁.path.b - γ₁.path.a)
    (γ₂.path.a - (γ₂.path.b - γ₂.path.a)) (γ₂.path.b - γ₂.path.a) f
  · simp only [ha, hb, mem_Icc]; norm_num
  · exact sub_nonneg.mpr γ₁.path.ordered
  · exact sub_nonneg.mpr γ₂.path.ordered
  · exact hcompat
  · rw [ha]; ring
  · ring
  · ring
  · rw [hb]; ring
  · simpa only [ha] using h₁
  · intro t ht
    rw [hb] at ht
    rw [h₂ ht]
    exact congrArg (γ₂ : ℝ → ℂ) (by ring)
  · exact hf₁
  · exact hf₂

end PiecewiseC1Path
end D12Complex
