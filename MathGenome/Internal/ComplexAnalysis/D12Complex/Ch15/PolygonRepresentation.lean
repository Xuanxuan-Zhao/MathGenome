import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.PolygonRepresentation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.FiniteCycleCauchy
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.IndexComputations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.MetricSpace.Thickening
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.TrianglePrimitiveCriterion
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Topology.Algebra.Module.Cardinality

noncomputable section
open Set Metric Filter

namespace D12Complex.PolygonRepresentation

theorem zero_isPolygonalCycle : IsPolygonalCycle (0 : IntegralCycle) := by
  intro γ hγ
  simp only [IntegralCycle.zero_chain, Finsupp.support_zero,
    Finset.notMem_empty] at hγ

/-- Pair the incoming and outgoing edges at each vertex. This gives a
permutation of the finite edge set whose orbits are directed closed walks.
No connectivity assumption, plane separation, or choice of Jordan interior
is required. The orbits are realized below as actual polygonal paths. -/
theorem exists_edge_successor (E : Finset (ℂ × ℂ))
    (hbalance : ∀ v : ℂ, (E.filter (fun e => e.1 = v)).card =
      (E.filter (fun e => e.2 = v)).card) :
    ∃ σ : Equiv.Perm E, ∀ e : E, (σ e).val.1 = e.val.2 := by
  classical
  have hcard (p : ℂ × ℂ → Prop) [DecidablePred p] :
      Fintype.card {e : E // p e.val} = (E.filter p).card := by
    let ep : {e : E // p e.val} ≃ {e // e ∈ E.filter p} := {
      toFun := fun e => ⟨e.val.val, Finset.mem_filter.mpr ⟨e.val.property, e.property⟩⟩
      invFun := fun e => ⟨⟨e.val, (Finset.mem_filter.mp e.property).1⟩,
        (Finset.mem_filter.mp e.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Fintype.card_congr ep).trans (Fintype.card_coe _)
  let ef (v : ℂ) : {e : E // e.val.2 = v} ≃ {e : E // e.val.1 = v} :=
    Fintype.equivOfCardEq (by
      rw [hcard (fun e => e.2 = v), hcard (fun e => e.1 = v)]
      exact (hbalance v).symm)
  exact ⟨Equiv.ofFiberEquiv ef, Equiv.ofFiberEquiv_map ef⟩

/-- Remove both orientations of every paired edge before constructing paths.
The remaining directed edge set is still balanced at every vertex. -/
theorem balanced_edges_cancel_reverse {α : Type*} [DecidableEq α]
    (E : Finset (α × α))
    (hbalance : ∀ v, (E.filter (fun e => e.1 = v)).card =
      (E.filter (fun e => e.2 = v)).card) :
    ∀ v, ((E.filter (fun e => e.swap ∉ E)).filter (fun e => e.1 = v)).card =
      ((E.filter (fun e => e.swap ∉ E)).filter (fun e => e.2 = v)).card := by
  intro v
  have hpairs : ((E.filter (fun e => e.1 = v)).filter (fun e => e.swap ∈ E)).card =
      ((E.filter (fun e => e.2 = v)).filter (fun e => e.swap ∈ E)).card := by
    apply Finset.card_bij (fun e _ => e.swap)
    · intro e he
      simp only [Finset.mem_filter] at he
      simpa only [Finset.mem_filter, Prod.fst_swap, Prod.snd_swap, Prod.swap_swap]
        using And.intro (And.intro he.2 he.1.2) he.1.1
    · intro e _ e' _ he
      exact Prod.swap_injective he
    · intro e he
      simp only [Finset.mem_filter] at he
      refine ⟨e.swap, ?_, Prod.swap_swap e⟩
      simpa only [Finset.mem_filter, Prod.fst_swap, Prod.snd_swap, Prod.swap_swap]
        using And.intro (And.intro he.2 he.1.2) he.1.1
  have htail := (Finset.card_filter_add_card_filter_not
    (s := E.filter (fun e => e.1 = v)) (fun e => e.swap ∈ E))
  have hhead := (Finset.card_filter_add_card_filter_not
    (s := E.filter (fun e => e.2 = v)) (fun e => e.swap ∈ E))
  rw [Finset.filter_comm (fun e : α × α => e.swap ∉ E) (fun e => e.1 = v),
    Finset.filter_comm (fun e : α × α => e.swap ∉ E) (fun e => e.2 = v)]
  have hb := hbalance v
  omega

/-- An antisymmetric edge sum is unchanged by deleting pairs of oppositely
directed edges. This cancellation is on edges, before any path is formed. -/
theorem edge_sum_cancel_reverse {α : Type*} [DecidableEq α]
    (E : Finset (α × α)) (g : α × α → ℂ)
    (hrev : ∀ e ∈ E, e.swap ∈ E → g e.swap = -g e) :
    (∑ e ∈ E.filter (fun e => e.swap ∉ E), g e) = ∑ e ∈ E, g e := by
  have hzero : (∑ e ∈ E.filter (fun e => e.swap ∈ E), g e) = 0 := by
    refine Finset.sum_involution (fun e _ => e.swap) ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter] at he
      rw [hrev e he.1 he.2, add_neg_cancel]
    · intro e he hne heq
      simp only [Finset.mem_filter] at he
      have h := hrev e he.1 he.2
      rw [heq] at h
      exact hne (by linear_combination (1 / 2 : ℂ) * (eq_neg_iff_add_eq_zero.mp h))
    · intro e he
      simp only [Finset.mem_filter] at he
      exact Finset.mem_filter.mpr ⟨he.2, by simpa using he.1⟩
    · intro e _
      exact Prod.swap_swap e
  have h := Finset.sum_filter_add_sum_filter_not E (fun e => e.swap ∈ E) g
  simpa only [hzero, zero_add] using h

/- A finite vertex list is realized on consecutive unit intervals. Keeping the
   parametrization explicit is essential: the cycle trace does not quotient
   out edges that cancel only at the level of integrals. -/
private def polygonMap (v : ℕ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => v 0
  | n + 1 => fun t => if t ≤ (n : ℝ) then polygonMap v n t else
      AffineMap.lineMap (v n) (v (n + 1)) (t - n)

private theorem polygonMap_zero (v : ℕ → ℂ) (n : ℕ) :
    polygonMap v n 0 = v 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [polygonMap, ite_eq_left (Nat.cast_nonneg n)] using ih

private theorem polygonMap_last (v : ℕ → ℂ) (n : ℕ) :
    polygonMap v n n = v n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [polygonMap, Nat.cast_add, Nat.cast_one]
    rw [ite_eq_right (by linarith : ¬ (n : ℝ) + 1 ≤ n)]
    simp

private theorem polygonMap_piece (v : ℕ → ℂ) (n i : ℕ) (hi : i < n) :
    EqOn (polygonMap v n)
      (fun t => AffineMap.lineMap (v i) (v (i + 1)) (t - i))
      (Icc (i : ℝ) ((i : ℝ) + 1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro t ht
    by_cases hin : i < n
    · have hle : t ≤ (n : ℝ) := by
        have hic : (i : ℝ) + 1 ≤ n := by exact_mod_cast hin
        exact ht.2.trans hic
      simp only [polygonMap, ite_eq_left hle]
      exact ih hin ht
    · have hie : i = n := by omega
      subst i
      simp only [polygonMap]
      split_ifs with hle
      · have heq : t = (n : ℝ) := le_antisymm hle ht.1
        subst t
        simp [polygonMap_last]
      · rfl

private theorem polygonMap_continuous (v : ℕ → ℂ) (n : ℕ) :
    ContinuousOn (polygonMap v n) (Icc 0 (n : ℝ)) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih =>
    have hleft : ContinuousOn (polygonMap v (n + 1)) (Icc 0 (n : ℝ)) :=
      ih.congr (fun t ht => by simp only [polygonMap, ite_eq_left ht.2])
    have hright : ContinuousOn (polygonMap v (n + 1)) (Icc (n : ℝ) ((n : ℝ) + 1)) :=
      (AffineMap.lineMap_continuous.comp (continuous_id.sub continuous_const)).continuousOn.congr
        (polygonMap_piece v (n + 1) n (by omega))
    have hc := hleft.union_of_isClosed hright isClosed_Icc isClosed_Icc
    simpa only [Icc_union_Icc_eq_Icc (Nat.cast_nonneg n) (by linarith :
      (n : ℝ) ≤ n + 1), Nat.cast_add, Nat.cast_one] using hc

private def polygonPath (v : ℕ → ℂ) (n : ℕ) : ComplexPath :=
  ⟨0, n, Nat.cast_nonneg n, polygonMap v n, polygonMap_continuous v n⟩

private def polygonPartition (v : ℕ → ℂ) (n : ℕ) : C1Partition (polygonPath v n) where
  count := n
  node := fun i => (i.val : ℝ)
  strictMono := by
    intro i j hij
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  first := by simp [polygonPath]
  last := by simp [polygonPath]
  smooth := by
    intro i
    have hdiff : ContDiff ℝ 1
        (fun t : ℝ => AffineMap.lineMap (v i) (v (i + 1)) (t - i)) := by
      simp only [AffineMap.lineMap_apply_module']
      exact ((contDiff_id.sub contDiff_const).smul contDiff_const).add contDiff_const
    apply hdiff.contDiffOn.congr
    intro t ht
    exact polygonMap_piece v n i i.isLt (by simpa using ht)

private def polygonPiecewisePath (v : ℕ → ℂ) (n : ℕ) : PiecewiseC1Path :=
  ⟨polygonPath v n, ⟨polygonPartition v n⟩⟩

private theorem polygonMap_node (v : ℕ → ℂ) (n i : ℕ) (hi : i ≤ n) :
    polygonMap v n i = v i := by
  by_cases hlt : i < n
  · simpa using polygonMap_piece v n i hlt (left_mem_Icc.mpr (by linarith :
      (i : ℝ) ≤ i + 1))
  · have heq : i = n := by omega
    subst i
    exact polygonMap_last v n

private theorem polygonPiecewisePath_polygonal (v : ℕ → ℂ) (n : ℕ) :
    IsPolygonalPath (polygonPiecewisePath v n) := by
  refine ⟨polygonPartition v n, ?_⟩
  intro i
  change Fin n at i
  intro t ht
  dsimp only [polygonPiecewisePath, PiecewiseC1Path.path, polygonPath,
    polygonPartition, Fin.val_castSucc, Fin.val_succ]
  rw [polygonMap_node v n i (Nat.le_of_lt i.isLt),
    polygonMap_node v n (i.val + 1) i.isLt]
  rw [polygonMap_piece v n i i.isLt (by simpa [C1Partition.pieceSet,
    polygonPartition] using ht)]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, div_one,
    AffineMap.lineMap_apply_module', Complex.real_smul]
  ring

private theorem polygonMap_mem (v : ℕ → ℂ) (S : Set ℂ) (n : ℕ)
    (hzero : v 0 ∈ S) (hedge : ∀ i < n, segment ℝ (v i) (v (i + 1)) ⊆ S) :
    ∀ t ∈ Icc 0 (n : ℝ), polygonMap v n t ∈ S := by
  induction n with
  | zero => intro t ht; exact hzero
  | succ n ih =>
    intro t ht
    by_cases htn : t ≤ (n : ℝ)
    · simp only [polygonMap, ite_eq_left htn]
      exact ih (fun i hi => hedge i (by omega)) t ⟨ht.1, htn⟩
    · have htp : t ∈ Icc (n : ℝ) ((n : ℝ) + 1) :=
        ⟨le_of_lt (lt_of_not_ge htn), by simpa using ht.2⟩
      rw [polygonMap_piece v (n + 1) n (by omega) htp]
      exact hedge n (by omega) (lineMap_mem_segment ℝ _ _
        ⟨sub_nonneg.mpr htp.1, by linarith [htp.2]⟩)

private theorem polygonPiecewisePath_trace (v : ℕ → ℂ) (n : ℕ) :
    (polygonPiecewisePath v n).trace =
      {v 0} ∪ ⋃ i : Fin n, segment ℝ (v i) (v (i + 1)) := by
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    exact polygonMap_mem v _ n (Or.inl rfl)
      (fun i hi z hz => Or.inr (mem_iUnion.mpr ⟨⟨i, hi⟩, hz⟩)) t ht
  · rintro z (hz | hz)
    · obtain rfl := mem_singleton_iff.mp hz
      exact ⟨0, ⟨le_rfl, Nat.cast_nonneg _⟩, polygonMap_zero v n⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      rw [segment_eq_image_lineMap] at hi
      obtain ⟨s, hs, rfl⟩ := hi
      refine ⟨s + i, ⟨add_nonneg hs.1 (Nat.cast_nonneg _), ?_⟩, ?_⟩
      · change s + i ≤ (n : ℝ)
        have hic : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
        linarith [hs.2]
      · change polygonMap v n (s + i) = _
        rw [polygonMap_piece v n i i.isLt (by constructor <;> linarith [hs.1, hs.2])]
        simp

/-- Every finite sequence of vertices has a genuine piecewise C1 polygonal
traversal. Its integral, for every continuous integrand on its trace, is
the sum of the integrals of its oriented edges. Repeated vertices and the
zero-edge path are allowed. -/
theorem exists_polygonal_path (v : ℕ → ℂ) (n : ℕ) :
    ∃ γ : PiecewiseC1Path, γ.path.a = 0 ∧ γ.path.b = n ∧
      γ.path.source = v 0 ∧ γ.path.target = v n ∧ IsPolygonalPath γ ∧
      γ.trace = {v 0} ∪ ⋃ i : Fin n, segment ℝ (v i) (v (i + 1)) ∧
      (∀ i < n, EqOn γ
        (fun t => AffineMap.lineMap (v i) (v (i + 1)) (t - i))
        (Icc (i : ℝ) ((i : ℝ) + 1))) ∧
      (∀ f : ℂ → ℂ, ContinuousOn f γ.trace →
        γ.integral f = ∑ i : Fin n, segmentIntegral f (v i) (v (i + 1))) := by
  refine ⟨polygonPiecewisePath v n, rfl, rfl, polygonMap_zero v n,
    polygonMap_last v n, polygonPiecewisePath_polygonal v n,
    polygonPiecewisePath_trace v n, ?_, ?_⟩
  · exact fun i hi => polygonMap_piece v n i hi
  · intro f hf
    rw [PiecewiseC1Path.integral_eq_partition (polygonPiecewisePath v n)
      (polygonPartition v n) f hf]
    unfold C1Partition.integral
    apply Finset.sum_congr rfl
    intro i _
    change Fin n at i
    let η := segmentPath (v i) (v (i + 1))
    have heq : EqOn (polygonPiecewisePath v n)
        (fun t => η (t - i)) (Icc (i : ℝ) ((i : ℝ) + 1)) :=
      polygonMap_piece v n i i.isLt
    have hseg : segment ℝ (v i) (v (i + 1)) ⊆
        (polygonPiecewisePath v n).trace := by
      rw [segment_eq_image_lineMap]
      rintro z ⟨s, hs, rfl⟩
      refine ⟨s + i, ⟨add_nonneg hs.1 (Nat.cast_nonneg _), ?_⟩, ?_⟩
      · change s + i ≤ (n : ℝ)
        have hic : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
        linarith [hs.2]
      · change polygonMap v n (s + i) = _
        rw [polygonMap_piece v n i i.isLt (by constructor <;> linarith [hs.1, hs.2])]
        simp
    have hfη : ContinuousOn f η.trace := by
      change ContinuousOn f (segmentPath (v i) (v (i + 1))).trace
      rw [segmentPath_trace]
      exact hf.mono hseg
    calc
      _ = ∫ t in (i : ℝ)..((i : ℝ) + 1),
          f (polygonMap v n t) * deriv (polygonMap v n) t := by
        dsimp only [polygonPartition, Fin.val_castSucc, Fin.val_succ,
          Nat.cast_add, Nat.cast_one]
        simp only [Nat.cast_add, Nat.cast_one]
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        simp only [C1Partition.pieceSet,
          polygonPath, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at ht ⊢
        rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
        rfl
      _ = η.integral f := by
        apply PiecewiseC1Path.integral_affine_piece (polygonMap v n) η
          (-i) 1 (i : ℝ) ((i : ℝ) + 1) (by linarith) f
          (by dsimp [η, segmentPath, PiecewiseC1Path.path]; ring)
          (by dsimp [η, segmentPath, PiecewiseC1Path.path]; ring) _ hfη
        intro t ht
        change polygonMap v n t = AffineMap.lineMap (v i) (v (i + 1)) (-↑i + 1 * t)
        rw [one_mul, neg_add_eq_sub]
        exact polygonMap_piece v n i i.isLt ht
      _ = _ := rfl

/-- The successor permutation decomposes all the edges into finitely many
closed directed walks, each edge occurring exactly once. Fixed points of the
permutation give one-edge walks, so self edges are retained as well. -/
theorem exists_edge_walks (E : Finset (ℂ × ℂ))
    (hbalance : ∀ v : ℂ, (E.filter (fun e => e.1 = v)).card =
      (E.filter (fun e => e.2 = v)).card) :
    ∃ (B : Type) (_ : Fintype B) (n : B → ℕ) (v : B → ℕ → E),
      (∀ b, 0 < n b ∧ v b (n b) = v b 0 ∧
        ∀ i, (v b (i + 1)).val.1 = (v b i).val.2) ∧
      (∀ g : E → ℂ, (∑ b, ∑ i : Fin (n b), g (v b i)) = ∑ e : E, g e) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_edge_successor E hbalance
  let S := Equiv.Perm.SameCycle.setoid σ
  let B := Quotient S
  let : Fintype B := Fintype.ofFinite B
  let q : E → B := Quotient.mk S
  let n : B → ℕ := fun b => Function.minimalPeriod σ b.out
  let v : B → ℕ → E := fun b i => (σ ^ i) b.out
  have hn (b : B) : 0 < n b :=
    Function.minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts b.out)
  have hv (b : B) (i : ℕ) : q (v b i) = b := by
    apply Eq.trans _ (Quotient.out_eq b)
    exact Quotient.sound
      (Equiv.Perm.sameCycle_pow_left.mpr (Equiv.Perm.SameCycle.refl σ b.out))
  let e (b : B) : Fin (n b) ≃ {x : E // q x = b} :=
    Equiv.ofBijective (fun i => ⟨v b i, hv b i⟩) (by
      constructor
      · intro i j hij
        apply Fin.ext
        have h := congrArg Subtype.val hij
        apply Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt |>.mp
        simpa only [Equiv.Perm.iterate_eq_pow] using h
      · intro x
        have hrel : σ.SameCycle b.out x.val :=
          Quotient.exact ((Quotient.out_eq b).trans x.property.symm)
        obtain ⟨k, hk⟩ := hrel.exists_nat_pow_eq
        refine ⟨⟨k % n b, Nat.mod_lt _ (hn b)⟩, Subtype.ext ?_⟩
        change (σ ^ (k % n b)) b.out = x.val
        rw [← Equiv.Perm.iterate_eq_pow, Function.iterate_mod_minimalPeriod_eq,
          Equiv.Perm.iterate_eq_pow]
        exact hk)
  let ε : (Σ b : B, Fin (n b)) ≃ E :=
    (Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv q)
  refine ⟨B, inferInstance, n, v, ?_, ?_⟩
  · intro b
    refine ⟨hn b, ?_, ?_⟩
    · change (σ ^ Function.minimalPeriod σ b.out) b.out = (σ ^ 0) b.out
      simpa only [Equiv.Perm.iterate_eq_pow, pow_zero, Equiv.Perm.one_apply] using
        (Function.iterate_minimalPeriod (f := σ) (x := b.out))
    · intro i
      simpa only [v, pow_succ', Equiv.Perm.mul_apply] using hσ ((σ ^ i) b.out)
  · intro g
    exact (Fintype.sum_sigma (fun p => g (ε p))).symm.trans (ε.sum_comp g)

/-- Realize a balanced finite set of directed edges as an actual polygonal
integer cycle. Its active trace is contained in the union of the edges, and
every continuous contour integral is precisely the directed edge sum. -/
theorem exists_polygonal_cycle_of_balanced_edges (E : Finset (ℂ × ℂ))
    (hbalance : ∀ v : ℂ, (E.filter (fun e => e.1 = v)).card =
      (E.filter (fun e => e.2 = v)).card) :
    ∃ Γ : IntegralCycle, IsPolygonalCycle Γ ∧
      Γ.trace ⊆ ⋃ e : E, segment ℝ e.val.1 e.val.2 ∧
      ∀ f : ℂ → ℂ, ContinuousOn f (⋃ e : E, segment ℝ e.val.1 e.val.2) →
        Γ.integral f = ∑ e : E, segmentIntegral f e.val.1 e.val.2 := by
  classical
  obtain ⟨B, instB, n, v, hv, hsum⟩ := exists_edge_walks E hbalance
  let w : B → ℕ → ℂ := fun b i => (v b i).val.1
  have hex (b : B) : ∃ γ : PiecewiseC1Path,
      γ.IsClosed ∧ IsPolygonalPath γ ∧
      γ.trace ⊆ ⋃ e : E, segment ℝ e.val.1 e.val.2 ∧
      ∀ f : ℂ → ℂ, ContinuousOn f (⋃ e : E, segment ℝ e.val.1 e.val.2) →
        γ.integral f = ∑ i : Fin (n b),
          segmentIntegral f (v b i).val.1 (v b i).val.2 := by
    obtain ⟨γ, _, _, hsource, htarget, hpoly, htrace, _, hint⟩ :=
      exists_polygonal_path (w b) (n b)
    have hγtrace : γ.trace ⊆ ⋃ e : E, segment ℝ e.val.1 e.val.2 := by
      rw [htrace]
      rintro z (hz | hz)
      · obtain rfl := mem_singleton_iff.mp hz
        exact mem_iUnion.mpr ⟨v b 0, left_mem_segment ℝ _ _⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
        exact mem_iUnion.mpr ⟨v b i, by simpa only [w, (hv b).2.2] using hi⟩
    refine ⟨γ, ?_, hpoly, hγtrace, ?_⟩
    · change γ.path.target = γ.path.source
      rw [htarget, hsource]
      exact congrArg (fun e : E => e.val.1) (hv b).2.1
    · intro f hf
      rw [hint f (hf.mono hγtrace)]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (segmentIntegral f (w b i)) ((hv b).2.2 i)
  choose γ hclosed hpoly htrace hint using hex
  let C : IntegralChain := ∑ b : B, Finsupp.single (γ b) (1 : ℤ)
  have hsupport (η : PiecewiseC1Path) (hη : η ∈ C.support) : ∃ b, η = γ b := by
    obtain ⟨b, _, hb⟩ := Finsupp.mem_support_finsetSum η hη
    exact ⟨b, by simpa only [Finsupp.support_single _ one_ne_zero,
      Finset.mem_singleton] using hb⟩
  let Γ : IntegralCycle := ⟨C, fun η hη => by
    obtain ⟨b, rfl⟩ := hsupport η hη
    exact hclosed b⟩
  refine ⟨Γ, ?_, ?_, ?_⟩
  · intro η hη
    obtain ⟨b, rfl⟩ := hsupport η hη
    exact hpoly b
  · rintro z ⟨η, hη, hz⟩
    obtain ⟨b, rfl⟩ := hsupport η hη
    exact htrace b hz
  · intro f hf
    change C.integral f = _
    calc
      C.integral f = ∑ b : B, (γ b).integral f := by
        unfold C IntegralChain.integral
        rw [← Finsupp.sum_finsetSum_index (fun η => by simp)
          (fun η m k => by simp [add_mul])]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finsupp.sum_single_index]
        · simp
        · simp
      _ = ∑ b : B, ∑ i : Fin (n b),
          segmentIntegral f (v b i).val.1 (v b i).val.2 :=
        Finset.sum_congr rfl (fun b _ => hint b f hf)
      _ = _ := hsum (fun e => segmentIntegral f e.val.1 e.val.2)

/-- It remains to calculate reciprocal edge sums in a grid construction.
This bridge transfers those sums to the canonical cycle index, using the
actual active trace rather than a trace reduced modulo edge cancellation. -/
theorem exists_polygonal_cycle_of_edge_kernels (K U : Set ℂ)
    (E : Finset (ℂ × ℂ))
    (hbalance : ∀ v : ℂ, (E.filter (fun e => e.1 = v)).card =
      (E.filter (fun e => e.2 = v)).card)
    (htrace : (⋃ e : E, segment ℝ e.val.1 e.val.2) ⊆ U \ K)
    (hone : ∀ a ∈ K, (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (∑ e : E, segmentIntegral (fun w => 1 / (w - a)) e.val.1 e.val.2) = 1)
    (hnull : ∀ a, a ∉ U → (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (∑ e : E, segmentIntegral (fun w => 1 / (w - a)) e.val.1 e.val.2) = 0) :
    ∃ Γ : IntegralCycle, IsPolygonalCycle Γ ∧ Γ.trace ⊆ U \ K ∧
      (∀ a ∈ K, Γ.index a = 1) ∧ (∀ a, a ∉ U → Γ.index a = 0) := by
  obtain ⟨Γ, hpoly, hΓ, hint⟩ := exists_polygonal_cycle_of_balanced_edges E hbalance
  have hindex (a : ℂ) (ha : a ∉ ⋃ e : E, segment ℝ e.val.1 e.val.2) :
      Γ.index a = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∑ e : E, segmentIntegral (fun w => 1 / (w - a)) e.val.1 e.val.2 := by
    rw [IntegralCycle.index_eq_integral Γ a (fun hz => ha (hΓ hz))]
    have hc : ContinuousOn (fun w : ℂ => 1 / (w - a))
        (⋃ e : E, segment ℝ e.val.1 e.val.2) := by
      apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      intro w hw
      change w - a ≠ 0
      exact sub_ne_zero.mpr (fun h => ha (h ▸ hw))
    rw [hint _ hc]
  refine ⟨Γ, hpoly, hΓ.trans htrace, ?_, ?_⟩
  · intro a ha
    rw [hindex a (fun ht => (htrace ht).2 ha)]
    exact hone a ha
  · intro a ha
    rw [hindex a (fun ht => ha (htrace ht).1)]
    exact hnull a ha

/-- A compact set and a disjoint finite contour have a positive uniform gap.
This does not impose nonemptiness on either one. -/
theorem positivelySeparated_of_disjoint (K : Set ℂ) (hK : IsCompact K)
    (Γ : IntegralCycle) (hd : Disjoint K Γ.trace) : PositivelySeparated K Γ := by
  obtain ⟨δ, hδ, hgap⟩ := hK.exists_thickening_subset_open
    (PiecewiseC1Length.chain_trace_compact Γ.chain).isClosed.isOpen_compl
    (fun z hz => disjoint_left.mp hd hz)
  refine ⟨δ, hδ, fun z hz w hw => le_of_not_gt (fun hlt => ?_)⟩
  have hwt : w ∈ thickening δ K := by
    rw [mem_thickening_iff]
    exact ⟨z, hz, by simpa only [dist_comm] using hlt⟩
  exact hgap hwt hw

/-- Once the contour has index one on K and index zero outside U, the full
cycle theorem applies at every point of K, including grid-line points. -/
theorem representation_of_index (K U : Set ℂ) (f : ℂ → ℂ)
    (Γ : IntegralCycle) (hf : HolomorphicOn U f) (hKU : K ⊆ U)
    (hΓ : Γ.trace ⊆ U \ K)
    (hnull : ∀ w, w ∉ U → Γ.index w = 0)
    (hone : ∀ z ∈ K, Γ.index z = 1) :
    ∀ z ∈ K, f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      Γ.integral (fun w => f w / (w - z)) := by
  intro z hz
  have hzt : z ∉ Γ.trace := fun ht => (hΓ ht).2 hz
  simpa only [hone z hz, one_mul] using
    FiniteCycleCauchy.cycle_cauchy_formula U f Γ hf
      (fun w hw => (hΓ hw).1) hnull z (hKU hz) hzt

/-- The transform appearing in the representation is continuous at every
point off the actual active trace, with no regularity assumption on K. -/
theorem continuousAt_cauchyTransform (Γ : IntegralCycle) (f : ℂ → ℂ)
    (hf : ContinuousOn f Γ.trace) (z : ℂ) (hz : z ∉ Γ.trace) :
    ContinuousAt (fun a => (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      Γ.integral (fun w => f w / (w - a))) z := by
  have hc := (FiniteCycleCauchy.hasDerivAt_kernel_integral Γ.chain f hf 0 z hz).continuousAt
  simpa only [Nat.zero_add, pow_one, IntegralCycle.integral] using
    hc.const_mul (2 * Real.pi * Complex.I : ℂ)⁻¹

/-- Countably many coordinate levels cannot obstruct density in the plane.
This applies to every rectangular grid, independently of how K meets it. -/
theorem dense_off_coordinate_levels (A B : Set ℝ) (hA : A.Countable) (hB : B.Countable) :
    Dense {z : ℂ | z.re ∉ A ∧ z.im ∉ B} := by
  exact ((hA.dense_compl ℝ).prod (hB.dense_compl ℝ)).preimage
    Complex.equivRealProdCLM.toHomeomorph.isOpenMap

/-- Off-grid points are dense in every open region, including regions that
contain compact sets made entirely of grid-line points. -/
theorem off_grid_dense_on_open (h : ℝ) (V : Set ℂ) (hV : IsOpen V) :
    V ⊆ closure ({z : ℂ |
      z.re ∉ Set.range (fun m : ℤ => h * m) ∧
      z.im ∉ Set.range (fun m : ℤ => h * m)} ∩ V) := by
  simpa only [inter_comm] using
    (dense_off_coordinate_levels (range (fun m : ℤ => h * m))
      (range (fun m : ℤ => h * m)) (countable_range _)
      (countable_range _)).open_subset_closure_inter hV

/-- In a grid argument one must prove the off-grid formula on a full open
neighborhood, not merely on the off-grid part of K. This lemma then extends
the formula to all of that neighborhood, even when K is contained in grid
lines. Its hypotheses use density in V, without asserting density in K. -/
theorem representation_of_dense (Γ : IntegralCycle) (U V D : Set ℂ)
    (f : ℂ → ℂ) (hf : HolomorphicOn U f) (hΓ : Γ.trace ⊆ U)
    (hVU : V ⊆ U) (htrace : Disjoint V Γ.trace)
    (hdense : V ⊆ closure (D ∩ V))
    (heq : ∀ z ∈ D ∩ V, f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      Γ.integral (fun w => f w / (w - z))) :
    ∀ z ∈ V, f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      Γ.integral (fun w => f w / (w - z)) := by
  intro z hz
  have hfc : ContinuousOn f Γ.trace := fun w hw =>
    (hf.2 w (hΓ hw)).continuousAt.continuousWithinAt
  have hc := ((hf.2 z (hVU hz)).continuousAt.sub
    (continuousAt_cauchyTransform Γ f hfc z (disjoint_left.mp htrace hz)))
  have hmap : MapsTo
      (f - fun a => (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        Γ.integral (fun w => f w / (w - a))) (D ∩ V) ({0} : Set ℂ) := by
    intro w hw
    exact sub_eq_zero.mpr (heq w hw)
  have hm := hc.continuousWithinAt.mem_closure (hdense hz) hmap
  simpa only [closure_singleton, mem_singleton_iff, Pi.sub_apply, sub_eq_zero] using hm

/-- Local constancy supplies a legitimate extension from a dense subset of an
open region to every point of that region. The dense set need not meet K. -/
theorem index_eq_of_dense (Γ : IntegralCycle) (V D : Set ℂ) (c : ℂ)
    (htrace : Disjoint V Γ.trace)
    (hdense : V ⊆ closure (D ∩ V)) (heq : ∀ z ∈ D ∩ V, Γ.index z = c) :
    ∀ z ∈ V, Γ.index z = c := by
  intro z hz
  have hzt : z ∉ Γ.trace := disjoint_left.mp htrace hz
  have hloc := IndexProperties.cycle_index_locally_constant Γ z hzt
  obtain ⟨w, hwloc, hwD⟩ := mem_closure_iff_nhds.mp (hdense hz)
    {w | w ∉ Γ.trace ∧ Γ.index w = Γ.index z} hloc
  exact hwloc.2.symm.trans (heq w hwD)

/-- The source's empty compact set case is handled by the zero cycle. -/
theorem empty_polygon_representation (U : Set ℂ) (f : ℂ → ℂ) :
    ∃ Γ : IntegralCycle, IsPolygonalCycle Γ ∧ Γ.trace ⊆ U \ (∅ : Set ℂ) ∧
      PositivelySeparated ∅ Γ ∧ Γ = 0 ∧
      ∀ z ∈ (∅ : Set ℂ), f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        Γ.integral (fun w => f w / (w - z)) := by
  refine ⟨0, zero_isPolygonalCycle, ?_, ?_, rfl, ?_⟩
  · simp
  · exact ⟨1, zero_lt_one, fun z hz => False.elim hz⟩
  · simp

namespace Grid
attribute [local instance] Classical.propDecidable
abbrev Vertex := ℤ × ℤ

def point (h : ℝ) (p : Vertex) : ℂ := ⟨h * p.1, h * p.2⟩

def vertex (p : Vertex) (i : Fin 4) : Vertex :=
  if i = 0 then p else if i = 1 then (p.1 + 1, p.2) else
    if i = 2 then (p.1 + 1, p.2 + 1) else (p.1, p.2 + 1)

def edge (h : ℝ) (p : Vertex) (i : Fin 4) : ℂ × ℂ :=
  (point h (vertex p i), point h (vertex p (i + 1)))

theorem point_injective {h : ℝ} (hh : h ≠ 0) : Function.Injective (point h) := by
  intro p q hpq
  have hx := congrArg Complex.re hpq
  have hy := congrArg Complex.im hpq
  change h * p.1 = h * q.1 at hx
  change h * p.2 = h * q.2 at hy
  exact Prod.ext (Int.cast_injective (mul_left_cancel₀ hh hx))
    (Int.cast_injective (mul_left_cancel₀ hh hy))

theorem edge_injective {h : ℝ} (hh : h ≠ 0) :
    Function.Injective (fun e : Vertex × Fin 4 => edge h e.1 e.2) := by
  rintro ⟨p,i⟩ ⟨q,j⟩ he
  have h₁ := point_injective hh (congrArg Prod.fst he)
  have h₂ := point_injective hh (congrArg Prod.snd he)
  have h₁x := congrArg Prod.fst h₁
  have h₁y := congrArg Prod.snd h₁
  have h₂x := congrArg Prod.fst h₂
  have h₂y := congrArg Prod.snd h₂
  fin_cases i <;> fin_cases j <;>
    norm_num [vertex] at h₁x h₁y h₂x h₂y ⊢ <;>
    (try omega) <;> apply Prod.ext <;> omega

def edges (h : ℝ) (S : Finset Vertex) : Finset (ℂ × ℂ) :=
  (S ×ˢ Finset.univ).image (fun e => edge h e.1 e.2)

theorem sum_edges {A : Type*} [AddCommMonoid A] {h : ℝ} (hh : h ≠ 0)
    (S : Finset Vertex) (g : ℂ × ℂ → A) :
    (∑ e ∈ edges h S, g e) = ∑ p ∈ S, ∑ i : Fin 4, g (edge h p i) := by
  classical
  rw [edges, Finset.sum_image (fun _ _ _ _ he => edge_injective hh he),
    Finset.sum_product]

theorem edges_balanced {h : ℝ} (hh : h ≠ 0) (S : Finset Vertex) (z : ℂ) :
    ((edges h S).filter (fun e => e.1 = z)).card =
      ((edges h S).filter (fun e => e.2 = z)).card := by
  classical
  have hc (P : ℂ × ℂ → Prop) [DecidablePred P] :
      ((edges h S).filter P).card = ∑ e ∈ edges h S, if P e then (1 : ℕ) else 0 := by
    simp
  rw [hc, hc, sum_edges hh, sum_edges hh]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Fin.sum_univ_four, edge, vertex]
  norm_num
  omega

/-- A grid cell is the closed coordinate square, with positive orientation
on its four explicitly directed sides. -/
def cell (h : ℝ) (p : Vertex) : Set ℂ :=
  {z | h * p.1 ≤ z.re ∧ z.re ≤ h * (p.1 + 1) ∧
    h * p.2 ≤ z.im ∧ z.im ≤ h * (p.2 + 1)}

def neighbor (p : Vertex) (i : Fin 4) : Vertex :=
  if i = 0 then (p.1, p.2 - 1) else if i = 1 then (p.1 + 1, p.2) else
    if i = 2 then (p.1, p.2 + 1) else (p.1 - 1, p.2)

theorem edge_reverse (h : ℝ) (p : Vertex) (i : Fin 4) :
    edge h (neighbor p i) (i + 2) = (edge h p i).swap := by
  fin_cases i <;> simp [edge, vertex, neighbor, point]

theorem cell_convex (h : ℝ) (p : Vertex) : Convex ℝ (cell h p) := by
  convert ((convex_Icc (h * p.1) (h * (p.1 + 1))).linear_preimage
    Complex.reCLM.toLinearMap).inter
    ((convex_Icc (h * p.2) (h * (p.2 + 1))).linear_preimage
      Complex.imCLM.toLinearMap) using 1
  ext z
  simp [cell, and_assoc]

theorem vertex_mem_cell {h : ℝ} (hh : 0 ≤ h) (p : Vertex) (i : Fin 4) :
    point h (vertex p i) ∈ cell h p := by
  fin_cases i <;> simp [point, vertex, cell, Int.cast_add, hh, mul_add]

theorem side_subset_cell {h : ℝ} (hh : 0 ≤ h) (p : Vertex) (i : Fin 4) :
    segment ℝ (edge h p i).1 (edge h p i).2 ⊆ cell h p :=
  (cell_convex h p).segment_subset (vertex_mem_cell hh p i)
    (vertex_mem_cell hh p (i + 1))

theorem side_subset_neighbor {h : ℝ} (hh : 0 ≤ h) (p : Vertex) (i : Fin 4) :
    segment ℝ (edge h p i).1 (edge h p i).2 ⊆ cell h (neighbor p i) := by
  have ht := side_subset_cell hh (neighbor p i) (i + 2)
  rw [edge_reverse] at ht
  simpa only [Prod.fst_swap, Prod.snd_swap, segment_symm] using ht

/-- If every square meeting V is selected, every surviving directed side
misses V. This treats side endpoints and grid vertices as well. -/
theorem boundary_avoids (h : ℝ) (hh : 0 ≤ h) (S : Finset Vertex) (V : Set ℂ)
    (hselected : ∀ p, (cell h p ∩ V).Nonempty → p ∈ S) :
    Disjoint V (⋃ e : (edges h S).filter (fun e => e.swap ∉ edges h S),
      segment ℝ e.val.1 e.val.2) := by
  classical
  apply disjoint_left.mpr
  intro z hz hzt
  obtain ⟨e,he⟩ := mem_iUnion.mp hzt
  obtain ⟨heS, hrev⟩ := Finset.mem_filter.mp e.property
  obtain ⟨⟨p,i⟩,hpi,heq⟩ := Finset.mem_image.mp heS
  change edge h p i = e.val at heq
  rw [← heq] at he hrev
  have hn : neighbor p i ∈ S :=
    hselected _ ⟨z, side_subset_neighbor hh p i he, hz⟩
  apply hrev
  rw [← edge_reverse h p i]
  exact Finset.mem_image.mpr ⟨(neighbor p i, i + 2),
    Finset.mem_product.mpr ⟨hn, Finset.mem_univ _⟩, rfl⟩

/-- The closed square tiling covers every point, including grid lines. -/
def containingCell (h : ℝ) (z : ℂ) : Vertex :=
  (⌊z.re / h⌋, ⌊z.im / h⌋)

theorem mem_containingCell {h : ℝ} (hh : 0 < h) (z : ℂ) :
    z ∈ cell h (containingCell h z) := by
  have hr := Int.floor_le (z.re / h)
  have hr' := Int.lt_floor_add_one (z.re / h)
  have hi := Int.floor_le (z.im / h)
  have hi' := Int.lt_floor_add_one (z.im / h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [containingCell, mul_comm] using (le_div_iff₀ hh).mp hr
  · simpa [containingCell, mul_comm] using ((div_lt_iff₀ hh).mp hr').le
  · simpa [containingCell, mul_comm] using (le_div_iff₀ hh).mp hi
  · simpa [containingCell, mul_comm] using ((div_lt_iff₀ hh).mp hi').le

theorem dist_le_two_mul {h : ℝ} (_hh : 0 ≤ h) {p : Vertex} {z w : ℂ}
    (hz : z ∈ cell h p) (hw : w ∈ cell h p) : dist z w ≤ 2 * h := by
  have hr : |(z - w).re| ≤ h := by
    rw [Complex.sub_re, abs_le]
    constructor <;> linarith [hz.1, hz.2.1, hw.1, hw.2.1]
  have hi : |(z - w).im| ≤ h := by
    rw [Complex.sub_im, abs_le]
    constructor <;> linarith [hz.2.2.1, hz.2.2.2, hw.2.2.1, hw.2.2.2]
  rw [dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

/-- Only finitely many cells can meet a bounded set. No regularity or
nonempty-interior hypothesis on that set is used. -/
theorem finite_cells_meeting {h : ℝ} (hh : 0 < h) {V : Set ℂ}
    (hV : Bornology.IsBounded V) : {p : Vertex | (cell h p ∩ V).Nonempty}.Finite := by
  obtain ⟨R, hR, hbound⟩ := hV.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + h) / h)
  have hN' : R + h < (N : ℝ) * h := (div_lt_iff₀ hh).mp hN
  apply (Set.finite_Icc ((-(N : ℤ)), -(N : ℤ)) ((N : ℤ), (N : ℤ))).subset
  rintro p ⟨z,hzp,hzV⟩
  have hzr := (abs_le.mp ((Complex.abs_re_le_norm z).trans (hbound z hzV)))
  have hzi := (abs_le.mp ((Complex.abs_im_le_norm z).trans (hbound z hzV)))
  have hrlo : -(N : ℝ) ≤ p.1 := by nlinarith [hzp.2.1]
  have hrhi : (p.1 : ℝ) ≤ N := by nlinarith [hzp.1]
  have hilo : -(N : ℝ) ≤ p.2 := by nlinarith [hzp.2.2.2]
  have hihi : (p.2 : ℝ) ≤ N := by nlinarith [hzp.2.2.1]
  exact ⟨⟨by exact_mod_cast hrlo, by exact_mod_cast hilo⟩,
    ⟨by exact_mod_cast hrhi, by exact_mod_cast hihi⟩⟩

theorem cell_isClosed (h : ℝ) (p : Vertex) : IsClosed (cell h p) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

/-- Choose a finite thickened grid neighborhood. Every selected square is
inside U, K lies in the open V, and every square meeting V is selected. -/
theorem exists_finite_grid_neighborhood (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (h : ℝ) (S : Finset Vertex) (V : Set ℂ), 0 < h ∧ IsOpen V ∧
      K ⊆ V ∧ (∀ p, (cell h p ∩ V).Nonempty ↔ p ∈ S) ∧
      (⋃ p ∈ S, cell h p) ⊆ U := by
  classical
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_thickening_subset_open hU hKU
  let h := δ / 4
  have hh : 0 < h := by dsimp [h]; linarith
  let V := thickening h K
  let S := (finite_cells_meeting hh (hK.isBounded.thickening (δ := h))).toFinset
  refine ⟨h,S,V,hh,isOpen_thickening,self_subset_thickening hh K,?_,?_⟩
  · intro p
    simp [S,V]
  · intro z hz
    obtain ⟨p,hpS,hzp⟩ := mem_iUnion₂.mp hz
    obtain ⟨w,hwp,hwV⟩ := (Set.Finite.mem_toFinset _).mp hpS
    obtain ⟨a,haK,hwa⟩ := mem_thickening_iff.mp hwV
    apply hδU
    rw [mem_thickening_iff]
    refine ⟨a,haK,?_⟩
    have hzw := dist_le_two_mul hh.le hzp hwp
    have htri := dist_triangle z w a
    dsimp [h] at hzw hwa
    linarith

/-- An explicit side has a constant grid coordinate. -/
theorem side_on_grid {h : ℝ} (hh : 0 ≤ h) (p : Vertex) (i : Fin 4)
    {z : ℂ} (hz : z ∈ segment ℝ (edge h p i).1 (edge h p i).2) :
    z.re ∈ Set.range (fun m : ℤ => h * m) ∨
      z.im ∈ Set.range (fun m : ℤ => h * m) := by
  have hp := side_subset_cell hh p i hz
  have hn := side_subset_neighbor hh p i hz
  fin_cases i
  · right
    refine ⟨p.2,?_⟩
    simp only [cell, mem_ofPred_eq, neighbor, Fin.zero_eta, ↓reduceIte,
      Int.cast_sub, Int.cast_one] at hp hn
    linarith
  · left
    refine ⟨p.1 + 1,?_⟩
    norm_num [cell, neighbor] at hp hn ⊢
    linarith
  · right
    refine ⟨p.2 + 1,?_⟩
    norm_num [cell, neighbor] at hp hn ⊢
    linarith
  · left
    refine ⟨p.1,?_⟩
    norm_num [cell, neighbor] at hp hn ⊢
    linarith

def offGrid (h : ℝ) : Set ℂ :=
  {z | z.re ∉ Set.range (fun m : ℤ => h * m) ∧
    z.im ∉ Set.range (fun m : ℤ => h * m)}

theorem mem_cell_iff_containingCell {h : ℝ} (hh : 0 < h) {a : ℂ}
    (ha : a ∈ offGrid h) (p : Vertex) : a ∈ cell h p ↔ p = containingCell h a := by
  constructor
  · intro hp
    have hr : a.re < h * (p.1 + 1) := lt_of_le_of_ne hp.2.1 (by
      intro he
      exact ha.1 ⟨p.1 + 1, by simpa using he.symm⟩)
    have hi : a.im < h * (p.2 + 1) := lt_of_le_of_ne hp.2.2.2 (by
      intro he
      exact ha.2 ⟨p.2 + 1, by simpa using he.symm⟩)
    have hrp : ⌊a.re / h⌋ = p.1 := Int.floor_eq_iff.mpr
      ⟨(le_div_iff₀ hh).mpr (by simpa [mul_comm] using hp.1),
       (div_lt_iff₀ hh).mpr (by simpa [mul_comm] using hr)⟩
    have hip : ⌊a.im / h⌋ = p.2 := Int.floor_eq_iff.mpr
      ⟨(le_div_iff₀ hh).mpr (by simpa [mul_comm] using hp.2.2.1),
       (div_lt_iff₀ hh).mpr (by simpa [mul_comm] using hi)⟩
    exact Prod.ext hrp.symm hip.symm
  · rintro rfl
    exact mem_containingCell hh a

/-- The normalized reciprocal integral over one positively oriented square.
The canonical rectangle-index theorem is applied to the actual affine
polygonal parametrization, and only at points off its trace. -/
theorem cell_kernel {h : ℝ} (hh : 0 < h) (p : Vertex) (a : ℂ)
    (ha : a ∈ offGrid h) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (∑ i : Fin 4, segmentIntegral (fun w => 1 / (w - a))
        (edge h p i).1 (edge h p i).2) = if a ∈ cell h p then 1 else 0 := by
  classical
  let v : ℕ → ℂ := fun n => point h (vertex p (Fin.ofNat 4 n))
  obtain ⟨γ,hstart,hend,hsource,htarget,hpoly,htrace,hpiece,hint⟩ :=
    exists_polygonal_path v 4
  have hv0 : v 0 = point h p := rfl
  have hv1 : v 1 = point h (p.1 + 1,p.2) := rfl
  have hv2 : v 2 = point h (p.1 + 1,p.2 + 1) := rfl
  have hv3 : v 3 = point h (p.1,p.2 + 1) := rfl
  have hv4 : v 4 = point h p := rfl
  have htr : Specs.D12Complex.Ch04.IndexComputations.rectangle_traversal
      γ (point h p) 1 h h := by
    refine ⟨hstart, by simpa using hend, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [hpiece 0 (by omega) (by norm_num; exact ht)]
      simp only [Nat.reduceAdd,hv0,hv1]
      apply Complex.ext <;> simp [point,AffineMap.lineMap_apply_module',
        Complex.mul_re,Complex.mul_im] <;> ring
    · intro t ht
      rw [hpiece 1 (by omega) (by norm_num; exact ht)]
      simp only [Nat.reduceAdd,hv1,hv2]
      apply Complex.ext <;> simp [point,AffineMap.lineMap_apply_module',
        Complex.mul_re,Complex.mul_im] <;> ring
    · intro t ht
      rw [hpiece 2 (by omega) (by norm_num; exact ht)]
      simp only [Nat.reduceAdd,hv2,hv3]
      apply Complex.ext <;> simp [point,AffineMap.lineMap_apply_module',
        Complex.mul_re,Complex.mul_im] <;> ring
    · intro t ht
      rw [hpiece 3 (by omega) (by norm_num; exact ht)]
      simp only [Nat.reduceAdd,hv3,hv4]
      apply Complex.ext <;> simp [point,AffineMap.lineMap_apply_module',
        Complex.mul_re,Complex.mul_im] <;> ring
  have hat : a ∉ γ.trace := by
    rw [htrace]
    rintro (ha0 | haedge)
    · have he : a = v 0 := mem_singleton_iff.mp ha0
      exact ha.1 ⟨p.1, by simp [he,v,vertex,point]⟩
    · obtain ⟨i,hi⟩ := mem_iUnion.mp haedge
      have hie : (v i, v (i + 1)) = edge h p i := by fin_cases i <;> rfl
      have hg := side_on_grid hh.le p i (by simpa only [← hie] using hi)
      exact hg.elim ha.1 ha.2
  have hc : ContinuousOn (fun w : ℂ => 1 / (w - a)) γ.trace :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun z hz => sub_ne_zero.mpr (fun he => hat (he ▸ hz)))
  have hindex : γ.index a = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      (∑ i : Fin 4, segmentIntegral (fun w => 1 / (w - a))
        (edge h p i).1 (edge h p i).2) := by
    rw [IndexOperationsHomotopy.path_index_eq_integral γ a hat, hint _ hc]
    congr 1
  rw [← hindex]
  have hr := IndexComputations.rectangle_index γ (point h p) 1 a h h
    (by simp) hh hh htr
  by_cases hp : a ∈ cell h p
  · rw [ite_eq_left hp]
    apply hr.1
    have hlo : h * p.1 < a.re := lt_of_le_of_ne hp.1 (by
      intro he
      exact ha.1 ⟨p.1,he⟩)
    have hhi : a.re < h * (p.1 + 1) := lt_of_le_of_ne hp.2.1 (by
      intro he
      exact ha.1 ⟨p.1 + 1, by simpa using he.symm⟩)
    have vlo : h * p.2 < a.im := lt_of_le_of_ne hp.2.2.1 (by
      intro he
      exact ha.2 ⟨p.2,he⟩)
    have vhi : a.im < h * (p.2 + 1) := lt_of_le_of_ne hp.2.2.2 (by
      intro he
      exact ha.2 ⟨p.2 + 1, by simpa using he.symm⟩)
    simp only [div_one, Complex.sub_re, Complex.sub_im, point]
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · rw [ite_eq_right hp]
    apply hr.2
    simp only [div_one, Complex.sub_re, Complex.sub_im, point]
    intro hb
    exact hp ⟨by linarith [hb.1],by linarith [hb.2.1],
      by linarith [hb.2.2.1],by linarith [hb.2.2.2]⟩

/-- Realize the cancelled grid boundary as a canonical integer polygonal
cycle, and compute its index at every off-grid point. -/
theorem exists_boundary_cycle {h : ℝ} (hh : 0 < h) (S : Finset Vertex) :
    ∃ Γ : IntegralCycle, IsPolygonalCycle Γ ∧
      Γ.trace ⊆ ⋃ e : (edges h S).filter (fun e => e.swap ∉ edges h S),
        segment ℝ e.val.1 e.val.2 ∧
      ∀ a ∈ offGrid h, Γ.index a = if containingCell h a ∈ S then 1 else 0 := by
  classical
  let E := edges h S
  let B := E.filter (fun e => e.swap ∉ E)
  obtain ⟨Γ,hpoly,htrace,hint⟩ := exists_polygonal_cycle_of_balanced_edges B
    (balanced_edges_cancel_reverse E (edges_balanced hh.ne' S))
  refine ⟨Γ,hpoly,htrace,?_⟩
  intro a ha
  have hraw : a ∉ ⋃ e : E, segment ℝ e.val.1 e.val.2 := by
    intro ht
    obtain ⟨e,he⟩ := mem_iUnion.mp ht
    obtain ⟨⟨p,i⟩,_,heq⟩ := Finset.mem_image.mp e.property
    have hg := side_on_grid hh.le p i (by simpa only [heq] using he)
    exact hg.elim ha.1 ha.2
  have hsub : (⋃ e : B, segment ℝ e.val.1 e.val.2) ⊆
      ⋃ e : E, segment ℝ e.val.1 e.val.2 := by
    intro z hz
    obtain ⟨e,he⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨⟨e.val,(Finset.mem_filter.mp e.property).1⟩,he⟩
  have hc : ContinuousOn (fun w : ℂ => 1 / (w - a))
      (⋃ e : E, segment ℝ e.val.1 e.val.2) :=
    continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun z hz => sub_ne_zero.mpr (fun he => hraw (he ▸ hz)))
  rw [IntegralCycle.index_eq_integral Γ a (fun ht => hraw (hsub (htrace ht))),
    hint _ (hc.mono hsub), Finset.sum_coe_sort B
      (fun e : ℂ × ℂ => segmentIntegral (fun w => 1 / (w - a)) e.1 e.2)]
  have hcancel := edge_sum_cancel_reverse E
    (fun e => segmentIntegral (fun w => 1 / (w - a)) e.1 e.2) (by
      intro e he hrev
      exact segmentIntegral_reverse _ _ _ (hc.mono (fun z hz =>
        mem_iUnion.mpr ⟨⟨e,he⟩,hz⟩)))
  rw [hcancel, sum_edges hh.ne' S, Finset.mul_sum]
  simp_rw [cell_kernel hh _ a ha, mem_cell_iff_containingCell hh ha]
  exact Finset.sum_ite_eq' S (containingCell h a) (fun _ => (1 : ℂ))

/-- The selected closed cell union is closed and contains every surviving
side, so its open complement is a valid region for the exterior extension. -/
theorem boundary_subset_cells {h : ℝ} (hh : 0 ≤ h) (S : Finset Vertex) :
    (⋃ e : (edges h S).filter (fun e => e.swap ∉ edges h S),
      segment ℝ e.val.1 e.val.2) ⊆ ⋃ p ∈ S, cell h p := by
  intro z hz
  obtain ⟨e,he⟩ := mem_iUnion.mp hz
  obtain ⟨⟨p,i⟩,hpi,heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp e.property).1
  exact mem_iUnion₂.mpr ⟨p,(Finset.mem_product.mp hpi).1,
    side_subset_cell hh p i (by simpa only [heq] using he)⟩

/-- Density is used on open regions, independently of the intersections
of K and U-complement with grid lines. -/
theorem exists_enclosing_cycle (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ Γ : IntegralCycle, IsPolygonalCycle Γ ∧ Γ.trace ⊆ U \ K ∧
      (∀ z ∈ K, Γ.index z = 1) ∧ (∀ z, z ∉ U → Γ.index z = 0) := by
  classical
  obtain ⟨h,S,V,hh,hV,hKV,hS,hcellsU⟩ :=
    exists_finite_grid_neighborhood K U hK hU hKU
  obtain ⟨Γ,hpoly,htrace,hindex⟩ := exists_boundary_cycle hh S
  let L := ⋃ p ∈ S, cell h p
  have hL : IsClosed L := isClosed_biUnion_finset (fun p hp => cell_isClosed h p)
  have hΓL : Γ.trace ⊆ L := htrace.trans (boundary_subset_cells hh.le S)
  have hdis : Disjoint V Γ.trace :=
    (boundary_avoids h hh.le S V (fun p hp => (hS p).mp hp)).mono_right htrace
  refine ⟨Γ,hpoly,fun z hz => ⟨hcellsU (hΓL hz),
    fun hzK => disjoint_left.mp hdis (hKV hzK) hz⟩,?_,?_⟩
  · have heq : ∀ z ∈ offGrid h ∩ V, Γ.index z = 1 := by
      intro z hz
      rw [hindex z hz.1, ite_eq_left]
      exact (hS _).mp ⟨z,mem_containingCell hh z,hz.2⟩
    exact fun z hz => index_eq_of_dense Γ V (offGrid h) 1 hdis
      (off_grid_dense_on_open h V hV) heq z (hKV hz)
  · have hdisL : Disjoint Lᶜ Γ.trace := disjoint_left.mpr
      (fun _ hz ht => hz (hΓL ht))
    have heq : ∀ z ∈ offGrid h ∩ Lᶜ, Γ.index z = 0 := by
      intro z hz
      rw [hindex z hz.1, ite_eq_right]
      intro hp
      exact hz.2 (mem_iUnion₂.mpr ⟨containingCell h z,hp,mem_containingCell hh z⟩)
    intro z hz
    exact index_eq_of_dense Γ Lᶜ (offGrid h) 0 hdisL
      (off_grid_dense_on_open h Lᶜ hL.isOpen_compl) heq z
      (fun hzL => hz (hcellsU hzL))

end Grid

/-- A geometric polygonal cycle surrounds K with index one and has index
zero outside U; this construction is independent of the function. -/
theorem exists_polygonal_cycle (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ Γ : IntegralCycle, IsPolygonalCycle Γ ∧ Γ.trace ⊆ U \ K ∧
      (K = ∅ → Γ = 0) ∧ (∀ z ∈ K, Γ.index z = 1) ∧
      (∀ w, w ∉ U → Γ.index w = 0) := by
  by_cases hKe : K = ∅
  · subst K
    refine ⟨0, zero_isPolygonalCycle, ?_, fun _ => rfl, ?_, ?_⟩
    · simp
    · simp
    · intro w _
      exact IntegralCycle.zero_index w
  · obtain ⟨Γ,hpoly,htrace,hone,hnull⟩ := Grid.exists_enclosing_cycle K U hK hU hKU
    exact ⟨Γ,hpoly,htrace,fun he => False.elim (hKe he),hone,hnull⟩

theorem polygon_representation :
    Specs.D12Complex.Ch15.PolygonRepresentation.polygon_representation_type := by
  intro K U f hK hU hKU hf
  obtain ⟨Γ, hpoly, hΓ, hzero, hone, hnull⟩ :=
    exists_polygonal_cycle K U hK hU hKU
  refine ⟨Γ, hpoly, hΓ, ?_, hzero,
    representation_of_index K U f Γ hf hKU hΓ hnull hone⟩
  exact positivelySeparated_of_disjoint K hK Γ
    (disjoint_left.mpr (fun _ hz hw => (hΓ hw).2 hz))

end D12Complex.PolygonRepresentation
