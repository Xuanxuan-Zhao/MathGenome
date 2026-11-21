import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.ContinuousTraceDiagonal
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceBasisCyclicity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2Kernel
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Order.Disjointed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u v w
namespace ExpandedFA.IntegralOperators.ContinuousTraceDiagonal
open TraceIdeals.TraceClassDefinitions

variable {𝕜 : Type} [RCLike 𝕜] {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Strong convergence of uniformly bounded left factors passes through the
trace against a trace-class operator. The proof uses its actual singular
expansion and dominated convergence of the resulting absolutely summable
scalar series. -/
lemma trace_tendsto_comp_of_strong (T : H →L[𝕜] H) (hT : IsTraceClass T)
    (P : ℕ → H →L[𝕜] H) (M : ℝ) (hM : ∀ n, ‖P n‖ ≤ M)
    (hP : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)) :
    Tendsto (fun n => trace ((P n).comp T)) atTop (𝓝 (trace T)) := by
  obtain ⟨S⟩ := CompactSpectral.SingularExpansion.compact_singular_system 𝕜 H H T hT.1
  have hs := (singularSystem_sum 𝕜 H H T hT S).1
  have hp (n : ℕ) (j : S.Index) : ‖P n (S.leftVector j)‖ ≤ M := by
    calc
      _ ≤ ‖P n‖ * ‖S.leftVector j‖ := (P n).le_opNorm _
      _ = ‖P n‖ := by rw [S.left_orthonormal.norm_eq_one j, mul_one]
      _ ≤ M := hM n
  have htrace (n : ℕ) : trace ((P n).comp T) =
      ∑' j, (S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) (P n (S.leftVector j)) := by
    apply TraceIdeals.TraceBasisCyclicity.trace_of_expansion ((P n).comp T)
      S.sigma (fun j => P n (S.leftVector j)) S.rightVector
      (fun j => (S.positive j).le) hs ((M ^ 2 + 1) / 2)
    · intro j
      rw [S.right_orthonormal.norm_eq_one j]
      have hMj : 0 ≤ M := (norm_nonneg _).trans (hp n j)
      nlinarith [sq_le_sq₀ (norm_nonneg (P n (S.leftVector j))) hMj |>.mpr (hp n j)]
    · intro x
      simpa only [ContinuousLinearMap.comp_apply, map_smul] using (S.expansion x).mapL (P n)
  have htraceT : trace T =
      ∑' j, (S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) (S.leftVector j) := by
    apply TraceIdeals.TraceBasisCyclicity.trace_of_expansion T S.sigma S.leftVector S.rightVector
      (fun j => (S.positive j).le) hs 1
    · intro j
      rw [S.left_orthonormal.norm_eq_one j, S.right_orthonormal.norm_eq_one j]
      norm_num
    · exact S.expansion
  simp_rw [htrace, htraceT]
  apply tendsto_tsum_of_dominated_convergence (hs.mul_right M)
  · intro j
    exact tendsto_const_nhds.mul (tendsto_const_nhds.inner (hP (S.leftVector j)))
  · apply Eventually.of_forall
    intro n j
    rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (S.positive j).le]
    apply mul_le_mul_of_nonneg_left _ (S.positive j).le
    calc
      _ ≤ ‖S.rightVector j‖ * ‖P n (S.leftVector j)‖ := norm_inner_le_norm _ _
      _ ≤ M := by rw [S.right_orthonormal.norm_eq_one j, one_mul]; exact hp n j

theorem strong_trace_limit : Spec.StrongTraceLimit.{v} := by
  intro 𝕜 _ H _ _ _ T hT P M hM hP
  exact trace_tendsto_comp_of_strong T hT P M hM hP

/-- Uniformly bounded convergence on a dense range extends to all vectors. -/
lemma strong_tendsto_of_dense_range
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {A : Type*} (f : A → H) (hf : DenseRange f)
    (P : ℕ → H →L[𝕜] H) (hbound : ∀ n, ‖P n‖ ≤ 1)
    (hP : ∀ a, Tendsto (fun n => P n (f a)) atTop (𝓝 (f a))) :
    ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x) := by
  intro x
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨a, ha⟩ := hf.exists_dist_lt x (show 0 < ε / 4 by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hP a) (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm] at ha ⊢
  have he : ‖P n (f a) - f a‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN n hn
  have hp : ‖P n (x - f a)‖ ≤ ‖x - f a‖ :=
    ((P n).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hbound n))
  calc
    ‖P n x - x‖ = ‖P n (x - f a) + (P n (f a) - f a) + (f a - x)‖ := by
      congr 1
      rw [map_sub]
      abel
    _ ≤ ‖P n (x - f a)‖ + ‖P n (f a) - f a‖ + ‖f a - x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < ε := by rw [norm_sub_rev (f a) x]; linarith

section FinitePartitions
open Set
theorem exists_finite_small_measurable_partition {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (A : Fin n → Set Q),
      (∀ i, MeasurableSet (A i)) ∧ _root_.Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = univ ∧
      (∀ i (x : Q), x ∈ A i → ∀ y ∈ A i, dist x y < ε) := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := finite_cover_balls_of_compact
    (s := (univ : Set Q)) isCompact_univ (half_pos hε)
  letI : Fintype t := ht.fintype
  let c : Fin (Fintype.card t) → Q := fun i => ((Fintype.equivFin t).symm i).val
  let B : Fin (Fintype.card t) → Set Q := fun i => Metric.ball (c i) (ε / 2)
  have hB : ⋃ i, B i = univ := by
    apply Subset.antisymm (subset_univ _)
    intro x hx
    rcases mem_iUnion₂.mp (hcover hx) with ⟨y, hy, hxy⟩
    exact mem_iUnion.mpr ⟨(Fintype.equivFin t) ⟨y, hy⟩, by simpa [B, c] using hxy⟩
  refine ⟨Fintype.card t, disjointed B, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [disjointed_eq_inter_compl]
    exact Metric.isOpen_ball.measurableSet.inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => Metric.isOpen_ball.measurableSet.compl)
  · exact disjoint_disjointed B
  · simpa [iUnion_disjointed] using hB
  · intro i x hx y hy
    have hx' := disjointed_subset B i hx
    have hy' := disjointed_subset B i hy
    have hx'' : dist x (c i) < ε/2 := hx'
    have hy'' : dist (c i) y < ε/2 := by simpa [B, Metric.mem_ball, dist_comm] using hy'
    linarith [dist_triangle x (c i) y]


theorem discard_null_cells {Q : Type u} [MeasurableSpace Q]
    (μ : Measure Q) (n : ℕ) (A : Fin n → Set Q)
    (hA : ∀ i, MeasurableSet (A i))
    (hd : _root_.Pairwise (fun i j => Disjoint (A i) (A j)))
    (hc : (⋃ i, A i) = univ) :
    ∃ (m : ℕ) (C : Fin m → Set Q),
      (∀ i, MeasurableSet (C i)) ∧
      _root_.Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ i, μ (C i) ≠ 0) ∧
      (∀ᵐ x ∂μ, ∃ i, x ∈ C i) ∧
      (∀ i, ∃ j, C i = A j) := by
  classical
  let I := {i : Fin n // μ (A i) ≠ 0}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let C : Fin (Fintype.card I) → Set Q := fun i => A (e i).val
  refine ⟨Fintype.card I, C, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hA (e i).val
  · intro i j hij
    apply hd
    intro heq
    exact hij (e.injective (Subtype.ext heq))
  · exact fun i => (e i).property
  · have hn : μ (⋃ i : {i : Fin n // μ (A i) = 0}, A i.val) = 0 :=
      measure_iUnion_null fun i => i.property
    have ha : ∀ᵐ x ∂μ, x ∉ ⋃ i : {i : Fin n // μ (A i) = 0}, A i.val := by
      rw [ae_iff]
      simpa only [not_not, setOf_mem_eq] using hn
    filter_upwards [ha] with x hx
    obtain ⟨i, hi⟩ : ∃ i, x ∈ A i := mem_iUnion.mp (by rw [hc]; exact mem_univ x)
    have hi' : μ (A i) ≠ 0 := by
      intro hz
      exact hx (mem_iUnion.mpr ⟨⟨i, hz⟩, hi⟩)
    exact ⟨e.symm ⟨i, hi'⟩, by simpa [C] using hi⟩
  · exact fun i => ⟨(e i).val, rfl⟩

/-- Finite measurable conull partitions of arbitrarily small mesh, with all null
cells discarded. It also handles empty spaces and zero measures. -/
theorem exists_finite_positive_small_partition {Q : Type u}
    [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (A : Fin n → Set Q),
      (∀ i, MeasurableSet (A i)) ∧
      _root_.Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ i, μ (A i) ≠ 0) ∧
      (∀ᵐ x ∂μ, ∃ i, x ∈ A i) ∧
      (∀ i (x : Q), x ∈ A i → ∀ y ∈ A i, dist x y < ε) := by
  obtain ⟨n, A, hA, hd, hc, hm⟩ := exists_finite_small_measurable_partition (Q := Q) ε hε
  obtain ⟨m, C, hC, hdC, hpC, hcC, hsC⟩ := discard_null_cells μ n A hA hd hc
  refine ⟨m, C, hC, hdC, hpC, hcC, ?_⟩
  intro i x hx y hy
  obtain ⟨j, hj⟩ := hsC i
  rw [hj] at hx hy
  exact hm j x hx y hy

theorem exists_finite_positive_partition_sequence {Q : Type u}
    [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
    (μ : Measure Q) :
    ∃ (N : ℕ → ℕ) (A : ∀ n, Fin (N n) → Set Q),
      (∀ n i, MeasurableSet (A n i)) ∧
      (∀ n, _root_.Pairwise (fun i j => Disjoint (A n i) (A n j))) ∧
      (∀ n i, μ (A n i) ≠ 0) ∧
      (∀ n, ∀ᵐ x ∂μ, ∃ i, x ∈ A n i) ∧
      (∀ n i (x : Q), x ∈ A n i → ∀ y ∈ A n i,
        dist x y < 1 / ((n : ℝ) + 1)) := by
  have h : ∀ n : ℕ, ∃ (m : ℕ) (A : Fin m → Set Q),
      (∀ i, MeasurableSet (A i)) ∧
      _root_.Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ i, μ (A i) ≠ 0) ∧
      (∀ᵐ x ∂μ, ∃ i, x ∈ A i) ∧
      (∀ i (x : Q), x ∈ A i → ∀ y ∈ A i,
        dist x y < 1 / ((n : ℝ) + 1)) := fun n =>
    exists_finite_positive_small_partition μ (1 / ((n : ℝ) + 1)) (by positivity)
  choose N A hA hd hp hc hm using h
  exact ⟨N, A, hA, hd, hp, hc, hm⟩

end FinitePartitions

section FiniteAveraging
variable {Q : Type u} [MeasurableSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]

def cellVector (C : Set Q) (hC : MeasurableSet C) : Lp ℂ 2 μ :=
  indicatorConstLp 2 hC (measure_ne_top μ C) (((Real.sqrt (μ.real C))⁻¹ : ℝ) : ℂ)

lemma cellVector_ae (C : Set Q) (hC : MeasurableSet C) :
    (cellVector μ C hC : Q → ℂ) =ᵐ[μ]
      C.indicator (fun _ => (((Real.sqrt (μ.real C))⁻¹ : ℝ) : ℂ)) :=
  indicatorConstLp_coeFn

lemma cellVectors_orthonormal {ι : Type*} (C : ι → Set Q)
    (hC : ∀ i, MeasurableSet (C i)) (hpos : ∀ i, μ (C i) ≠ 0)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j))) :
    Orthonormal ℂ (fun i => cellVector μ (C i) (hC i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [cellVector, cellVector, L2.inner_indicatorConstLp_indicatorConstLp]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, Set.inter_self]
    have hm : 0 < μ.real (C i) := ENNReal.toReal_pos (hpos i) (measure_ne_top μ _)
    have hs : Real.sqrt (μ.real (C i)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hm)
    simp only [RCLike.inner_apply, Complex.conj_ofReal, Complex.real_smul]
    have hsq := Real.sq_sqrt hm.le
    norm_cast
    field_simp
    nlinarith
  · rw [if_neg hij, Set.disjoint_iff_inter_eq_empty.mp (hdisj hij)]
    simp

section AbstractProjection
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]
variable {ι : Type*} [Fintype ι]

def cellProjection (b : ι → H) : H →L[𝕜] H := ∑ i, rankOne (b i) (b i)

lemma cellProjection_apply (b : ι → H) (x : H) :
    cellProjection (𝕜 := 𝕜) b x = ∑ i, inner 𝕜 (b i) x • b i := by
  simp [cellProjection, rankOne, TraceIdeals.TraceClassDefinitions.Spec.RankOneValue]

lemma cellProjection_fix_sum (b : ι → H) (hb : Orthonormal 𝕜 b) (c : ι → 𝕜) :
    cellProjection (𝕜 := 𝕜) b (∑ i, c i • b i) = ∑ i, c i • b i := by
  simp only [cellProjection_apply, hb.inner_right_fintype]

lemma cellProjection_norm_apply_le (b : ι → H) (hb : Orthonormal 𝕜 b) (x : H) :
    ‖cellProjection (𝕜 := 𝕜) b x‖ ≤ ‖x‖ := by
  have hnorm : ‖cellProjection (𝕜 := 𝕜) b x‖ ^ 2 = ∑ i, ‖inner 𝕜 (b i) x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner 𝕜, cellProjection_apply]
    simp only [sum_inner, inner_smul_left, hb.inner_right_fintype, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [RCLike.conj_mul]
    simp
  have hle := hb.sum_inner_products_le x (s := Finset.univ)
  nlinarith [norm_nonneg x, norm_nonneg (cellProjection (𝕜 := 𝕜) b x)]

lemma cellProjection_norm_le (b : ι → H) (hb : Orthonormal 𝕜 b) :
    ‖cellProjection (𝕜 := 𝕜) b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using cellProjection_norm_apply_le b hb x

lemma cellProjection_approx (b : ι → H) (hb : Orthonormal 𝕜 b) (c : ι → 𝕜) (x : H) :
    ‖cellProjection (𝕜 := 𝕜) b x - x‖ ≤ 2 * ‖x - ∑ i, c i • b i‖ := by
  let g := ∑ i, c i • b i
  calc
    ‖cellProjection (𝕜 := 𝕜) b x - x‖ = ‖cellProjection (𝕜 := 𝕜) b (x-g) + (g-x)‖ := by
      congr 1
      rw [map_sub, cellProjection_fix_sum b hb]
      abel
    _ ≤ ‖cellProjection (𝕜 := 𝕜) b (x-g)‖ + ‖g-x‖ := norm_add_le _ _
    _ ≤ 2 * ‖x-g‖ := by
      rw [norm_sub_rev g x]
      have hh := cellProjection_norm_apply_le b hb (x-g)
      linarith
end AbstractProjection

section StepApproximation
variable {ι : Type*} [Fintype ι]

lemma cellStep_ae (C : ι → Set Q) (hC : ∀ i, MeasurableSet (C i))
    (hpos : ∀ i, μ (C i) ≠ 0) (v : ι → ℂ) :
    (((∑ i, (v i * (Real.sqrt (μ.real (C i)) : ℂ)) • cellVector μ (C i) (hC i)) : Lp ℂ 2 μ) : Q → ℂ)
      =ᵐ[μ] fun x => ∑ i, (C i).indicator (fun _ => v i) x := by
  have hb := ae_all_iff.2 (fun i => cellVector_ae μ (C i) (hC i))
  have hs := ae_all_iff.2 (fun i => Lp.coeFn_smul
    (v i * (Real.sqrt (μ.real (C i)) : ℂ)) (cellVector μ (C i) (hC i)))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i => (v i * (Real.sqrt (μ.real (C i)) : ℂ)) • cellVector μ (C i) (hC i)), hb, hs]
      with x hx hxB hxS
  rw [hx]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hxS i]
  dsimp only [Pi.smul_apply, smul_eq_mul]
  rw [hxB i]
  by_cases hxi : x ∈ C i
  · rw [Set.indicator_of_mem hxi, Set.indicator_of_mem hxi]
    have hm : 0 < μ.real (C i) := ENNReal.toReal_pos (hpos i) (measure_ne_top μ _)
    have hsqrt : (Real.sqrt (μ.real (C i)) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hm).ne'
    simp only [Complex.ofReal_inv]
    field_simp
  · simp [hxi]

lemma cellProjection_approx_of_oscillation (C : ι → Set Q)
    (hC : ∀ i, MeasurableSet (C i)) (hpos : ∀ i, μ (C i) ≠ 0)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : ∀ᵐ x ∂μ, ∃ i, x ∈ C i)
    (f : Lp ℂ 2 μ) (f₀ : Q → ℂ) (hf : (f : Q → ℂ) =ᵐ[μ] f₀)
    (v : ι → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hosc : ∀ i x, x ∈ C i → ‖f₀ x - v i‖ ≤ δ) :
    ‖cellProjection (𝕜 := ℂ) (fun i => cellVector μ (C i) (hC i)) f - f‖ ≤
      2 * ((measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * δ) := by
  classical
  let c : ι → ℂ := fun i => v i * (Real.sqrt (μ.real (C i)) : ℂ)
  let g : Lp ℂ 2 μ := ∑ i, c i • cellVector μ (C i) (hC i)
  have hstep := cellStep_ae μ C hC hpos v
  have hbound : ‖f-g‖ ≤ (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * δ := by
    apply Lp.norm_le_of_ae_bound hδ
    filter_upwards [Lp.coeFn_sub f g, hf, hstep, hcover] with x hx hxf hxg hxc
    rw [hx]
    change ‖f x - g x‖ ≤ δ
    rw [hxf, hxg]
    obtain ⟨i, hi⟩ := hxc
    have hsum : (∑ j, (C j).indicator (fun _ => v j) x) = v i := by
      rw [Finset.sum_eq_single i]
      · exact Set.indicator_of_mem hi _
      · intro j _ hji
        have hj : x ∉ C j := fun hxj => Set.disjoint_left.mp (hdisj hji) hxj hi
        exact Set.indicator_of_notMem hj _
      · simp
    rw [hsum]
    exact hosc i x hi
  exact (cellProjection_approx _ (cellVectors_orthonormal μ C hC hpos hdisj) c f).trans
    (mul_le_mul_of_nonneg_left hbound (by norm_num))
end StepApproximation

section ContinuousApproximation
open Filter
variable [MetricSpace Q] [CompactSpace Q] [BorelSpace Q]

lemma cellProjection_tendsto_continuous
    (N : ℕ → ℕ) (C : (n : ℕ) → Fin (N n) → Set Q)
    (hC : ∀ n i, MeasurableSet (C n i))
    (hpos : ∀ n i, μ (C n i) ≠ 0)
    (hdisj : ∀ n, Pairwise (fun i j => Disjoint (C n i) (C n j)))
    (hcover : ∀ n, ∀ᵐ x ∂μ, ∃ i, x ∈ C n i)
    (hmesh : ∀ ε > 0, ∀ᶠ n in atTop, ∀ i x, x ∈ C n i →
      ∀ y ∈ C n i, dist x y < ε)
    (f : C(Q, ℂ)) :
    Tendsto (fun n => cellProjection (𝕜 := ℂ)
      (fun i => cellVector μ (C n i) (hC n i)) (ContinuousMap.toLp 2 μ ℂ f))
      atTop (𝓝 (ContinuousMap.toLp 2 μ ℂ f)) := by
  classical
  let a : (n : ℕ) → Fin (N n) → Q := fun n i =>
    Classical.choose (nonempty_of_measure_ne_zero (hpos n i))
  have ha (n : ℕ) (i : Fin (N n)) : a n i ∈ C n i :=
    Classical.choose_spec (nonempty_of_measure_ne_zero (hpos n i))
  let B : ℝ := (measureUnivNNReal μ : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹
  have hB : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η := ε / (2 * (B + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous f.continuous) η hη
  filter_upwards [hmesh δ hδ] with n hn
  have hosc (i : Fin (N n)) (x : Q) (hx : x ∈ C n i) :
      ‖f x - f (a n i)‖ ≤ η := by
    exact le_of_lt (by simpa only [dist_eq_norm] using huc (hn i x hx (a n i) (ha n i)))
  have hh := cellProjection_approx_of_oscillation μ (C n) (hC n) (hpos n) (hdisj n)
    (hcover n) (ContinuousMap.toLp 2 μ ℂ f) f (ContinuousMap.coeFn_toLp μ f)
    (fun i => f (a n i)) η hη.le hosc
  rw [dist_eq_norm]
  apply hh.trans_lt
  change 2 * (B * η) < ε
  have heq : 2 * ((B + 1) * η) = ε := by dsimp [η]; field_simp
  nlinarith
end ContinuousApproximation

end FiniteAveraging

section CellSums
lemma sum_cell_integral {Q : Type u} [MeasurableSpace Q] (μ : Measure Q)
    {ι : Type*} [Fintype ι] (C : ι → Set Q) (hm : ∀ i, MeasurableSet (C i))
    (hd : Pairwise (fun i j => Disjoint (C i) (C j))) (hc : ∀ᵐ x ∂μ, ∃ i, x ∈ C i)
    {f : Q → ℂ} (hf : Integrable f μ) :
    (∑ i, ∫ x in C i, f x ∂μ) = ∫ x, f x ∂μ := by
  rw [← integral_iUnion_fintype hm hd (fun i => hf.integrableOn)]
  rw [Measure.restrict_eq_self_of_ae_mem]
  simpa only [Set.mem_iUnion] using hc

lemma sum_cell_mass {Q : Type u} [MeasurableSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    {ι : Type*} [Fintype ι] (C : ι → Set Q) (hm : ∀ i, MeasurableSet (C i))
    (hd : Pairwise (fun i j => Disjoint (C i) (C j))) (hc : ∀ᵐ x ∂μ, ∃ i, x ∈ C i) :
    (∑ i, μ.real (C i)) = μ.real Set.univ := by
  rw [← measureReal_iUnion_fintype hd hm]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hc] with x hx
  simp only [Set.mem_iUnion, Set.mem_univ]
  exact eq_true hx

lemma sum_cell_error {Q : Type u} [MeasurableSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    {ι : Type*} [Fintype ι] (C : ι → Set Q) (hm : ∀ i, MeasurableSet (C i))
    (hd : Pairwise (fun i j => Disjoint (C i) (C j))) (hc : ∀ᵐ x ∂μ, ∃ i, x ∈ C i)
    {f : Q → ℂ} (hf : Integrable f μ) (a : ι → ℂ) (δ : ℝ)
    (ha : ∀ i, ‖a i - ∫ x in C i, f x ∂μ‖ ≤ δ * μ.real (C i)) :
    ‖(∑ i, a i) - ∫ x, f x ∂μ‖ ≤ δ * μ.real Set.univ := by
  rw [← sum_cell_integral μ C hm hd hc hf, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖a i - ∫ x in C i, f x ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ i, δ * μ.real (C i) := Finset.sum_le_sum (fun i _ => ha i)
    _ = _ := by rw [← Finset.mul_sum, sum_cell_mass μ C hm hd hc]

end CellSums

section CellKernel
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
variable (μ : Measure Q) [IsFiniteMeasure μ]

lemma indicator_kernel_coefficient (k : C(Q × Q, ℂ)) (s : Set Q)
    (hs : MeasurableSet s) (c : ℝ) (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hK : ∀ f : Lp ℂ 2 μ, (K f : Q → ℂ) =ᵐ[μ]
      fun x => ∫ y, k (x, y) * f y ∂μ) :
    let b := indicatorConstLp 2 hs (measure_ne_top μ s) (c : ℂ)
    inner ℂ b (K b) = (c : ℂ) ^ 2 * ∫ x in s, ∫ y in s, k (x,y) ∂μ ∂μ := by
  dsimp only
  rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
  calc
    _ = ∫ x in s, (c : ℂ) * (∫ y, k (x,y) *
        indicatorConstLp 2 hs (measure_ne_top μ s) (c : ℂ) y ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (hK (indicatorConstLp 2 hs (measure_ne_top μ s) (c : ℂ)))] with x hx
      simp [hx, mul_comm]
    _ = ∫ x in s, (c : ℂ) * ((∫ y in s, k (x,y) ∂μ) * c) ∂μ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      apply congrArg ((c : ℂ) * ·)
      rw [← integral_mul_const]
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [@indicatorConstLp_coeFn Q ℂ _ 2 μ _ s hs (measure_ne_top μ s) (c : ℂ)] with y hy
      rw [hy]
      by_cases hy' : y ∈ s <;> simp [hy']
    _ = (c : ℂ)^2 * ∫ x in s, ∫ y in s, k (x,y) ∂μ ∂μ := by
      calc
        _ = ∫ x in s, (c : ℂ)^2 * (∫ y in s, k (x,y) ∂μ) ∂μ := by
          congr 1
          ext x
          ring
        _ = _ := integral_const_mul _ _

lemma normalized_indicator_kernel_coefficient (k : C(Q × Q, ℂ)) (s : Set Q)
    (hs : MeasurableSet s) (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hK : ∀ f : Lp ℂ 2 μ, (K f : Q → ℂ) =ᵐ[μ]
      fun x => ∫ y, k (x, y) * f y ∂μ) :
    let b := indicatorConstLp 2 hs (measure_ne_top μ s)
      (((Real.sqrt (μ.real s))⁻¹ : ℝ) : ℂ)
    inner ℂ b (K b) = ((μ.real s)⁻¹ : ℂ) *
      ∫ x in s, ∫ y in s, k (x,y) ∂μ ∂μ := by
  dsimp only
  rw [indicator_kernel_coefficient μ k s hs _ K hK]
  congr 1
  rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt (measureReal_nonneg)]
  simp

lemma kernel_cell_error (k : C(Q × Q, ℂ)) (s : Set Q)
    (hs : MeasurableSet s) (hspos : μ s ≠ 0) (δ : ℝ)
    (hδ : ∀ x ∈ s, ∀ y ∈ s, ‖k (x,y) - k (x,x)‖ ≤ δ)
    (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hK : ∀ f : Lp ℂ 2 μ, (K f : Q → ℂ) =ᵐ[μ]
      fun x => ∫ y, k (x, y) * f y ∂μ) :
    let b := indicatorConstLp 2 hs (measure_ne_top μ s)
      (((Real.sqrt (μ.real s))⁻¹ : ℝ) : ℂ)
    ‖inner ℂ b (K b) - ∫ x in s, k (x,x) ∂μ‖ ≤ δ * μ.real s := by
  dsimp only
  rw [normalized_indicator_kernel_coefficient μ k s hs K hK]
  have ha : 0 < μ.real s := ENNReal.toReal_pos hspos (measure_ne_top μ s)
  have hai : 0 ≤ (μ.real s)⁻¹ := inv_nonneg.mpr ha.le
  have hprod : Integrable (fun p : Q × Q => k p) ((μ.restrict s).prod (μ.restrict s)) :=
    (ContinuousMap.memLp (p := 1) _ ℂ k).integrable le_rfl
  have hf := hprod.integral_prod_left
  have hg : Integrable (fun x => k (x,x)) (μ.restrict s) :=
    (ContinuousMap.memLp (p := 1) _ ℂ
      ⟨fun x => k (x,x), k.continuous.comp (continuous_id.prodMk continuous_id)⟩).integrable le_rfl
  rw [← integral_const_mul, ← integral_sub (hf.const_mul _) hg]
  have hmass : (μ.restrict s).real Set.univ = μ.real s := by
    simp only [Measure.real, Measure.restrict_apply_univ]
  conv_rhs => rw [← hmass]
  apply norm_integral_le_of_norm_le_const
  rw [ae_restrict_iff' hs]
  apply Eventually.of_forall
  intro x hx
  have hkx : Integrable (fun y => k (x,y)) (μ.restrict s) :=
    (ContinuousMap.memLp (p := 1) _ ℂ
      ⟨fun y => k (x,y), k.continuous.comp (continuous_const.prodMk continuous_id)⟩).integrable le_rfl
  have hpoint : ((μ.real s)⁻¹ : ℂ) * (∫ y in s, k (x,y) ∂μ) - k (x,x) =
      ((μ.real s)⁻¹ : ℂ) * (∫ y in s, k (x,y) - k (x,x) ∂μ) := by
    rw [integral_sub hkx (integrable_const _), integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, Complex.real_smul]
    rw [mul_sub]
    congr 1
    rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    change k (x,x) = (((μ.real s)⁻¹ * μ.real s : ℝ) : ℂ) * k (x,x)
    rw [inv_mul_cancel₀ ha.ne', Complex.ofReal_one, one_mul]
  change ‖((μ.real s)⁻¹ : ℂ) * (∫ y in s, k (x,y) ∂μ) - k (x,x)‖ ≤ δ
  rw [hpoint, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  calc
    _ ≤ (μ.real s)⁻¹ * (δ * (μ.restrict s).real Set.univ) := by
      apply mul_le_mul_of_nonneg_left _ hai
      apply norm_integral_le_of_norm_le_const
      rw [ae_restrict_iff' hs]
      exact Eventually.of_forall (fun y hy => hδ x hx y hy)
    _ = δ := by
      simp only [Measure.real, Measure.restrict_apply_univ]
      change (μ.real s)⁻¹ * (δ * μ.real s) = δ
      field_simp

end CellKernel

theorem eventually_cell_oscillation {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    {ι : ℕ → Type v} (A : ∀ n, ι n → Set Q)
    (hm : ∀ n i (x : Q), x ∈ A n i → ∀ y ∈ A n i,
      dist x y < 1 / ((n : ℝ) + 1))
    (f : C(Q, ℂ)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ i (x : Q), x ∈ A n i → ∀ y ∈ A n i, ‖f x - f y‖ < δ := by
  obtain ⟨η, hη, hf⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous) δ hδ
  have he : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < η :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hη)
  filter_upwards [he] with n hn
  intro i x hx y hy
  simpa only [dist_eq_norm] using hf ((hm n i x hx y hy).trans hn)

theorem eventually_kernel_cell_oscillation {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    {ι : ℕ → Type v} (A : ∀ n, ι n → Set Q)
    (hm : ∀ n i (x : Q), x ∈ A n i → ∀ y ∈ A n i,
      dist x y < 1 / ((n : ℝ) + 1))
    (k : C(Q × Q, ℂ)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ i (x : Q), x ∈ A n i → ∀ y ∈ A n i,
      ‖k (x, y) - k (x, x)‖ < δ := by
  obtain ⟨η, hη, hk⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous k.continuous) δ hδ
  have he : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < η :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hη)
  filter_upwards [he] with n hn
  intro i x hx y hy
  have hd : dist (x, y) (x, x) < η := by
    simpa only [dist_prod_same_left, dist_comm] using (hm n i x hx y hy).trans hn
  simpa only [dist_eq_norm] using hk hd

theorem eventually_cell_mesh {Q : Type u} [MetricSpace Q]
    {ι : ℕ → Type v} (A : ∀ n, ι n → Set Q)
    (hm : ∀ n i (x : Q), x ∈ A n i → ∀ y ∈ A n i,
      dist x y < 1 / ((n : ℝ) + 1)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i (x : Q), x ∈ A n i → ∀ y ∈ A n i,
      dist x y < ε := by
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hε)
  filter_upwards [he] with n hn
  exact fun i x hx y hy => (hm n i x hx y hy).trans hn

section KernelLimit
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]
variable (μ : Measure Q) [IsFiniteMeasure μ]

lemma kernel_cell_sum_tendsto {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (C : ∀ n, ι n → Set Q) (hm : ∀ n i, MeasurableSet (C n i))
    (hd : ∀ n, Pairwise (fun i j => Disjoint (C n i) (C n j)))
    (hp : ∀ n i, μ (C n i) ≠ 0)
    (hc : ∀ n, ∀ᵐ x ∂μ, ∃ i, x ∈ C n i)
    (hmesh : ∀ n i (x : Q), x ∈ C n i → ∀ y ∈ C n i,
      dist x y < 1 / ((n : ℝ) + 1))
    (k : C(Q × Q, ℂ)) (K : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hK : ∀ f : Lp ℂ 2 μ, (K f : Q → ℂ) =ᵐ[μ]
      fun x => ∫ y, k (x, y) * f y ∂μ) :
    Tendsto (fun n => ∑ i, inner ℂ (cellVector μ (C n i) (hm n i))
      (K (cellVector μ (C n i) (hm n i)))) atTop (𝓝 (∫ x, k (x,x) ∂μ)) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hmass : 0 ≤ μ.real Set.univ := measureReal_nonneg
  let δ : ℝ := ε / (μ.real Set.univ + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have he := eventually_kernel_cell_oscillation C hmesh k δ hδ
  filter_upwards [he] with n hn
  rw [dist_eq_norm]
  have hg : Integrable (fun x => k (x,x)) μ :=
    (ContinuousMap.memLp (p := 1) _ ℂ
      ⟨fun x => k (x,x), k.continuous.comp (continuous_id.prodMk continuous_id)⟩).integrable le_rfl
  calc
    _ ≤ δ * μ.real Set.univ := by
      apply sum_cell_error μ
        (C n) (hm n) (hd n) (hc n) hg _ δ
      intro i
      simpa only [cellVector] using kernel_cell_error μ k (C n i) (hm n i)
        (hp n i) δ (fun x hx y hy => (hn i x hx y hy).le) K hK
    _ < δ * (μ.real Set.univ + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ ε (by linarith)

end KernelLimit

section Restriction
variable {X : Type u} [MeasurableSpace X] (μ : Measure X) {s : Set X}

/-- Inclusion of a measurable conull set preserves the measure pulled back to
that subtype, including when the measure and subtype are both empty. -/
lemma subtype_measurePreserving (hs : MeasurableSet s) (hconull : s ∈ ae μ) :
    MeasurePreserving (Subtype.val : s → X) (μ.comap Subtype.val) μ :=
  ⟨measurable_subtype_coe,
    (map_comap_subtype_coe hs μ).trans (Measure.restrict_eq_self_of_ae_mem hconull)⟩

/-- Restriction to a measurable conull set is a unitary of the ordinary L²
spaces. Surjectivity is proved by measurable extension, so neither nonempty
support nor a choice of a point outside the support is needed. -/
def conullRestrictionUnitary (hs : MeasurableSet s) (hconull : s ∈ ae μ) :
    Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.comap (Subtype.val : s → X)) := by
  let hm := subtype_measurePreserving μ hs hconull
  let L := Lp.compMeasurePreservingₗᵢ (p := 2) (E := ℂ) ℂ (Subtype.val : s → X) hm
  apply LinearIsometryEquiv.ofSurjective L
  intro g
  obtain ⟨f, hf, hfg⟩ := (MeasurableEmbedding.subtype_coe hs).exists_stronglyMeasurable_extend
    (Lp.stronglyMeasurable g) (fun _ => inferInstance)
  have hmem : MemLp f 2 μ := by
    rw [← hm.map_eq]
    apply (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff.mpr
    rw [hfg]
    exact Lp.memLp g
  refine ⟨hmem.toLp f, ?_⟩
  apply Lp.ext
  have hh := Lp.coeFn_compMeasurePreserving (hmem.toLp f) hm
  have heq := hm.quasiMeasurePreserving.ae_eq hmem.coeFn_toLp
  filter_upwards [hh, heq] with x hx hx'
  exact hx.trans (hx'.trans (congrFun hfg x))

lemma conullRestrictionUnitary_ae (hs : MeasurableSet s) (hconull : s ∈ ae μ)
    (f : Lp ℂ 2 μ) :
    (conullRestrictionUnitary μ hs hconull f : s → ℂ) =ᵐ[μ.comap Subtype.val]
      fun x => f x.val :=
  Lp.coeFn_compMeasurePreserving f (subtype_measurePreserving μ hs hconull)

end Restriction

section UnitaryTrace
variable {K : Type w} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

lemma trace_of_unitary_intertwining (U : H ≃ₗᵢ[𝕜] K)
    (T : H →L[𝕜] H) (R : K →L[𝕜] K) (hT : IsTraceClass T)
    (h : U.toContinuousLinearEquiv.toContinuousLinearMap.comp T =
      R.comp U.toContinuousLinearEquiv.toContinuousLinearMap) :
    IsTraceClass R ∧ trace T = trace R := by
  let A := U.toContinuousLinearEquiv.toContinuousLinearMap
  let B := U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hR : R = A.comp (T.comp B) := by
    ext x
    have hh := congrArg (fun F : H →L[𝕜] K => F (U.symm x)) h
    simpa [A, B] using hh.symm
  have hTB : IsTraceClass (T.comp B) := by
    simpa only [ContinuousLinearMap.id_comp] using
      (TraceIdeals.TraceNormIdeal.two_sided_ideal 𝕜 H H K H T
        (ContinuousLinearMap.id 𝕜 H) B hT).1
  have hc := TraceIdeals.TraceBasisCyclicity.rectangular_cyclicity 𝕜 K H
    (T.comp B) A (Or.inl hTB)
  have hback : (T.comp B).comp A = T := by ext x; simp [A, B]
  rw [← hR, hback] at hc
  exact ⟨hc.1, hc.2.2.symm⟩

lemma trace_finite_projection {ι : Type*} [Fintype ι] (b : ι → H)
    (hb : Orthonormal 𝕜 b) (T : H →L[𝕜] H) :
    trace ((∑ i, rankOne (b i) (b i)).comp T) =
      ∑ i, inner 𝕜 (b i) (T (b i)) := by
  have ht : trace ((∑ i, rankOne (b i) (b i)).comp T) =
      ∑' i, ((1 : ℝ) : 𝕜) * inner 𝕜 (T.adjoint (b i)) (b i) := by
    apply TraceIdeals.TraceBasisCyclicity.trace_of_expansion
      ((∑ i, rankOne (b i) (b i)).comp T)
      (fun _ => 1) b (fun i => T.adjoint (b i)) (fun _ => zero_le_one)
      Summable.of_finite ((1 + ‖T.adjoint‖ ^ 2) / 2)
    · intro i
      have hi := T.adjoint.le_opNorm (b i)
      rw [hb.norm_eq_one i, mul_one] at hi
      rw [hb.norm_eq_one i]
      nlinarith [sq_le_sq₀ (norm_nonneg (T.adjoint (b i))) (norm_nonneg T.adjoint) |>.mpr hi]
    · intro x
      convert hasSum_fintype (fun i => (((1 : ℝ) : 𝕜) *
        inner 𝕜 (T.adjoint (b i)) x) • b i) using 1
      simp only [ContinuousLinearMap.comp_apply, sum_apply,
        rankOne, TraceIdeals.TraceClassDefinitions.Spec.RankOneValue, ContinuousLinearMap.smulRight_apply,
        innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left, RCLike.ofReal_one, one_mul]
  rw [ht, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.ofReal_one, one_mul, ContinuousLinearMap.adjoint_inner_left]

end UnitaryTrace

section Support
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q] [MeasurableSpace Q] [BorelSpace Q]

lemma support_measurePreserving (μ : Measure Q) :
    MeasurePreserving (Subtype.val : μ.support → Q) (μ.comap Subtype.val) μ :=
  subtype_measurePreserving μ μ.isClosed_support.measurableSet μ.support_mem_ae

lemma support_measure_isOpenPos (μ : Measure Q) :
    (μ.comap (Subtype.val : μ.support → Q)).IsOpenPosMeasure := by
  constructor
  intro V hV hne
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
  obtain ⟨x, hx⟩ := hne
  rw [← Measure.map_apply measurable_subtype_coe hW.measurableSet,
    (support_measurePreserving μ).map_eq]
  exact ((Measure.mem_support_iff_forall x.val).mp x.property W (hW.mem_nhds hx)).ne'

lemma continuousKernelOperator_ae (μ : Measure Q) [IsFiniteMeasure μ]
    (k : C(Q × Q, ℂ)) (f : Lp ℂ 2 μ) :
    (Spec.continuousKernelOperator μ k f : Q → ℂ) =ᵐ[μ]
      fun x => ∫ y, k (x, y) * f y ∂μ := by
  have hk : MemLp k 2 (μ.prod μ) := ContinuousMap.memLp (μ.prod μ) ℂ k
  have hkclass : hk.toLp k = ContinuousMap.toLp 2 (μ.prod μ) ℂ k := by
    apply Lp.ext
    exact hk.coeFn_toLp.trans (ContinuousMap.coeFn_toLp (μ.prod μ) k).symm
  have hh := PartV.L2Kernel.kernel_representative_formula μ μ k f hk (Lp.memLp f)
  simpa only [hkclass, Lp.toLp_coeFn] using hh

lemma support_kernel_intertwining (μ : Measure Q) [IsFiniteMeasure μ]
    (k : C(Q × Q, ℂ)) :
    let S := μ.support
    let ν : Measure S := μ.comap Subtype.val
    letI : CompactSpace S := isCompact_iff_compactSpace.mp μ.isClosed_support.isCompact
    let U := conullRestrictionUnitary μ μ.isClosed_support.measurableSet μ.support_mem_ae
    let kS : C(S × S, ℂ) :=
      k.comp ⟨fun p => (p.1.val, p.2.val),
        continuous_subtype_val.prodMap continuous_subtype_val⟩
    U.toContinuousLinearEquiv.toContinuousLinearMap.comp (Spec.continuousKernelOperator μ k) =
      (Spec.continuousKernelOperator ν kS).comp U.toContinuousLinearEquiv.toContinuousLinearMap := by
  dsimp only
  letI : CompactSpace μ.support := isCompact_iff_compactSpace.mp μ.isClosed_support.isCompact
  let ν : Measure μ.support := μ.comap Subtype.val
  let U := conullRestrictionUnitary μ μ.isClosed_support.measurableSet μ.support_mem_ae
  let kS : C(μ.support × μ.support, ℂ) :=
    k.comp ⟨fun p => (p.1.val, p.2.val),
      continuous_subtype_val.prodMap continuous_subtype_val⟩
  ext1 f
  apply Lp.ext
  have hleft := conullRestrictionUnitary_ae μ μ.isClosed_support.measurableSet
    μ.support_mem_ae (Spec.continuousKernelOperator μ k f)
  have hmid := (support_measurePreserving μ).quasiMeasurePreserving.ae_eq_comp
    (continuousKernelOperator_ae μ k f)
  have hright := continuousKernelOperator_ae ν kS (U f)
  filter_upwards [hleft, hmid, hright] with x hx₁ hx₂ hx₃
  change (U (Spec.continuousKernelOperator μ k f)) x =
    (Spec.continuousKernelOperator ν kS (U f)) x
  simp only [Function.comp_apply] at hx₂
  rw [hx₁, hx₂, hx₃]
  calc
    (∫ y, k (x.val, y) * f y ∂μ) = ∫ y : μ.support, k (x.val, y.val) * f y.val ∂ν :=
      ((support_measurePreserving μ).integral_comp
        (MeasurableEmbedding.subtype_coe μ.isClosed_support.measurableSet)
        (fun y => k (x.val, y) * f y)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [conullRestrictionUnitary_ae μ μ.isClosed_support.measurableSet
        μ.support_mem_ae f] with y hy
      change k (x.val, y.val) * f y.val = k (x.val, y.val) * (U f) y
      rw [hy]

end Support

/-- Restricting to the closed measure support preserves the actual kernel
operator, trace class, trace, and diagonal integral. -/
theorem support_reduction : Spec.SupportReduction.{u} := by
  intro Q _ _ _ _ μ _
  dsimp only
  letI : CompactSpace μ.support := isCompact_iff_compactSpace.mp μ.isClosed_support.isCompact
  refine ⟨μ.measure_compl_support, support_measure_isOpenPos μ, ?_⟩
  let U := conullRestrictionUnitary μ μ.isClosed_support.measurableSet μ.support_mem_ae
  refine ⟨U, fun f => conullRestrictionUnitary_ae μ μ.isClosed_support.measurableSet
    μ.support_mem_ae f, ?_⟩
  intro k
  refine ⟨support_kernel_intertwining μ k, ?_, ?_⟩
  · intro hT
    exact trace_of_unitary_intertwining U _ _ hT (support_kernel_intertwining μ k)
  · exact (support_measurePreserving μ).integral_comp
      (MeasurableEmbedding.subtype_coe μ.isClosed_support.measurableSet)
      (fun x => k (x, x))

/-- Once the full-support identity is proved, the support unitary establishes
the finite-Radon application with its original hypotheses. -/
theorem diagonalTrace_of_fullSupport : Spec.SupportTransfer.{u} := by
  intro hfull Q _ _ _ _ μ _ k hT
  letI : CompactSpace μ.support := isCompact_iff_compactSpace.mp μ.isClosed_support.isCompact
  rcases support_reduction Q μ with ⟨hnull, hpos, U, hU, hkernels⟩
  letI : (μ.comap (Subtype.val : μ.support → Q)).IsOpenPosMeasure := hpos
  rcases hkernels k with ⟨hinter, htrace, hdiag⟩
  rcases htrace hT with ⟨hrestricted, heq⟩
  exact heq.trans ((hfull μ.support (μ.comap Subtype.val) _ hrestricted).trans hdiag)

/-- The general clause of the diagonal trace theorem, without a positivity or
Hermitian assumption. Finite cell projections give the same scalar sequence
two limits: the operator trace and the integral of the continuous diagonal. -/
theorem fullSupport_diagonalTrace : Spec.FullSupportDiagonalTrace.{u} := by
  intro Q _ _ _ _ μ _ _ k hK
  obtain ⟨N, C, hm, hd, hp, hc, hmesh⟩ := exists_finite_positive_partition_sequence μ
  let b : (n : ℕ) → Fin (N n) → Lp ℂ 2 μ :=
    fun n i => cellVector μ (C n i) (hm n i)
  let P : ℕ → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := fun n => cellProjection (𝕜 := ℂ) (b n)
  have hb (n : ℕ) : Orthonormal ℂ (b n) :=
    cellVectors_orthonormal μ (C n) (hm n) (hp n) (hd n)
  have hbound (n : ℕ) : ‖P n‖ ≤ 1 := cellProjection_norm_le (b n) (hb n)
  have hcont (f : C(Q, ℂ)) :
      Tendsto (fun n => P n (ContinuousMap.toLp 2 μ ℂ f))
        atTop (𝓝 (ContinuousMap.toLp 2 μ ℂ f)) :=
    cellProjection_tendsto_continuous μ N C hm hp hd hc (eventually_cell_mesh C hmesh) f
  have hstrong : ∀ f, Tendsto (fun n => P n f) atTop (𝓝 f) :=
    strong_tendsto_of_dense_range (ContinuousMap.toLp 2 μ ℂ)
      (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num)) P hbound hcont
  have ht := trace_tendsto_comp_of_strong (Spec.continuousKernelOperator μ k) hK
    P 1 hbound hstrong
  have hi := kernel_cell_sum_tendsto μ C hm hd hp hc hmesh k
    (Spec.continuousKernelOperator μ k) (continuousKernelOperator_ae μ k)
  have heq (n : ℕ) : trace ((P n).comp (Spec.continuousKernelOperator μ k)) =
      ∑ i, inner ℂ (b n i) (Spec.continuousKernelOperator μ k (b n i)) :=
    trace_finite_projection (b n) (hb n) (Spec.continuousKernelOperator μ k)
  simp_rw [heq] at ht
  exact tendsto_nhds_unique ht hi

/-- For an arbitrary finite Radon measure, restrict to its closed support and
apply the full-support identity through the natural L² unitary. -/
theorem diagonal_trace : Spec.DiagonalTrace.{u} :=
  diagonalTrace_of_fullSupport fullSupport_diagonalTrace

end ExpandedFA.IntegralOperators.ContinuousTraceDiagonal
