import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.PiecewiseC1Length
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcPrimitive
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace D12Complex.PiecewiseC1Length

abbrev polygonalLength := ComplexPath.polygonalLength
abbrev speedIntegral := @C1Partition.speedIntegral
abbrev weightedSpeedIntegral := @C1Partition.weightedSpeedIntegral
abbrev length := PiecewiseC1Path.length
abbrev traceSupNorm := PiecewiseC1Path.traceSupNorm
abbrev chainLengthBound := IntegralChain.lengthBound
abbrev chainTraceSupNorm := IntegralChain.traceSupNorm

/-- FTC identifies a C1 restriction with its genuine integral primitive.
The total extension is only differentiated in the interior. -/
theorem variation_of_contDiffOn {f : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    D11.Ch12.variation f a b =
      ENNReal.ofReal (∫ t in a..b, ‖derivWithin f (Icc a b) t‖) := by
  let d := derivWithin f (Icc a b)
  have hd : ContinuousOn d (Icc a b) :=
    ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mp hf).2
  have hi : IntervalIntegrable d volume a b := hd.intervalIntegrable_of_Icc hab.le
  have heq : EqOn f (D11.Ch12.AcPrimitive.primitive d (f a) a) (Icc a b) := by
    intro x hx
    have hix : IntervalIntegrable d volume a x := hi.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl hx.2)
    have hFTC : (∫ t in a..x, d t) = f x - f a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
        (hf.continuousOn.mono (Icc_subset_Icc le_rfl hx.2)) _ hix
      intro t ht
      have ht' : t ∈ Ioo a b := ⟨ht.1, ht.2.trans_le hx.2⟩
      have hdiff := (hf.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht')).differentiableAt
        (Icc_mem_nhds ht'.1 ht'.2)
      simpa only [d, derivWithin_of_mem_nhds (Icc_mem_nhds ht'.1 ht'.2)] using
        hdiff.hasDerivAt
    simp only [D11.Ch12.AcPrimitive.primitive, hFTC, add_sub_cancel]
  rw [D11.Ch12.variation_congr heq]
  exact D11.Ch12.AcPrimitive.primitive_variation d (f a) hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp hi)

/-- Additivity of the literal polygonal supremum along arbitrary finite nodes. -/
theorem variation_fin_partition (f : ℝ → ℂ) :
    ∀ {n : ℕ} (node : Fin (n + 1) → ℝ), Monotone node →
      D11.Ch12.variation f (node 0) (node (Fin.last n)) =
        ∑ i : Fin n, D11.Ch12.variation f (node i.castSucc) (node i.succ) := by
  intro n
  induction n with
  | zero => intro node _; simp [D11.Ch12.variation_self]
  | succ n ih =>
    intro node hm
    rw [Fin.sum_univ_succ]
    simp_rw [← Fin.succ_castSucc]
    rw [← ih (fun i => node i.succ) (fun _ _ h => hm (by simpa using h))]
    exact D11.Ch12.variation_additive f (hm (Fin.zero_le _))
      (hm (Fin.le_last _))

theorem speedIntegral_nonneg {γ : ComplexPath} (P : C1Partition γ) :
    0 ≤ P.speedIntegral := by
  apply Finset.sum_nonneg
  intro i _
  exact intervalIntegral.integral_nonneg_of_forall (P.piece_lt i).le (fun _ => norm_nonneg _)

theorem variation_eq_speedIntegral :
    Specs.D12Complex.Ch03.PiecewiseC1Length.variation_eq_speedIntegral_type := by
  intro γ P
  change D11.Ch12.variation (γ : ℝ → ℂ) γ.a γ.b = _
  rw [← P.first, ← P.last, variation_fin_partition γ P.node P.strictMono.monotone]
  simp_rw [variation_of_contDiffOn (P.piece_lt _) (P.smooth _)]
  unfold C1Partition.speedIntegral C1Partition.pieceSet
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    intervalIntegral.integral_nonneg_of_forall (P.piece_lt i).le (fun _ => norm_nonneg _))).symm

theorem length_eq_speedIntegral :
    Specs.D12Complex.Ch03.PiecewiseC1Length.length_eq_speedIntegral_type := by
  intro γ P
  change (Specs.D11.Ch12.variation_value (γ : ℝ → ℂ) γ.path.a γ.path.b).toReal = _
  rw [variation_eq_speedIntegral P, ENNReal.toReal_ofReal (speedIntegral_nonneg P)]

theorem speedIntegral_independent :
    Specs.D12Complex.Ch03.PiecewiseC1Length.speedIntegral_independent_type := by
  intro γ P Q
  exact (length_eq_speedIntegral ⟨γ, ⟨P⟩⟩ P).symm.trans
    (length_eq_speedIntegral ⟨γ, ⟨P⟩⟩ Q)

theorem piece_norm_deriv_integrable {γ : ComplexPath} (P : C1Partition γ)
    (i : Fin P.count) :
    IntervalIntegrable (fun t => ‖deriv γ t‖) volume
      (P.node i.castSucc) (P.node i.succ) := by
  simpa only [one_mul] using (P.piece_integrable_deriv (fun _ => 1) continuousOn_const i).norm

theorem speedIntegral_eq_intervalIntegral {γ : ComplexPath} (P : C1Partition γ) :
    P.speedIntegral = ∫ t in γ.a..γ.b, ‖deriv γ t‖ := by
  have hs := (intervalIntegral_fin_partition P.node (fun t => ‖deriv γ t‖)
    (piece_norm_deriv_integrable P)).2
  rw [P.first, P.last] at hs
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hs
  apply intervalIntegral.integral_congr_Ioo_of_le (P.piece_lt i).le
  intro t ht
  simp only [C1Partition.pieceSet, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

theorem length_eq_integral_norm_deriv :
    Specs.D12Complex.Ch03.PiecewiseC1Length.length_eq_integral_norm_deriv_type := by
  intro γ
  rw [length_eq_speedIntegral γ γ.partition, speedIntegral_eq_intervalIntegral]

theorem polygonalLength_eq_iSup :
    Specs.D12Complex.Ch03.PiecewiseC1Length.polygonalLength_eq_iSup_type := by
  intro γ
  change (⨆ p : D11.Ch12.IntervalPartition γ.path.a γ.path.b,
    D11.Ch12.partitionSum (γ : ℝ → ℂ) p).toReal = _
  rw [ENNReal.toReal_iSup (fun p => by
    unfold D11.Ch12.partitionSum
    exact ENNReal.sum_ne_top.mpr (fun _ _ => enorm_ne_top))]
  congr 1
  funext p
  simp only [D11.Ch12.partitionSum, ENNReal.toReal_sum (fun _ _ => enorm_ne_top),
    toReal_enorm]

theorem length_nonneg (γ : PiecewiseC1Path) : 0 ≤ γ.length := ENNReal.toReal_nonneg

theorem length_degenerate :
    Specs.D12Complex.Ch03.PiecewiseC1Length.length_degenerate_type := by
  intro γ heq
  change (D11.Ch12.variation (γ : ℝ → ℂ) γ.path.a γ.path.b).toReal = 0
  rw [heq, D11.Ch12.variation_self, ENNReal.toReal_zero]

theorem length_constant :
    Specs.D12Complex.Ch03.PiecewiseC1Length.length_constant_type := by
  intro γ z hz
  change (D11.Ch12.variation (γ : ℝ → ℂ) γ.path.a γ.path.b).toReal = 0
  rw [D11.Ch12.variation_eq_eVariationOn]
  have hv : eVariationOn (γ : ℝ → ℂ) (Icc γ.path.a γ.path.b) = 0 := by
    apply (eVariationOn.eq_zero_iff _).mpr
    intro x hx y hy
    rw [hz x hx, hz y hy, edist_self]
  rw [hv, ENNReal.toReal_zero]

theorem norm_integral_le_weightedSpeedIntegral :
    Specs.D12Complex.Ch03.PiecewiseC1Length.norm_integral_le_weightedSpeedIntegral_type := by
  intro γ P f hf
  rw [PiecewiseC1Path.integral_eq_partition γ P f hf]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  simpa only [norm_mul] using
    (intervalIntegral.norm_integral_le_integral_norm (P.piece_lt i).le
      (f := fun t => f (γ t) * derivWithin γ (P.pieceSet i) t))

/-- A bound on f along the actual trace gives the sharp length multiplier. -/
theorem weightedSpeedIntegral_le_mul_bound (γ : PiecewiseC1Path)
    (P : C1Partition γ.path) (f : ℂ → ℂ) (hf : ContinuousOn f γ.trace)
    {M : ℝ} (hM : ∀ z ∈ γ.trace, ‖f z‖ ≤ M) :
    P.weightedSpeedIntegral f ≤ γ.length * M := by
  rw [length_eq_speedIntegral γ P, C1Partition.speedIntegral, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hd := ((P.piece_c1_iff i).mp (P.smooth i)).2
  have hcomp : ContinuousOn (fun t => ‖f (γ t)‖) (P.pieceSet i) := by
    exact (hf.comp (γ.path.continuousOn.mono (P.piece_subset i))
      (fun t ht => ⟨t, P.piece_subset i ht, rfl⟩)).norm
  rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_mono_on (P.piece_lt i).le
    ((hcomp.mul hd.norm).intervalIntegrable_of_Icc (P.piece_lt i).le)
    ((hd.norm.mul_const M).intervalIntegrable_of_Icc (P.piece_lt i).le)
  intro t ht
  exact (mul_le_mul_of_nonneg_right
    (hM (γ t) ⟨t, P.piece_subset i ht, rfl⟩) (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem norm_integral_le_mul_bound (γ : PiecewiseC1Path) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) {M : ℝ} (hM : ∀ z ∈ γ.trace, ‖f z‖ ≤ M) :
    ‖γ.integral f‖ ≤ γ.length * M :=
  (norm_integral_le_weightedSpeedIntegral γ γ.partition f hf).trans
    (weightedSpeedIntegral_le_mul_bound γ γ.partition f hf hM)

theorem norm_le_traceSupNorm (γ : PiecewiseC1Path) (f : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) {z : ℂ} (hz : z ∈ γ.trace) :
    ‖f z‖ ≤ γ.traceSupNorm f := by
  apply le_csSup ((γ.path.trace_compact.image_of_continuousOn hf.norm).bddAbove)
  exact ⟨z, hz, rfl⟩

theorem weightedSpeedIntegral_le_length_mul :
    Specs.D12Complex.Ch03.PiecewiseC1Length.weightedSpeedIntegral_le_length_mul_type := by
  intro γ P f hf
  exact weightedSpeedIntegral_le_mul_bound γ P f hf (fun _ hz => norm_le_traceSupNorm γ f hf hz)

theorem norm_integral_le_length_mul :
    Specs.D12Complex.Ch03.PiecewiseC1Length.norm_integral_le_length_mul_type := by
  intro γ f hf
  exact norm_integral_le_mul_bound γ f hf (fun _ hz => norm_le_traceSupNorm γ f hf hz)

theorem weightedSpeedIntegral_eq_intervalIntegral (γ : PiecewiseC1Path)
    (P : C1Partition γ.path) (f : ℂ → ℂ) (hf : ContinuousOn f γ.trace) :
    P.weightedSpeedIntegral f =
      ∫ t in γ.path.a..γ.path.b, ‖f (γ t)‖ * ‖deriv γ t‖ := by
  have hi (i : Fin P.count) :
      IntervalIntegrable (fun t => ‖f (γ t)‖ * ‖deriv γ t‖) volume
        (P.node i.castSucc) (P.node i.succ) := by
    simpa only [norm_mul] using (P.piece_integrable_deriv f hf i).norm
  have hs := (intervalIntegral_fin_partition P.node _ hi).2
  rw [P.first, P.last] at hs
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hs
  apply intervalIntegral.integral_congr_Ioo_of_le (P.piece_lt i).le
  intro t ht
  simp only [C1Partition.pieceSet, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

theorem contour_estimates :
    Specs.D12Complex.Ch03.PiecewiseC1Length.contour_estimates_type := by
  intro γ f hf
  rw [← weightedSpeedIntegral_eq_intervalIntegral γ γ.partition f hf]
  exact ⟨norm_integral_le_weightedSpeedIntegral γ γ.partition f hf,
    weightedSpeedIntegral_le_length_mul γ γ.partition f hf⟩

theorem integral_sub (γ : PiecewiseC1Path) (f g : ℂ → ℂ)
    (hf : ContinuousOn f γ.trace) (hg : ContinuousOn g γ.trace) :
    γ.integral (fun z => f z - g z) = γ.integral f - γ.integral g := by
  change γ.partition.integral _ = γ.partition.integral f - γ.partition.integral g
  unfold C1Partition.integral
  simp_rw [sub_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact intervalIntegral.integral_sub (γ.partition.piece_integrable f hf i)
    (γ.partition.piece_integrable g hg i)

theorem integral_tendsto_uniform :
    Specs.D12Complex.Ch03.PiecewiseC1Length.integral_tendsto_uniform_type := by
  intro γ F f hF hconv
  have hf := hconv.continuousOn (Eventually.of_forall hF).frequently
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hL : 0 < γ.length + 1 := by linarith [length_nonneg γ]
  have hδ : 0 < ε / (γ.length + 1) := div_pos hε hL
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv _ hδ] with n hn
  rw [dist_eq_norm, ← integral_sub γ (F n) f (hF n) hf]
  have hbound := norm_integral_le_mul_bound γ (fun z => F n z - f z) ((hF n).sub hf)
    (M := ε / (γ.length + 1)) (fun z hz => by
      simpa only [← dist_eq_norm, dist_comm] using (hn z hz).le)
  apply hbound.trans_lt
  rw [← mul_div_assoc, div_lt_iff₀ hL]
  nlinarith

/-- Every active summand has its trace contained in the chain trace. -/
theorem trace_subset_chain (Γ : IntegralChain) {γ : PiecewiseC1Path}
    (hγ : γ ∈ Γ.support) : γ.trace ⊆ Γ.trace := fun _ hz => ⟨γ, hγ, hz⟩

theorem chain_trace_compact (Γ : IntegralChain) : IsCompact Γ.trace := by
  have heq : Γ.trace = ⋃ γ ∈ Γ.support, γ.trace := by
    ext z
    simp only [IntegralChain.trace, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [heq]
  exact Γ.support.finite_toSet.isCompact_biUnion (fun γ _ => γ.path.trace_compact)

theorem norm_intCast_complex (m : ℤ) : ‖(m : ℂ)‖ = |(m : ℝ)| := by
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]

theorem chain_norm_integral_le_sum :
    Specs.D12Complex.Ch03.PiecewiseC1Length.chain_norm_integral_le_sum_type := by
  intro Γ f hf
  unfold IntegralChain.integral Finsupp.sum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro γ hγ
  rw [norm_mul, norm_intCast_complex]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_le_length_mul γ f (hf.mono (trace_subset_chain Γ hγ))) (abs_nonneg _)

theorem chain_norm_integral_le_mul_bound (Γ : IntegralChain) (f : ℂ → ℂ)
    (hf : ContinuousOn f Γ.trace) {M : ℝ} (hM : ∀ z ∈ Γ.trace, ‖f z‖ ≤ M) :
    ‖Γ.integral f‖ ≤ Γ.lengthBound * M := by
  unfold IntegralChain.integral Finsupp.sum IntegralChain.lengthBound
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro γ hγ
  rw [norm_mul, norm_intCast_complex, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_le_mul_bound γ f (hf.mono (trace_subset_chain Γ hγ))
      (fun z hz => hM z (trace_subset_chain Γ hγ hz))) (abs_nonneg _)

theorem chain_norm_integral_le_length_mul :
    Specs.D12Complex.Ch03.PiecewiseC1Length.chain_norm_integral_le_length_mul_type := by
  intro Γ f hf
  apply chain_norm_integral_le_mul_bound Γ f hf
  intro z hz
  apply le_csSup (((chain_trace_compact Γ).image_of_continuousOn hf.norm).bddAbove)
  exact ⟨z, hz, rfl⟩

theorem chain_integral_tendsto_uniform :
    Specs.D12Complex.Ch03.PiecewiseC1Length.chain_integral_tendsto_uniform_type := by
  intro Γ F f hF hconv
  unfold IntegralChain.integral Finsupp.sum
  apply tendsto_finsetSum
  intro γ hγ
  exact tendsto_const_nhds.mul (integral_tendsto_uniform γ F f
    (fun n => (hF n).mono (trace_subset_chain Γ hγ))
    (hconv.mono (trace_subset_chain Γ hγ)))

end D12Complex.PiecewiseC1Length
