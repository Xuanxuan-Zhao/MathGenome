import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.HardyCZEndpoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.AtomicHardySpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SingularIntegrals.CalderonZygmundWeak11

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal lp

namespace ExpandedFA.Hardy.HardyCZEndpoint
open SingularIntegrals StandardConvolution CZWeak AtomicHardySpaceSpec HardyCZEndpointSpec

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

lemma endpointConstant_nonneg (T : StandardConvolutionOperator 𝕜 d) :
    0 ≤ endpointConstant T := by
  unfold endpointConstant
  have := T.kernel.constant_nonneg
  positivity

/-- The essential atom bound also controls its squared integral. -/
lemma atom_energy (a : Atoms 𝕜 d) :
    ∃ (c : Space d) (r : ℝ), 0 < r ∧
      SupportedAE (a.val : Space d → 𝕜) (Metric.closedBall c r) ∧
      MemLp (a.val : Space d → 𝕜) 2 ∧
      (∫ x, ‖a.val x‖ ^ 2) ≤ (volume.real (Metric.ball c r))⁻¹ := by
  rcases a.property.2 with ⟨c, r, hr, hm0, hmt, hb⟩
  let V := volume.real (Metric.ball c r)
  have hV : 0 < V := ENNReal.toReal_pos hm0 hmt
  have ha := MeasureTheory.L1.integrable_coeFn a.val
  have hp : ∀ᵐ x, ‖a.val x‖ ^ 2 ≤ V⁻¹ * ‖a.val x‖ := by
    filter_upwards [hb] with x hx
    nlinarith [mul_le_mul_of_nonneg_right hx.2 (norm_nonneg (a.val x))]
  have hi : Integrable (fun x => ‖a.val x‖ ^ 2) :=
    (ha.norm.const_mul V⁻¹).mono' ((Lp.aestronglyMeasurable a.val).norm.pow 2)
      (by simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hp)
  refine ⟨c, r, hr, ?_, (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable a.val)).mpr hi, ?_⟩
  · filter_upwards [hb] with x hx hn
    exact hx.1 (fun hxB => hn (Metric.ball_subset_closedBall hxB))
  · calc
      (∫ x, ‖a.val x‖ ^ 2) ≤ ∫ x, V⁻¹ * ‖a.val x‖ :=
        integral_mono_ae hi (ha.norm.const_mul _) hp
      _ = V⁻¹ * ‖a.val‖ := by
        rw [integral_const_mul, MeasureTheory.L1.norm_eq_integral_norm]
      _ ≤ V⁻¹ := mul_le_of_le_one_right (inv_nonneg.mpr hV.le)
        (AtomicHardySpace.atom_norm_le volume a)

/-- Doubling of ball volume, also for the singleton in dimension zero. -/
lemma doubled_ball_volume (c : Space d) (r : ℝ) (hr : 0 < r) :
    volume.real (Metric.closedBall c (2 * r)) =
      (2 : ℝ) ^ d * volume.real (Metric.ball c r) := by
  have hb : volume.real (Metric.ball c r) =
      r ^ d * volume.real (Metric.ball (0 : Space d) 1) := by
    simp only [measureReal_def, Measure.addHaar_ball_of_pos volume c hr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ Module.finrank ℝ (Space d))]
    simp [Space, ExpandedFA.Fourier.Euclidean]
  rw [Measure.addHaar_real_closedBall volume c (by positivity)]
  simp only [Space, ExpandedFA.Fourier.Euclidean, finrank_euclideanSpace, Fintype.card_fin] at *
  rw [hb, mul_pow]
  ring

/-- A polynomial version of the local Cauchy--Schwarz estimate, avoiding a
square root in the final (nonoptimal) endpoint constant. -/
lemma local_norm_integral (v : L2 𝕜 d) (c : Space d) (r V : ℝ)
    (hV : 0 < V) :
    IntegrableOn (fun x => ‖v x‖) (Metric.closedBall c r) ∧
    (∫ x in Metric.closedBall c r, ‖v x‖) ≤
      V * ‖v‖ ^ 2 + V⁻¹ * volume.real (Metric.closedBall c r) := by
  let B := Metric.closedBall c r
  have he : Integrable (fun x => ‖v x‖ ^ 2) :=
    (Lp.memLp v).integrable_norm_pow (by norm_num)
  have hc : IntegrableOn (fun _ : Space d => V⁻¹) B :=
    integrableOn_const measure_closedBall_lt_top.ne
  have hg : IntegrableOn (fun x => V * ‖v x‖ ^ 2 + V⁻¹) B :=
    (he.const_mul V).integrableOn.add hc
  have hp (x : Space d) : ‖v x‖ ≤ V * ‖v x‖ ^ 2 + V⁻¹ := by
    have hsq := sq_nonneg (V * ‖v x‖ - 1)
    have hI : V * V⁻¹ = 1 := mul_inv_cancel₀ hV.ne'
    nlinarith [norm_nonneg (v x)]
  have hi : IntegrableOn (fun x => ‖v x‖) B :=
    hg.mono' (Lp.aestronglyMeasurable v).norm.restrict
      (ae_of_all _ fun x => by simpa only [norm_norm] using hp x)
  refine ⟨hi, ?_⟩
  calc
    (∫ x in B, ‖v x‖) ≤ ∫ x in B, V * ‖v x‖ ^ 2 + V⁻¹ :=
      integral_mono_ae hi hg (ae_of_all _ hp)
    _ = V * (∫ x in B, ‖v x‖ ^ 2) + V⁻¹ * volume.real B := by
      rw [integral_add (he.const_mul V).integrableOn hc, integral_const_mul, integral_const]
      simp [smul_eq_mul, mul_comm]
    _ ≤ V * (∫ x, ‖v x‖ ^ 2) + V⁻¹ * volume.real B := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (setIntegral_le_integral he (ae_of_all _ fun x => sq_nonneg _)) hV.le) le_rfl
    _ = _ := by rw [← norm_L2_sq]

/-- Uniform control of images of the source atoms under the original L² map. -/
theorem atom_estimate : AtomEstimate := by
  intro 𝕜 _ d T a
  obtain ⟨c, r, hr, hs, h2, he⟩ := atom_energy a
  let V := volume.real (Metric.ball c r)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  let v := h2.toLp a.val
  have hev : ‖v‖ ^ 2 ≤ V⁻¹ := by
    rw [norm_L2_sq]
    calc
      (∫ x, ‖v x‖ ^ 2) = ∫ x, ‖a.val x‖ ^ 2 :=
        integral_congr_ae (h2.coeFn_toLp.mono fun x hx => by dsimp [v]; rw [hx])
      _ ≤ _ := he
  have hTv : ‖T.operator v‖ ^ 2 ≤ ‖T.operator‖ ^ 2 * V⁻¹ := by
    calc
      ‖T.operator v‖ ^ 2 ≤ (‖T.operator‖ * ‖v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (T.operator.le_opNorm v) 2
      _ = ‖T.operator‖ ^ 2 * ‖v‖ ^ 2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hev (sq_nonneg _)
  obtain ⟨hi, hlocal⟩ := local_norm_integral (T.operator v) c (2 * r) V hV
  have hlocal' : (∫ x in Metric.closedBall c (2 * r), ‖T.operator v x‖) ≤
      ‖T.operator‖ ^ 2 + (2 : ℝ) ^ d := by
    apply hlocal.trans
    rw [doubled_ball_volume c r hr]
    calc
      V * ‖T.operator v‖ ^ 2 + V⁻¹ * (2 ^ d * V) ≤
          V * (‖T.operator‖ ^ 2 * V⁻¹) + V⁻¹ * (2 ^ d * V) := by
        gcongr
      _ = _ := by field_simp [ne_of_gt hV]
  let A := (((d : ℝ) * T.kernel.constant * 2 ^ (d + 1)) *
    ((d : ℝ) * volume.real (Metric.ball (0 : Space d) 1)) / 2)
  have hA : 0 ≤ A := by dsimp [A]; have := T.kernel.constant_nonneg; positivity
  have hout : IntegrableOn (fun x => ‖T.operator v x‖)
      (Metric.closedBall c (2 * r))ᶜ ∧
      (∫ x in (Metric.closedBall c (2 * r))ᶜ, ‖T.operator v x‖) ≤ A := by
    by_cases hd : 0 < d
    · obtain ⟨ho, hbound⟩ := cancellation_outside_ball hd T c r hr a.val
        (MeasureTheory.L1.integrable_coeFn a.val) h2 hs a.property.1
      refine ⟨ho, hbound.trans ?_⟩
      change A * (∫ x, ‖a.val x‖) ≤ A
      rw [← MeasureTheory.L1.norm_eq_integral_norm]
      exact mul_le_of_le_one_right hA (AtomicHardySpace.atom_norm_le volume a)
    · have hd : d = 0 := by omega
      subst d
      have hball : Metric.closedBall c (2 * r) = univ := by
        ext x
        simp [Subsingleton.elim x c, show 0 ≤ 2 * r by positivity]
      simp [hball, A]
  have hi' : Integrable (fun x => ‖T.operator v x‖) := by
    have := hi.union hout.1
    simpa only [union_compl_self, integrableOn_univ] using this
  refine ⟨h2, (integrable_norm_iff (Lp.aestronglyMeasurable _)).mp hi', ?_⟩
  rw [← integral_add_compl Metric.isClosed_closedBall.measurableSet hi']
  exact (add_le_add hlocal' hout.2).trans_eq (by dsimp [endpointConstant, A]; ring)

/-- Compatibility on L¹ ∩ L² identifies atom outputs with the weak extension. -/
lemma weak_atom_bound (T : StandardConvolutionOperator 𝕜 d)
    (S : CZWeak.L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d)
    (hS : IsCompatibleExtension T S) (a : Atoms 𝕜 d) :
    ∃ g : CZWeak.L1 𝕜 d,
      (g : Space d → 𝕜) =ᵐ[volume] (S a.val : Space d → 𝕜) ∧
      ‖g‖ ≤ endpointConstant T := by
  obtain ⟨h2, hi, hn⟩ := atom_estimate 𝕜 d T a
  have he := hS.1 a.val (Lp.memLp a.val) h2
  rw [Lp.toLp_coeFn] at he
  refine ⟨hi.toL1 _, hi.coeFn_toL1.trans he.symm, ?_⟩
  rw [MeasureTheory.L1.norm_eq_integral_norm]
  exact (integral_congr_ae (hi.coeFn_toL1.mono fun x hx => congrArg norm hx)).le.trans hn

/-- Absolute atomic sums give the same output as the weak extension. The two
limits are compared in measure, so this does not assume L¹ continuity of S. -/
lemma compatible_series (T : StandardConvolutionOperator 𝕜 d)
    (S : CZWeak.L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d)
    (hS : IsCompatibleExtension T S)
    (a : ℕ → Atoms 𝕜 d) (b : ℕ → 𝕜) (hb : Summable (fun j => ‖b j‖))
    (f : CZWeak.L1 𝕜 d) (hf : HasSum (fun j => b j • (a j).val) f) :
    ∃ g : CZWeak.L1 𝕜 d,
      (g : Space d → 𝕜) =ᵐ[volume] (S f : Space d → 𝕜) ∧
      ‖g‖ ≤ endpointConstant T * ∑' j, ‖b j‖ := by
  choose g hg hgn using fun j => weak_atom_bound T S hS (a j)
  have hbound (j : ℕ) : ‖b j • g j‖ ≤ endpointConstant T * ‖b j‖ := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgn j) (norm_nonneg _)
  have hs : Summable (fun j => b j • g j) :=
    (hb.mul_left (endpointConstant T)).of_norm_bounded hbound
  let G : CZWeak.L1 𝕜 d := ∑' j, b j • g j
  let u : ℕ → CZWeak.L1 𝕜 d := fun n => ∑ j ∈ Finset.range n, b j • (a j).val
  let v : ℕ → CZWeak.L1 𝕜 d := fun n => ∑ j ∈ Finset.range n, b j • g j
  have heq (n : ℕ) : (v n : Space d → 𝕜) =ᵐ[volume] (S (u n) : Space d → 𝕜) := by
    have hterm (j : ℕ) : ((b j • g j : CZWeak.L1 𝕜 d) : Space d → 𝕜) =ᵐ[volume]
        (S (b j • (a j).val) : Space d → 𝕜) := by
      rw [map_smul]
      exact (Lp.coeFn_smul _ _).trans
        (((hg j).const_smul (b j)).trans (AEEqFun.coeFn_smul _ _).symm)
    dsimp [u, v]
    rw [map_sum]
    exact (Lp.coeFn_finsetSum _ _).trans
      ((eventuallyEq_sum fun j _ => hterm j).trans (AEEqFun.coeFn_finsetSum _ _).symm)
  have hv : TendstoInMeasure volume (fun n => (v n : Space d → 𝕜)) atTop G :=
    tendstoInMeasure_of_tendsto_Lp hs.hasSum.tendsto_sum_nat
  have hu : TendstoInMeasure volume (fun n => (S (u n) : Space d → 𝕜)) atTop (S f) :=
    extension_tendstoInMeasure T S hS u f hf.tendsto_sum_nat
  refine ⟨G, tendstoInMeasure_ae_unique hv (hu.congr_left fun n => (heq n).symm), ?_⟩
  exact hs.hasSum.norm_le_of_bounded
    (by simpa only [tsum_mul_left] using (hb.mul_left (endpointConstant T)).hasSum) hbound

lemma compatible_synthesis (T : StandardConvolutionOperator 𝕜 d)
    (S : CZWeak.L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d)
    (hS : IsCompatibleExtension T S)
    (c : CoefficientsValue (𝕜 := 𝕜) (volume : Measure (Space d))) :
    ∃ g : CZWeak.L1 𝕜 d,
      (g : Space d → 𝕜) =ᵐ[volume] (S (SynthesisValue volume c) : Space d → 𝕜) ∧
      ‖g‖ ≤ endpointConstant T * ‖c‖ := by
  have := AtomicHardySpace.euclidean_atoms_nonempty d 𝕜
  obtain ⟨a, b, hb, hf⟩ := AtomicHardySpace.coefficient_sequence volume c
  obtain ⟨g, hg, hn⟩ := compatible_series T S hS a b hb.summable _ hf
  exact ⟨g, hg, hb.tsum_eq ▸ hn⟩

/-- Passing to the quotient uses its actual quotient norm. -/
lemma compatible_hardy (T : StandardConvolutionOperator 𝕜 d)
    (S : CZWeak.L1 𝕜 d →ₗ[𝕜] MeasurableClasses 𝕜 d)
    (hS : IsCompatibleExtension T S) (h : Hardy 𝕜 d) :
    ∃ g : CZWeak.L1 𝕜 d,
      (g : Space d → 𝕜) =ᵐ[volume] (S (EmbeddingValue volume h) : Space d → 𝕜) ∧
      ‖g‖ ≤ endpointConstant T * ‖h‖ := by
  obtain ⟨c₀, hc₀⟩ := (KernelValue (𝕜 := 𝕜) (volume : Measure (Space d))).mkQ_surjective h
  obtain ⟨g, hg, _⟩ := compatible_synthesis T S hS c₀
  have he₀ : SynthesisValue volume c₀ = EmbeddingValue volume h :=
    congrArg (EmbeddingValue volume) hc₀
  rw [he₀] at hg
  refine ⟨g, hg, le_of_forall_pos_le_add fun ε hε => ?_⟩
  let C := endpointConstant T
  have hC : 0 ≤ C := endpointConstant_nonneg T
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  obtain ⟨c, hc, hcn⟩ := Submodule.Quotient.norm_mk_lt h hδ
  obtain ⟨g', hg', hgn⟩ := compatible_synthesis T S hS c
  have he : SynthesisValue volume c = EmbeddingValue volume h :=
    congrArg (EmbeddingValue volume) hc
  rw [he] at hg'
  have hgg : g = g' := Lp.ext (hg.trans hg'.symm)
  rw [hgg]
  calc
    ‖g'‖ ≤ C * ‖c‖ := hgn
    _ ≤ C * (‖h‖ + ε / (C + 1)) := mul_le_mul_of_nonneg_left hcn.le hC
    _ ≤ C * ‖h‖ + ε := by
      have hsmall : C * (ε / (C + 1)) ≤ ε := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
        nlinarith
      nlinarith

/-- The bounded endpoint map is the restriction of the previously constructed
weak (1,1) operator, for the original atoms and their quotient norm. -/
theorem endpoint : Endpoint := by
  intro 𝕜 _ d T
  obtain ⟨S, hS, _⟩ := unique_extension 𝕜 d T
  choose g hg hgn using fun h : Hardy 𝕜 d => compatible_hardy T S hS h
  let L : Hardy 𝕜 d →ₗ[𝕜] CZWeak.L1 𝕜 d := {
    toFun := g
    map_add' x y := by
      apply Lp.ext
      have he : (S (EmbeddingValue volume (x + y)) : Space d → 𝕜) =ᵐ[volume]
          (fun z => S (EmbeddingValue volume x) z + S (EmbeddingValue volume y) z) := by
        rw [map_add, map_add]
        exact AEEqFun.coeFn_add _ _
      exact (hg (x + y)).trans (he.trans
        (((Lp.coeFn_add _ _).trans ((hg x).add (hg y))).symm))
    map_smul' k x := by
      change g (k • x) = k • g x
      apply Lp.ext
      have he : (S (EmbeddingValue volume (k • x)) : Space d → 𝕜) =ᵐ[volume]
          (fun z => k • S (EmbeddingValue volume x) z) := by
        rw [map_smul, map_smul]
        exact AEEqFun.coeFn_smul _ _
      exact (hg (k • x)).trans (he.trans
        (((Lp.coeFn_smul _ _).trans ((hg x).const_smul k)).symm)) }
  let E : Hardy 𝕜 d →L[𝕜] CZWeak.L1 𝕜 d :=
    L.mkContinuous (endpointConstant T) hgn
  refine ⟨E, E.opNorm_le_bound (endpointConstant_nonneg T) hgn, ?_⟩
  intro S' hS' h
  have heq := extension_unique 𝕜 d T S S' hS hS'
  rw [← heq]
  exact hg h

end ExpandedFA.Hardy.HardyCZEndpoint
