import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ImproperDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C08.UniformC1Limit
import MathGenome.Internal.MultivariableAnalysis.D04.C08.ProperDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C08.UniformTailsContinuity
import MathGenome.Internal.MultivariableAnalysis.D04.C03.HigherInterfaces

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter Topology
open scoped BigOperators
namespace D04.ImproperDerivative
open JordanRegions ImproperExhaustions AbsoluteConvergence ProperDerivative UniformTailsContinuity

/-- Signed operator convergence suffices; no majorant is assumed. -/
theorem improper_derivative : Specs.D04.C08.ImproperDerivative.improper_derivativeType := by
  intro n m k Ω P K f p₀ r hΩ hK hP hr hBP hlocal hC hAi hD ha G hG
  let B := Metric.closedBall p₀ r
  let F := fun p => exhaustionIntegral K (fun x => f x p)
  have hd : TendstoUniformlyOn (fun j => totalDerivative (truncatedIntegral K f j))
      G atTop B := by
    apply hG.congr
    exact Eventually.of_forall (fun j p hp => (hD j p hp).symm)
  obtain ⟨H, hH, hGc, hHC, hHD⟩ := uniform_c1_limit p₀ r hr _ G hC ha hd
  have he : EqOn F H B := by
    intro p hp
    exact (hH.tendsto_at hp).limUnder_eq
  have hFu : TendstoUniformlyOn (truncatedIntegral K f) F atTop B := by
    exact hH.congr_right he.symm
  have hFC : CrOn 1 (interior B) F :=
    (crOn_congr 1 (interior B) H F isOpen_interior (he.mono interior_subset).symm).mp hHC
  refine ⟨hFu, hGc, hFC, fun p hp => ?_⟩
  have hHp : HasFDerivAt H (G p) p :=
    (hasTotalDerivative_iff_hasFDerivAt _ _ _ _ isOpen_interior hp).mp (hHD p hp).1
  have hFp : HasFDerivAt F (G p) p := hHp.congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (isOpen_interior.mem_nhds hp)
      (he.mono interior_subset))
  refine ⟨hFp, hFp.fderiv, fun h => ?_⟩
  have hh := ((ContinuousLinearMap.apply ℝ (E k) h).continuous.tendsto (G p)).comp
    (hG.tendsto_at (interior_subset hp))
  change Tendsto _ atTop (𝓝 (fderiv ℝ F p h))
  rw [hFp.fderiv]
  apply hh.congr'
  exact Eventually.of_forall (fun j => (integral_apply _ (hAi j p (interior_subset hp)) h).2)

/-- A finite sum of column bounds controls the operator norm. -/
lemma norm_le_sum_columns {m k : ℕ} (T : E m →L[ℝ] E k) :
    ‖T‖ ≤ ∑ i : Fin m, ‖T (standardBasis m i)‖ := by
  apply T.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro h
  rw [linear_expansion, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro i _
  rw [norm_smul, mul_comm ‖T (standardBasis m i)‖]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le h i) (norm_nonneg _)

theorem domination_derivative_tails :
    Specs.D04.C08.ImproperDerivative.domination_derivative_tailsType := by
  intro n m k Ω K B A hΩ hK hAi M hM hMpos hdom
  have hlim : Tendsto (fun j => (absoluteMass Ω M).toReal -
      regionIntegral (fun x : K j => |M x|)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (absoluteMass Ω M).toReal)).sub
      (absolute_mass_tendsto hΩ hM hK)
  have hcol (i : Fin m) : UniformCauchySeqOn
      (truncatedIntegral K (fun x p => A x p (standardBasis m i))) atTop B := by
    have hforward (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, ∀ j ≥ N, ∀ l ≥ j, ∀ p ∈ B,
        ‖truncatedIntegral K (fun x p => A x p (standardBasis m i)) l p -
          truncatedIntegral K (fun x p => A x p (standardBasis m i)) j p‖ < ε := by
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
      refine ⟨N, fun j hj l hjl p hp => ?_⟩
      let v := fun x => A x p (standardBasis m i)
      have hvL := (hAi l p hp).2 i
      have hvD : VectorRegionIntegrable (fun x : (K l \ K j : Set (E n)) => v x) :=
        ⟨jordan_bounded (jordan_diff (hK.1 l).2.1 (hK.1 j).2.1), fun a =>
          region_restrict (f := fun x => v x a) (hvL.2 a)
            (jordan_diff (hK.1 l).2.1 (hK.1 j).2.1) sdiff_subset⟩
      have hML : RegionIntegrable (fun x : K l => |M x|) :=
        locally_integrable_on_compact_jordan hΩ (locally_integrable_abs hM.1) (hK.1 l)
      have hMD : RegionIntegrable (fun x : (K l \ K j : Set (E n)) => |M x|) :=
        region_restrict (f := fun x => |M x|) hML (jordan_diff (hK.1 l).2.1 (hK.1 j).2.1) sdiff_subset
      change ‖vectorRegionIntegral (fun x : K l => v x) -
        vectorRegionIntegral (fun x : K j => v x)‖ < ε
      rw [← vector_integral_diff (f := v) (hK.1 l).2.1 (hK.1 j).2.1
        (regular_exhaustion_mono hK hjl) hvL]
      calc
        _ ≤ regionIntegral (fun x : (K l \ K j : Set (E n)) => ‖v x‖) := vector_norm_bound _ hvD
        _ ≤ regionIntegral (fun x : (K l \ K j : Set (E n)) => |M x|) := by
          apply region_mono (vector_integrable_norm _ hvD) hMD
          intro x
          have hx := (hK.1 l).2.2 x.property.1
          calc
            ‖v x‖ ≤ ‖A x p‖ * ‖standardBasis m i‖ := (A x p).le_opNorm _
            _ = ‖A x p‖ := by simp [standardBasis, EuclideanSpace.basisFun_apply]
            _ ≤ M x := hdom p hp x hx
            _ ≤ |M x| := le_abs_self _
        _ = regionIntegral (fun x : K l => |M x|) -
            regionIntegral (fun x : K j => |M x|) :=
          region_diff (f := fun x => |M x|) (hK.1 l).2.1 (hK.1 j).2.1 (regular_exhaustion_mono hK hjl) hML
        _ ≤ (absoluteMass Ω M).toReal - regionIntegral (fun x : K j => |M x|) :=
          sub_le_sub_right (integral_abs_le_mass hM.2 (hK.1 l)) _
        _ < ε := hN j hj
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hforward ε hε
    refine ⟨N, fun j hj l hl p hp => ?_⟩
    rcases le_total j l with hjl | hlj
    · simpa only [dist_eq_norm, norm_sub_rev] using hN j hj l hjl p hp
    · simpa only [dist_eq_norm] using hN l hl j hlj p hp
  have hc : UniformCauchySeqOn
      (fun j p => operatorRegionIntegral (fun x : K j => A x p)) atTop B := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    let δ := ε / ((m : ℝ) + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    choose N hN using fun i => (Metric.uniformCauchySeqOn_iff.mp (hcol i)) δ hδ
    refine ⟨Finset.univ.sup N, fun j hj l hl p hp => ?_⟩
    rw [dist_eq_norm]
    apply (norm_le_sum_columns _).trans_lt
    have hle : ∑ i : Fin m,
        ‖(operatorRegionIntegral (fun x : K j => A x p) -
          operatorRegionIntegral (fun x : K l => A x p)) (standardBasis m i)‖ ≤
        (m : ℝ) * δ := by
      calc
        _ ≤ ∑ _i : Fin m, δ := Finset.sum_le_sum (fun i _ => by
          rw [sub_apply, (integral_apply _ (hAi j p hp) _).2,
            (integral_apply _ (hAi l p hp) _).2]
          exact (hN i j ((Finset.le_sup (Finset.mem_univ i)).trans hj)
            l ((Finset.le_sup (Finset.mem_univ i)).trans hl) p hp).le)
        _ = _ := by simp
    apply hle.trans_lt
    dsimp [δ]
    have he : ε / ((m : ℝ) + 1) * ((m : ℝ) + 1) = ε :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  exact ⟨hc, (fun p => limUnder atTop (fun j => operatorRegionIntegral (fun x : K j => A x p))),
    hc.tendstoUniformlyOn_of_tendsto
    (fun p hp => (hc.cauchySeq hp).tendsto_limUnder)⟩

theorem absolute_exhaustion_independence :
    Specs.D04.C08.ImproperDerivative.absolute_exhaustion_independenceType := by
  intro n m k Ω K L f B hΩ hK hL hf p hp
  have hk := ((vector_absolute_exhaustion hΩ (hf p hp)).1 K hK).limUnder_eq
  have hl := ((vector_absolute_exhaustion hΩ (hf p hp)).1 L hL).limUnder_eq
  exact ⟨hk, hk.trans hl.symm⟩


/-- The uniform-limit argument also applies to each finite-dimensional tensor
space. This helper works in any complete target, with the same closed ball. -/
lemma c1_limit_of_tails {m : ℕ} {Y : Type} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [CompleteSpace Y]
    (p₀ : E m) (r : ℝ) (hr : 0 ≤ r) (u : ℕ → E m → Y)
    (hC : ∀ j, ∃ U, IsOpen U ∧ Metric.closedBall p₀ r ⊆ U ∧ CrOn 1 U (u j))
    (hd : UniformCauchySeqOn (fun j => totalDerivative (u j)) atTop
      (Metric.closedBall p₀ r))
    (ha : ∃ a, Tendsto (fun j => u j p₀) atTop (𝓝 a)) :
    let H := fun p => limUnder atTop (fun j => u j p)
    let G := fun p => limUnder atTop (fun j => totalDerivative (u j) p)
    TendstoUniformlyOn u H atTop (Metric.closedBall p₀ r) ∧
    TendstoUniformlyOn (fun j => totalDerivative (u j)) G atTop (Metric.closedBall p₀ r) ∧
    ContinuousOn H (Metric.closedBall p₀ r) ∧ ContinuousOn G (Metric.closedBall p₀ r) ∧
    ∀ p ∈ interior (Metric.closedBall p₀ r), HasFDerivAt H (G p) p := by
  let B := Metric.closedBall p₀ r
  have hdata (j : ℕ) : (∀ p ∈ B, HasFDerivAt (u j) (totalDerivative (u j) p) p) ∧
      ContinuousOn (totalDerivative (u j)) B := by
    obtain ⟨U, hU, hBU, hCj⟩ := hC j
    change TotalDifferentiableOn U (u j) ∧ ContinuousOn (totalDerivative (u j)) U at hCj
    refine ⟨fun p hp => ?_, hCj.2.mono hBU⟩
    obtain ⟨A, hA⟩ := hCj.1 p (hBU hp)
    have hh := (hasTotalDerivative_iff_hasFDerivAt _ _ _ _ hU (hBU hp)).mp hA
    change HasFDerivAt (u j) (fderiv ℝ (u j) p) p
    rw [hh.fderiv]
    exact hh
  obtain ⟨a, ha⟩ := ha
  have hu : UniformCauchySeqOn u atTop B := by
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    let δ := ε / (2 * (r + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ha.cauchySeq (ε / 2) (half_pos hε)
    obtain ⟨J, hJ⟩ := Metric.uniformCauchySeqOn_iff.mp hd δ hδ
    refine ⟨max N J, fun i hi j hj p hp => ?_⟩
    have hb := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx => ((hdata i).1 x hx |>.sub ((hdata j).1 x hx)).hasFDerivWithinAt)
      (fun x hx => (show ‖totalDerivative (u i) x - totalDerivative (u j) x‖ < δ by
        simpa only [dist_eq_norm] using hJ i ((le_max_right _ _).trans hi)
          j ((le_max_right _ _).trans hj) x hx).le)
      (convex_closedBall p₀ r) (Metric.mem_closedBall_self hr) hp
    have hp' : ‖p - p₀‖ ≤ r := by
      change dist p p₀ ≤ r at hp
      simpa only [dist_eq_norm] using hp
    have hbase := hN i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj)
    rw [dist_eq_norm] at hbase ⊢
    have htri : ‖u i p - u j p‖ ≤ ‖u i p₀ - u j p₀‖ +
        ‖(u i p - u j p) - (u i p₀ - u j p₀)‖ := norm_le_insert' _ _
    simp only [Pi.sub_apply] at hb
    have hmul := mul_le_mul_of_nonneg_left hp' hδ.le
    have he : δ * (2 * (r + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hUF : TendstoUniformlyOn u (fun p => limUnder atTop (fun j => u j p)) atTop B :=
    hu.tendstoUniformlyOn_of_tendsto (fun p hp => (hu.cauchySeq hp).tendsto_limUnder)
  have hUD : TendstoUniformlyOn (fun j => totalDerivative (u j))
      (fun p => limUnder atTop (fun j => totalDerivative (u j) p)) atTop B :=
    hd.tendstoUniformlyOn_of_tendsto (fun p hp => (hd.cauchySeq hp).tendsto_limUnder)
  refine ⟨hUF, hUD, hUF.continuousOn (Frequently.of_forall (fun j =>
    fun p hp => ((hdata j).1 p hp).continuousAt.continuousWithinAt)),
    hUD.continuousOn (Frequently.of_forall (fun j => (hdata j).2)), fun p hp => ?_⟩
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_interior (hUD.mono interior_subset)
    (fun j x hx => (hdata j).1 x (interior_subset hx))
    (fun x hx => hUF.tendsto_at (interior_subset hx)) hp

/-- Each finite order is proved by a new application in its tensor space. -/
theorem finite_improper_derivatives :
    Specs.D04.C08.ImproperDerivative.finite_improper_derivativesType := by
  intro n m k Ω P K f p₀ r s hΩ hK hP hr hBP hC hd ha hproper
  let B := Metric.closedBall p₀ r
  let V := interior B
  let F := fun p => exhaustionIntegral K (fun x => f x p)
  let T := fun (q j : ℕ) => higherDifferential q (truncatedIntegral K f j)
  let H := fun (q : ℕ) p => limUnder atTop (fun j => T q j p)
  let G := fun (q : ℕ) p => limUnder atTop (fun j => totalDerivative (T q j) p)
  have hl (q : ℕ) (hq : q ≤ s) :=
    c1_limit_of_tails p₀ r hr (T q) (hC q hq) (hd q hq) (ha q hq)
  have hsucc (q : ℕ) (hq : q ≤ s) :
      TendstoUniformlyOn (T (q + 1))
        (fun p => differentialSuccEquiv (E m) (E k) q (G q p)) atTop B :=
    (differentialSuccEquiv (E m) (E k) q).toContinuousLinearMap.uniformContinuous.comp_tendstoUniformlyOn
      (hl q hq).2.1
  have hnext (q : ℕ) (hq : q ≤ s) : EqOn (H (q + 1))
      (fun p => differentialSuccEquiv (E m) (E k) q (G q p)) B := by
    intro p hp
    exact ((hsucc q hq).tendsto_at hp).limUnder_eq
  have hU (q : ℕ) (hq : q ≤ s + 1) : TendstoUniformlyOn (T q) (H q) atTop B := by
    cases q with
    | zero => exact (hl 0 (Nat.zero_le _)).1
    | succ q => exact (hsucc q (by omega)).congr_right (hnext q (by omega)).symm
  have hHc (q : ℕ) (hq : q ≤ s + 1) : ContinuousOn (H q) B := by
    cases q with
    | zero => exact (hl 0 (Nat.zero_le _)).2.2.1
    | succ q =>
      exact ((differentialSuccEquiv (E m) (E k) q).continuous.comp_continuousOn
        (hl q (by omega)).2.2.2.1).congr (fun p hp => hnext q (by omega) hp)
  let ev₀ := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E m) (E k) (fun i => Fin.elim0 i)
  have hF : EqOn F (fun p => ev₀ (H 0 p)) B := by
    intro p hp
    exact (ev₀.continuous.tendsto _ |>.comp ((hU 0 (Nat.zero_le _)).tendsto_at hp)).limUnder_eq
  have hUF : TendstoUniformlyOn (truncatedIntegral K f) F atTop B :=
    (ev₀.uniformContinuous.comp_tendstoUniformlyOn (hU 0 (Nat.zero_le _))).congr_right hF.symm
  have hEq : ∀ q ≤ s + 1, EqOn (higherDifferential q F) (H q) V := by
    intro q hq
    induction q with
    | zero =>
      intro p hp
      apply ContinuousMultilinearMap.ext
      intro v
      change F p = H 0 p v
      exact (hF (interior_subset hp)).trans
        (congrArg (H 0 p) (Subsingleton.elim _ _))
    | succ q ih =>
      have ih := ih (by omega)
      intro p hp
      have he : totalDerivative (higherDifferential q F) p = totalDerivative (H q) p :=
        (Filter.eventuallyEq_of_mem (isOpen_interior.mem_nhds hp) ih).fderiv_eq
      rw [higherDifferential_succ, he]
      have hdp := (hl q (by omega)).2.2.2.2 p hp
      change differentialSuccEquiv (E m) (E k) q (fderiv ℝ (H q) p) = _
      rw [hdp.fderiv]
      exact (hnext q (by omega) (interior_subset hp)).symm
  have hcont (q : ℕ) (hq : q ≤ s + 1) : ContinuousOn (higherDifferential q F) V :=
    ((hHc q hq).mono interior_subset).congr (fun p hp => hEq q hq hp)
  have hdiff (q : ℕ) (hq : q < s + 1) : DifferentiableOn ℝ (higherDifferential q F) V := by
    intro p hp
    have hh := (hl q (by omega)).2.2.2.2 p hp
    have he := Filter.eventuallyEq_of_mem (isOpen_interior.mem_nhds hp) (hEq q (by omega))
    exact (hh.congr_of_eventuallyEq he).differentiableAt.differentiableWithinAt
  have hCr : CrOn (s + 1) V F := by
    apply (crOn_iff_contDiffOn (s + 1) V F isOpen_interior).mpr
    apply (contDiffOn_nat_iff_continuousOn_differentiableOn isOpen_interior.uniqueDiffOn).mpr
    constructor
    · intro q hq
      exact (hcont q hq).congr (iteratedFDerivWithin_of_isOpen q isOpen_interior)
    · intro q hq
      exact (hdiff q hq).congr (iteratedFDerivWithin_of_isOpen q isOpen_interior)
  refine ⟨hUF, hCr, fun q hq => ⟨⟨H q, hU q hq, hEq q hq⟩, fun p hp v => ?_⟩⟩
  have hv := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => E m) (E k) v).continuous.tendsto _).comp
    ((hU q hq).tendsto_at (interior_subset hp))
  have heq := congrArg (fun z => z v) (hEq q hq hp)
  change Tendsto _ atTop (𝓝 (higherDifferential q F p v))
  rw [heq]
  exact hv.congr' (Eventually.of_forall (fun j => (hproper q hq j p (interior_subset hp) v).2))

end D04.ImproperDerivative
