import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.GlobalH2
import MathGenome.Internal.LinearPDE.P201.Elliptic.BoundaryH2
import MathGenome.Internal.LinearPDE.P201.Common.ExactTrace
import Batteries.Tactic.OpenPrivate
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option backward.isDefEq.respectTransparency false

noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
open Set TopologicalSpace MeasureTheory Metric
open scoped NNReal ENNReal InnerProductSpace ContDiff Manifold
namespace P201.GlobalH2

open private h2_first_order_classes from MathGenome.Internal.LinearPDE.P201.Elliptic.BoundaryH2

/-- Boundedness supplies the only additional condition needed by the
Lipschitz trace theorem; every C¹,¹ graph is already a Lipschitz graph. -/
theorem boundedC11_isLipschitz {m : ℕ} (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1)))) (hc : HasC11Boundary Ω) :
    IsBoundedLipschitzOpen Ω := by
  refine ⟨Ω.isOpen.preimage (graphFrame m).continuous, ?_, ?_⟩
  · change Bornology.IsBounded ((graphFrame m) ⁻¹' (Ω : Set (Space (m + 1))))
    have he : (graphFrame m) ⁻¹' (Ω : Set (Space (m + 1))) =
        (graphFrame m).symm '' (Ω : Set (Space (m + 1))) := by
      ext x
      constructor
      · intro hx
        exact ⟨(graphFrame m) x, hx, (graphFrame m).symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        change (graphFrame m) ((graphFrame m).symm y) ∈ Ω
        rwa [(graphFrame m).apply_symm_apply]
    rw [he]
    exact (graphFrame m).symm.isometry.lipschitzWith.isBounded_image hb
  · intro p hp
    obtain ⟨C, hC, _⟩ := hc p hp
    exact ⟨C, hC⟩

/-- The derivative classes and their boundary traces use the common full
Hilbert norms, without a new regularity assumption on the solution. -/
theorem gradientTrace : P201Specs.GlobalH2.gradientTraceStatement := by
  intro m Ω hb hc
  let hLip := boundedC11_isLipschitz Ω hb hc
  obtain ⟨T, S, hT, _, _, _⟩ := Trace.exact_trace m Ω hLip
  refine ⟨hLip, T, hT, ?_⟩
  intro u w hw
  obtain ⟨v, d, hv, hd, _, hdn⟩ := h2_first_order_classes Ω w
  have hvu : v = u := hilbertUnderlyingInjective Ω 1 (hv.trans hw)
  subst v
  refine ⟨d, hd, ?_⟩
  intro j
  calc
    ‖T (d j)‖ ≤ ‖T‖ * ‖d j‖ := T.le_opNorm _
    _ ≤ ‖T‖ * ((1 + ((m + 1 : ℕ) : ℝ)) * ‖w‖) :=
      mul_le_mul_of_nonneg_left (hdn j) (ContinuousLinearMap.opNorm_nonneg T)
    _ = _ := (mul_assoc _ _ _).symm

/-- The global estimate in ambient dimension one requires no boundary
flattening or finite-cover argument. -/
theorem globalEstimateOne (Ω : Domain 1) (M L : ℝ≥0) (theta : ℝ)
    (ht : 0 < theta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Space 1 → Space 1 →L[ℝ] Space 1,
      P201Specs.InteriorH2.CoefficientBounds Ω A M L theta →
      ∀ (u : H10 ℝ Ω) (f : Lp ℝ Ω 2), P201Specs.InteriorH2.WeakEquation Ω A u.val f →
      ∃ w : H ℝ Ω 2, hUnderlying Ω 2 w = hZeroUnderlying Ω u ∧
        ‖w‖ ≤ C * (‖f‖ + ‖u‖) := by
  obtain ⟨C, hC, h⟩ := BoundaryH2.dimensionOneEstimate Ω M L theta ht
  refine ⟨C, hC, ?_⟩
  intro A hA u f heq
  obtain ⟨w, hw, hn⟩ := h A hA u.val f heq
  exact ⟨w, hw, by simpa only [add_comm, Submodule.norm_coe] using hn⟩



/-- A local H² representative identifies the restriction of the same
ambient derivative distribution. No compatibility of chosen representatives
on overlaps is an input. -/
lemma derivative_pairing_local {n : ℕ} (Ω U : Domain n)
    (f g : Space n → ℝ) (hf : LocallyIntegrableOn f Ω volume)
    (hg : LocallyIntegrableOn g U volume)
    (hfg : f =ᵐ[domainMeasure U] g) (α : MultiIndex n)
    (φ : Test ℝ Ω) (ψ : Test ℝ U) (hφψ : (φ : Space n → ℝ) = ψ) :
    distributionDerivative α (regularDistribution Ω f) φ =
      distributionDerivative α (regularDistribution U g) ψ := by
  let l := α.sort (· ≤ ·)
  have he : (P102.U4.testPartialWord Ω l φ : Space n → ℝ) =
      P102.U4.testPartialWord U l ψ := by
    rw [P102.U4.testPartialWord_coe, hφψ, P102.U4.testPartialWord_coe]
  simp only [distributionDerivative, P201Specs.distributionDerivative,
    P102.U4.distributionPartial, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  congr 1
  simp only [regularDistribution, P201Specs.regularDistribution, P102.U4.regularDistribution]
  rw [TestFunction.integralAgainstBilinCLM_eq_integral hf,
    TestFunction.integralAgainstBilinCLM_eq_integral hg]
  change (∫ x, P102.U4.testPartialWord Ω l φ x * f x) =
    ∫ x, P102.U4.testPartialWord U l ψ x * g x
  rw [he]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' U.isOpen.measurableSet).mp hfg] with x hx
  by_cases hxU : x ∈ U
  · rw [hx hxU]
  · rw [(P102.U4.testPartialWord U l ψ).zero_on_compl hxU]
    simp

lemma localSecondDerivativeBound {n : ℕ} (Ω U : Domain n)
    (u : H ℝ Ω 1) (w : H ℝ U 2)
    (hwu : (hUnderlying U 2 w : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying Ω 1 u)
    (j k : Fin n) (φ : Test ℝ Ω) (ψ : Test ℝ U)
    (hφψ : (φ : Space n → ℝ) = ψ) :
    ‖distributionDerivative {k} (regularDistribution Ω (hFirstDerivative u j)) φ‖ ≤
      ‖w‖ * (eLpNorm ψ 2 (domainMeasure U)).toReal := by
  let α : P102.U4.SobolevIndex n 2 := ⟨{k} + {j}, by simp⟩
  have hd : distributionDerivative {j} (regularDistribution Ω (hUnderlying Ω 1 u)) =
      regularDistribution Ω (hFirstDerivative u j) :=
    hilbertDerivativeDistribution Ω 1 u ⟨{j}, by simp⟩
  have hdw : distributionDerivative ({k} + {j}) (regularDistribution U (hUnderlying U 2 w)) =
      regularDistribution U (w.val α) := hilbertDerivativeDistribution U 2 w α
  have he : distributionDerivative {k} (regularDistribution Ω (hFirstDerivative u j)) =
      distributionDerivative ({k} + {j}) (regularDistribution Ω (hUnderlying Ω 1 u)) := by
    rw [← hd]
    exact (P102.U4.derivative_add n ℝ Ω {k} {j} _).symm
  rw [he, derivative_pairing_local Ω U _ _
    (P102.U4.domainLp_locallyIntegrable Ω 2 _) (P102.U4.domainLp_locallyIntegrable U 2 _)
    hwu.symm ({k} + {j}) φ ψ hφψ, hdw,
    P102.U4.regularLp_pairing U 2, P102.U4.lpTestPairing_eq_integral]
  calc
    _ ≤ (eLpNorm ψ 2 (domainMeasure U)).toReal *
        (eLpNorm (w.val α) 2 (domainMeasure U)).toReal :=
      P102.U4.DifferenceQuotient.integral_mul_bound
        (Lp.memLp (w.val α)) (ψ.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport)
    _ ≤ (eLpNorm ψ 2 (domainMeasure U)).toReal * ‖w‖ := by
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      rw [← Lp.norm_def]
      exact PiLp.norm_apply_le w.val α
    _ = _ := mul_comm _ _

/-- Finite local H² data patch through their distributional identities.
The estimate does not require any compatibility certificate on overlaps. -/
theorem finiteH2Assembly {n : ℕ} (Ω : Domain n) {ι : Type*} [Fintype ι]
    (O : ι → Domain n)
    (hcover : closure (Ω : Set (Space n)) ⊆ ⋃ i, (O i : Set (Space n)))
    (u : H ℝ Ω 1) (w : ∀ i, H ℝ (Ω ⊓ O i) 2)
    (hw : ∀ i, (hUnderlying (Ω ⊓ O i) 2 (w i) : Space n → ℝ)
      =ᵐ[domainMeasure (Ω ⊓ O i)] hUnderlying Ω 1 u) :
    ∃ v : H ℝ Ω 2, hUnderlying Ω 2 v = hUnderlying Ω 1 u ∧
      ‖v‖ ≤ (Fintype.card (P102.U4.SobolevIndex n 2) : ℝ) *
        (‖u‖ + ∑ i, ‖w i‖) := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := 𝓘(ℝ, Space n)) isClosed_closure (fun i => (O i : Set (Space n)))
    (fun i => (O i).isOpen) hcover
  let B : ℝ≥0 := ∑ i, ‖w i‖₊
  have hB : (B : ℝ) = ∑ i, ‖w i‖ := by simp [B]
  have hbound (j k : Fin n) (φ : Test ℝ Ω) :
      ‖distributionDerivative {k} (regularDistribution Ω (hFirstDerivative u j)) φ‖ ≤
        (B : ℝ) * (eLpNorm φ 2 (domainMeasure Ω)).toReal := by
    let ψ : ι → Test ℝ Ω := fun i =>
      P102.U4.coefficientTestProduct ⟨ρ i, (ρ i).contMDiff.contDiff.contDiffOn⟩ φ
    have hsum : φ = ∑ i, ψ i := by
      ext x
      have heval : (∑ i, ψ i) x = ∑ i, ρ i x * φ x := by
        change (FunLike.coeAddMonoidHom (Test ℝ Ω) (Space n) ℝ (∑ i, ψ i)) x = _
        rw [map_sum, Finset.sum_apply]
        rfl
      rw [heval, ← Finset.sum_mul]
      by_cases hx : x ∈ tsupport φ
      · have hs : ∑ i, ρ i x = 1 := by
          simpa only [finsum_eq_sum_of_fintype] using
            ρ.sum_eq_one (subset_closure (φ.tsupport_subset hx))
        rw [hs, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    have hψsupp (i : ι) : tsupport (ψ i) ⊆ Ω ⊓ O i := by
      intro x hx
      refine ⟨(ψ i).tsupport_subset hx, ?_⟩
      exact hρ i (tsupport_mul_subset_left hx)
    let ψU (i : ι) : Test ℝ (Ω ⊓ O i) :=
      ⟨ψ i, (ψ i).contDiff, (ψ i).hasCompactSupport, hψsupp i⟩
    have hnorm (i : ι) : (eLpNorm (ψU i) 2 (domainMeasure (Ω ⊓ O i))).toReal ≤
        (eLpNorm φ 2 (domainMeasure Ω)).toReal := by
      apply ENNReal.toReal_mono
        (φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport).eLpNorm_ne_top
      calc
        _ ≤ eLpNorm (ψU i) 2 (domainMeasure Ω) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono inf_le_left le_rfl)
        _ ≤ eLpNorm φ 2 (domainMeasure Ω) := by
          apply eLpNorm_mono (ψU i).continuous.aestronglyMeasurable
          intro x
          change ‖ρ i x * φ x‖ ≤ ‖φ x‖
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i x)]
          exact mul_le_of_le_one_left (norm_nonneg _) (ρ.le_one i x)
    calc
      _ = ‖∑ i, distributionDerivative {k}
          (regularDistribution Ω (hFirstDerivative u j)) (ψ i)‖ := by
        conv_lhs => rw [hsum, map_sum]
      _ ≤ ∑ i, ‖distributionDerivative {k}
          (regularDistribution Ω (hFirstDerivative u j)) (ψ i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖w i‖ * (eLpNorm φ 2 (domainMeasure Ω)).toReal := by
        apply Finset.sum_le_sum
        intro i _
        exact (localSecondDerivativeBound Ω (Ω ⊓ O i) u (w i) (hw i)
          j k (ψ i) (ψU i) rfl).trans
            (mul_le_mul_of_nonneg_left (hnorm i) (norm_nonneg _))
      _ = _ := by rw [hB, Finset.sum_mul]
  have hg (j k : Fin n) :=
    P102.U4.DifferenceQuotient.exists_density_of_test_bound Ω 2 2 (by norm_num)
      (distributionDerivative {k} (regularDistribution Ω (hFirstDerivative u j))) B (hbound j k)
  choose g hgNorm hgD using hg
  have hgn (j k : Fin n) : ‖g j k‖ ≤ ∑ i, ‖w i‖ := by
    rw [Lp.norm_def, ← hB]
    exact_mod_cast ENNReal.toReal_mono ENNReal.coe_ne_top (hgNorm j k)
  apply InteriorH2.h2FromWeakDerivatives Ω (hUnderlying Ω 1 u) (hFirstDerivative u) g
    (‖u‖ + ∑ i, ‖w i‖)
  · intro j
    exact hilbertDerivativeDistribution Ω 1 u ⟨{j}, by simp⟩
  · exact hgD
  · exact (PiLp.norm_apply_le u.val (P102.U4.zeroSobolevIndex n 1)).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg _)))
  · intro j
    exact (InteriorH2.firstDerivative_norm_le Ω u j).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg _)))
  · intro j k
    exact (hgn j k).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- Uniform local estimates at every point of the closure. The ball and
constant are chosen before the coefficients, source and solution. -/
theorem localEstimateAt {m : ℕ} (Ω : Domain (m + 1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m + 1)))) (hc : HasC11Boundary Ω)
    (M L : ℝ≥0) (theta : ℝ) (ht : 0 < theta)
    (p : Space (m + 1)) (hp : p ∈ closure (Ω : Set (Space (m + 1)))) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ A : Space (m + 1) → Space (m + 1) →L[ℝ] Space (m + 1),
      P201Specs.InteriorH2.CoefficientBounds Ω A M L theta →
      P201Specs.BoundaryH2.SymmetricOn Ω A →
      ∀ (u : H10 ℝ Ω) (f : Lp ℝ Ω 2), P201Specs.InteriorH2.WeakEquation Ω A u.val f →
      ∃ w : H ℝ (P201Specs.BoundaryH2.neighborhood Ω p r) 2,
        (hUnderlying _ 2 w : Space (m + 1) → ℝ)
          =ᵐ[domainMeasure (P201Specs.BoundaryH2.neighborhood Ω p r)] hZeroUnderlying Ω u ∧
        ‖w‖ ≤ C * (‖f‖ + ‖u‖) := by
  by_cases hpΩ : p ∈ Ω
  · obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp Ω.isOpen p hpΩ
    let V : Domain (m + 1) := ⟨ball p (δ / 2), isOpen_ball⟩
    let U : Domain (m + 1) := ⟨ball p (δ / 4), isOpen_ball⟩
    have hUV : P201Specs.InteriorH2.RelativelyCompactIn U V := by
      refine ⟨(isCompact_closedBall p (δ / 4)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall, ?_⟩
      intro x hx
      have hx' : dist x p ≤ δ / 4 := closure_ball_subset_closedBall hx
      change dist x p < δ / 2
      linarith
    have hVΩ : P201Specs.InteriorH2.RelativelyCompactIn V Ω := by
      refine ⟨(isCompact_closedBall p (δ / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall, ?_⟩
      intro x hx
      apply hδΩ
      have hx' : dist x p ≤ δ / 2 := closure_ball_subset_closedBall hx
      change dist x p < δ
      linarith
    have hsub : V ≤ Ω := subset_closure.trans hVΩ.2
    have hUΩ : U ≤ Ω := (subset_closure.trans hUV.2).trans hsub
    have hN : P201Specs.BoundaryH2.neighborhood Ω p (δ / 4) = U :=
      inf_eq_right.mpr hUΩ
    obtain ⟨C, hC, hEstimate⟩ := InteriorH2.interiorH2Estimate (Nat.succ_le_succ (Nat.zero_le m))
      Ω V U hUV hVΩ M L theta ht
    refine ⟨δ / 4, C * (1 + ((m + 1 : ℕ) : ℝ)), by positivity, by positivity, ?_⟩
    intro A hA _ u f heq
    rw [hN]
    obtain ⟨v, hv, hvd, hvn⟩ := BoundaryH2.h1Restriction Ω V hsub u.val
    change ‖v‖ ≤ (1 + ((m + 1 : ℕ) : ℝ)) * ‖u‖ at hvn
    let g := InteriorH2.restrictLp hsub f
    have hg : (g : Space (m + 1) → ℝ) =ᵐ[domainMeasure V] f := InteriorH2.restrictLp_ae hsub f
    have hgn : ‖g‖ ≤ ‖f‖ := InteriorH2.restrictLp_norm_le hsub f
    have heqV := BoundaryH2.weakEquationRestriction Ω V hsub A u.val v f g hvd hg heq
    have hAV : P201Specs.InteriorH2.CoefficientBounds V A M L theta :=
      ⟨fun x hx => hA.1 x (hsub hx), hA.2.1.mono hsub, fun x hx => hA.2.2 x (hsub hx)⟩
    obtain ⟨w, hw, hwn⟩ := hEstimate A hAV v g heqV
    refine ⟨w, hw.trans (ae_restrict_of_ae_restrict_of_subset
      (subset_closure.trans hUV.2) hv), ?_⟩
    calc
      ‖w‖ ≤ C * (‖v‖ + ‖g‖) := hwn
      _ ≤ C * ((1 + ((m + 1 : ℕ) : ℝ)) * ‖u‖ + ‖f‖) := by gcongr
      _ ≤ (C * (1 + ((m + 1 : ℕ) : ℝ))) * (‖f‖ + ‖u‖) := by
        have hn : 0 ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_nonneg (mul_nonneg hC.le hn) (norm_nonneg f)]
  · have hpf : p ∈ frontier (Ω : Set (Space (m + 1))) := by
      rw [frontier, Ω.isOpen.interior_eq]
      exact ⟨hp, hpΩ⟩
    obtain ⟨R, r, C, hr, _, hC, hEstimate⟩ :=
      BoundaryH2.localBoundaryEstimate Ω hb hc p hpf M L theta ht
    refine ⟨r, C * (1 + ((m + 1 : ℕ) : ℝ)), hr, by positivity, ?_⟩
    intro A hA hSym u f heq
    obtain ⟨v, g, w, hv, hg, hw, hwn⟩ := hEstimate A hA hSym u f heq
    let V := P201Specs.BoundaryH2.neighborhood Ω p R
    have hsub : V ≤ Ω := inter_subset_left
    obtain ⟨v0, hv0, _, hv0n⟩ := BoundaryH2.h1Restriction Ω V hsub u.val
    have hvv : v = v0 := hilbertUnderlyingInjective V 1 (Lp.ext (hv.trans hv0.symm))
    have hgg : g = InteriorH2.restrictLp hsub f :=
      Lp.ext (hg.trans (InteriorH2.restrictLp_ae hsub f).symm)
    have hvn : ‖v‖ ≤ (1 + ((m + 1 : ℕ) : ℝ)) * ‖u‖ := by rwa [hvv]
    have hgn : ‖g‖ ≤ ‖f‖ := by rw [hgg]; exact InteriorH2.restrictLp_norm_le hsub f
    refine ⟨w, hw, ?_⟩
    calc
      ‖w‖ ≤ C * (‖v‖ + ‖g‖) := hwn
      _ ≤ C * ((1 + ((m + 1 : ℕ) : ℝ)) * ‖u‖ + ‖f‖) := by gcongr
      _ ≤ (C * (1 + ((m + 1 : ℕ) : ℝ))) * (‖f‖ + ‖u‖) := by
        have hn : 0 ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_nonneg (mul_nonneg hC.le hn) (norm_nonneg f)]

/-- The finite-cover assembly proves the source's global Dirichlet estimate. -/
theorem globalEstimate : P201Specs.GlobalH2.globalEstimateStatement := by
  classical
  intro m Ω hb hc M L theta ht
  have hlocal (p : closure (Ω : Set (Space (m + 1)))) :=
    localEstimateAt Ω hb hc M L theta ht p p.property
  choose r C hr hC hEstimate using hlocal
  obtain ⟨s, hs⟩ := (isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hb.closure⟩).elim_finite_subcover
    (fun p : closure (Ω : Set (Space (m + 1))) => ball p.val (r p))
    (fun _ => isOpen_ball) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, mem_ball_self (hr ⟨p, hp⟩)⟩)
  let O (i : s) : Domain (m + 1) := ⟨ball i.val.val (r i.val), isOpen_ball⟩
  have hcover : closure (Ω : Set (Space (m + 1))) ⊆ ⋃ i : s, (O i : Set (Space (m + 1))) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (hs hp)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hpi⟩
  let D : ℝ := 1 + ∑ i : s, C i.val
  have hD : 0 < D := by
    dsimp [D]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (hC i.val).le))
  let N : ℝ := Fintype.card (P102.U4.SobolevIndex (m + 1) 2)
  have hN : 0 < N := by
    letI : Nonempty (P102.U4.SobolevIndex (m + 1) 2) := ⟨P102.U4.zeroSobolevIndex _ _⟩
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  refine ⟨N * D, mul_pos hN hD, ?_⟩
  intro A hA hSym u f heq
  have hw (i : s) := hEstimate i.val A hA hSym u f heq
  choose w hwu hwn using hw
  obtain ⟨v, hv, hvn⟩ := finiteH2Assembly Ω O hcover u.val w hwu
  refine ⟨v, hv, ?_⟩
  calc
    ‖v‖ ≤ N * (‖u‖ + ∑ i : s, ‖w i‖) := hvn
    _ ≤ N * (‖u‖ + ∑ i : s, C i.val * (‖f‖ + ‖u‖)) := by gcongr; exact hwn _
    _ = N * (‖u‖ + (∑ i : s, C i.val) * (‖f‖ + ‖u‖)) := by rw [Finset.sum_mul]
    _ ≤ (N * D) * (‖f‖ + ‖u‖) := by
      dsimp [D]
      nlinarith [mul_nonneg hN.le (norm_nonneg f)]

open private h1_lipschitz_multiplier matrix_entry_bound matrix_entry_lipschitz
  matrix_component_expansion regularLpLinear derivative_sum from MathGenome.Internal.LinearPDE.P201.Elliptic.BoundaryH2

/-- Realizing the divergence of an H¹ matrix flux gives the weak equation
with its actual L² source. -/
lemma weakEquation_of_fluxClasses {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (v : H ℝ Ω 1)
    (hA : ContinuousOn A Ω) {M : ℝ} (hM : ∀ x ∈ Ω, ‖A x‖ ≤ M)
    (q : Fin n → Fin n → H ℝ Ω 1)
    (hq : ∀ i j, (hUnderlying Ω 1 (q i j) : Space n → ℝ) =ᵐ[domainMeasure Ω]
      (fun x => A x (coordinate n j) i * hFirstDerivative v j x)) :
    P201Specs.InteriorH2.WeakEquation Ω A v
      (-(∑ i, ∑ j, hFirstDerivative (q i j) i) : Lp ℝ Ω 2) := by
  let hm := InteriorH2.flux_memLp Ω A (hGradient v) hA hM
  let F : MeasureTheory.Lp (Space n) 2 (domainMeasure Ω) := hm.toLp _
  have hF : (F : Space n → Space n) =ᵐ[domainMeasure Ω]
      (fun x => A x (hGradient v x)) := hm.coeFn_toLp
  have hFi (i : Fin n) : regularDistribution Ω (fun x => F x i) =
      ∑ j, regularLpLinear Ω (hUnderlying Ω 1 (q i j)) := by
    rw [← map_sum]
    apply (P102.U4.regular_injectivity n ℝ Ω _ _
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        (((Lp.memLp F).eval_piLp i).locallyIntegrable (by norm_num)))
      (P102.U4.domainLp_locallyIntegrable Ω 2 _)).mpr
    filter_upwards [hF, InteriorH2.hGradient_ae v,
      ae_all_iff.mpr (fun j => hq i j),
      Lp.coeFn_fun_finsetSum Finset.univ (fun j => hUnderlying Ω 1 (q i j))]
      with x hx hgrad hqx hsum
    rw [hsum, hx, matrix_component_expansion]
    apply Finset.sum_congr rfl
    intro j _
    rw [hqx j, hgrad]
  have hd (i j : Fin n) : distributionDerivative {i}
      (regularLpLinear Ω (hUnderlying Ω 1 (q i j))) =
      regularLpLinear Ω (hFirstDerivative (q i j) i) :=
    hilbertDerivativeDistribution Ω 1 (q i j) ⟨{i}, by simp⟩
  have hdiv : negativeDivergenceDistribution Ω F =
      regularLpLinear Ω (-(∑ i, ∑ j, hFirstDerivative (q i j) i)) := by
    change -(∑ i, distributionDerivative {i} (regularDistribution Ω (fun x => F x i))) = _
    simp_rw [hFi, derivative_sum, hd]
    simp only [map_neg, map_sum]
  intro φ
  have he := congrArg (fun T : Distribution ℝ Ω => T φ) hdiv
  change negativeDivergenceDistribution Ω F φ = regularDistribution Ω _ φ at he
  rw [InteriorTesting.negativeDivergenceDistribution_pairing,
    P102.U4.regularLp_pairing, P102.U4.lpTestPairing_eq_integral] at he
  refine Eq.trans ?_ he
  apply integral_congr_ae
  filter_upwards [hF] with x hx
  rw [hx]

/-- The prescribed H² lift has an L² divergence-form source with a uniform
bound. No derivative of the original forcing is taken. -/
theorem h2LiftSource {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (M L : ℝ≥0)
    (hAL : LipschitzOnWith L A Ω) (hAM : ∀ x ∈ Ω, ‖A x‖ ≤ M)
    (w : H ℝ Ω 2) :
    ∃ (v : H ℝ Ω 1) (g : Lp ℝ Ω 2),
      hUnderlying Ω 1 v = hUnderlying Ω 2 w ∧
      ‖v‖ ≤ (1 + (n : ℝ)) * ‖w‖ ∧
      P201Specs.InteriorH2.WeakEquation Ω A v g ∧
      ‖g‖ ≤ (n : ℝ) ^ 2 * (1 + (n : ℝ)) ^ 2 * ((M : ℝ) + L) * ‖w‖ := by
  obtain ⟨v, d, hv, hd, hvn, hdn⟩ := h2_first_order_classes Ω w
  have hq (i j : Fin n) := h1_lipschitz_multiplier Ω
    (fun x => A x (coordinate n j) i) M L (matrix_entry_lipschitz Ω A i j hAL)
    (fun x hx => (matrix_entry_bound (A x) i j).trans (hAM x hx)) (d j)
  choose q hqu hqn using hq
  let g : Lp ℝ Ω 2 := -(∑ i, ∑ j, hFirstDerivative (q i j) i)
  have hqv (i j : Fin n) : (hUnderlying Ω 1 (q i j) : Space n → ℝ) =ᵐ[domainMeasure Ω]
      (fun x => A x (coordinate n j) i * hFirstDerivative v j x) := by
    simpa only [hd j] using hqu i j
  refine ⟨v, g, hv, hvn,
    weakEquation_of_fluxClasses Ω A v hAL.continuousOn hAM q hqv, ?_⟩
  have hbound (i j : Fin n) : ‖hFirstDerivative (q i j) i‖ ≤
      (1 + (n : ℝ)) ^ 2 * ((M : ℝ) + L) * ‖w‖ := by
    calc
      _ ≤ ‖q i j‖ := InteriorH2.firstDerivative_norm_le Ω (q i j) i
      _ ≤ (1 + (n : ℝ)) * ((M : ℝ) + L) * ‖d j‖ := hqn i j
      _ ≤ (1 + (n : ℝ)) * ((M : ℝ) + L) * ((1 + (n : ℝ)) * ‖w‖) := by
        gcongr; exact hdn j
      _ = _ := by ring
  calc
    ‖g‖ = ‖∑ i, ∑ j, hFirstDerivative (q i j) i‖ := norm_neg _
    _ ≤ ∑ i, ∑ j, ‖hFirstDerivative (q i j) i‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n,
        (1 + (n : ℝ)) ^ 2 * ((M : ℝ) + L) * ‖w‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbound i j))
    _ = _ := by simp; ring

/-- Subtraction of weak equations, in the actual full H¹ and L² classes.
Symmetry permits expressing every test pairing as a continuous linear
functional on the solution class. -/
lemma weakEquation_sub {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n)
    (hA : ContinuousOn A Ω) {M : ℝ} (hM : ∀ x ∈ Ω, ‖A x‖ ≤ M)
    (hSym : P201Specs.BoundaryH2.SymmetricOn Ω A)
    (u v : H ℝ Ω 1) (f g : Lp ℝ Ω 2)
    (hu : P201Specs.InteriorH2.WeakEquation Ω A u f)
    (hv : P201Specs.InteriorH2.WeakEquation Ω A v g) :
    P201Specs.InteriorH2.WeakEquation Ω A (u - v) (f - g : Lp ℝ Ω 2) := by
  intro φ
  obtain ⟨t, ht⟩ := InteriorTesting.exists_test_class Ω φ
  have htg := InteriorTesting.smooth_gradient_ae Ω t.val φ ht
  let hm := InteriorH2.flux_memLp Ω A (hGradient t.val) hA hM
  let F : MeasureTheory.Lp (Space n) 2 (domainMeasure Ω) := hm.toLp _
  have hF : (F : Space n → Space n) =ᵐ[domainMeasure Ω]
      (fun x => A x (hGradient t.val x)) := hm.coeFn_toLp
  have hpair (z : H ℝ Ω 1) : InteriorTesting.fluxFunctional Ω F z =
      ∫ x in Ω, inner ℝ (A x (hGradient z x)) (gradient φ x) := by
    rw [InteriorTesting.fluxFunctional_integral]
    apply integral_congr_ae
    filter_upwards [hF, htg, ae_restrict_mem Ω.isOpen.measurableSet] with x hx htx hxΩ
    rw [hx, htx, hSym x hxΩ, real_inner_comm]
  have hsource (r : Lp ℝ Ω 2) : regularLpLinear Ω r φ = ∫ x in Ω, r x * φ x := by
    change regularDistribution Ω r φ = _
    rw [P102.U4.regularLp_pairing, P102.U4.lpTestPairing_eq_integral]
  rw [← hpair, map_sub, hpair u, hpair v, hu φ, hv φ,
    ← hsource f, ← hsource g, ← hsource (f - g), map_sub]
  rfl

/-- Subtract the prescribed H² lift, apply the global zero-boundary
estimate to the actual H¹₀ difference, and add the lift back. -/
theorem liftedEstimate : P201Specs.GlobalH2.liftedEstimateStatement := by
  intro m Ω hb hc M L theta ht
  obtain ⟨C, hC, hEstimate⟩ := globalEstimate Ω hb hc M L theta ht
  let K1 : ℝ := 1 + ((m + 1 : ℕ) : ℝ)
  let K2 : ℝ := ((m + 1 : ℕ) : ℝ) ^ 2 * K1 ^ 2 * ((M : ℝ) + L)
  have hK1 : 0 ≤ K1 := by dsimp [K1]; positivity
  have hK2 : 0 ≤ K2 := by dsimp [K2]; positivity
  let D : ℝ := 1 + C * (1 + K1 + K2)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro A hA hSym u w f hzero heq
  obtain ⟨v, g, hv, hvn, heqv, hgn⟩ := h2LiftSource Ω A M L hA.2.1 hA.1 w
  obtain ⟨z, hz⟩ := hzero
  have hzv : z.val = u - v := by
    apply hilbertUnderlyingInjective Ω 1
    rw [map_sub, hv]
    exact hz
  have heqz : P201Specs.InteriorH2.WeakEquation Ω A z.val (f - g : Lp ℝ Ω 2) := by
    rw [hzv]
    exact weakEquation_sub Ω A hA.2.1.continuousOn hA.1 hSym u v f g heq heqv
  obtain ⟨z2, hz2, hz2n⟩ := hEstimate A hA hSym z (f - g) heqz
  refine ⟨z2 + w, ?_, ?_⟩
  · rw [map_add, hz2, hz]
    exact sub_add_cancel _ _
  · have hzn : ‖z‖ ≤ ‖u‖ + K1 * ‖w‖ := by
      change ‖z.val‖ ≤ _
      rw [hzv]
      exact (norm_sub_le u v).trans (add_le_add le_rfl hvn)
    have hfgn : ‖f - g‖ ≤ ‖f‖ + K2 * ‖w‖ :=
      (norm_sub_le f g).trans (add_le_add le_rfl hgn)
    calc
      ‖z2 + w‖ ≤ ‖z2‖ + ‖w‖ := norm_add_le _ _
      _ ≤ C * (‖f - g‖ + ‖z‖) + ‖w‖ := add_le_add hz2n le_rfl
      _ ≤ C * ((‖f‖ + K2 * ‖w‖) + (‖u‖ + K1 * ‖w‖)) + ‖w‖ := by gcongr
      _ ≤ D * (‖f‖ + ‖u‖ + ‖w‖) := by
        change C * ((‖f‖ + K2 * ‖w‖) + (‖u‖ + K1 * ‖w‖)) + ‖w‖ ≤
          (1 + C * (1 + K1 + K2)) * (‖f‖ + ‖u‖ + ‖w‖)
        nlinarith [norm_nonneg f, norm_nonneg u,
          mul_nonneg (mul_nonneg hC.le hK1) (norm_nonneg f),
          mul_nonneg (mul_nonneg hC.le hK2) (norm_nonneg f),
          mul_nonneg (mul_nonneg hC.le hK1) (norm_nonneg u),
          mul_nonneg (mul_nonneg hC.le hK2) (norm_nonneg u),
          mul_nonneg hC.le (norm_nonneg w)]

end P201.GlobalH2
