import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Common.SmoothFlux
import MathGenome.Internal.FourierSobolev.P102.U4.GraphArea
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology NNReal

namespace P201.SmoothFlux

/-! Geometric Gauss–Green for bounded Lipschitz open sets. The final
`smooth_flux` theorem constructs its normal and proves both integrabilities.
The local horizontal calculation uses Lipschitz differentiation and compact
support, and the finite chart assembly applies in every dimension m + 1. -/

theorem graph_flux : P201Specs.SmoothFlux.GraphFluxStatement := by
  intro m U ψ L hL a ha F v
  simpa only [inner_smul_left, RCLike.conj_to_real] using
    P102.U4.GraphArea.flux m U ψ L hL a ha (fun z => v z • F z)

theorem graph_normal : P201Specs.SmoothFlux.GraphNormalStatement := by
  intro m U ψ L hL a ha
  refine ⟨P102.U4.GraphArea.ae_normal m U ψ L hL a ha, ?_⟩
  intro x
  exact P102.U4.GraphArea.jacobian_smul_unitNormal (a x)

theorem boundary_finite : P201Specs.SmoothFlux.BoundaryFiniteStatement := by
  intro m Ω hΩ
  exact P102.Trace.Ordinary.boundaryMeasure_univ_lt_top (graphFrame m) Ω hΩ

theorem divergence_product : P201Specs.SmoothFlux.DivergenceProductStatement := by
  intro n F v x hF hv
  have hi : ∀ i : Fin n, DifferentiableAt ℝ (fun y => F y i) x := by
    intro i
    exact (PiLp.proj 2 (fun _ : Fin n => ℝ) i).differentiableAt.comp x hF
  change (∑ i : Fin n, fderiv ℝ (fun y => v y * F y i) x (coordinate n i)) = _
  simp only [fderiv_fun_mul hv (hi _), add_apply, smul_apply, smul_eq_mul,
    Finset.sum_add_distrib]
  simp only [P201Specs.gradient, P201Specs.divergence,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Finset.sum_mul]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem interval_flux : P201Specs.SmoothFlux.IntervalFluxStatement := by
  intro a b F v hab hF hv
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hs : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hF' := hF.continuousOn_derivWithin hs (by rfl)
  have hv' := hv.continuousOn_derivWithin hs (by rfl)
  have he := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt
    (u := v) (v := F) (u' := derivWithin v (Icc a b)) (v' := derivWithin F (Icc a b))
    (by simpa only [uIcc_of_le hab.le] using
      fun x hx => (hv.differentiableOn (by decide) x hx).hasDerivWithinAt)
    (by simpa only [uIcc_of_le hab.le] using
      fun x hx => (hF.differentiableOn (by decide) x hx).hasDerivWithinAt)
    (hv'.intervalIntegrable_of_Icc hab.le) (hF'.intervalIntegrable_of_Icc hab.le)
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at he
  convert he using 1
  congr 1
  funext x
  ring

theorem compact_closure {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω) :
    IsCompact (closure (Ω : Set (Space (m + 1)))) := by
  have hc := hΩ.2.1.isCompact_closure.image (graphFrame m).continuous
  change IsCompact ((graphFrame m) '' closure ((graphFrame m) ⁻¹' (Ω : Set _))) at hc
  have he : (graphFrame m) '' closure ((graphFrame m) ⁻¹' (Ω : Set _)) =
      closure (Ω : Set _) := by
    calc
      _ = closure ((graphFrame m) '' ((graphFrame m) ⁻¹' (Ω : Set _))) :=
        (graphFrame m).toHomeomorph.image_closure _
      _ = _ := congrArg closure ((graphFrame m).image_preimage _)
  rwa [he] at hc

theorem continuousOn_divergence {n : ℕ} {U : Set (Space n)}
    (hU : IsOpen U) {F : Space n → Space n} (hF : ContDiffOn ℝ 1 F U) :
    ContinuousOn (divergence F) U := by
  apply continuousOn_finsetSum
  intro i _
  have hp : ContDiff ℝ 1 (PiLp.proj 2 (fun _ : Fin n => ℝ) i) :=
    ContinuousLinearMap.contDiff _
  have hi : ContDiffOn ℝ 1 (fun y => F y i) U := hp.comp_contDiffOn hF
  exact (hi.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const

theorem bulk_integrable : P201Specs.SmoothFlux.BulkIntegrableStatement := by
  intro m Ω hΩ U F v hU hΩU hF hv
  let W := fun x => v x • F x
  have hW : ContDiffOn ℝ 1 W U := hv.smul hF
  have hi := ((continuousOn_divergence hU hW).mono hΩU).integrableOn_compact (μ := volume)
    (compact_closure Ω hΩ)
  apply (hi.mono_set subset_closure).congr
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact divergence_product F v x
    ((hF.differentiableOn (by decide) x (hΩU (subset_closure hx))).differentiableAt
      (hU.mem_nhds (hΩU (subset_closure hx))))
    ((hv.differentiableOn (by decide) x (hΩU (subset_closure hx))).differentiableAt
      (hU.mem_nhds (hΩU (subset_closure hx))))

theorem boundary_flux_integrable : P201Specs.SmoothFlux.BoundaryFluxIntegrableStatement := by
  intro m Ω hΩ ν hν F v hF hv
  let μ := boundaryMeasure Ω
  let : IsFiniteMeasure μ := ⟨boundary_finite Ω hΩ⟩
  have hK : IsCompact (frontier (Ω : Set (Space (m + 1)))) :=
    (compact_closure Ω hΩ).of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hW : ContinuousOn (fun x => v x • F x)
      (frontier (Ω : Set (Space (m + 1)))) := hv.smul hF
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hW
  have hFm : AEStronglyMeasurable F μ :=
    hF.aestronglyMeasurable isClosed_frontier.measurableSet
  have hvm : AEStronglyMeasurable v μ :=
    hv.aestronglyMeasurable isClosed_frontier.measurableSet
  apply (integrable_const C).mono' (hvm.mul (hFm.inner hν.1))
  filter_upwards [P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω, hν.2] with x hx hn
  have hnorm : ‖ν x‖ = 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using hn.1
  calc
    ‖v x * inner ℝ (F x) (ν x)‖ = ‖inner ℝ (v x • F x) (ν x)‖ := by
      rw [inner_smul_left, RCLike.conj_to_real]
    _ ≤ ‖v x • F x‖ * ‖ν x‖ := norm_inner_le_norm _ _
    _ ≤ C := by simpa only [hnorm, mul_one] using hC x hx

/-- Compact C¹ functions have zero integral of every directional derivative. -/
theorem integral_fderiv_eq_zero {n : ℕ} (f : Space n → ℝ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (e : Space n) :
    (∫ x, fderiv ℝ f x e) = 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x e) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ e)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Space n => (1 : ℝ)) (g := f) (v := e)
    (by simp)
    (by simpa using hi)
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const _) (fun x _ => hf.differentiable one_ne_zero x)
  simpa using h

/-- Support is preserved by taking divergence; this uses actual Fréchet derivatives. -/
theorem divergence_eq_zero_of_not_mem_tsupport {n : ℕ} (W : Space n → Space n)
    {x : Space n} (hx : x ∉ tsupport W) : divergence W x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hs : tsupport (fun y => W y i) ⊆ tsupport W :=
    tsupport_comp_subset (g := fun z : Space n => z i) (by simp) W
  have hd := fderiv_of_notMem_tsupport (𝕜 := ℝ) (f := fun y => W y i)
    (fun h => hx (hs h))
  simp only [hd, zero_apply]

theorem interior_divergence : P201Specs.SmoothFlux.InteriorDivergenceStatement := by
  intro n Ω W hW hc hs
  have hci : ∀ i : Fin n, HasCompactSupport (fun y => W y i) := by
    intro i
    exact hc.comp_left (g := fun z : Space n => z i) (by simp)
  have hdi : ∀ i : Fin n, ContDiff ℝ 1 (fun y => W y i) := by
    intro i
    exact (PiLp.proj 2 (fun _ : Fin n => ℝ) i).contDiff.comp hW
  have hI : ∀ i : Fin n, Integrable (fun x =>
      fderiv ℝ (fun y => W y i) x (coordinate n i)) := by
    intro i
    exact (((hdi i).continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport ((hci i).fderiv_apply ℝ _)
  have hi : Integrable (divergence W) := integrable_finsetSum _ (fun i _ => hI i)
  refine ⟨hi.integrableOn, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => divergence_eq_zero_of_not_mem_tsupport W (fun h => hx (hs h)))]
  change (∫ x, ∑ i : Fin n, fderiv ℝ (fun y => W y i) x (coordinate n i)) = 0
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp only [integral_fderiv_eq_zero _ (hdi _) (hci _), Finset.sum_const_zero]

open P102.U4.GraphPieces in
/-- A vertical line has its physical Euclidean parameter, with unit speed. -/
theorem vertical_line_isometry {m : ℕ} (x : Space m) :
    Isometry (fun t : ℝ => (WithLp.toLp 2 (x, t) : Ambient m)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, ← WithLp.toLp_sub]
  simp only [Prod.mk_sub_mk, sub_self]
  rw [WithLp.norm_toLp_snd, dist_eq_norm]

open P102.U4.GraphPieces in
/-- Chain rule along a vertical physical line. -/
theorem hasDerivAt_vertical_slice {m : ℕ} (f : Ambient m → ℝ)
    (hf : Differentiable ℝ f) (x : Space m) (t : ℝ) :
    HasDerivAt (fun s => f (WithLp.toLp 2 (x, s)))
      (fderiv ℝ f (WithLp.toLp 2 (x, t)) (WithLp.toLp 2 (0, (1 : ℝ)))) t := by
  have hl : HasDerivAt (fun s : ℝ => (WithLp.toLp 2 (x, s) : Ambient m))
      (WithLp.toLp 2 (0, (1 : ℝ))) t := by
    convert! ((WithLp.linearEquiv 2 ℝ (Space m × ℝ)).symm.toContinuousLinearEquiv.hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t)) using 1
  exact (hf _).hasFDerivAt.comp_hasDerivAt t hl

theorem vertical_slice : P201Specs.SmoothFlux.VerticalSliceStatement := by
  intro m W hW hc x b
  let f : P102.U4.GraphPieces.Ambient m → ℝ := fun z => (W z).ofLp.2
  have hf : ContDiff ℝ 1 f := P102.U4.GraphArea.vertical.contDiff.comp hW
  have hfc : HasCompactSupport f := hc.comp_left
    (g := fun z : P102.U4.GraphPieces.Ambient m => z.ofLp.2) rfl
  have hg : ContDiff ℝ 1 (fun t : ℝ => f (WithLp.toLp 2 (x, t))) := by
    exact hf.comp ((WithLp.linearEquiv 2 ℝ (Space m × ℝ)).symm.toContinuousLinearEquiv.contDiff.comp
      (contDiff_const.prodMk contDiff_id))
  have hgc : HasCompactSupport (fun t : ℝ => f (WithLp.toLp 2 (x, t))) :=
    hfc.comp_isClosedEmbedding (vertical_line_isometry x).isClosedEmbedding
  have hd : deriv (fun t : ℝ => f (WithLp.toLp 2 (x, t))) =
      fun t => fderiv ℝ f (WithLp.toLp 2 (x, t)) (WithLp.toLp 2 (0, (1 : ℝ))) := by
    funext t
    exact (hasDerivAt_vertical_slice f (hf.differentiable one_ne_zero) x t).deriv
  constructor
  · have hi := (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport (μ := volume) hgc.deriv
    simpa only [hd] using hi.integrableOn (s := Ioi b)
  · simpa only [hd] using HasCompactSupport.integral_Ioi_deriv_eq hg hgc b

open P102.U4.GraphPieces P102.U4.GraphArea in
/-- Local continuity is sufficient to make the epigraph measurable;
the arbitrary values of the graph function outside its base are irrelevant. -/
theorem isOpen_epigraphSide {m : ℕ} (U : Opens (Space m))
    (ψ : Space m → ℝ) (hψ : ContinuousOn ψ U) : IsOpen (epigraphSide U ψ) := by
  have hs : IsOpen ((horizontal (m := m)) ⁻¹' (U : Set (Space m))) :=
    U.isOpen.preimage (horizontal (m := m)).continuous
  have hf : ContinuousOn (fun z : Ambient m => ψ z.ofLp.1 - z.ofLp.2)
      ((horizontal (m := m)) ⁻¹' (U : Set (Space m))) :=
    (hψ.comp (horizontal (m := m)).continuous.continuousOn (fun _ h => h)).sub
      (vertical (m := m)).continuous.continuousOn
  convert hf.isOpen_inter_preimage hs (isOpen_Iio (a := 0)) using 1
  ext z
  change (z.ofLp.1 ∈ U ∧ ψ z.ofLp.1 < z.ofLp.2) ↔
    (z.ofLp.1 ∈ U ∧ ψ z.ofLp.1 - z.ofLp.2 < 0)
  simp only [sub_lt_zero]

open P102.U4.GraphPieces P102.U4.GraphArea in
/-- Fubini on an epigraph in the Euclidean L² frame. -/
theorem integral_epigraph_slices {m : ℕ} (U : Opens (Space m))
    (ψ : Space m → ℝ) (hψ : ContinuousOn ψ U) (f : Ambient m → ℝ)
    (hf : Integrable f) :
    (∫ z in epigraphSide U ψ, f z) =
      ∫ x in (U : Set (Space m)), ∫ t in Ioi (ψ x), f (WithLp.toLp 2 (x, t)) := by
  classical
  let D := epigraphSide U ψ
  have hD : MeasurableSet D := (isOpen_epigraphSide U ψ hψ).measurableSet
  have hp := WithLp.volume_preserving_toLp (Space m) ℝ
  have hi := hp.integrable_comp_of_integrable (hf.indicator hD)
  rw [← integral_indicator hD, ← hp.integral_comp
    (MeasurableEquiv.toLp 2 (Space m × ℝ)).measurableEmbedding, Measure.volume_eq_prod,
    integral_prod (fun z : Space m × ℝ => D.indicator f (WithLp.toLp 2 z)) hi,
    ← integral_indicator U.isOpen.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : ψ x < t
    · simp [D, epigraphSide, hx, ht]
    · simp [D, epigraphSide, hx, ht]
  · simp [D, epigraphSide, hx]

theorem vertical_epigraph : P201Specs.SmoothFlux.VerticalEpigraphStatement := by
  intro m U ψ L hψ W hW hc
  let f : P102.U4.GraphPieces.Ambient m → ℝ := fun z => (W z).ofLp.2
  let e : P102.U4.GraphPieces.Ambient m := WithLp.toLp 2 (0, (1 : ℝ))
  have hf : ContDiff ℝ 1 f := P102.U4.GraphArea.vertical.contDiff.comp hW
  have hfc : HasCompactSupport f := hc.comp_left
    (g := fun z : P102.U4.GraphPieces.Ambient m => z.ofLp.2) rfl
  have hi : Integrable (fun z => fderiv ℝ f z e) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ e)
  have hE := integral_epigraph_slices U ψ hψ.continuousOn (fun z => fderiv ℝ f z e) hi
  have hslice : ∀ x : Space m,
      (∫ t in Ioi (ψ x), fderiv ℝ f (WithLp.toLp 2 (x, t)) e) =
        -(W (P102.U4.GraphPieces.graph ψ x)).ofLp.2 :=
    fun x => (vertical_slice W hW hc x (ψ x)).2
  refine ⟨hi.integrableOn, ?_, ?_⟩
  · classical
    let D := P102.U4.GraphArea.epigraphSide U ψ
    have hD : MeasurableSet D := (isOpen_epigraphSide U ψ hψ.continuousOn).measurableSet
    have hp := WithLp.volume_preserving_toLp (Space m) ℝ
    have hInt := (hp.integrable_comp_of_integrable (hi.indicator hD)).integral_prod_left
    have hEq : (fun x : Space m => ∫ t : ℝ,
        D.indicator (fun z => fderiv ℝ f z e) (WithLp.toLp 2 (x, t))) =
        (U : Set (Space m)).indicator (fun x => -(W (P102.U4.GraphPieces.graph ψ x)).ofLp.2) := by
      funext x
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx, ← hslice x, ← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        filter_upwards [] with t
        by_cases ht : ψ x < t <;> simp [D, P102.U4.GraphArea.epigraphSide, hx, ht]
      · simp [D, P102.U4.GraphArea.epigraphSide, hx]
    change Integrable (fun x : Space m => ∫ t : ℝ,
      D.indicator (fun z => fderiv ℝ f z e) (WithLp.toLp 2 (x, t))) at hInt
    rw [hEq, integrable_indicator_iff U.isOpen.measurableSet] at hInt
    convert hInt.neg using 1
    funext x
    simp only [Pi.neg_apply, neg_neg]
  · change (∫ z in P102.U4.GraphArea.epigraphSide U ψ, fderiv ℝ f z e) = _
    rw [hE]
    simp_rw [hslice]
    exact integral_neg _

/-- Divergence depends only on the germ of a vector field. -/
theorem divergence_congr_of_eventuallyEq {n : ℕ} {W Z : Space n → Space n}
    {x : Space n} (h : W =ᶠ[𝓝 x] Z) : divergence W x = divergence Z x := by
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y => W y i) =ᶠ[𝓝 x] (fun y => Z y i) :=
    h.mono (fun _ h => congrArg (fun z : Space n => z i) h)
  rw [hi.fderiv_eq]

/-- Finite sums commute with the ordinary coordinate divergence. -/
theorem divergence_sum {n k : ℕ} (W : Fin k → Space n → Space n) (x : Space n)
    (hW : ∀ j, DifferentiableAt ℝ (W j) x) :
    divergence (fun y => ∑ j, W j y) x = ∑ j, divergence (W j) x := by
  have hd : ∀ (i : Fin n) (j : Fin k),
      DifferentiableAt ℝ (fun y => W j y i) x := by
    intro i j
    exact (PiLp.proj 2 (fun _ : Fin n => ℝ) i).differentiableAt.comp x (hW j)
  change (∑ i : Fin n, fderiv ℝ (fun y => (∑ j, W j y) i) x (coordinate n i)) = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply, fderiv_fun_sum (fun j _ => hd _ j),
    sum_apply]
  exact Finset.sum_comm

theorem partition_divergence : P201Specs.SmoothFlux.PartitionDivergenceStatement := by
  intro n k χ W x hχ hW hsum
  rw [← divergence_sum (fun i y => χ i y • W y) x (fun i => (hχ i).smul hW)]
  apply divergence_congr_of_eventuallyEq
  filter_upwards [hsum] with y hy
  rw [← Finset.sum_smul, hy, one_smul]

theorem compact_localization : P201Specs.SmoothFlux.CompactLocalizationStatement := by
  intro n K U W hK hU hKU hW
  obtain ⟨S, hS, hKS, hSU, hSc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨T, _hTc, hT, hKT, hTS⟩ := exists_compact_closed_between hK hS hKS
  obtain ⟨χ, hχ, _hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hS hT hTS
  have hχtsupport : tsupport χ = closure S := congrArg closure hχsupport
  have hχcompact : HasCompactSupport χ := by
    change IsCompact (tsupport χ)
    rwa [hχtsupport]
  let Z : Space n → Space n := fun x => χ x • W x
  have hZ : ContDiff ℝ 1 Z := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact hχ.contDiffAt.smul
        ((hW x (hSU (hχtsupport ▸ hx))).contDiffAt (hU.mem_nhds (hSU (hχtsupport ▸ hx))))
    · apply (contDiffAt_const (c := (0 : Space n))).congr_of_eventuallyEq
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hx)] with y hy
      change χ y • W y = 0
      simp only [hy, Pi.zero_apply, zero_smul]
  have hZcompact : HasCompactSupport Z := hχcompact.smul_right
  have hZsupp : tsupport Z ⊆ U :=
    (tsupport_smul_subset_left χ W).trans (hχtsupport ▸ hSU)
  refine ⟨Z, interior T, isOpen_interior, hKT,
    (interior_subset.trans hTS).trans (subset_closure.trans hSU), hZ,
    hZcompact, hZsupp, ?_⟩
  intro x hx
  change χ x • W x = W x
  rw [(hχone x).mp (interior_subset hx), one_smul]

theorem finite_flux_assembly : P201Specs.SmoothFlux.FiniteFluxAssemblyStatement := by
  intro n k Ω μ ν W χ V hV hΩV hW hχ hsum hμ hbulk hbdy hlocal
  have hdiv : ∀ x ∈ (Ω : Set (Space n)),
      (∑ i, divergence (fun y => χ i y • W y) x) = divergence W x := by
    intro x hx
    have hxV := hΩV (subset_closure hx)
    apply partition_divergence χ W x (fun i => (hχ i).differentiable one_ne_zero x)
      ((hW.differentiableOn one_ne_zero x hxV).differentiableAt (hV.mem_nhds hxV))
    filter_upwards [hV.mem_nhds hxV] with y hy using hsum y hy
  have hdivAE : (fun x => ∑ i, divergence (fun y => χ i y • W y) x) =ᵐ[
      volume.restrict (Ω : Set (Space n))] divergence W := by
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx using hdiv x hx
  have hbdyAE : (fun x => ∑ i, χ i x * inner ℝ (W x) (ν x)) =ᵐ[μ]
      (fun x => inner ℝ (W x) (ν x)) := by
    filter_upwards [hμ] with x hx
    rw [← Finset.sum_mul, hsum x (hΩV hx), one_mul]
  refine ⟨(integrable_finsetSum _ (fun i _ => hbulk i)).congr hdivAE,
    (integrable_finsetSum _ (fun i _ => hbdy i)).congr hbdyAE, ?_⟩
  rw [← integral_congr_ae hdivAE, integral_finsetSum _ (fun i _ => hbulk i),
    ← integral_congr_ae hbdyAE, integral_finsetSum _ (fun i _ => hbdy i)]
  exact Finset.sum_congr rfl (fun i _ => hlocal i)

theorem compact_lipschitz_ftc : P201Specs.SmoothFlux.CompactLipschitzFTCStatement := by
  intro f L hf hc
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_lt
  have hleft : -R ∉ tsupport f := by
    intro hx
    have := hbound (-R) hx
    exact (lt_irrefl R) (by simpa only [norm_neg, Real.norm_of_nonneg hR.le] using this)
  have hright : R ∉ tsupport f := by
    intro hx
    have := hbound R hx
    exact (lt_irrefl R) (by simpa only [Real.norm_of_nonneg hR.le] using this)
  have hs : tsupport (deriv f) ⊆ Ioc (-R) R := by
    intro x hx
    have hb := hbound x (tsupport_deriv_subset hx)
    rw [Real.norm_eq_abs, abs_lt] at hb
    exact ⟨hb.1, hb.2.le⟩
  have hac : AbsolutelyContinuousOnInterval f (-R) R := hf.lipschitzOnWith.absolutelyContinuousOnInterval
  have hab : -R ≤ R := by linarith
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hac.intervalIntegrable_deriv
  refine ⟨(integrableOn_iff_integrable_of_support_subset ((subset_tsupport _).trans hs)).mp hi, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-R) R)
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)))]
  rw [← intervalIntegral.integral_of_le hab, hac.integral_deriv_eq_sub,
    image_eq_zero_of_notMem_tsupport hleft, image_eq_zero_of_notMem_tsupport hright, sub_self]

theorem map_restrict_hausdorff {X Y : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ᵢ Y) (d : ℕ) (S : Set X) :
    Measure.map e ((μHE[d] : Measure X).restrict S) =
      (μHE[d] : Measure Y).restrict (e '' S) := by
  calc
    _ = Measure.map e ((μHE[d] : Measure X).restrict (e ⁻¹' (e '' S))) := by
      rw [Set.preimage_image_eq S e.injective]
    _ = (Measure.map e (μHE[d] : Measure X)).restrict (e '' S) :=
      (e.toHomeomorph.measurableEmbedding.restrict_map _ _).symm
    _ = _ := by rw [(e.measurePreserving_euclideanHausdorffMeasure d).map_eq]

open P102.U4.GraphPieces P102.U4.GraphArea P102.Sobolev.Geometry in
theorem chart_surface_map : P201Specs.SmoothFlux.ChartSurfaceMapStatement := by
  intro m e Ω C
  let q := C.frame.toIsometryEquiv.trans e.toIsometryEquiv
  have h := map_restrict_hausdorff q m
    (graph C.graphFunction '' Metric.ball C.center C.radius)
  change Measure.map (fun z => e (C.frame z))
    ((μHE[m] : Measure (Ambient m)).restrict (graph C.graphFunction '' Metric.ball C.center C.radius)) = _
  have hq : (fun z => e (C.frame z)) = (q : Ambient m → Space (m + 1)) := rfl
  rw [hq, h]
  change (μHE[m] : Measure (Space (m + 1))).restrict
    ((fun z => e (C.frame z)) '' (graph C.graphFunction '' Metric.ball C.center C.radius)) = _
  rw [← Set.image_comp]
  change (μHE[m] : Measure (Space (m + 1))).restrict
    ((e ∘ C.frame ∘ graph C.graphFunction) '' Metric.ball C.center C.radius) = _
  rw [P102.Trace.Ordinary.physical_graph_image_eq e Ω C]
  change _ = ((μHE[m] : Measure (Space (m + 1))).restrict
    (frontier (Ω : Set (Space (m + 1))))).restrict
      (e '' chartImage C.frame C.graphFunction C.center C.radius C.height)
  rw [Measure.restrict_restrict]
  · rw [Set.inter_comm]
  · exact (e.toHomeomorph.isOpenMap _ (chartImage_open C.frame C.graph_lipschitz)).measurableSet

theorem divergence_eq_trace {n : ℕ} (F : Space n → Space n) (x : Space n)
    (hF : DifferentiableAt ℝ F x) :
    divergence F x = LinearMap.trace ℝ (Space n) (fderiv ℝ F x).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  have h := (PiLp.proj 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.comp x hF.hasFDerivAt
  rw [show fderiv ℝ (fun y => F y i) x =
    (PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp (fderiv ℝ F x) from h.fderiv]
  simp [P201Specs.coordinate, P102.U4.coordinateVector, EuclideanSpace.inner_single_left]

theorem trace_fderiv_affine_pullback {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E']
    (e : E ≃ᵃⁱ[ℝ] E') (F : E' → E') (x : E)
    (hF : DifferentiableAt ℝ F (e x)) :
    LinearMap.trace ℝ E
      (fderiv ℝ (fun y => e.linearIsometryEquiv.symm (F (e y))) x).toLinearMap =
      LinearMap.trace ℝ E' (fderiv ℝ F (e x)).toLinearMap := by
  let q := e.linearIsometryEquiv.toContinuousLinearEquiv
  have he : HasFDerivAt e q.toContinuousLinearMap x :=
    e.toAffineIsometry.toContinuousAffineMap.hasFDerivAt
  have h := q.symm.hasFDerivAt.comp x (hF.hasFDerivAt.comp x he)
  change LinearMap.trace ℝ E (fderiv ℝ (q.symm ∘ F ∘ e) x).toLinearMap = _
  rw [h.fderiv]
  change LinearMap.trace ℝ E
    (q.toLinearEquiv.symm.conj (fderiv ℝ F (e x)).toLinearMap) = _
  exact LinearMap.trace_conj' _ _

open P102.U4.GraphPieces P102.U4.GraphArea

theorem graphFrame_symm_horizontal {m : ℕ} (i : Fin m) :
    (graphFrame m).symm (coordinate (m+1) i.castSucc) =
      (WithLp.toLp 2 (coordinate m i, (0 : ℝ)) : Ambient m) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · ext j
    change (P102.Trace.Ordinary.alignedCoordinates m (coordinate (m+1) i.castSucc)).ofLp.1 j = _
    rw [P102.Trace.Ordinary.alignedCoordinates_horizontal]
    simp [P102.U4.coordinateVector, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  · change (P102.Trace.Ordinary.alignedCoordinates m (coordinate (m+1) i.castSucc)).ofLp.2 = _
    rw [P102.Trace.Ordinary.alignedCoordinates_height]
    simp [P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]

theorem graphFrame_symm_vertical {m : ℕ} :
    (graphFrame m).symm (coordinate (m+1) (Fin.last m)) =
      (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)) : Ambient m) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · ext j
    change (P102.Trace.Ordinary.alignedCoordinates m (coordinate (m+1) (Fin.last m))).ofLp.1 j = _
    rw [P102.Trace.Ordinary.alignedCoordinates_horizontal]
    simp [P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]
  · change (P102.Trace.Ordinary.alignedCoordinates m (coordinate (m+1) (Fin.last m))).ofLp.2 = _
    rw [P102.Trace.Ordinary.alignedCoordinates_height]
    simp [P102.U4.coordinateVector, EuclideanSpace.basisFun_apply]


theorem ambient_trace_eq_components {m : ℕ} (W : Ambient m → Ambient m)
    (z : Ambient m) (hW : DifferentiableAt ℝ W z) :
    LinearMap.trace ℝ (Ambient m) (fderiv ℝ W z).toLinearMap =
      (∑ i : Fin m, fderiv ℝ (fun y => (W y).ofLp.1 i) z
        (WithLp.toLp 2 (coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (W y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ))) := by
  rw [LinearMap.trace_eq_sum_inner _
    ((EuclideanSpace.basisFun (Fin (m+1)) ℝ).map (graphFrame m).symm)]
  simp only [OrthonormalBasis.map_apply]
  change (∑ i : Fin (m+1), inner ℝ ((graphFrame m).symm (coordinate (m+1) i))
    (fderiv ℝ W z ((graphFrame m).symm (coordinate (m+1) i)))) = _
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [graphFrame_symm_horizontal]
    have h := ((PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp horizontal).hasFDerivAt.comp z hW.hasFDerivAt
    rw [show fderiv ℝ (fun y => (W y).ofLp.1 i) z =
      ((PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp horizontal).comp (fderiv ℝ W z) from h.fderiv]
    simp [WithLp.prod_inner_apply, P102.U4.coordinateVector, EuclideanSpace.inner_single_left,
      horizontal]
  · rw [graphFrame_symm_vertical]
    have h := (vertical (m := m)).hasFDerivAt.comp z hW.hasFDerivAt
    rw [show fderiv ℝ (fun y => (W y).ofLp.2) z =
      (vertical (m := m)).comp (fderiv ℝ W z) from h.fderiv]
    simp [WithLp.prod_inner_apply, vertical, RCLike.inner_apply]

theorem affine_chart_divergence {m : ℕ}
    (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (F : Space (m+1) → Space (m+1))
    (z : Ambient m) (hF : DifferentiableAt ℝ F (graphFrame m (e z))) :
    let W : Ambient m → Ambient m := fun y => e.linearIsometryEquiv.symm
      ((graphFrame m).symm (F (graphFrame m (e y))))
    divergence F (graphFrame m (e z)) =
      (∑ i : Fin m, fderiv ℝ (fun y => (W y).ofLp.1 i) z
        (WithLp.toLp 2 (coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (W y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ))) := by
  let a := e.trans (graphFrame m).toAffineIsometryEquiv
  let W : Ambient m → Ambient m := fun y => e.linearIsometryEquiv.symm
      ((graphFrame m).symm (F (graphFrame m (e y))))
  have ha : HasFDerivAt a a.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap z :=
    a.toAffineIsometry.toContinuousAffineMap.hasFDerivAt
  have hW : DifferentiableAt ℝ W z :=
    a.linearIsometryEquiv.symm.differentiableAt.comp z (hF.comp z ha.differentiableAt)
  have ht := trace_fderiv_affine_pullback a F z hF
  change LinearMap.trace ℝ (Ambient m) (fderiv ℝ W z).toLinearMap = _ at ht
  rw [divergence_eq_trace F _ hF]
  exact ht.symm.trans (ambient_trace_eq_components W z hW)


section
open Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ray_isometry (e : E) (he : ‖e‖ = 1) (z : E) :
    Isometry (fun t : ℝ => z + t • e) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, he, mul_one, dist_eq_norm]

theorem hasFDerivAt_ray_primitive (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (e : E) (he : ‖e‖ = 1) (z₀ : E) :
    HasFDerivAt (fun z => ∫ t in Ioi (0 : ℝ), f (z + t • e))
      (∫ t in Ioi (0 : ℝ), fderiv ℝ f (z₀ + t • e)) z₀ := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  obtain ⟨R, hR, hbound⟩ := (hc.fderiv ℝ).isBounded.exists_pos_norm_lt
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hd
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z₀)
  let T : ℝ := R + ‖z₀‖ + 1
  let b : ℝ → ℝ := (Icc 0 T).indicator (fun _ => C)
  have hb : Integrable b (volume.restrict (Ioi 0)) := by
    apply Integrable.integrableOn
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by simp only [Real.volume_Icc]; finiteness)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball z₀ 1)
    (bound := b) (ball_mem_nhds z₀ zero_lt_one)
  · filter_upwards [] with z
    exact (hf.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable
  · exact (hf.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).integrable_of_hasCompactSupport
      (hc.comp_isClosedEmbedding (ray_isometry e he z₀).isClosedEmbedding) |>.integrableOn
  · exact (hd.comp (continuous_const.add (continuous_id.smul continuous_const))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    by_cases htT : t ≤ T
    · change ‖fderiv ℝ f (z + t • e)‖ ≤ (Icc 0 T).indicator (fun _ => C) t
      rw [indicator_of_mem (show t ∈ Icc 0 T from ⟨ht.le, htT⟩)]
      exact hC _
    · have hn : z + t • e ∉ tsupport (fderiv ℝ f) := by
        intro hx
        have hnorm := hbound _ hx
        have hznorm : ‖z‖ < ‖z₀‖ + 1 := by
          rw [mem_ball, dist_eq_norm] at hz
          have := norm_add_le (z - z₀) z₀
          rw [sub_add_cancel] at this
          linarith
        have htri := norm_sub_le (z + t • e) z
        rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_of_nonneg ht.le] at htri
        change ¬ t ≤ R + ‖z₀‖ + 1 at htT
        linarith
      rw [image_eq_zero_of_notMem_tsupport hn, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hC0) _
  · exact hb
  · filter_upwards [] with t z _
    convert! (hf.differentiable one_ne_zero _).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const (t • e)) using 1

 theorem integrable_ray_fderiv (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (e : E) (he : ‖e‖ = 1) (z : E) :
    Integrable (fun t : ℝ => fderiv ℝ f (z + t • e)) :=
  ((hf.continuous_fderiv one_ne_zero).comp
    (continuous_const.add (continuous_id.smul continuous_const))).integrable_of_hasCompactSupport
      ((hc.fderiv ℝ).comp_isClosedEmbedding (ray_isometry e he z).isClosedEmbedding)

theorem integral_ray_vertical_fderiv (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (e : E) (he : ‖e‖ = 1) (z : E) :
    (∫ t in Ioi (0 : ℝ), fderiv ℝ f (z + t • e) e) = -f z := by
  have hg : ContDiff ℝ 1 (fun t : ℝ => f (z + t • e)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hgc : HasCompactSupport (fun t : ℝ => f (z + t • e)) :=
    hc.comp_isClosedEmbedding (ray_isometry e he z).isClosedEmbedding
  have hd : deriv (fun t : ℝ => f (z + t • e)) =
      fun t => fderiv ℝ f (z + t • e) e := by
    funext t
    simpa only [Function.comp_def, Pi.add_apply, Pi.smul_apply, id_eq, zero_add, one_smul] using
      ((hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t z).add ((hasDerivAt_id t).smul_const e))).deriv
  simpa only [hd, zero_smul, add_zero] using HasCompactSupport.integral_Ioi_deriv_eq hg hgc 0

theorem ray_primitive_derivative_apply (f : E → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (e : E) (he : ‖e‖ = 1) (z h : E) (c : ℝ) :
    (fderiv ℝ (fun z => ∫ t in Ioi (0 : ℝ), f (z + t • e)) z) (h + c • e) =
      (∫ t in Ioi (0 : ℝ), fderiv ℝ f (z + t • e) h) - c * f z := by
  rw [(hasFDerivAt_ray_primitive f hf hc e he z).fderiv,
    ContinuousLinearMap.integral_apply (integrable_ray_fderiv f hf hc e he z).integrableOn]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [integral_add ((integrable_ray_fderiv f hf hc e he z).apply_continuousLinearMap h).integrableOn
    (((integrable_ray_fderiv f hf hc e he z).apply_continuousLinearMap e).const_mul c).integrableOn,
    integral_const_mul, integral_ray_vertical_fderiv f hf hc e he z, mul_neg, sub_eq_add_neg]

open scoped InnerProductSpace
open P102.U4 P102.U4.GraphPieces P102.U4.GraphArea

theorem fderiv_graph_ray_primitive {m : ℕ} (f : Ambient m → ℝ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (ψ : Space m → ℝ)
    {x a : Space m} (hψ : HasFDerivAt ψ (innerSL ℝ a) x) (q : Space m) :
    fderiv ℝ (fun x => ∫ t in Ioi (0 : ℝ),
      f (graph ψ x + t • (WithLp.toLp 2 (0, (1 : ℝ)) : Ambient m))) x q =
      (∫ t in Ioi (0 : ℝ),
        fderiv ℝ f (graph ψ x + t • (WithLp.toLp 2 (0, (1 : ℝ)) : Ambient m))
          (WithLp.toLp 2 (q, (0 : ℝ)))) - inner ℝ a q * f (graph ψ x) := by
  let e : Ambient m := WithLp.toLp 2 (0, (1 : ℝ))
  have he : ‖e‖ = 1 := by simp only [e, WithLp.norm_toLp_snd, norm_one]
  have hQ := (hasFDerivAt_ray_primitive f hf hc e he (graph ψ x)).comp x
    (P102.U4.GraphArea.hasFDerivAt_graph hψ)
  change (fderiv ℝ ((fun z => ∫ t in Ioi (0 : ℝ), f (z + t • e)) ∘ graph ψ) x) q = _
  rw [hQ.fderiv, ContinuousLinearMap.comp_apply]
  change (∫ t in Ioi (0 : ℝ), fderiv ℝ f (graph ψ x + t • e))
    ((affineGraph a) q) = _
  have ha : affineGraph a q = WithLp.toLp 2 (q, (0 : ℝ)) + inner ℝ a q • e := by
    apply WithLp.ofLp_injective
    simp [affineGraph, e]
  rw [ha]
  simpa only [(hasFDerivAt_ray_primitive f hf hc e he (graph ψ x)).fderiv] using
    (ray_primitive_derivative_apply f hf hc e he (graph ψ x)
    (WithLp.toLp 2 (q, (0 : ℝ))) (inner ℝ a q))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem exists_lipschitz_ray_primitive (f : H → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (e : H) (he : ‖e‖ = 1) :
    ∃ K : ℝ≥0, LipschitzWith K (fun z => ∫ t in Ioi (0 : ℝ), f (z + t • e)) := by
  obtain ⟨R, hR, hbound⟩ := (hc.fderiv ℝ).isBounded.exists_pos_norm_lt
  obtain ⟨C, hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv one_ne_zero)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let K : ℝ≥0 := ⟨C * (2 * R), by positivity⟩
  refine ⟨K, lipschitzWith_of_nnnorm_fderiv_le
    (fun z => (hasFDerivAt_ray_primitive f hf hc e he z).differentiableAt) ?_⟩
  intro z
  rw [← NNReal.coe_le_coe]
  change ‖fderiv ℝ (fun z => ∫ t in Ioi (0 : ℝ), f (z + t • e)) z‖ ≤ C * (2 * R)
  rw [(hasFDerivAt_ray_primitive f hf hc e he z).fderiv]
  let J : Set ℝ := Icc (-R - inner ℝ e z) (R - inner ℝ e z)
  let g : ℝ → H →L[ℝ] ℝ := (Ioi 0).indicator (fun t => fderiv ℝ f (z + t • e))
  have hz : ∀ t ∉ J, g t = 0 := by
    intro t ht
    by_cases ht0 : 0 < t
    · change (Ioi 0).indicator (fun t => fderiv ℝ f (z + t • e)) t = 0
      rw [indicator_of_mem (show t ∈ Ioi 0 from ht0)]
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hnorm := hbound _ hx
      have hip := norm_inner_le_norm (𝕜 := ℝ) e (z + t • e)
      have hself : inner ℝ e e = 1 := by simpa only [he, one_pow] using real_inner_self_eq_norm_sq e
      rw [inner_add_right, inner_smul_right, hself, mul_one, he, one_mul] at hip
      rw [Real.norm_eq_abs, abs_le] at hip
      have hj : t ∈ J := by
        change -R - inner ℝ e z ≤ t ∧ t ≤ R - inner ℝ e z
        constructor <;> linarith [hip.1, hip.2]
      exact ht hj
    · exact indicator_of_notMem ht0 _
  rw [← integral_indicator measurableSet_Ioi,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  calc
    ‖∫ t in J, g t‖ ≤ C * volume.real J :=
      norm_setIntegral_le_of_norm_le_const (by simp only [J, Real.volume_Icc]; finiteness)
        (fun t _ => by
          by_cases ht : 0 < t
          · change ‖(Ioi 0).indicator (fun t => fderiv ℝ f (z + t • e)) t‖ ≤ C
            rw [indicator_of_mem (show t ∈ Ioi 0 from ht)]
            exact hC _
          · change ‖(Ioi 0).indicator (fun t => fderiv ℝ f (z + t • e)) t‖ ≤ C
            rw [indicator_of_notMem (show t ∉ Ioi 0 from ht), norm_zero]
            exact hC0)
    _ = C * (2 * R) := by
      change C * volume.real (Icc (-R - inner ℝ e z) (R - inner ℝ e z)) = _
      rw [Real.volume_real_Icc]
      have heq : R - inner ℝ e z - (-R - inner ℝ e z) = 2 * R := by ring
      rw [heq, max_eq_left (by positivity)]

end

theorem ray_primitive : P201Specs.SmoothFlux.RayPrimitiveStatement := by
  intro E _ _ f hf hc e he z₀
  exact hasFDerivAt_ray_primitive f hf hc e he z₀

section
open Metric P102.Sobolev.Geometry

/-- Graph epigraph and the upper sheared cylinder agree inside the symmetric chart. -/
theorem epigraph_inter_chart {m : ℕ}
    (e : Ambient m ≃ᵃⁱ[ℝ] Ambient m) (γ : Space m → ℝ)
    (c : Space m) (r h : ℝ) (hh : 0 < h) :
    (e '' epigraphSide ⟨ball c r, isOpen_ball⟩ γ) ∩ chartImage e γ c r h =
      e '' (shear γ '' upperCylinder c r h) := by
  rw [chartImage, ← Set.image_inter e.injective]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, w, hw, rfl⟩
    refine ⟨w, ⟨hw.1, ?_, hw.2.2⟩, rfl⟩
    have hz' : γ w.ofLp.1 < γ w.ofLp.1 + w.ofLp.2 := hz.2
    exact (lt_add_iff_pos_right _).mp hz'
  · rintro ⟨w, hw, rfl⟩
    constructor
    · exact ⟨hw.1, (lt_add_iff_pos_right _).mpr hw.2.1⟩
    · exact ⟨w, ⟨hw.1, by linarith [hw.2.1], hw.2.2⟩, rfl⟩

theorem chart_local_geometry {m : ℕ} {G : Set (Ambient m)}
    (C : BoundaryChart G) {p : Ambient m}
    (hp : p ∈ C.frame '' (graph C.graphFunction '' ball C.center C.radius)) :
    (C.frame '' epigraphSide ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction)
        =ᶠ[𝓝 p] G ∧
    (C.frame '' (graph C.graphFunction '' ball C.center C.radius))
        =ᶠ[𝓝 p] frontier G := by
  have hpQ : p ∈ chartImage C.frame C.graphFunction C.center C.radius C.height := by
    rw [← C.boundary] at hp
    exact hp.2
  have hQ := (chartImage_open C.frame C.graph_lipschitz).mem_nhds hpQ
  constructor
  · filter_upwards [hQ] with z hz
    have hset : G ∩ chartImage C.frame C.graphFunction C.center C.radius C.height =
        (C.frame '' epigraphSide ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction) ∩
          chartImage C.frame C.graphFunction C.center C.radius C.height :=
      C.side.trans (epigraph_inter_chart C.frame C.graphFunction C.center C.radius C.height C.height_pos).symm
    have hm := congrArg (fun S : Set (Ambient m) => z ∈ S) hset
    simpa only [mem_inter_iff, hz, and_true] using hm.symm
  · filter_upwards [hQ] with z hz
    have hm := congrArg (fun S : Set (Ambient m) => z ∈ S) C.boundary
    simpa only [mem_inter_iff, hz, and_true] using hm.symm

/-- A differentiable graph point supplies the actual outward normal and its
full tangent hyperplane for the given open set. -/
theorem chart_normal_at {m : ℕ} {G : Set (Ambient m)}
    (C : BoundaryChart G) (x a : Space m) (hx : x ∈ ball C.center C.radius)
    (hd : HasFDerivAt C.graphFunction (innerSL ℝ a) x) :
    OutwardUnitNormal G (frontier G) (C.frame (graph C.graphFunction x))
      (C.frame.linearIsometryEquiv (unitNormal a)) ∧
    tangentConeAt ℝ (frontier G) (C.frame (graph C.graphFunction x)) =
      ((ℝ ∙ C.frame.linearIsometryEquiv (unitNormal a))ᗮ : Set (Ambient m)) := by
  have hp : C.frame (graph C.graphFunction x) ∈
      C.frame '' (graph C.graphFunction '' ball C.center C.radius) := ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨hG, hS⟩ := chart_local_geometry C hp
  constructor
  · exact outward_congr hG hS (outward_affine_image C.frame
      (outward m ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction x a hx hd))
  · rw [← tangentConeAt_congr (nhdsWithin_eq_iff_eventuallyEqSet.mpr hS),
      tangentCone_affine_image]
    have ht := tangent_orthogonal ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction x a hx hd
    change tangentConeAt ℝ (graph C.graphFunction '' ball C.center C.radius)
      (graph C.graphFunction x) = _ at ht
    rw [ht, isometry_image_orthogonal_singleton]

end

section
open Metric P102.U4 P102.Sobolev.Geometry

def chartNormal {m : ℕ} {G : Set (Ambient m)} (C : BoundaryChart G)
    (a : Space m → Space m) (p : Ambient m) : Ambient m :=
  C.frame.linearIsometryEquiv (normalField a (C.frame.symm p))

theorem measurable_chartNormal {m : ℕ} {G : Set (Ambient m)} (C : BoundaryChart G)
    {a : Space m → Space m} (ha : Measurable a) : Measurable (chartNormal C a) :=
  C.frame.linearIsometryEquiv.continuous.measurable.comp
    ((measurable_normalField ha).comp C.frame.symm.continuous.measurable)

theorem chart_normal_ae {m : ℕ} {G : Set (Ambient m)} (C : BoundaryChart G)
    (a : Space m → Space m)
    (ha : GradientRepresentative ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction a) :
    ∀ᵐ p ∂(μHE[m] : Measure (Ambient m)).restrict (frontier G),
      p ∈ chartImage C.frame C.graphFunction C.center C.radius C.height →
        OutwardUnitNormal G (frontier G) p (chartNormal C a p) ∧
        tangentConeAt ℝ (frontier G) p =
          ((ℝ ∙ chartNormal C a p)ᗮ : Set (Ambient m)) := by
  let U : Opens (Space m) := ⟨ball C.center C.radius, isOpen_ball⟩
  have hs : ∀ᵐ p ∂(μHE[m] : Measure (Ambient m)).restrict
      (C.frame '' (graph C.graphFunction '' ball C.center C.radius)),
      OutwardUnitNormal G (frontier G) p (chartNormal C a p) ∧
        tangentConeAt ℝ (frontier G) p =
          ((ℝ ∙ chartNormal C a p)ᗮ : Set (Ambient m)) := by
    have hm : Measure.map C.frame
        ((μHE[m] : Measure (Ambient m)).restrict (graph C.graphFunction '' ball C.center C.radius)) =
        (μHE[m] : Measure (Ambient m)).restrict
          (C.frame '' (graph C.graphFunction '' ball C.center C.radius)) :=
      map_restrict_hausdorff C.frame.toIsometryEquiv m _
    rw [← hm]
    apply C.frame.toHomeomorph.measurableEmbedding.ae_map_iff.mpr
    change ∀ᵐ z ∂surfaceMeasure U C.graphFunction,
      OutwardUnitNormal G (frontier G) (C.frame z) (chartNormal C a (C.frame z)) ∧
        tangentConeAt ℝ (frontier G) (C.frame z) =
          ((ℝ ∙ chartNormal C a (C.frame z))ᗮ : Set (Ambient m))
    rw [← map_weighted_volume U C.graphFunction C.constant C.graph_lipschitz a ha]
    apply (borelParam_embedding U C.graphFunction C.graph_lipschitz.continuousOn).ae_map_iff.mpr
    apply (withDensity_absolutelyContinuous _ _)
    filter_upwards [ha.2, ae_restrict_mem isOpen_ball.measurableSet] with x hd hx
    rw [borelParam_eq U C.graphFunction hx]
    simpa only [chartNormal, AffineIsometryEquiv.symm_apply_apply, normalField, graph,
      WithLp.ofLp_toLp] using chart_normal_at C x (a x) hx hd
  have hQ : MeasurableSet (chartImage C.frame C.graphFunction C.center C.radius C.height) :=
    (chartImage_open C.frame C.graph_lipschitz).measurableSet
  have hμ : (μHE[m] : Measure (Ambient m)).restrict
      (C.frame '' (graph C.graphFunction '' ball C.center C.radius)) =
      ((μHE[m] : Measure (Ambient m)).restrict (frontier G)).restrict
        (chartImage C.frame C.graphFunction C.center C.radius C.height) := by
    rw [← C.boundary, Measure.restrict_restrict hQ, Set.inter_comm]
  rw [hμ] at hs
  exact (ae_restrict_iff' hQ).mp hs

/-- Finitely many measurable local witnesses can be patched without any
compatibility assumption, by giving the newly added patch precedence. -/
theorem finite_measurable_pasting {X E ι : Type*}
    [MeasurableSpace X] [MeasurableSpace E] [Zero E]
    (μ : Measure X) (s : ι → Set X) (f : ι → X → E)
    (P : X → E → Prop) (hs : ∀ i, MeasurableSet (s i))
    (hf : ∀ i, Measurable (f i))
    (hP : ∀ i, ∀ᵐ x ∂μ, x ∈ s i → P x (f i x)) (t : Finset ι) :
    ∃ g : X → E, Measurable g ∧
      ∀ᵐ x ∂μ, (∃ i ∈ t, x ∈ s i) → P x (g x) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 0, measurable_const, by simp⟩
  | @insert i t hi ih =>
    obtain ⟨g, hg, hgp⟩ := ih
    refine ⟨(s i).piecewise (f i) g, (hf i).piecewise (hs i) hg, ?_⟩
    filter_upwards [hP i, hgp] with x hxi hxt hx
    by_cases hxs : x ∈ s i
    · rw [piecewise_eq_of_mem _ _ _ hxs]
      exact hxi hxs
    · rw [piecewise_eq_of_notMem _ _ _ hxs]
      apply hxt
      obtain ⟨j, hj, hxj⟩ := hx
      have hjt : j ∈ t := by
        rcases Finset.mem_insert.mp hj with rfl | h
        · exact False.elim (hxs hxj)
        · exact h
      exact ⟨j, hjt, hxj⟩


theorem geometric_normal_exists_ambient {m : ℕ} {G : Set (Ambient m)}
    (hG : IsLipschitzOpen G) :
    ∃ ν : Ambient m → Ambient m, Measurable ν ∧
      ∀ᵐ p ∂(μHE[m] : Measure (Ambient m)).restrict (frontier G),
        OutwardUnitNormal G (frontier G) p (ν p) ∧
          tangentConeAt ℝ (frontier G) p = ((ℝ ∙ ν p)ᗮ : Set (Ambient m)) := by
  classical
  obtain ⟨n, C, hcover⟩ := finite_boundary_cover hG
  have hgrad (i : Fin n) := gradient_existence m
    ⟨ball (C i).center (C i).radius, isOpen_ball⟩ (C i).graphFunction
    (C i).constant (C i).graph_lipschitz
  choose a ha using hgrad
  let S (i : Fin n) := chartImage (C i).frame (C i).graphFunction
    (C i).center (C i).radius (C i).height
  let μ := (μHE[m] : Measure (Ambient m)).restrict (frontier G)
  let P (p v : Ambient m) := OutwardUnitNormal G (frontier G) p v ∧
    tangentConeAt ℝ (frontier G) p = ((ℝ ∙ v)ᗮ : Set (Ambient m))
  obtain ⟨ν, hνm, hνp⟩ := finite_measurable_pasting μ S
    (fun i => chartNormal (C i) (a i)) P
    (fun i => (chartImage_open (C i).frame (C i).graph_lipschitz).measurableSet)
    (fun i => measurable_chartNormal (C i) (ha i).1)
    (fun i => chart_normal_ae (C i) (a i) (ha i)) Finset.univ
  refine ⟨ν, hνm, ?_⟩
  filter_upwards [hνp, ae_restrict_mem isClosed_frontier.measurableSet] with p hp hpf
  apply hp
  obtain ⟨i, hpi⟩ := mem_iUnion.mp (hcover hpf)
  refine ⟨i, Finset.mem_univ _, ?_⟩
  exact chartImage_mono (C i).frame (C i).graphFunction (C i).center
    (by linarith [(C i).radius_pos]) (by linarith [(C i).height_pos]) hpi

open P102.Sobolev.Extension in
/-- Existence of a Borel physical geometric normal, with the local hyperplane
property retained for a.e. uniqueness. -/
theorem geometric_normal_exists {m : ℕ} (Ω : P201.Domain (m + 1))
    (hΩ : P201.IsBoundedLipschitzOpen Ω) :
    ∃ ν : P201.Space (m + 1) → P201.Space (m + 1), Measurable ν ∧
      P201Specs.SmoothFlux.IsGeometricNormalField Ω ν ∧
      ∀ᵐ p ∂P201.boundaryMeasure Ω,
        tangentConeAt ℝ
          (frontier (geometricOpen (P201.graphFrame m) Ω : Set (Ambient m)))
          ((P201.graphFrame m).symm p) =
            ((ℝ ∙ (P201.graphFrame m).symm (ν p))ᗮ : Set (Ambient m)) := by
  let e := P201.graphFrame m
  let G : Set (Ambient m) := geometricOpen e Ω
  let μ := (μHE[m] : Measure (Ambient m)).restrict (frontier G)
  obtain ⟨η, hηm, hη⟩ := geometric_normal_exists_ambient hΩ
  let ν : P201.Space (m + 1) → P201.Space (m + 1) := fun p => e (η (e.symm p))
  have hνm : Measurable ν := e.continuous.measurable.comp
    (hηm.comp e.symm.continuous.measurable)
  have hμ : Measure.map e μ = P201.boundaryMeasure Ω := by
    have h := map_restrict_hausdorff e.toIsometryEquiv m (frontier G)
    have hfront : e '' frontier G = frontier (Ω : Set (P201.Space (m + 1))) := by
      calc
        _ = frontier (e '' G) := e.toHomeomorph.image_frontier _
        _ = _ := congrArg frontier (e.image_preimage _)
    change Measure.map e ((μHE[m] : Measure (Ambient m)).restrict (frontier G)) =
      (μHE[m] : Measure (P201.Space (m + 1))).restrict (e '' frontier G) at h
    change Measure.map e ((μHE[m] : Measure (Ambient m)).restrict (frontier G)) = _
    simpa only [P201.boundaryMeasure, P201Specs.boundaryMeasure,
      P102.Trace.Ordinary.boundaryMeasure, hfront] using h
  have hgood : ∀ᵐ p ∂P201.boundaryMeasure Ω,
      P201Specs.SmoothFlux.GeometricNormalAt Ω p (ν p) ∧
      tangentConeAt ℝ (frontier G) (e.symm p) =
        ((ℝ ∙ e.symm (ν p))ᗮ : Set (Ambient m)) := by
    rw [← hμ]
    apply e.toHomeomorph.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hη] with p hp
    simpa only [P201Specs.SmoothFlux.GeometricNormalAt, ν, e,
      LinearIsometryEquiv.coe_toHomeomorph, LinearIsometryEquiv.symm_apply_apply] using hp
  exact ⟨ν, hνm, ⟨hνm.aestronglyMeasurable, hgood.mono (fun _ h => h.1)⟩,
    hgood.mono (fun _ h => h.2)⟩


end

theorem affine_measurePreserving {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E'] [BorelSpace E'] (e : E ≃ᵃⁱ[ℝ] E') :
    MeasurePreserving e (volume : Measure E) (volume : Measure E') := by
  convert (measurePreserving_add_right (volume : Measure E') (e 0)).comp
    e.linearIsometryEquiv.measurePreserving using 1
  funext x
  simpa only [Function.comp_apply, vadd_eq_add, add_zero] using (e.map_vadd 0 x)

theorem integral_affine_preimage {E E' : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E'] [BorelSpace E'] (e : E ≃ᵃⁱ[ℝ] E')
    (s : Set E') (hs : MeasurableSet s) (f : E' → ℝ) :
    (∫ x in e ⁻¹' s, f (e x)) = ∫ y in s, f y := by
  exact ((affine_measurePreserving e).restrict_preimage hs).integral_comp
    e.toHomeomorph.measurableEmbedding f

theorem setIntegral_eq_of_support {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (s t : Set E) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (f : E → ℝ) (h : ∀ x, f x ≠ 0 → (x ∈ s ↔ x ∈ t)) :
    (∫ x in s, f x ∂μ) = ∫ x in t, f x ∂μ := by
  rw [← integral_indicator hs, ← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : f x = 0
  · exact (Set.indicator_apply_eq_zero.mpr (fun _ => hx)).trans
      (Set.indicator_apply_eq_zero.mpr (fun _ => hx)).symm
  · by_cases hxs : x ∈ s
    · simp [hxs, (h x hx).mp hxs]
    · have hxt : x ∉ t := fun hxt => hxs ((h x hx).mpr hxt)
      simp [hxs, hxt]


section
open Metric P102.Sobolev.Geometry P102.Sobolev.Extension

theorem chart_normal_unique {m : ℕ} (Ω : P201.Domain (m + 1))
    (C : BoundaryChart (geometricOpen (P201.graphFrame m) Ω : Set (Ambient m)))
    (x a : Space m) (hx : x ∈ ball C.center C.radius)
    (hd : HasFDerivAt C.graphFunction (innerSL ℝ a) x)
    (w : P201.Space (m + 1))
    (hw : P201Specs.SmoothFlux.GeometricNormalAt Ω
      (P201.graphFrame m (C.frame (graph C.graphFunction x))) w) :
    w = P201.graphFrame m (C.frame.linearIsometryEquiv (unitNormal a)) := by
  have hC := chart_normal_at C x a hx hd
  change OutwardUnitNormal _ _
    ((P201.graphFrame m).symm (P201.graphFrame m (C.frame (graph C.graphFunction x))))
    ((P201.graphFrame m).symm w) at hw
  rw [LinearIsometryEquiv.symm_apply_apply] at hw
  have heq := outward_unique hC.2 hC.1 hw
  exact ((P201.graphFrame m).apply_symm_apply w).symm.trans
    (congrArg (P201.graphFrame m) heq.symm)

/-- Every geometric normal field agrees in each Lipschitz chart, modulo that
chart's exact Hausdorff surface measure, with the normalized graph normal. -/
theorem geometric_normal_chart_ae {m : ℕ} (Ω : P201.Domain (m + 1))
    (C : BoundaryChart (geometricOpen (P201.graphFrame m) Ω : Set (Ambient m)))
    (a : Space m → Space m)
    (ha : GradientRepresentative ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction a)
    (ν : P201.Space (m + 1) → P201.Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν) :
    ∀ᵐ z ∂surfaceMeasure ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction,
      ν (P201.graphFrame m (C.frame z)) =
        P201.graphFrame m (C.frame.linearIsometryEquiv (normalField a z)) := by
  let e := P201.graphFrame m
  let U : Opens (Space m) := ⟨ball C.center C.radius, isOpen_ball⟩
  have hmap := chart_surface_map m e Ω C
  have hemb : MeasurableEmbedding (fun z => e (C.frame z)) :=
    (e.toHomeomorph.measurableEmbedding).comp C.frame.toHomeomorph.measurableEmbedding
  have hgeom : ∀ᵐ z ∂surfaceMeasure U C.graphFunction,
      P201Specs.SmoothFlux.GeometricNormalAt Ω (e (C.frame z)) (ν (e (C.frame z))) := by
    apply (hemb.ae_map_iff (μ := surfaceMeasure U C.graphFunction)
      (p := fun p => P201Specs.SmoothFlux.GeometricNormalAt Ω p (ν p))).mp
    rw [hmap]
    exact ae_restrict_of_ae hν.2
  rw [← map_weighted_volume U C.graphFunction C.constant C.graph_lipschitz a ha] at hgeom ⊢
  apply (borelParam_embedding U C.graphFunction C.graph_lipschitz.continuousOn).ae_map_iff.mpr
  have hgeombase := (borelParam_embedding U C.graphFunction C.graph_lipschitz.continuousOn).ae_map_iff.mp hgeom
  have hgrad : ∀ᵐ x ∂(volume.restrict (U : Set (Space m))).withDensity (density a),
      HasFDerivAt C.graphFunction (innerSL ℝ (a x)) x :=
    (withDensity_absolutelyContinuous _ _) ha.2
  filter_upwards [hgeombase, hgrad,
    (withDensity_absolutelyContinuous _ _) (ae_restrict_mem isOpen_ball.measurableSet)] with x hxgeom hd hx
  rw [borelParam_eq U C.graphFunction hx] at hxgeom ⊢
  simpa only [normalField, graph, WithLp.ofLp_toLp] using
    chart_normal_unique Ω C x (a x) hx hd (ν (e (C.frame (graph C.graphFunction x)))) hxgeom

/-- A.e. uniqueness of the actual geometric normal field. -/
theorem geometric_normal_unique {m : ℕ} (Ω : P201.Domain (m + 1))
    (hΩ : P201.IsBoundedLipschitzOpen Ω)
    (ν η : P201.Space (m + 1) → P201.Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν)
    (hη : P201Specs.SmoothFlux.IsGeometricNormalField Ω η) :
    ν =ᵐ[P201.boundaryMeasure Ω] η := by
  obtain ⟨ζ, _, hζ, hcone⟩ := geometric_normal_exists Ω hΩ
  filter_upwards [hζ.2, hν.2, hη.2, hcone] with p hpζ hpν hpη hc
  have hn := outward_unique hc hpζ hpν
  have hm := outward_unique hc hpζ hpη
  exact (P201.graphFrame m).symm.injective (hn.symm.trans hm)

end

section
open Metric P102.Sobolev.Geometry P102.Sobolev.Extension

theorem physical_chart_flux_integrand_ae {m : ℕ} (Ω : P201.Domain (m + 1))
    (C : BoundaryChart (geometricOpen (P201.graphFrame m) Ω : Set (Ambient m)))
    (a : Space m → Space m)
    (ha : GradientRepresentative ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction a)
    (ν : P201.Space (m + 1) → P201.Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν)
    (W : P201.Space (m + 1) → P201.Space (m + 1)) :
    (fun z => inner ℝ (W (P201.graphFrame m (C.frame z)))
      (ν (P201.graphFrame m (C.frame z))))
      =ᵐ[surfaceMeasure ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction]
        fun z => inner ℝ (C.frame.linearIsometryEquiv.symm
          ((P201.graphFrame m).symm (W (P201.graphFrame m (C.frame z))))) (normalField a z) := by
  let e := P201.graphFrame m
  filter_upwards [geometric_normal_chart_ae Ω C a ha ν hν] with z hz
  rw [hz]
  calc
    _ = inner ℝ (e.symm (W (e (C.frame z))))
        (C.frame.linearIsometryEquiv (normalField a z)) := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (e.inner_map_map (e.symm (W (e (C.frame z)))))
          (C.frame.linearIsometryEquiv (normalField a z))
    _ = _ := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (C.frame.linearIsometryEquiv.inner_map_map
          (C.frame.linearIsometryEquiv.symm (e.symm (W (e (C.frame z))))))
          (normalField a z)

/-- For a field supported in one actual chart, the physical boundary flux
is exactly the graph conormal integral. This statement needs no regularity
or integrability assumptions on the field: the general area theorem already
identifies the Bochner integrals and their integrability domains. -/
theorem physical_chart_flux {m : ℕ} (Ω : P201.Domain (m + 1))
    (C : BoundaryChart (geometricOpen (P201.graphFrame m) Ω : Set (Ambient m)))
    (a : Space m → Space m)
    (ha : GradientRepresentative ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction a)
    (ν : P201.Space (m + 1) → P201.Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν)
    (W : P201.Space (m + 1) → P201.Space (m + 1))
    (hW : tsupport W ⊆ P201.graphFrame m ''
      chartImage C.frame C.graphFunction C.center C.radius C.height) :
    (∫ p, inner ℝ (W p) (ν p) ∂P201.boundaryMeasure Ω) =
      ∫ x in ball C.center C.radius,
        inner ℝ (C.frame.linearIsometryEquiv.symm ((P201.graphFrame m).symm
          (W (P201.graphFrame m (C.frame (graph C.graphFunction x)))))) (conormal (a x)) := by
  let e := P201.graphFrame m
  let Q := e '' chartImage C.frame C.graphFunction C.center C.radius C.height
  let U : Opens (Space m) := ⟨ball C.center C.radius, isOpen_ball⟩
  let Z : Ambient m → Ambient m := fun z => C.frame.linearIsometryEquiv.symm
    (e.symm (W (e (C.frame z))))
  have hQ : MeasurableSet Q :=
    (e.toHomeomorph.isOpenMap _ (chartImage_open C.frame C.graph_lipschitz)).measurableSet
  have hemb : MeasurableEmbedding (fun z => e (C.frame z)) :=
    e.toHomeomorph.measurableEmbedding.comp C.frame.toHomeomorph.measurableEmbedding
  have hintegrand := physical_chart_flux_integrand_ae Ω C a ha ν hν W
  calc
    _ = ∫ p in Q, inner ℝ (W p) (ν p) ∂P201.boundaryMeasure Ω := by
      rw [← integral_indicator hQ]
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ Q
      · rw [indicator_of_mem hp]
      · rw [indicator_of_notMem hp]
        have hz : W p = 0 := by
          by_contra hne
          exact hp (hW (subset_tsupport W hne))
        simp only [hz, inner_zero_left]
    _ = ∫ z, inner ℝ (W (e (C.frame z))) (ν (e (C.frame z)))
        ∂surfaceMeasure U C.graphFunction := by
      rw [← chart_surface_map m e Ω C]
      exact hemb.integral_map _
    _ = ∫ z, inner ℝ (Z z) (normalField a z) ∂surfaceMeasure U C.graphFunction :=
      integral_congr_ae hintegrand
    _ = _ := (flux m U C.graphFunction C.constant C.graph_lipschitz a ha Z).2




theorem physical_chart_flux_integrable_iff {m : ℕ} (Ω : P201.Domain (m + 1))
    (C : BoundaryChart (geometricOpen (P201.graphFrame m) Ω : Set (Ambient m)))
    (a : Space m → Space m)
    (ha : GradientRepresentative ⟨ball C.center C.radius, isOpen_ball⟩ C.graphFunction a)
    (ν : P201.Space (m + 1) → P201.Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν)
    (W : P201.Space (m + 1) → P201.Space (m + 1))
    (hW : tsupport W ⊆ P201.graphFrame m ''
      chartImage C.frame C.graphFunction C.center C.radius C.height) :
    Integrable (fun p => inner ℝ (W p) (ν p)) (P201.boundaryMeasure Ω) ↔
      IntegrableOn (fun x =>
        inner ℝ (C.frame.linearIsometryEquiv.symm ((P201.graphFrame m).symm
          (W (P201.graphFrame m (C.frame (graph C.graphFunction x)))))) (conormal (a x)))
        (ball C.center C.radius) volume := by
  let e := P201.graphFrame m
  let Q := e '' chartImage C.frame C.graphFunction C.center C.radius C.height
  let U : Opens (Space m) := ⟨ball C.center C.radius, isOpen_ball⟩
  let Z : Ambient m → Ambient m := fun z => C.frame.linearIsometryEquiv.symm
    (e.symm (W (e (C.frame z))))
  have hQ : MeasurableSet Q :=
    (e.toHomeomorph.isOpenMap _ (chartImage_open C.frame C.graph_lipschitz)).measurableSet
  have hemb : MeasurableEmbedding (fun z => e (C.frame z)) :=
    e.toHomeomorph.measurableEmbedding.comp C.frame.toHomeomorph.measurableEmbedding
  have hid : Q.indicator (fun p => inner ℝ (W p) (ν p)) =
      (fun p => inner ℝ (W p) (ν p)) := by
    funext p
    by_cases hp : p ∈ Q
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp]
      have hz : W p = 0 := by
        by_contra hne
        exact hp (hW (subset_tsupport W hne))
      simp only [hz, inner_zero_left]
  calc
    _ ↔ IntegrableOn (fun p => inner ℝ (W p) (ν p)) Q (P201.boundaryMeasure Ω) := by
      conv_lhs => rw [← hid]
      exact integrable_indicator_iff hQ
    _ ↔ Integrable (fun z => inner ℝ (W (e (C.frame z))) (ν (e (C.frame z))))
        (surfaceMeasure U C.graphFunction) := by
      change Integrable _ ((P201.boundaryMeasure Ω).restrict Q) ↔ _
      rw [← chart_surface_map m e Ω C]
      exact hemb.integrable_map_iff
    _ ↔ Integrable (fun z => inner ℝ (Z z) (normalField a z))
        (surfaceMeasure U C.graphFunction) :=
      integrable_congr (physical_chart_flux_integrand_ae Ω C a ha ν hν W)
    _ ↔ _ := (flux m U C.graphFunction C.constant C.graph_lipschitz a ha Z).1


end

section
open Metric P102.U4 P102.Sobolev.Geometry P102.Sobolev.Extension

theorem local_bulk_transport {m : ℕ} (Ω : Domain (m+1))
    (C : BoundaryChart (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (W : Space (m+1) → Space (m+1)) (hW : ContDiff ℝ 1 W)
    (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ (graphFrame m) ''
      chartImage C.frame C.graphFunction C.center C.radius C.height) :
    let Z : Ambient m → Ambient m := fun y => C.frame.linearIsometryEquiv.symm
      ((graphFrame m).symm (W (graphFrame m (C.frame y))))
    let d : Ambient m → ℝ := fun z =>
      (∑ i : Fin m, fderiv ℝ (fun y => (Z y).ofLp.1 i) z
        (WithLp.toLp 2 (coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (Z y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))
    let D := epigraphSide (⟨ball C.center C.radius, isOpen_ball⟩ : Opens (Space m)) C.graphFunction
    IntegrableOn (divergence W) Ω ∧ IntegrableOn d D ∧
      (∫ x in Ω, divergence W x) = ∫ z in D, d z := by
  let Z : Ambient m → Ambient m := fun y => C.frame.linearIsometryEquiv.symm
      ((graphFrame m).symm (W (graphFrame m (C.frame y))))
  let d : Ambient m → ℝ := fun z =>
      (∑ i : Fin m, fderiv ℝ (fun y => (Z y).ofLp.1 i) z
        (WithLp.toLp 2 (coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (Z y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))
  let D := epigraphSide (⟨ball C.center C.radius, isOpen_ball⟩ : Opens (Space m)) C.graphFunction
  let a := C.frame.trans (graphFrame m).toAffineIsometryEquiv
  let f : Ambient m → ℝ := fun y => divergence W (a y)
  have hdf : ∀ y, d y = f y := by
    intro y
    exact (affine_chart_divergence C.frame W y (hW.differentiable one_ne_zero _)).symm
  have hdcs : Function.support (divergence W) ⊆ tsupport W := by
    intro x hx
    by_contra hn
    exact hx (divergence_eq_zero_of_not_mem_tsupport W hn)
  have hdcompact : HasCompactSupport (divergence W) := by
    exact hc.of_isClosed_subset isClosed_closure (closure_minimal hdcs (isClosed_tsupport W))
  have hdcontinuous : Continuous (divergence W) :=
    continuousOn_univ.mp (continuousOn_divergence isOpen_univ hW.contDiffOn)
  have hi : Integrable (divergence W) := hdcontinuous.integrable_of_hasCompactSupport hdcompact
  have hif : Integrable f := (affine_measurePreserving a).integrable_comp_of_integrable hi
  have hD : MeasurableSet D := (isOpen_epigraphSide _ _ C.graph_lipschitz.continuousOn).measurableSet
  have hsets : ∀ y, f y ≠ 0 →
      (y ∈ a ⁻¹' (Ω : Set (Space (m+1))) ↔ y ∈ D) := by
    intro y hy
    have hyts : a y ∈ tsupport W := hdcs hy
    rcases hs hyts with ⟨p, hp, hpa⟩
    have hpeq : p = C.frame y := (graphFrame m).injective hpa
    have hyQ : C.frame y ∈ chartImage C.frame C.graphFunction C.center C.radius C.height := hpeq ▸ hp
    have hside := congrArg (fun S : Set (Ambient m) => C.frame y ∈ S)
      (C.side.trans (epigraph_inter_chart C.frame C.graphFunction C.center C.radius C.height C.height_pos).symm)
    simp only [mem_inter_iff, hyQ, and_true, mem_image, C.frame.injective.eq_iff,
      exists_eq_right] at hside
    exact Iff.of_eq hside
  refine ⟨hi.integrableOn, ?_, ?_⟩
  · exact hif.integrableOn.congr (Filter.Eventually.of_forall (fun y => (hdf y).symm))
  · rw [← integral_affine_preimage a _ Ω.isOpen.measurableSet]
    trans ∫ z in D, f z
    · exact setIntegral_eq_of_support volume _ _
        (Ω.isOpen.measurableSet.preimage a.continuous.measurable) hD f hsets
    · exact integral_congr_ae (Filter.Eventually.of_forall (fun y => (hdf y).symm))

end

theorem integral_fderiv_eq_zero_of_lipschitz_compact {m : ℕ} {f : Space m → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hc : HasCompactSupport f) (q : Space m) :
    Integrable (fun x => fderiv ℝ f x q) ∧ (∫ x, fderiv ℝ f x q) = 0 := by
  have hEq : (fun x => lineDeriv ℝ f x q) =ᵐ[volume] (fun x => fderiv ℝ f x q) := by
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
    exact hx.lineDeriv_eq_fderiv
  have hi := ((hf.locallyIntegrable_lineDeriv (μ := volume) q).congr hEq).integrableOn_isCompact
    (hc.fderiv_apply ℝ q)
  refine ⟨(integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).mp hi, ?_⟩
  rw [← integral_congr_ae hEq]
  have hz := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume)
    (f := fun _ : Space m => (1 : ℝ)) (g := f) (LipschitzWith.const 1) hf hc (-q)
  simpa only [lineDeriv, deriv_const, neg_neg, zero_mul, integral_zero, mul_one] using hz.symm


section
open Metric P102.Sobolev.Geometry P102.Sobolev.Extension

/-- The finite partition turns the chartwise theorem into a global theorem for
an ambient compact C¹ vector field. The only premise is the remaining actual
local chart volume-to-flux computation. -/
theorem compact_flux_of_chart_flux
    (hlocal : ∀ {m : ℕ} (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
      ∀ (ν : Space (m + 1) → Space (m + 1)),
      P201Specs.SmoothFlux.IsGeometricNormalField Ω ν →
      ∀ (C : BoundaryChart (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
        (W : Space (m + 1) → Space (m + 1)),
        ContDiff ℝ 1 W → HasCompactSupport W →
        tsupport W ⊆ graphFrame m ''
          chartImage C.frame C.graphFunction C.center C.radius C.height →
        (∫ x in (Ω : Set (Space (m + 1))), divergence W x) =
          ∫ x, inner ℝ (W x) (ν x) ∂boundaryMeasure Ω)
    {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (ν : Space (m + 1) → Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν)
    (W : Space (m + 1) → Space (m + 1))
    (hW : ContDiff ℝ 1 W) (_hc : HasCompactSupport W) :
    IntegrableOn (divergence W) (Ω : Set (Space (m + 1))) volume ∧
      Integrable (fun x => inner ℝ (W x) (ν x)) (boundaryMeasure Ω) ∧
      (∫ x in (Ω : Set (Space (m + 1))), divergence W x) =
        ∫ x, inner ℝ (W x) (ν x) ∂boundaryMeasure Ω := by
  let e := graphFrame m
  let G : Set (Ambient m) := geometricOpen e Ω
  obtain ⟨n, C, r, a, hra, hcover, V, χ, hVo, hGV, hχ, hsum, hint, hsep, hsupp⟩ :=
    finite_localization m G hΩ
  let φ : Fin (n + 1) → Space (m + 1) → ℝ := fun i x => χ i (e.symm x)
  let T : Set (Space (m + 1)) := e '' V
  have hT : IsOpen T := e.toHomeomorph.isOpenMap _ hVo
  have hΩT : closure (Ω : Set (Space (m + 1))) ⊆ T := by
    intro x hx
    have hxG : e.symm x ∈ closure G := by
      change e.symm x ∈ closure (e.toHomeomorph ⁻¹' (Ω : Set (Space (m + 1))))
      rw [← e.toHomeomorph.preimage_closure]
      simpa only [mem_preimage, LinearIsometryEquiv.coe_toHomeomorph,
        LinearIsometryEquiv.apply_symm_apply] using hx
    exact ⟨e.symm x, hGV hxG, e.apply_symm_apply x⟩
  have hφ : ∀ i, ContDiff ℝ 1 (φ i) := by
    intro i
    exact ((hχ i).1.comp e.symm.contDiff).of_le (by simp)
  have hφsupp (i : Fin (n + 1)) : tsupport (φ i) ⊆ e '' tsupport (χ i) := by
    intro x hx
    change x ∈ tsupport (χ i ∘ e.symm.toHomeomorph) at hx
    rw [tsupport_comp_eq_preimage _ e.symm.toHomeomorph] at hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  have hφc : ∀ i, HasCompactSupport (φ i) := by
    intro i
    exact (hχ i).2.1.comp_homeomorph e.symm.toHomeomorph
  have hφsum : ∀ x ∈ T, ∑ i, φ i x = 1 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    simpa only [φ, LinearIsometryEquiv.symm_apply_apply] using hsum z hz
  have hpiece : ∀ i, ContDiff ℝ 1 (fun x => φ i x • W x) :=
    fun i => (hφ i).smul hW
  have hpiecec : ∀ i, HasCompactSupport (fun x => φ i x • W x) :=
    fun i => (hφc i).smul_right
  have hpiecebulk : ∀ i, IntegrableOn (divergence (fun x => φ i x • W x))
      (Ω : Set (Space (m + 1))) volume := by
    intro i
    exact (((continuousOn_divergence isOpen_univ (hpiece i).contDiffOn).mono
      (subset_univ _)).integrableOn_compact (μ := volume) (compact_closure Ω hΩ)).mono_set subset_closure
  have hpiecebdy : ∀ i, Integrable (fun x => φ i x * inner ℝ (W x) (ν x))
      (boundaryMeasure Ω) := by
    intro i
    exact boundary_flux_integrable Ω hΩ ν hν W (φ i)
      hW.continuous.continuousOn (hφ i).continuous.continuousOn
  have hμ : ∀ᵐ x ∂boundaryMeasure Ω, x ∈ closure (Ω : Set (Space (m + 1))) := by
    filter_upwards [P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω] with x hx
    exact frontier_subset_closure hx
  have hlocalpiece : ∀ i, (∫ x in (Ω : Set (Space (m + 1))),
      divergence (fun y => φ i y • W y) x) =
      ∫ x, φ i x * inner ℝ (W x) (ν x) ∂boundaryMeasure Ω := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hs : tsupport (fun x => φ 0 x • W x) ⊆ (Ω : Set (Space (m + 1))) := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := hφsupp 0 (tsupport_smul_subset_left (φ 0) W hx)
        exact hint hz
      rw [(interior_divergence Ω (fun x => φ 0 x • W x) (hpiece 0) (hpiecec 0) hs).2]
      symm
      apply integral_eq_zero_of_ae
      filter_upwards [P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω] with x hx
      have hz : φ 0 x = 0 := by
        by_contra hn
        obtain ⟨z, hz, heq⟩ := hφsupp 0 (subset_tsupport (φ 0) hn)
        have hxΩ : x ∈ (Ω : Set (Space (m + 1))) := by
          rw [← heq]
          exact hint hz
        exact (Ω.isOpen.frontier_eq ▸ hx).2 hxΩ
      simp only [hz, zero_mul, Pi.zero_apply]
    · have hs : tsupport (fun x => φ j.succ x • W x) ⊆ e ''
          chartImage (C j).frame (C j).graphFunction (C j).center (C j).radius (C j).height := by
        intro x hx
        obtain ⟨z, hz, rfl⟩ := hφsupp j.succ (tsupport_smul_subset_left (φ j.succ) W hx)
        exact ⟨z, chartImage_mono (C j).frame (C j).graphFunction (C j).center
          (hra j).2.1.le (hra j).2.2.2.le (hsupp j hz), rfl⟩
      simpa only [inner_smul_left, RCLike.conj_to_real] using
        hlocal Ω hΩ ν hν (C j) (fun x => φ j.succ x • W x)
          (hpiece j.succ) (hpiecec j.succ) hs
  exact finite_flux_assembly Ω (boundaryMeasure Ω) ν W φ T hT hΩT hW.contDiffOn
    hφ hφsum hμ hpiecebulk hpiecebdy hlocalpiece

/-- The full original smooth-flux assertion follows from the actual local
chart theorem, with no global identity or normal-existence certificate assumed. -/
theorem smooth_flux_of_chart_flux
    (hlocal : ∀ {m : ℕ} (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
      ∀ (ν : Space (m + 1) → Space (m + 1)),
      P201Specs.SmoothFlux.IsGeometricNormalField Ω ν →
      ∀ (C : BoundaryChart (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
        (W : Space (m + 1) → Space (m + 1)),
        ContDiff ℝ 1 W → HasCompactSupport W →
        tsupport W ⊆ graphFrame m ''
          chartImage C.frame C.graphFunction C.center C.radius C.height →
        (∫ x in (Ω : Set (Space (m + 1))), divergence W x) =
          ∫ x, inner ℝ (W x) (ν x) ∂boundaryMeasure Ω)
    : P201Specs.SmoothFlux.SmoothFluxStatement := by
  intro m Ω hΩ
  obtain ⟨ν, hνm, hν, hνcone⟩ := geometric_normal_exists Ω hΩ
  refine ⟨ν, hν, ?_⟩
  intro U F v hU hΩU hF hv
  have hW : ContDiffOn ℝ 1 (fun x => v x • F x) U := hv.smul hF
  obtain ⟨Z, V, hV, hKV, hVU, hZ, hZc, hZsupp, hZW⟩ :=
    compact_localization (closure (Ω : Set (Space (m + 1)))) U
      (fun x => v x • F x) (compact_closure Ω hΩ) hU hΩU hW
  have hflux := compact_flux_of_chart_flux hlocal Ω hΩ ν hν Z hZ hZc
  have hdiv : ∀ x ∈ (Ω : Set (Space (m + 1))), divergence Z x =
      inner ℝ (F x) (gradient v x) + divergence F x * v x := by
    intro x hx
    have hxV := hKV (subset_closure hx)
    have heq : Z =ᶠ[𝓝 x] (fun y => v y • F y) := by
      filter_upwards [hV.mem_nhds hxV] with y hy using hZW hy
    rw [divergence_congr_of_eventuallyEq heq]
    have hxU := hΩU (subset_closure hx)
    exact divergence_product F v x
      ((hF.differentiableOn one_ne_zero x hxU).differentiableAt (hU.mem_nhds hxU))
      ((hv.differentiableOn one_ne_zero x hxU).differentiableAt (hU.mem_nhds hxU))
  have hbdy : (fun x => inner ℝ (Z x) (ν x)) =ᵐ[boundaryMeasure Ω]
      (fun x => v x * inner ℝ (F x) (ν x)) := by
    filter_upwards [P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω] with x hx
    rw [hZW (hKV (frontier_subset_closure hx)), inner_smul_left, RCLike.conj_to_real]
  refine ⟨bulk_integrable Ω hΩ U F v hU hΩU hF hv,
    boundary_flux_integrable Ω hΩ ν hν F v
      (hF.continuousOn.mono (frontier_subset_closure.trans hΩU))
      (hv.continuousOn.mono (frontier_subset_closure.trans hΩU)), ?_⟩
  calc
    _ = ∫ x in (Ω : Set (Space (m + 1))), divergence Z x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      exact (hdiv x hx).symm
    _ = ∫ x, inner ℝ (Z x) (ν x) ∂boundaryMeasure Ω := hflux.2.2
    _ = _ := integral_congr_ae hbdy

end

section
open Metric P102.U4 P102.Sobolev.Geometry P102.Sobolev.Extension

theorem chart_pullback_properties {m : ℕ} (Ω : Domain (m+1))
    (C : BoundaryChart (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (W : Space (m+1) → Space (m+1)) (hW : ContDiff ℝ 1 W)
    (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ (graphFrame m) ''
      chartImage C.frame C.graphFunction C.center C.radius C.height) :
    let Z : Ambient m → Ambient m := fun y => C.frame.linearIsometryEquiv.symm
      ((graphFrame m).symm (W (graphFrame m (C.frame y))))
    ContDiff ℝ 1 Z ∧ HasCompactSupport Z ∧
      tsupport Z ⊆ strip (ball C.center C.radius) := by
  let a := C.frame.trans (graphFrame m).toAffineIsometryEquiv
  let q := (graphFrame m).symm.trans C.frame.linearIsometryEquiv.symm
  let Z : Ambient m → Ambient m := fun y => q (W (a y))
  have ha : ContDiff ℝ 1 a := a.toAffineIsometry.toContinuousAffineMap.contDiff
  have hZ : ContDiff ℝ 1 Z := q.contDiff.comp (hW.comp ha)
  have hcZ : HasCompactSupport Z :=
    (hc.comp_homeomorph a.toHomeomorph).comp_left q.map_zero
  refine ⟨hZ, hcZ, ?_⟩
  have ht : tsupport Z ⊆ a ⁻¹' tsupport W :=
    (tsupport_comp_subset q.map_zero (W ∘ a)).trans
      (tsupport_comp_subset_preimage W a.continuous)
  intro z hz
  rcases hs (ht hz) with ⟨p, hp, hpa⟩
  have hpz : p = C.frame z := (graphFrame m).injective hpa
  have hzQ : C.frame z ∈ chartImage C.frame C.graphFunction C.center C.radius C.height := hpz ▸ hp
  rcases hzQ with ⟨p, ⟨y, hy, rfl⟩, h⟩
  have hyz : shear C.graphFunction y = z := C.frame.injective h
  rw [← hyz]
  exact hy.1

end

theorem graph_ray_primitive_compact_support {m : ℕ} (f : Ambient m → ℝ)
    (hc : HasCompactSupport f) (ψ : Space m → ℝ) :
    HasCompactSupport (fun x => ∫ t in Ioi (0 : ℝ),
      f (graph ψ x + t • (WithLp.toLp 2 (0, (1 : ℝ)) : Ambient m))) := by
  let K : Set (Space m) := (horizontal (m := m)) '' tsupport f
  have hK : IsCompact K := hc.image (horizontal (m := m)).continuous
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hxK
  apply hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  apply hxK
  refine ⟨_, hz, ?_⟩
  simp [horizontal, graph]

theorem graph_ray_primitive_lipschitz {m : ℕ} (f : Ambient m → ℝ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (ψ : Space m → ℝ)
    {L : ℝ≥0} (hψ : LipschitzWith L ψ) :
    ∃ K : ℝ≥0, LipschitzWith K (fun x => ∫ t in Ioi (0 : ℝ),
      f (graph ψ x + t • (WithLp.toLp 2 (0, (1 : ℝ)) : Ambient m))) := by
  let e : Ambient m := WithLp.toLp 2 (0, (1 : ℝ))
  have he : ‖e‖ = 1 := by simp only [e, WithLp.norm_toLp_snd, norm_one]
  obtain ⟨K, hK⟩ := exists_lipschitz_ray_primitive f hf hc e he
  have hgraph := lipschitzOnWith_univ.mp
    (P102.U4.GraphArea.graph_lipschitzOn (U := Set.univ) hψ.lipschitzOnWith)
  exact ⟨_, hK.comp hgraph⟩


theorem integral_Ioi_translate (g : ℝ → ℝ) (b : ℝ) :
    (∫ t in Ioi (0 : ℝ), g (b + t)) = ∫ t in Ioi b, g t := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  convert integral_add_left_eq_self (μ := volume) ((Ioi b).indicator g) b using 1
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : 0 < t
  · have hbt : b < b + t := by linarith
    simp only [indicator_of_mem (show t ∈ Ioi 0 from ht),
      indicator_of_mem (show b + t ∈ Ioi b from hbt)]
  · have hbt : ¬ b < b + t := by linarith
    simp only [indicator_of_notMem (show t ∉ Ioi 0 from ht),
      indicator_of_notMem (show b + t ∉ Ioi b from hbt)]

theorem tsupport_graph_ray_primitive_subset {m : ℕ} (f : Ambient m → ℝ)
    (hc : HasCompactSupport f) (ψ : Space m → ℝ) :
    tsupport (fun x => ∫ t in Ioi (0 : ℝ),
      f (graph ψ x + t • (WithLp.toLp 2 (0, (1 : ℝ)) : Ambient m))) ⊆
        (horizontal (m := m)) '' tsupport f := by
  have hK : IsCompact ((horizontal (m := m)) '' tsupport f) :=
    hc.image (horizontal (m := m)).continuous
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hxK
  apply hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  apply image_eq_zero_of_notMem_tsupport
  intro hz
  apply hxK
  refine ⟨_, hz, ?_⟩
  simp [horizontal, graph]

theorem integrable_epigraph_slices {m : ℕ} (U : TopologicalSpace.Opens (Space m))
    (ψ : Space m → ℝ) (hψ : ContinuousOn ψ U) (f : Ambient m → ℝ)
    (hf : Integrable f) :
    IntegrableOn (fun x => ∫ t in Ioi (ψ x), f (WithLp.toLp 2 (x, t))) U volume := by
  classical
  let D := epigraphSide U ψ
  have hD : MeasurableSet D := (P201.SmoothFlux.isOpen_epigraphSide U ψ hψ).measurableSet
  have hp := WithLp.volume_preserving_toLp (Space m) ℝ
  have hInt := (hp.integrable_comp_of_integrable (hf.indicator hD)).integral_prod_left
  have hEq : (fun x : Space m => ∫ t : ℝ, D.indicator f (WithLp.toLp 2 (x, t))) =
      (U : Set (Space m)).indicator (fun x => ∫ t in Ioi (ψ x), f (WithLp.toLp 2 (x, t))) := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, ← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with t
      by_cases ht : ψ x < t <;> simp [D, epigraphSide, hx, ht]
    · simp [D, epigraphSide, hx]
  change Integrable (fun x : Space m => ∫ t : ℝ,
    D.indicator f (WithLp.toLp 2 (x, t))) at hInt
  rw [hEq, integrable_indicator_iff U.isOpen.measurableSet] at hInt
  exact hInt

theorem horizontal_epigraph_scalar {m : ℕ} (U : TopologicalSpace.Opens (Space m))
    (ψ : Space m → ℝ) (L : ℝ≥0) (hψ : LipschitzOnWith L ψ U)
    (a : Space m → Space m) (ha : GradientRepresentative U ψ a)
    (f : Ambient m → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (horizontal (m := m)) ⁻¹' (U : Set (Space m))) (q : Space m) :
    IntegrableOn (fun z => fderiv ℝ f z (WithLp.toLp 2 (q, (0 : ℝ))))
      (epigraphSide U ψ) volume ∧
    IntegrableOn (fun x => f (graph ψ x) * inner ℝ (a x) q) U volume ∧
    (∫ z in epigraphSide U ψ, fderiv ℝ f z (WithLp.toLp 2 (q, (0 : ℝ)))) =
      ∫ x in (U : Set (Space m)), f (graph ψ x) * inner ℝ (a x) q := by
  obtain ⟨g, hg, heq⟩ := hψ.extend_real
  let e : Ambient m := WithLp.toLp 2 (0, (1 : ℝ))
  let Q : Space m → ℝ := fun x => ∫ t in Ioi (0 : ℝ), f (graph g x + t • e)
  let H : Ambient m → ℝ := fun z => fderiv ℝ f z (WithLp.toLp 2 (q, (0 : ℝ)))
  let A : Space m → ℝ := fun x => ∫ t in Ioi (ψ x), H (WithLp.toLp 2 (x, t))
  have hHi : Integrable H := ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hc.fderiv_apply ℝ _)
  have hAi : IntegrableOn A U volume := integrable_epigraph_slices U ψ hψ.continuousOn H hHi
  obtain ⟨K, hK⟩ := graph_ray_primitive_lipschitz f hf hc g hg
  have hQc : HasCompactSupport Q := graph_ray_primitive_compact_support f hc g
  have hQs : tsupport Q ⊆ U := by
    intro x hx
    rcases tsupport_graph_ray_primitive_subset f hc g hx with ⟨z, hz, rfl⟩
    exact hs hz
  obtain ⟨hDi, hD0⟩ := integral_fderiv_eq_zero_of_lipschitz_compact hK hQc q
  have hD0U : (∫ x in (U : Set (Space m)), fderiv ℝ Q x q) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    exact hD0
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hQs h)), zero_apply]
  have hAE : (fun x => fderiv ℝ Q x q) =ᵐ[volume.restrict (U : Set (Space m))]
      (fun x => A x - f (graph ψ x) * inner ℝ (a x) q) := by
    filter_upwards [ha.2, ae_restrict_mem U.isOpen.measurableSet] with x hax hx
    have hgg : g =ᶠ[𝓝 x] ψ := by
      filter_upwards [U.isOpen.mem_nhds hx] with y hy
      exact (heq hy).symm
    have hgx : g x = ψ x := (heq hx).symm
    have hD := fderiv_graph_ray_primitive f hf hc g (hax.congr_of_eventuallyEq hgg) q
    change fderiv ℝ Q x q = _ at hD
    rw [hD]
    have hpt : ∀ t, graph g x + t • e = WithLp.toLp 2 (x, ψ x + t) := by
      intro t
      apply WithLp.ofLp_injective
      simp [graph, e, hgx]
    change (∫ t in Ioi (0 : ℝ), H (graph g x + t • e)) -
      inner ℝ (a x) q * f (graph g x) = _
    simp_rw [hpt]
    rw [integral_Ioi_translate (fun t => H (WithLp.toLp 2 (x, t))) (ψ x)]
    rw [show graph g x = graph ψ x by simp only [graph, hgx]]
    change A x - inner ℝ (a x) q * f (graph ψ x) = _
    rw [mul_comm (inner ℝ (a x) q)]
  have hBi : IntegrableOn (fun x => f (graph ψ x) * inner ℝ (a x) q) U volume := by
    apply (hAi.sub hDi.integrableOn).congr
    filter_upwards [hAE] with x hx
    change A x - fderiv ℝ Q x q = f (graph ψ x) * inner ℝ (a x) q
    linarith
  refine ⟨hHi.integrableOn, hBi, ?_⟩
  rw [P201.SmoothFlux.integral_epigraph_slices U ψ hψ.continuousOn H hHi]
  have hEqInt := integral_congr_ae hAE
  rw [integral_sub hAi hBi, hD0U] at hEqInt
  linarith


theorem epigraph_divergence {m : ℕ} (U : TopologicalSpace.Opens (Space m))
    (ψ : Space m → ℝ) (L : ℝ≥0) (hψ : LipschitzOnWith L ψ U)
    (a : Space m → Space m) (ha : GradientRepresentative U ψ a)
    (W : Ambient m → Ambient m) (hW : ContDiff ℝ 1 W) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ (horizontal (m := m)) ⁻¹' (U : Set (Space m))) :
    IntegrableOn (fun z =>
      (∑ i : Fin m, fderiv ℝ (fun y => (W y).ofLp.1 i) z
        (WithLp.toLp 2 (P201.coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (W y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))) (epigraphSide U ψ) volume ∧
    IntegrableOn (fun x => inner ℝ (W (graph ψ x)) (conormal (a x))) U volume ∧
    (∫ z in epigraphSide U ψ,
      (∑ i : Fin m, fderiv ℝ (fun y => (W y).ofLp.1 i) z
        (WithLp.toLp 2 (P201.coordinate m i, (0 : ℝ)))) +
      fderiv ℝ (fun y => (W y).ofLp.2) z
        (WithLp.toLp 2 ((0 : Space m), (1 : ℝ)))) =
      ∫ x in (U : Set (Space m)), inner ℝ (W (graph ψ x)) (conormal (a x)) := by
  have hFi : ∀ i : Fin m,
      IntegrableOn (fun z => fderiv ℝ (fun y => (W y).ofLp.1 i) z
        (WithLp.toLp 2 (P201.coordinate m i, (0 : ℝ)))) (epigraphSide U ψ) volume ∧
      IntegrableOn (fun x => (W (graph ψ x)).ofLp.1 i * inner ℝ (a x) (P201.coordinate m i)) U volume ∧
      (∫ z in epigraphSide U ψ, fderiv ℝ (fun y => (W y).ofLp.1 i) z
        (WithLp.toLp 2 (P201.coordinate m i, (0 : ℝ)))) =
      ∫ x in (U : Set (Space m)), (W (graph ψ x)).ofLp.1 i * inner ℝ (a x) (P201.coordinate m i) := by
    intro i
    have hf : ContDiff ℝ 1 (fun y => (W y).ofLp.1 i) :=
      (((PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp horizontal).contDiff).comp hW
    have hs' : tsupport (fun y => (W y).ofLp.1 i) ⊆ tsupport W :=
      tsupport_comp_subset (g := fun z : Ambient m => z.ofLp.1 i) (by simp) W
    exact horizontal_epigraph_scalar U ψ L hψ a ha _ hf
      (hc.comp_left (g := fun z : Ambient m => z.ofLp.1 i) (by simp))
      (hs'.trans hs) (P201.coordinate m i)
  obtain ⟨hVi, hVbi, hV⟩ := P201.SmoothFlux.vertical_epigraph U ψ L hψ W hW hc
  have hflux : ∀ x : Space m,
      (∑ i : Fin m, (W (graph ψ x)).ofLp.1 i * inner ℝ (a x) (P201.coordinate m i)) -
        (W (graph ψ x)).ofLp.2 = inner ℝ (W (graph ψ x)) (conormal (a x)) := by
    intro x
    simp [conormal, WithLp.prod_inner_apply, PiLp.inner_apply, RCLike.inner_apply,
      P201.coordinate, P201Specs.coordinate, P102.U4.coordinateVector,
      sub_eq_add_neg, mul_comm]
  have hBi : IntegrableOn (fun x => inner ℝ (W (graph ψ x)) (conormal (a x))) U volume := by
    apply ((integrable_finsetSum Finset.univ (fun i _ => (hFi i).2.1)).sub hVbi).congr
    filter_upwards [] with x
    exact hflux x
  refine ⟨(integrable_finsetSum Finset.univ (fun i _ => (hFi i).1)).add hVi, hBi, ?_⟩
  rw [integral_add (integrable_finsetSum Finset.univ (fun i _ => (hFi i).1)) hVi,
    integral_finsetSum Finset.univ (fun i _ => (hFi i).1), hV]
  simp_rw [(hFi _).2.2]
  rw [← integral_finsetSum Finset.univ (fun i _ => (hFi i).2.1), ← sub_eq_add_neg, ← integral_sub
    (integrable_finsetSum Finset.univ (fun i _ => (hFi i).2.1)) hVbi]
  apply integral_congr_ae
  filter_upwards [] with x
  exact hflux x


section
open Metric P102.Sobolev.Geometry P102.Sobolev.Extension

theorem local_chart_flux {m : ℕ} (Ω : Domain (m + 1))
    (C : BoundaryChart (geometricOpen (graphFrame m) Ω : Set (Ambient m)))
    (ν : Space (m + 1) → Space (m + 1))
    (hν : P201Specs.SmoothFlux.IsGeometricNormalField Ω ν)
    (W : Space (m + 1) → Space (m + 1)) (hW : ContDiff ℝ 1 W)
    (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ graphFrame m ''
      chartImage C.frame C.graphFunction C.center C.radius C.height) :
    (∫ x in (Ω : Set (Space (m + 1))), divergence W x) =
      ∫ x, inner ℝ (W x) (ν x) ∂boundaryMeasure Ω := by
  let U : Opens (Space m) := ⟨ball C.center C.radius, isOpen_ball⟩
  let Z : Ambient m → Ambient m := fun y => C.frame.linearIsometryEquiv.symm
    ((graphFrame m).symm (W (graphFrame m (C.frame y))))
  obtain ⟨a, ha⟩ := gradient_existence m U C.graphFunction C.constant C.graph_lipschitz
  obtain ⟨hZ, hZc, hZs⟩ := chart_pullback_properties Ω C W hW hc hs
  have hb := local_bulk_transport Ω C W hW hc hs
  have he := epigraph_divergence U C.graphFunction C.constant C.graph_lipschitz
    a ha Z hZ hZc hZs
  have hf := physical_chart_flux Ω C a ha ν hν W hs
  exact hb.2.2.trans (he.2.2.trans hf.symm)

theorem smooth_flux : P201Specs.SmoothFlux.SmoothFluxStatement := by
  apply smooth_flux_of_chart_flux
  intro m Ω _hΩ ν hν C W hW hc hs
  exact local_chart_flux Ω C ν hν W hW hc hs

end

end P201.SmoothFlux
