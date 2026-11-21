import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.BoundaryPatchExtension
import MathGenome.Internal.FourierSobolev.P102.Trace.GraphFractionalTransport
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal
namespace P102.Trace.BoundaryPatchExtension
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry
open MeasuredFractional

variable {m : ℕ} {Ω : Set (Ambient m)}

lemma patch_eq (C : BoundaryChart Ω) :
    patch C = frontier Ω ∩ chartImage C.frame C.graphFunction C.center C.radius C.height := by
  rw [C.boundary, patch, GraphFractionalTransport.graphMap, image_comp]

lemma patch_measurableSet (C : BoundaryChart Ω) : MeasurableSet (patch C) := by
  rw [patch_eq]
  exact isClosed_frontier.measurableSet.inter (chartImage_open C.frame C.graph_lipschitz).measurableSet

lemma graphMeasure_eq (C : BoundaryChart Ω) :
    GraphFractionalTransport.graphMeasure C.frame C.graphFunction (ball C.center C.radius) =
      (surfaceMeasure Ω).restrict (patch C) := by
  rw [GraphFractionalTransport.graphMeasure, surfaceMeasure,
    Measure.restrict_restrict (patch_measurableSet C)]
  congr 1
  exact (inter_eq_left.mpr (by change patch C ⊆ frontier Ω; rw [patch_eq]; exact inter_subset_left)).symm

/-- Finite total area follows from a finite geometric cover, including an empty one. -/
lemma surfaceMeasure_lt_top (hΩ : IsLipschitzOpen Ω) : surfaceMeasure Ω univ < ∞ := by
  classical
  obtain ⟨n, C, r, a, hsmall, hcover, _⟩ := finite_localization m Ω hΩ
  have hcov : frontier Ω ⊆ ⋃ i, patch (C i) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [patch_eq]
    exact ⟨hx, chartImage_mono (C i).frame (C i).graphFunction (C i).center
      (hsmall i).2.1.le (hsmall i).2.2.2.le hi⟩
  rw [surfaceMeasure, Measure.restrict_apply_univ]
  apply (measure_mono hcov).trans_lt
  apply (measure_iUnion_fintype_le _ (fun i => patch (C i))).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro i hi
  have hle := ((graph_geometry_in_frame m (ball (C i).center (C i).radius)
    (C i).graphFunction (C i).constant (C i).graph_lipschitz
    (C i).frame).2.2 _ Subset.rfl).2
  exact hle.trans_lt (ENNReal.mul_lt_top (by simp) measure_ball_lt_top)

/-- The gap depends on the actual compact support and full physical chart. -/
lemma compact_support_gap (C : BoundaryChart Ω) {K : Set (Ambient m)}
    (hK : IsCompact K)
    (hKU : K ⊆ chartImage C.frame C.graphFunction C.center C.radius C.height) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ frontier Ω, y ∉ patch C → δ ≤ dist x y := by
  let U := chartImage C.frame C.graphFunction C.center C.radius C.height
  have hU : IsOpen U := chartImage_open C.frame C.graph_lipschitz
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_forall_lt_edist hK hU.isClosed_compl
    (Set.disjoint_left.mpr (fun _ hx hy => hy (hKU hx)))
  refine ⟨δ, hδ, fun x hx y hy hyp => ?_⟩
  have hyU : y ∈ Uᶜ := by
    intro hyU
    exact hyp (by rw [patch_eq]; exact ⟨hy, hyU⟩)
  have h := hsep x hx y hyU
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at h
  exact (ENNReal.ofReal_le_ofReal_iff (show 0 ≤ dist x y from dist_nonneg)).mp h.le

lemma pullback_memLp
    (hcomparison : GraphFractionalTransport.Expected.LocalGraphComparison)
    (hm : 1 ≤ m) (C : BoundaryChart Ω) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p < ∞)
    {𝕜 : Type} [RCLike 𝕜] {q : Ambient m → 𝕜}
    (hq : MemLp q p (surfaceMeasure Ω)) : MemLp (pullback C q) p volume := by
  obtain ⟨A, _, hA⟩ := hcomparison m hm s hs hs1 p hp hpt C.constant
  have hmem := (hA C.center C.radius C.radius_pos C.graphFunction
    C.graph_lipschitz C.frame 𝕜 q).2.2.2.2.2.2.2.2
  apply (memLp_indicator_iff_restrict isOpen_ball.measurableSet.nullMeasurableSet).mpr
  apply hmem.mp
  rw [graphMeasure_eq]
  exact hq.restrict _


section Energy
variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [NormedAddCommGroup E]

/-- The actual diagonal-zero integrand, in curried form. -/
def energyIntegrand (m : ℕ) (s : ℝ) (p : ℝ≥0∞) (q : X → E) (x y : X) : ℝ≥0∞ := by
  classical
  exact if x = y then 0 else ‖q x - q y‖ₑ ^ p.toReal /
    ENNReal.ofReal (dist x y) ^ ((m : ℝ) + s * p.toReal)

lemma energyIntegrand_aemeasurable (m : ℕ) (s : ℝ) (p : ℝ≥0∞)
    {μ ν : Measure X} [SigmaFinite μ] [SigmaFinite ν] {q : X → E}
    (hμ : AEStronglyMeasurable q μ) (hν : AEStronglyMeasurable q ν) :
    AEMeasurable (Function.uncurry (energyIntegrand m s p q)) (μ.prod ν) := by
  have hk : Measurable (metricKernel (X := X) m s p) := by
    unfold metricKernel
    apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
    fun_prop
  have hi : AEStronglyMeasurable (fun z : X × X => q z.1 - q z.2) (μ.prod ν) :=
    (hμ.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).sub
      (hν.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  convert hk.aemeasurable.mul (hi.enorm.pow_const p.toReal) using 1
  ext z
  change energyIntegrand m s p q z.1 z.2 = _
  simp only [Pi.mul_apply, energyIntegrand, metricKernel]
  split_ifs <;> simp [div_eq_mul_inv, mul_comm]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma energyIntegrand_symm (m : ℕ) (s : ℝ) (p : ℝ≥0∞) (q : X → E) (x y : X) :
    energyIntegrand m s p q x y = energyIntegrand m s p q y x := by
  classical
  simp only [energyIntegrand, eq_comm, dist_comm, enorm_sub_rev]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma energyIntegrand_le_of_zero (m : ℕ) (s : ℝ) (p : ℝ≥0∞) {q : X → E}
    (hp : 0 < p.toReal) (ha : 0 ≤ (m : ℝ) + s * p.toReal)
    {δ : ℝ} {x y : X} (hy : q y = 0) (hgap : q x ≠ 0 → δ ≤ dist x y) :
    energyIntegrand m s p q x y ≤
      (ENNReal.ofReal δ ^ ((m : ℝ) + s * p.toReal))⁻¹ * ‖q x‖ₑ ^ p.toReal := by
  classical
  by_cases hxy : x = y
  · simp [energyIntegrand, hxy]
  by_cases hx : q x = 0
  · simp [energyIntegrand, hxy, hx, hy, ENNReal.zero_rpow_of_pos hp]
  simp only [energyIntegrand, ite_eq_right hxy, hy, sub_zero, div_eq_mul_inv]
  rw [mul_comm]
  gcongr
  exact hgap hx

/-- A support-dependent artificial-edge estimate on a finite metric measure.
The measure need only be concentrated on S. Supports and representatives are a.e. -/
lemma energy_le_restrict_add_mass (m : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (s : ℝ) (p : ℝ≥0∞) (hp : 0 < p.toReal)
    (ha : 0 ≤ (m : ℝ) + s * p.toReal) {q : X → E}
    (hq : AEStronglyMeasurable q μ) {P S : Set X} (hP : MeasurableSet P)
    (hS : ∀ᵐ x ∂μ, x ∈ S) (hzero : ∀ᵐ x ∂μ.restrict Pᶜ, q x = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ x ∂μ, q x ≠ 0 → ∀ y ∈ S, y ∉ P → δ ≤ dist x y) :
    metricEnergy m μ s p q ≤ metricEnergy m (μ.restrict P) s p q +
      (2 * μ univ * (ENNReal.ofReal δ ^ ((m : ℝ) + s * p.toReal))⁻¹) * lpMass μ p q := by
  let d : ℝ≥0∞ := (ENNReal.ofReal δ ^ ((m : ℝ) + s * p.toReal))⁻¹
  have hd : d ≠ ∞ := by
    exact ENNReal.inv_ne_top.mpr ((ENNReal.rpow_pos (by positivity) (by simp)).ne')
  have hcoef : μ univ * d ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) hd
  let F := energyIntegrand m s p q
  have hsplit (x : X) : (∫⁻ y, F x y ∂μ) =
      (∫⁻ y in P, F x y ∂μ) + ∫⁻ y in Pᶜ, F x y ∂μ :=
    (lintegral_add_compl _ hP).symm
  have hcross : (∫⁻ x in P, ∫⁻ y in Pᶜ, F x y ∂μ ∂μ) ≤
      (μ univ * d) * lpMass μ p q := by
    calc
      _ ≤ ∫⁻ x in P, (μ univ * d) * ‖q x‖ₑ ^ p.toReal ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hgap] with x hx
        calc
          _ ≤ ∫⁻ y in Pᶜ, d * ‖q x‖ₑ ^ p.toReal ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_of_ae hS, ae_restrict_mem hP.compl, hzero] with y hy hyP hy0
            exact energyIntegrand_le_of_zero m s p hp ha hy0 (fun hqx => hx hqx y hy hyP)
          _ = (d * ‖q x‖ₑ ^ p.toReal) * μ Pᶜ := by simp
          _ ≤ (d * ‖q x‖ₑ ^ p.toReal) * μ univ :=
            by gcongr; exact subset_univ _
          _ = _ := by ac_rfl
      _ = (μ univ * d) * lpMass (μ.restrict P) p q :=
        lintegral_const_mul' _ _ hcoef
      _ ≤ _ := by
        apply mul_le_mul' le_rfl
        exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hrest : (∫⁻ x in Pᶜ, ∫⁻ y, F x y ∂μ ∂μ) ≤
      (μ univ * d) * lpMass μ p q := by
    calc
      _ ≤ ∫⁻ x in Pᶜ, d * lpMass μ p q ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hS, ae_restrict_mem hP.compl, hzero] with x hx hxP hx0
        calc
          _ ≤ ∫⁻ y, d * ‖q y‖ₑ ^ p.toReal ∂μ := by
            apply lintegral_mono_ae
            filter_upwards [hgap] with y hy
            rw [show F x y = F y x from energyIntegrand_symm m s p q x y]
            exact energyIntegrand_le_of_zero m s p hp ha hx0 (fun hqy => hy hqy x hx hxP)
          _ = _ := lintegral_const_mul' _ _ hd
      _ = (d * lpMass μ p q) * μ Pᶜ := by simp
      _ ≤ (d * lpMass μ p q) * μ univ := by gcongr; exact subset_univ _
      _ = _ := by ac_rfl
  have hm : AEMeasurable (fun x => ∫⁻ y in P, F x y ∂μ) (μ.restrict P) :=
    (energyIntegrand_aemeasurable m s p hq.restrict hq.restrict).lintegral_prod_right
  change (∫⁻ x, ∫⁻ y, F x y ∂μ ∂μ) ≤ _
  rw [← lintegral_add_compl (fun x => ∫⁻ y, F x y ∂μ) hP]
  conv_lhs => enter [1, 2, x]; rw [hsplit x]
  rw [lintegral_add_left' hm]
  calc
    _ ≤ (metricEnergy m (μ.restrict P) s p q + (μ univ * d) * lpMass μ p q) +
        (μ univ * d) * lpMass μ p q := by
      exact add_le_add (add_le_add le_rfl hcross) hrest
    _ = _ := by dsimp [d]; rw [two_mul]; ring

omit [BorelSpace X] [SecondCountableTopology X] in
lemma metricEnergy_congr_ae (m : ℕ) (μ : Measure X) (s : ℝ) (p : ℝ≥0∞)
    {q r : X → E} (h : q =ᵐ[μ] r) : metricEnergy m μ s p q = metricEnergy m μ s p r := by
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  apply lintegral_congr_ae
  filter_upwards [h] with y hy
  simp only [hx, hy]

omit [BorelSpace X] [SecondCountableTopology X] in
lemma metricEnergy_mono_measure (m : ℕ) {μ ν : Measure X} (s : ℝ) (p : ℝ≥0∞)
    (q : X → E) (h : μ ≤ ν) : metricEnergy m μ s p q ≤ metricEnergy m ν s p q := by
  apply lintegral_mono' h
  intro x
  exact lintegral_mono' h (fun _ => le_rfl)

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma lpMass_eq_eLpNorm_pow (μ : Measure X) (p : ℝ≥0∞) {q : X → E}
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) (hq : AEStronglyMeasurable q μ) :
    lpMass μ p q = eLpNorm q p μ ^ p.toReal := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hq, ← ENNReal.rpow_mul,
    one_div_mul_cancel (ENNReal.toReal_pos hp0 hpt).ne', ENNReal.rpow_one]
  rfl

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma indicator_ae_eq_of_zero {μ : Measure X} {P : Set X} (hP : MeasurableSet P)
    {q : X → E} (hzero : ∀ᵐ x ∂μ.restrict Pᶜ, q x = 0) :
    P.indicator q =ᵐ[μ] q := by
  classical
  have hzero' := (ae_restrict_iff' hP.compl).mp hzero
  filter_upwards [hzero'] with x hx
  by_cases hxP : x ∈ P
  · simp [hxP]
  · simp [hxP, hx hxP]

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma eLpNorm_restrict_eq_of_zero {μ : Measure X} {P : Set X} (hP : MeasurableSet P)
    (p : ℝ≥0∞) {q : X → E} (hzero : ∀ᵐ x ∂μ.restrict Pᶜ, q x = 0) :
    eLpNorm q p (μ.restrict P) = eLpNorm q p μ := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hP.nullMeasurableSet]
  exact eLpNorm_congr_ae (indicator_ae_eq_of_zero hP hzero)

omit [MetricSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma lpMass_restrict_eq_of_zero {μ : Measure X} {P : Set X} (hP : MeasurableSet P)
    (p : ℝ≥0∞) (hp : 0 < p.toReal) {q : X → E}
    (hzero : ∀ᵐ x ∂μ.restrict Pᶜ, q x = 0) :
    lpMass (μ.restrict P) p q = lpMass μ p q := by
  have hz : (∫⁻ x in Pᶜ, ‖q x‖ₑ ^ p.toReal ∂μ) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hzero] with x hx
    simp [hx, ENNReal.zero_rpow_of_pos hp]
  unfold lpMass
  rw [← lintegral_add_compl (μ := μ) (fun x => ‖q x‖ₑ ^ p.toReal) hP, hz, add_zero]


end Energy
lemma supported_zero_off_patch (C : BoundaryChart Ω) {K : Set (Ambient m)}
    (hKU : K ⊆ chartImage C.frame C.graphFunction C.center C.radius C.height)
    {E : Type*} [Zero E] {q : Ambient m → E}
    (hsupp : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ K → q x = 0) :
    ∀ᵐ x ∂(surfaceMeasure Ω).restrict (patch C)ᶜ, q x = 0 := by
  filter_upwards [ae_restrict_of_ae hsupp,
    ae_restrict_of_ae (ae_restrict_mem isClosed_frontier.measurableSet),
    ae_restrict_mem (patch_measurableSet C).compl] with x hx hxb hxP
  apply hx
  intro hxK
  exact hxP (by rw [patch_eq]; exact ⟨hxb, hKU hxK⟩)

/-- Analytic estimate using only the graph comparison premise. -/
lemma patch_extension_of_comparison
    (hcomparison : GraphFractionalTransport.Expected.LocalGraphComparison) :
    Expected.PatchExtension := by
  intro m hm Ω hΩ C K hK hKU s hs hs1 p hp hpt
  classical
  let μ := surfaceMeasure Ω
  letI : IsFiniteMeasure μ := ⟨surfaceMeasure_lt_top hΩ⟩
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
  have hpn := hpt.ne
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hpn
  have hr : 0 ≤ 1 / p.toReal := by positivity
  have ha : 0 ≤ (m : ℝ) + s * p.toReal := by positivity
  obtain ⟨G, hG, hcomp⟩ := hcomparison m hm s hs hs1 p hp hpt C.constant
  obtain ⟨δ, hδ, hgap⟩ := compact_support_gap C hK hKU
  let T : ℝ≥0∞ := 2 * μ univ *
    (ENNReal.ofReal δ ^ ((m : ℝ) + s * p.toReal))⁻¹
  have hT : T ≠ ∞ := by
    dsimp [T]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
      (ENNReal.inv_ne_top.mpr (ENNReal.rpow_pos (by positivity) (by simp)).ne')
  let D : ℝ≥0∞ := (G : ℝ≥0∞) * (1 + T)
  have hD : D ≠ ∞ := ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨by simp, hT⟩)
  let A : ℝ≥0 := G + D.toNNReal ^ (1 / p.toReal) + 1
  have hA : (A : ℝ≥0∞) = (G : ℝ≥0∞) + D ^ (1 / p.toReal) + 1 := by
    simp only [A, ENNReal.coe_add, ENNReal.coe_one,
      ENNReal.coe_rpow_of_nonneg _ hr, ENNReal.coe_toNNReal hD]
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro 𝕜 _ q hq hsupp
  have hv := pullback_memLp hcomparison hm C hs hs1 hp hpt hq
  refine ⟨hv, ?_⟩
  have hz := supported_zero_off_patch C hKU hsupp
  have hb := hq.restrict (patch C)
  rw [← graphMeasure_eq C] at hb
  have hbcomp := hcomp C.center C.radius C.radius_pos C.graphFunction
    C.graph_lipschitz C.frame 𝕜 q
  have hmem := hbcomp.2.2.2.2.2.2.2.2.mp hb
  let N := metricNorm m volume s p (pullback C q)
  have hnLp : eLpNorm (pullback C q) p volume ≤ N := le_self_add
  have hnSemi : metricSeminorm m volume s p (pullback C q) ≤ N := le_add_self
  have heqLp : eLpNorm (q ∘ GraphFractionalTransport.graphMap C.frame C.graphFunction)
      p (volume.restrict (ball C.center C.radius)) = eLpNorm (pullback C q) p volume :=
    (eLpNorm_indicator_eq_eLpNorm_restrict isOpen_ball.measurableSet.nullMeasurableSet).symm
  have hmassbase : lpMass (volume.restrict (ball C.center C.radius)) p
      (q ∘ GraphFractionalTransport.graphMap C.frame C.graphFunction) ≤ N ^ p.toReal := by
    rw [lpMass_eq_eLpNorm_pow _ _ hp0 hpn hmem.aestronglyMeasurable, heqLp]
    exact ENNReal.rpow_le_rpow hnLp hpR.le
  have hmass : lpMass μ p q ≤ (G : ℝ≥0∞) * N ^ p.toReal := by
    rw [← lpMass_restrict_eq_of_zero (patch_measurableSet C) p hpR hz,
      ← graphMeasure_eq C]
    exact hbcomp.2.1.trans (mul_le_mul' le_rfl hmassbase)
  have hpull : q ∘ GraphFractionalTransport.graphMap C.frame C.graphFunction =ᵐ[
      volume.restrict (ball C.center C.radius)] pullback C q := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    exact (indicator_of_mem hx _).symm
  have hEbase : metricEnergy m (volume.restrict (ball C.center C.radius)) s p
      (q ∘ GraphFractionalTransport.graphMap C.frame C.graphFunction) ≤ N ^ p.toReal := by
    rw [metricEnergy_congr_ae m _ s p hpull]
    apply (metricEnergy_mono_measure m s p (pullback C q) Measure.restrict_le_self).trans
    have he : metricEnergy m volume s p (pullback C q) =
        metricSeminorm m volume s p (pullback C q) ^ p.toReal := by
      rw [metricSeminorm, ← ENNReal.rpow_mul, one_div_mul_cancel hpR.ne', ENNReal.rpow_one]
    rw [he]
    exact ENNReal.rpow_le_rpow hnSemi hpR.le
  have hElocal : metricEnergy m (μ.restrict (patch C)) s p q ≤
      (G : ℝ≥0∞) * N ^ p.toReal := by
    rw [← graphMeasure_eq C]
    exact hbcomp.2.2.2.2.2.1.trans (mul_le_mul' le_rfl hEbase)
  have hE : metricEnergy m μ s p q ≤ D * N ^ p.toReal := by
    have h := energy_le_restrict_add_mass m μ s p hpR ha hq.aestronglyMeasurable
      (patch_measurableSet C) (ae_restrict_mem isClosed_frontier.measurableSet) hz hδ (by
        filter_upwards [hsupp] with x hx hqx
        have hxK : x ∈ K := by by_contra h; exact hqx (hx h)
        exact hgap x hxK)
    calc
      _ ≤ metricEnergy m (μ.restrict (patch C)) s p q + T * lpMass μ p q := h
      _ ≤ (G : ℝ≥0∞) * N ^ p.toReal + T * ((G : ℝ≥0∞) * N ^ p.toReal) :=
        add_le_add hElocal (mul_le_mul' le_rfl hmass)
      _ = _ := by dsimp [D]; ring
  have hsemi : metricSeminorm m μ s p q ≤ D ^ (1 / p.toReal) * N := by
    calc
      _ ≤ (D * N ^ p.toReal) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow hE hr
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul,
          mul_one_div_cancel hpR.ne', ENNReal.rpow_one]
  have hlp : eLpNorm q p μ ≤ (G : ℝ≥0∞) * N := by
    rw [← eLpNorm_restrict_eq_of_zero (patch_measurableSet C) p hz,
      ← graphMeasure_eq C]
    exact hbcomp.2.2.2.1.trans (by rw [heqLp]; exact mul_le_mul' le_rfl hnLp)
  change eLpNorm q p μ + metricSeminorm m μ s p q ≤ (A : ℝ≥0∞) * N
  calc
    _ ≤ (G : ℝ≥0∞) * N + D ^ (1 / p.toReal) * N := add_le_add hlp hsemi
    _ = ((G : ℝ≥0∞) + D ^ (1 / p.toReal)) * N := (add_mul _ _ _).symm
    _ ≤ (A : ℝ≥0∞) * N := by
      apply mul_le_mul' _ le_rfl
      rw [hA]
      exact le_self_add


/-- The entire boundary has finite Euclidean-normalized surface measure. -/
theorem finite_surface_measure : Expected.FiniteSurfaceMeasure :=
  fun _ _ hΩ => surfaceMeasure_lt_top hΩ

/-- Pushing a compactly supported chart piece to the entire boundary is bounded
by its whole-space zero-extended tangential norm. -/
theorem patch_extension_bound : Expected.PatchExtension :=
  patch_extension_of_comparison GraphFractionalTransport.local_graph_comparison

end P102.Trace.BoundaryPatchExtension
