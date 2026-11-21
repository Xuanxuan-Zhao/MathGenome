import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.MovingEndpoints
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch17.LaplaceError

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology MeasureTheory
namespace D04.MovingEndpoints

abbrev orientedIntegral := @Specs.D04.C08.MovingEndpoints.Model.orientedIntegral

variable {m k : ℕ} {P : Set (E m)}

lemma time_continuous {Y : Type*} [TopologicalSpace Y]
    {g : ℝ → E m → Y}
    (hg : ContinuousOn (fun z : ℝ × E m => g z.1 z.2) (univ ×ˢ P))
    {p : E m} (hp : p ∈ P) : Continuous (fun t => g t p) :=
  hg.comp_continuous (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, hp⟩)

lemma primitive_continuous {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {g : ℝ → E m → Y}
    (hg : ContinuousOn (fun z : ℝ × E m => g z.1 z.2) (univ ×ˢ P)) (c : ℝ) :
    ContinuousOn (fun z : ℝ × E m => ∫ t in c..z.1, g t z.2) (univ ×ˢ P) := by
  have hc : Continuous (fun z : P × ℝ => g z.2 z.1) :=
    hg.comp_continuous (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
      (fun z => ⟨mem_univ _, z.1.property⟩)
  have hi := intervalIntegral.continuous_parametric_primitive_of_continuous (μ := MeasureTheory.volume)
    (a₀ := c) (f := fun (p : P) t => g t p) hc
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hi.comp ((continuous_snd.comp continuous_subtype_val).subtype_mk
    (fun z => z.property.2) |>.prodMk (continuous_fst.comp continuous_subtype_val))

lemma fixed_integral_hasFDerivAt (hP : IsOpen P)
    (f : ℝ → E m → E k) (A : ℝ → E m → E m →L[ℝ] E k)
    (hf : ContinuousOn (fun z : ℝ × E m => f z.1 z.2) (univ ×ˢ P))
    (hA : ContinuousOn (fun z : ℝ × E m => A z.1 z.2) (univ ×ˢ P))
    (hd : ∀ t p, p ∈ P → HasFDerivAt (f t) (A t p) p)
    (c s : ℝ) (p : E m) (hp : p ∈ P) :
    HasFDerivAt (fun q => ∫ t in c..s, f t q) (∫ t in c..s, A t p) p := by
  obtain ⟨r, hr, hrP⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hP.mem_nhds hp)
  have hcomp : IsCompact (uIcc c s ×ˢ Metric.closedBall p r) :=
    isCompact_uIcc.prod (isCompact_closedBall p r)
  obtain ⟨M, hM⟩ := hcomp.bddAbove_image
    (hA.norm.mono (prod_mono (subset_univ _) hrP))
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q t => f t q) (F' := fun q t => A t q)
    (μ := MeasureTheory.volume) (a := c) (b := s)
    (s := Metric.closedBall p r) (bound := fun _ => M)
    (Metric.closedBall_mem_nhds p hr)
  · filter_upwards [hP.mem_nhds hp] with q hq
    exact (time_continuous hf hq).aestronglyMeasurable
  · exact (time_continuous hf hp).intervalIntegrable _ _
  · exact (time_continuous hA hp).aestronglyMeasurable
  · apply Eventually.of_forall
    intro t ht q hq
    apply hM
    exact ⟨(t, q), ⟨uIoc_subset_uIcc ht, hq⟩, rfl⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun t _ q hq => hd t q (hrP hq))

lemma primitive_hasFDerivAt (hP : IsOpen P)
    (f : ℝ → E m → E k) (A : ℝ → E m → E m →L[ℝ] E k)
    (hf : ContinuousOn (fun z : ℝ × E m => f z.1 z.2) (univ ×ˢ P))
    (hA : ContinuousOn (fun z : ℝ × E m => A z.1 z.2) (univ ×ˢ P))
    (hd : ∀ t p, p ∈ P → HasFDerivAt (f t) (A t p) p)
    (c s : ℝ) (p : E m) (hp : p ∈ P) :
    HasFDerivAt (fun z : ℝ × E m => ∫ t in c..z.1, f t z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (f s p)).coprod (∫ t in c..s, A t p))
      (s, p) := by
  have hU : IsOpen (univ ×ˢ P : Set (ℝ × E m)) := isOpen_univ.prod hP
  have hsp : (s, p) ∈ (univ ×ˢ P : Set (ℝ × E m)) := ⟨mem_univ _, hp⟩
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (u := (s, p)) (𝕜 := ℝ)
    (f := fun s p => ∫ t in c..s, f t p)
    (f₁ := fun s p => ContinuousLinearMap.toSpanSingleton ℝ (f s p))
    (f₂ := fun s p => ∫ t in c..s, A t p)
  · filter_upwards [hU.mem_nhds hsp] with z hz
    have hc := time_continuous hf hz.2
    exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).hasFDerivAt
  · filter_upwards [hU.mem_nhds hsp] with z hz
    exact fixed_integral_hasFDerivAt hP f A hf hA hd c z.1 z.2 hz.2
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (E k)).continuous.comp_continuousOn hf
      _ hsp).continuousAt (hU.mem_nhds hsp)
  · exact (primitive_continuous hA c _ hsp).continuousAt (hU.mem_nhds hsp)

/-- On continuous integrands the computational interval integral is the
coordinatewise oriented Darboux integral used in the statement. -/
lemma orientedIntegral_eq_intervalIntegral {f : ℝ → E k} {a b : ℝ}
    (hf : ContinuousOn f (uIcc a b)) :
    SingleVariableAnalysis.Riemann.OrientedRealVectorIntegrable k f a b ∧
    orientedIntegral f a b = ∫ t in a..b, f t := by
  classical
  have hcoord (i : Fin k) : ContinuousOn (fun t => f t i) (uIcc a b) :=
    (PiLp.continuous_apply 2 _ i).comp_continuousOn hf
  have hri (i : Fin k) : SingleVariableAnalysis.Riemann.OrientedRealIntegrable
      (fun t => f t i) a b :=
    SingleVariableAnalysis.Riemann.real_continuous_integrable _ min_le_max
      (fun t ht => (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr
        (hcoord i t ht))
  refine ⟨hri, ?_⟩
  ext i
  change (if h : SingleVariableAnalysis.Riemann.OrientedRealIntegrable
    (fun t => f t i) a b then _ else 0) = _
  rw [dite_eq_left (hri i)]
  have hcomp := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin k => ℝ) i).intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    (hf.intervalIntegrable (μ := MeasureTheory.volume))
  change _ = (∫ t in a..b, f t) i
  change (∫ t in a..b, f t i) = (∫ t in a..b, f t) i at hcomp
  rw [← hcomp]
  change SingleVariableAnalysis.Riemann.O.realIntegralValue _ _ = _
  unfold SingleVariableAnalysis.Riemann.O.realIntegralValue
  split_ifs with hab
  · simpa only [min_eq_left hab, max_eq_right hab] using SingleVariableAnalysis.LaplaceError.real_continuous_integral_eq _ _ _ min_le_max
      (hcoord i) (hri i)
  · rw [intervalIntegral.integral_symm]
    congr 1
    have hba := le_of_not_ge hab
    simpa only [min_eq_right hba, max_eq_left hba] using
      SingleVariableAnalysis.LaplaceError.real_continuous_integral_eq _ _ _ hba
        (by simpa only [uIcc_of_ge hba] using hcoord i)
        (by simpa only [SingleVariableAnalysis.Riemann.OrientedRealIntegrable,
          SingleVariableAnalysis.Riemann.O.realIntegrableValue, min_eq_right hba,
          max_eq_left hba] using hri i)

/-- The Leibniz rule when the time variable is globally defined. Parameter
values outside the open set remain entirely unrestricted. -/
lemma global_time_rule (hP : IsOpen P)
    (f : ℝ → E m → E k) (A : ℝ → E m → E m →L[ℝ] E k)
    (hf : ContinuousOn (fun z : ℝ × E m => f z.1 z.2) (univ ×ˢ P))
    (hA : ContinuousOn (fun z : ℝ × E m => A z.1 z.2) (univ ×ˢ P))
    (hd : ∀ t p, p ∈ P → HasFDerivAt (f t) (A t p) p)
    (a b : E m → ℝ) (ha : CrOn 1 P a) (hb : CrOn 1 P b) :
    let F := fun p => ∫ t in a p..b p, f t p
    let B := fun p => (∫ t in a p..b p, A t p) +
      (fderiv ℝ b p).smulRight (f (b p) p) -
      (fderiv ℝ a p).smulRight (f (a p) p)
    (∀ p ∈ P, HasFDerivAt F (B p) p) ∧ ContinuousOn B P := by
  dsimp only
  have hda (p : E m) (hp : p ∈ P) : HasFDerivAt a (fderiv ℝ a p) p := by
    obtain ⟨L, hL⟩ := ha.1 p hp
    exact ((hasTotalDerivative_iff_hasFDerivAt P a L p hP hp).mp hL).differentiableAt.hasFDerivAt
  have hdb (p : E m) (hp : p ∈ P) : HasFDerivAt b (fderiv ℝ b p) p := by
    obtain ⟨L, hL⟩ := hb.1 p hp
    exact ((hasTotalDerivative_iff_hasFDerivAt P b L p hP hp).mp hL).differentiableAt.hasFDerivAt
  have hac : ContinuousOn a P := fun p hp => (hda p hp).continuousAt.continuousWithinAt
  have hbc : ContinuousOn b P := fun p hp => (hdb p hp).continuousAt.continuousWithinAt
  have graph_a : ContinuousOn (fun p => (a p, p)) P := hac.prodMk continuousOn_id
  have graph_b : ContinuousOn (fun p => (b p, p)) P := hbc.prodMk continuousOn_id
  have hBa : ContinuousOn (fun p => ∫ t in 0..a p, A t p) P :=
    (primitive_continuous hA 0).comp graph_a (fun p hp => ⟨mem_univ _, hp⟩)
  have hBb : ContinuousOn (fun p => ∫ t in 0..b p, A t p) P :=
    (primitive_continuous hA 0).comp graph_b (fun p hp => ⟨mem_univ _, hp⟩)
  have hAB : ContinuousOn (fun p => ∫ t in a p..b p, A t p) P := by
    apply (hBb.sub hBa).congr
    intro p hp
    exact (intervalIntegral.integral_interval_sub_left
      ((time_continuous hA hp).intervalIntegrable (μ := MeasureTheory.volume) 0 (b p))
      ((time_continuous hA hp).intervalIntegrable (μ := MeasureTheory.volume) 0 (a p))).symm
  have hf_a : ContinuousOn (fun p => f (a p) p) P :=
    hf.comp graph_a (fun p hp => ⟨mem_univ _, hp⟩)
  have hf_b : ContinuousOn (fun p => f (b p) p) P :=
    hf.comp graph_b (fun p hp => ⟨mem_univ _, hp⟩)
  refine ⟨?_, (hAB.add ?_).sub ?_⟩
  · intro p hp
    have h1 := (primitive_hasFDerivAt hP f A hf hA hd 0 (b p) p hp).comp p (f := fun q => (b q, q))
      ((hdb p hp).prodMk (hasFDerivAt_id p))
    have h2 := (primitive_hasFDerivAt hP f A hf hA hd 0 (a p) p hp).comp p (f := fun q => (a q, q))
      ((hda p hp).prodMk (hasFDerivAt_id p))
    have h := h1.sub h2
    have he : (fun q => (∫ t in 0..b q, f t q) - ∫ t in 0..a q, f t q) =ᶠ[𝓝 p]
        (fun q => ∫ t in a q..b q, f t q) := by
      filter_upwards [hP.mem_nhds hp] with q hq
      exact intervalIntegral.integral_interval_sub_left
        ((time_continuous hf hq).intervalIntegrable (μ := MeasureTheory.volume) _ _)
        ((time_continuous hf hq).intervalIntegrable (μ := MeasureTheory.volume) _ _)
    apply (h.congr_of_eventuallyEq he.symm).congr_fderiv
    ext v
    have hi := intervalIntegral.integral_interval_sub_left
      ((time_continuous hA hp).intervalIntegrable (μ := MeasureTheory.volume) 0 (b p))
      ((time_continuous hA hp).intervalIntegrable (μ := MeasureTheory.volume) 0 (a p))
    have hiv := congrArg (fun L : E m →L[ℝ] E k => L v) hi
    simp only [sub_apply] at hiv
    simp only [sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smulRight_apply]
    rw [← hiv]
    abel
  · exact isBoundedBilinearMap_smulRight.continuous.comp_continuousOn (hb.2.prodMk hf_b)
  · exact isBoundedBilinearMap_smulRight.continuous.comp_continuousOn (ha.2.prodMk hf_a)

/-- A compact interval strictly containing two prescribed points of an open
interval. This also applies when the two points coincide or are reversed. -/
lemma compact_interval_inside {I : Set ℝ} (hI : IsOpen I) (hIc : OrdConnected I)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    ∃ l u, Icc l u ⊆ I ∧ x ∈ Ioo l u ∧ y ∈ Ioo l u := by
  have hmin : min x y ∈ I := by rcases le_total x y with h | h <;> simp [h, hx, hy]
  have hmax : max x y ∈ I := by rcases le_total x y with h | h <;> simp [h, hx, hy]
  obtain ⟨l₀, u₀, hlo, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hmin)
  obtain ⟨l₁, u₁, hhi, hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hmax)
  obtain ⟨l, hl₀, hl⟩ := exists_between hlo.1
  obtain ⟨u, hu, hu₁⟩ := exists_between hhi.2
  have hlI : l ∈ I := hsub ⟨hl₀, hl.trans hlo.2⟩
  have huI : u ∈ I := hsub' ⟨hhi.1.trans hu, hu₁⟩
  exact ⟨l, u, hIc.out hlI huI,
    ⟨hl.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hu⟩,
    ⟨hl.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hu⟩⟩

/-- Localizing time does not impose any differentiability in time. -/
lemma interval_local_rule {I : Set ℝ} (hI : IsOpen I) (hIc : OrdConnected I) (hP : IsOpen P)
    (f : ℝ → E m → E k) (A : ℝ → E m → E m →L[ℝ] E k)
    (hf : ContinuousOn (fun z : ℝ × E m => f z.1 z.2) (I ×ˢ P))
    (hA : ContinuousOn (fun z : ℝ × E m => A z.1 z.2) (I ×ˢ P))
    (hd : ∀ t ∈ I, ∀ p ∈ P, HasFDerivAt (f t) (A t p) p)
    (a b : E m → ℝ) (ha : CrOn 1 P a) (hb : CrOn 1 P b)
    (haI : MapsTo a P I) (hbI : MapsTo b P I) (p : E m) (hp : p ∈ P) :
    let F := fun p => ∫ t in a p..b p, f t p
    HasFDerivAt F ((∫ t in a p..b p, A t p) +
      (fderiv ℝ b p).smulRight (f (b p) p) -
      (fderiv ℝ a p).smulRight (f (a p) p)) p ∧
    ContinuousAt (fderiv ℝ F) p := by
  dsimp only
  obtain ⟨l, u, hluI, halu, hblu⟩ := compact_interval_inside hI hIc (haI hp) (hbI hp)
  have hlu : l ≤ u := halu.1.le.trans halu.2.le
  let τ : ℝ → ℝ := fun t => max l (min u t)
  have hτ : Continuous τ := continuous_const.max (continuous_const.min continuous_id)
  have hτmem (t : ℝ) : τ t ∈ Icc l u :=
    ⟨le_max_left _ _, max_le hlu (min_le_left _ _)⟩
  have hτI (t : ℝ) : τ t ∈ I := hluI (hτmem t)
  have hτeq {t : ℝ} (ht : t ∈ Icc l u) : τ t = t := by
    simp only [τ, min_eq_right ht.2, max_eq_right ht.1]
  let g := fun t p => f (τ t) p
  let C := fun t p => A (τ t) p
  have hg : ContinuousOn (fun z : ℝ × E m => g z.1 z.2) (univ ×ˢ P) :=
    hf.comp (hτ.prodMap continuous_id).continuousOn (fun z hz => ⟨hτI _, hz.2⟩)
  have hC : ContinuousOn (fun z : ℝ × E m => C z.1 z.2) (univ ×ˢ P) :=
    hA.comp (hτ.prodMap continuous_id).continuousOn (fun z hz => ⟨hτI _, hz.2⟩)
  have hgd (t q) (hq : q ∈ P) : HasFDerivAt (g t) (C t q) q := hd _ (hτI t) q hq
  let B := fun q => (∫ t in a q..b q, C t q) +
    (fderiv ℝ b q).smulRight (g (b q) q) - (fderiv ℝ a q).smulRight (g (a q) q)
  have hglobal := global_time_rule hP g C hg hC hgd a b ha hb
  change (∀ q ∈ P, HasFDerivAt (fun q => ∫ t in a q..b q, g t q) (B q) q) ∧
    ContinuousOn B P at hglobal
  have hac : ContinuousAt a p := by
    obtain ⟨L, hL⟩ := ha.1 p hp
    exact ((hasTotalDerivative_iff_hasFDerivAt P a L p hP hp).mp hL).continuousAt
  have hbc : ContinuousAt b p := by
    obtain ⟨L, hL⟩ := hb.1 p hp
    exact ((hasTotalDerivative_iff_hasFDerivAt P b L p hP hp).mp hL).continuousAt
  have heq : (fun q => ∫ t in a q..b q, f t q) =ᶠ[𝓝 p]
      (fun q => ∫ t in a q..b q, g t q) := by
    filter_upwards [hac.eventually (Ioo_mem_nhds halu.1 halu.2),
      hbc.eventually (Ioo_mem_nhds hblu.1 hblu.2)] with q hqa hqb
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [g]
    rw [hτeq (uIcc_subset_Icc ⟨hqa.1.le, hqa.2.le⟩ ⟨hqb.1.le, hqb.2.le⟩ ht)]
  have hBp : B p = (∫ t in a p..b p, A t p) +
      (fderiv ℝ b p).smulRight (f (b p) p) -
      (fderiv ℝ a p).smulRight (f (a p) p) := by
    dsimp only [B, g, C]
    rw [hτeq ⟨halu.1.le, halu.2.le⟩, hτeq ⟨hblu.1.le, hblu.2.le⟩]
    congr 2
    apply intervalIntegral.integral_congr
    intro t ht
    change A (τ t) p = A t p
    rw [hτeq (uIcc_subset_Icc ⟨halu.1.le, halu.2.le⟩ ⟨hblu.1.le, hblu.2.le⟩ ht)]
  refine ⟨hBp ▸ (hglobal.1 p hp).congr_of_eventuallyEq heq, ?_⟩
  have hc : ContinuousAt (fderiv ℝ (fun q => ∫ t in a q..b q, g t q)) p := by
    apply ((hglobal.2 p hp).continuousAt (hP.mem_nhds hp)).congr_of_eventuallyEq
    filter_upwards [hP.mem_nhds hp] with q hq
    exact (hglobal.1 q hq).fderiv
  exact hc.congr_of_eventuallyEq heq.fderiv

/-- Leibniz' rule for finite-dimensional vector parameters, with oriented
scalar Riemann integration. No time derivative or ordering is assumed. -/
theorem moving_endpoints : Specs.D04.C08.MovingEndpoints.moving_endpointsType := by
  intro m k I P hI hIc hP f A hf hA hd a b ha hb haI hbI
  let F := fun p => orientedIntegral (fun t => f t p) (a p) (b p)
  let H := fun p => ∫ t in a p..b p, f t p
  let B := fun p => (∫ t in a p..b p, A t p) +
    (fderiv ℝ b p).smulRight (f (b p) p) -
    (fderiv ℝ a p).smulRight (f (a p) p)
  have hfc (p : E m) (hp : p ∈ P) : ContinuousOn (fun t => f t p) (uIcc (a p) (b p)) :=
    hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hIc.uIcc_subset (haI hp) (hbI hp) ht, hp⟩)
  have hAc (p : E m) (hp : p ∈ P) : ContinuousOn (fun t => A t p) (uIcc (a p) (b p)) :=
    hA.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨hIc.uIcc_subset (haI hp) (hbI hp) ht, hp⟩)
  have hdir (p : E m) (hp : p ∈ P) (h : E m) :
      ContinuousOn (fun t => A t p h) (uIcc (a p) (b p)) :=
    ((continuous_id.clm_apply continuous_const).comp_continuousOn (hAc p hp))
  have hR (p : E m) (hp : p ∈ P) := orientedIntegral_eq_intervalIntegral (hfc p hp)
  have hRd (p : E m) (hp : p ∈ P) (h : E m) :=
    orientedIntegral_eq_intervalIntegral (hdir p hp h)
  have heq (p : E m) (hp : p ∈ P) : F =ᶠ[𝓝 p] H := by
    filter_upwards [hP.mem_nhds hp] with q hq
    exact (hR q hq).2
  have hlocal (p : E m) (hp : p ∈ P) :
      HasFDerivAt H (B p) p ∧ ContinuousAt (fderiv ℝ H) p :=
    interval_local_rule hI hIc hP f A hf hA hd a b ha hb haI hbI p hp
  have hder (p : E m) (hp : p ∈ P) : HasFDerivAt F (B p) p :=
    (hlocal p hp).1.congr_of_eventuallyEq (heq p hp)
  have hCr : CrOn 1 P F := by
    change TotalDifferentiableOn P F ∧ ContinuousOn (totalDerivative F) P
    refine ⟨fun p hp => ⟨B p, (hasTotalDerivative_iff_hasFDerivAt P F (B p) p hP hp).mpr
      (hder p hp)⟩, ?_⟩
    intro p hp
    exact ((hlocal p hp).2.congr_of_eventuallyEq (heq p hp).fderiv).continuousWithinAt
  refine ⟨fun p hp => ⟨(hR p hp).1, fun h => (hRd p hp h).1⟩, hCr, fun p hp =>
    ⟨(hder p hp).differentiableAt, fun h => ?_⟩⟩
  rw [(hder p hp).fderiv]
  change (∫ t in a p..b p, A t p) h +
    (fderiv ℝ b p h) • f (b p) p - (fderiv ℝ a p h) • f (a p) p = _
  rw [ContinuousLinearMap.intervalIntegral_apply (hAc p hp).intervalIntegrable h]
  exact congrArg (fun v : E k => v + (fderiv ℝ b p h) • f (b p) p -
    (fderiv ℝ a p h) • f (a p) p) (hRd p hp h).2.symm

end D04.MovingEndpoints
