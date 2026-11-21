import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.ChartIndependentTangentSpaces
import MathGenome.Internal.MultivariableAnalysis.D04.C14.RegularLevelsAndGraphs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04
abbrev chartDifferential := @Specs.D04.C14.ChartIndependentTangentSpaces.Model.chartDifferential
abbrev tangentSpace := @Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace
abbrev twoSidedVelocities := @Specs.D04.C14.ChartIndependentTangentSpaces.Model.twoSidedVelocities
abbrev oneSidedVelocities := @Specs.D04.C14.ChartIndependentTangentSpaces.Model.oneSidedVelocities

namespace EmbeddedChart
variable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}

theorem differential_extension (c : EmbeddedChart r k n M) {u : E k}
    (hu : u ∈ c.source) {W : Set (E k)} {g : E k → E n}
    (hW : IsOpen W) (huW : u ∈ W) (he : EqOn g c.toFun (c.source ∩ W))
    (hg : DifferentiableAt ℝ g u) : chartDifferential c u = fderiv ℝ g u := by
  change fderivWithin ℝ c.toFun c.source u = fderiv ℝ g u
  apply HasFDerivWithinAt.fderivWithin _ (c.source_uniqueDiff u hu)
  exact hg.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq
    (eventuallyEq_of_mem (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW))) he.symm)
    (he ⟨hu, huW⟩).symm

theorem hasDifferential (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r)
    {u : E k} (hu : u ∈ c.source) :
    HasFDerivWithinAt c.toFun (chartDifferential c u) c.source u := by
  obtain ⟨W, g, hW, huW, he, hg, _⟩ := c.regular u hu
  have hd := (hg.contDiffAt (hW.mem_nhds huW)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))
  rw [c.differential_extension hu hW huW he hd]
  exact hd.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq
    (eventuallyEq_of_mem (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW))) he.symm)
    (he ⟨hu, huW⟩).symm

theorem differential_injective (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r)
    {u : E k} (hu : u ∈ c.source) : Function.Injective (chartDifferential c u) := by
  obtain ⟨W, g, hW, huW, he, hg, hinj⟩ := c.regular u hu
  have hd := (hg.contDiffAt (hW.mem_nhds huW)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))
  rw [c.differential_extension hu hW huW he hd]
  exact hinj u huW

theorem differential_transition (c d : EmbeddedChart r k n M)
    (hr : ManifoldRegularity r) (hkn : k ≤ n) {u : E k} (hu : u ∈ chartOverlap c d) :
    ∃ A : E k ≃L[ℝ] E k,
      chartDifferential c u = (chartDifferential d (chartTransition c d u)).comp
        A.toContinuousLinearMap := by
  obtain ⟨A, hA, _⟩ := chart_transition_derivatives c d hr hkn u hu
  refine ⟨A, (c.overlap_uniqueDiff d u hu).eq (f := c.toFun) ?_ ?_⟩
  · exact (c.hasDifferential hr hu.1).mono inter_subset_left
  · exact ((d.hasDifferential hr (c.transition_mem d hu).1).comp u hA
      (fun v hv => (c.transition_mem d hv).1)).congr'
      (fun v hv => (d.right_inv _ ⟨(c.map_source hv.1).1, hv.2⟩).symm) hu

end EmbeddedChart
open EmbeddedChart

theorem chartDifferential_extension :
    Specs.D04.C14.ChartIndependentTangentSpaces.chartDifferential_extensionType := by
  intro r k n M c _ u hu W g hW huW he hg
  exact EmbeddedChart.differential_extension c hu hW huW he hg

theorem chart_independence :
    Specs.D04.C14.ChartIndependentTangentSpaces.chart_independenceType := by
  intro r k n M c d hr hkn u hu v hv he
  have hcd : u ∈ chartOverlap c d := ⟨hu, by change c.toFun u ∈ d.ambient; rw [he]; exact (d.map_source hv).2⟩
  have hdc : v ∈ chartOverlap d c := ⟨hv, by change d.toFun v ∈ c.ambient; rw [← he]; exact (c.map_source hu).2⟩
  have ht : chartTransition c d u = v := by
    change d.invFun (c.toFun u) = v
    rw [he, d.left_inv _ hv]
  have ht' : chartTransition d c v = u := by
    change c.invFun (d.toFun v) = u
    rw [← he, c.left_inv _ hu]
  obtain ⟨A, hA⟩ := EmbeddedChart.differential_transition c d hr hkn hcd
  obtain ⟨B, hB⟩ := EmbeddedChart.differential_transition d c hr hkn hdc
  rw [ht] at hA
  rw [ht'] at hB
  apply le_antisymm
  · rintro w ⟨z, rfl⟩
    exact ⟨A z, (DFunLike.congr_fun hA z).symm⟩
  · rintro w ⟨z, rfl⟩
    exact ⟨B z, (DFunLike.congr_fun hB z).symm⟩

theorem tangentSpace_chart :
    Specs.D04.C14.ChartIndependentTangentSpaces.tangentSpace_chartType := by
  intro r k n M c hr hkn u hu
  apply le_antisymm
  · apply iSup_le
    intro d
    apply iSup_le
    intro v
    apply iSup_le
    intro hv
    apply iSup_le
    intro he
    exact le_of_eq (chart_independence d c hr hkn v hv u hu he)
  · exact le_iSup_of_le c (le_iSup_of_le u (le_iSup_of_le hu (le_iSup_of_le rfl le_rfl)))

theorem tangentSpace_finrank :
    Specs.D04.C14.ChartIndependentTangentSpaces.tangentSpace_finrankType := by
  intro r k n M hM x hx
  obtain ⟨c, u, hu, he⟩ := hM.2.2 x hx
  rw [← he, tangentSpace_chart c hM.1 hM.2.1 u hu.1]
  exact derivative_rank _ (EmbeddedChart.differential_injective c hM.1 hu.1)

theorem tangentSpace_zero :
    Specs.D04.C14.ChartIndependentTangentSpaces.tangentSpace_zeroType := by
  intro r n M hM x hx
  exact Submodule.finrank_eq_zero.mp (tangentSpace_finrank hM x hx)


/-- A velocity of a curve germ in a chart lies in the derivative range.
Only differentiability at the marked parameter is needed for this direction. -/
theorem curve_velocity_mem_range {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    {u : E k} (hu : u ∈ c.source) {γ : ℝ → E n} {v : E n} {s : Set ℝ}
    (hs : UniqueDiffWithinAt ℝ s 0) (hγ : HasDerivWithinAt γ v s 0)
    (hγ0 : γ 0 = c.toFun u) (hM : ∀ᶠ t in 𝓝[s] 0, γ t ∈ M) :
    v ∈ LinearMap.range (chartDifferential c u).toLinearMap := by
  obtain ⟨W, g, hW, huW, he, hg, _⟩ := c.regular u hu
  have hdg := (hg.contDiffAt (hW.mem_nhds huW)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))
  obtain ⟨O, J, hO, hxO, hJ, hJe⟩ := chart_inverse_extension c hr hkn u hu
  obtain ⟨T, hT, hTe⟩ := continuousOn_iff'.mp c.continuous_invFun W hW
  have hx := c.map_source hu
  have hxT : c.toFun u ∈ T := by
    have hh : c.toFun u ∈ c.invFun ⁻¹' W ∩ (M ∩ c.ambient) :=
      ⟨by simpa only [mem_preimage, c.left_inv u hu] using huW, hx⟩
    rw [hTe] at hh
    exact hh.1
  have hJx : J (c.toFun u) = u := by
    rw [hJe ⟨hx, hxO⟩, c.left_inv u hu]
  have hdJ := (hJ.contDiffAt (hO.mem_nhds hxO)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))
  have hγcont : Tendsto γ (𝓝[s] 0) (𝓝 (c.toFun u)) := by
    have hh := hγ.continuousWithinAt
    change Tendsto γ (𝓝[s] 0) (𝓝 (γ 0)) at hh
    rwa [hγ0] at hh
  have hev : ∀ᶠ t in 𝓝[s] 0, γ t ∈ (c.ambient ∩ O) ∩ T :=
    hγcont.eventually (((c.ambient_open.inter hO).inter hT).mem_nhds ⟨⟨hx.2, hxO⟩, hxT⟩)
  have heq : (fun t => g (J (γ t))) =ᶠ[𝓝[s] 0] γ := by
    filter_upwards [hev, hM] with t ht hMt
    have hxma : γ t ∈ M ∩ c.ambient := ⟨hMt, ht.1.1⟩
    have hiW : c.invFun (γ t) ∈ W := by
      have hh : γ t ∈ T ∩ (M ∩ c.ambient) := ⟨ht.2, hxma⟩
      rw [← hTe] at hh
      exact hh.1
    rw [hJe ⟨hxma, ht.1.2⟩, he ⟨c.map_target hxma, hiW⟩, c.right_inv _ hxma]
  have hdJ' : HasFDerivAt J (fderiv ℝ J (c.toFun u)) (γ 0) := by
    simpa only [hγ0] using hdJ.hasFDerivAt
  have hdg' : HasFDerivAt g (fderiv ℝ g u) (J (γ 0)) := by
    simpa only [hγ0, hJx] using hdg.hasFDerivAt
  have hd := hdg'.comp_hasDerivWithinAt 0 (hdJ'.comp_hasDerivWithinAt 0 hγ)
  have he0 : g (J (γ 0)) = γ 0 := by rw [hγ0, hJx, he ⟨hu, huW⟩]
  have hd' : HasDerivWithinAt γ
      ((fderiv ℝ g u) ((fderiv ℝ J (c.toFun u)) v)) s 0 :=
    hd.congr_of_eventuallyEq heq.symm he0.symm
  refine ⟨(fderiv ℝ J (c.toFun u)) v, ?_⟩
  change chartDifferential c u _ = v
  rw [EmbeddedChart.differential_extension c hu hW huW he hdg]
  exact hs.eq_deriv s hd' hγ

/-- Kernel identification for the actual regular-level subset of its open domain. -/
theorem tangentSpace_regular_level :
    Specs.D04.C14.ChartIndependentTangentSpaces.tangentSpace_regular_levelType := by
  intro r k n O g hr hkn hO hg hsurj x hx
  have hrank : ∀ y ∈ O, g y = 0 →
      Module.finrank ℝ (LinearMap.range (fderiv ℝ g y).toLinearMap) = n-k :=
    fun y hy hz => RegularLevels.range_finrank_of_surjective _ (hsurj y hy hz)
  have hM := (boundaryless_iff.mp (RegularLevels.regular_zero_set O g hr hkn hO hg hrank)).1
  obtain ⟨c, u, hu, hux⟩ := hM.2.2 x hx
  have hcu : c.toFun u ∈ O := (c.map_source hu.1).1.1
  have hdg := (hg.contDiffAt (hO.mem_nhds hcu)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))
  have hdcomp := hdg.hasFDerivAt.comp_hasFDerivWithinAt u
    (EmbeddedChart.hasDifferential c hr hu.1)
  have hzero : (fderiv ℝ g (c.toFun u)).comp (chartDifferential c u) = 0 := by
    apply (EmbeddedChart.source_uniqueDiff c u hu.1).eq hdcomp
    exact (hasFDerivWithinAt_const (0 : E (n-k)) u c.source).congr'
      (fun v hv => (c.map_source hv).1.2) hu.1
  have hle : tangentSpace r k (O ∩ g ⁻¹' {0}) x ≤ (fderiv ℝ g x).ker := by
    rw [← hux]
    change Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace r k _ _ ≤ _
    rw [tangentSpace_chart c hr hkn u hu.1]
    rintro v ⟨w, rfl⟩
    exact DFunLike.congr_fun hzero w
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hdim := (fderiv ℝ g x).toLinearMap.finrank_range_add_finrank_ker
  rw [hrank x hx.1 hx.2] at hdim
  simp only [finrank_euclideanSpace_fin] at hdim
  rw [tangentSpace_finrank hM x hx]
  omega


/-- Restricting a boundary chart differentiates by the flat inclusion. -/
theorem tangentSpace_intrinsic_boundary :
    Specs.D04.C14.ChartIndependentTangentSpaces.tangentSpace_intrinsic_boundaryType := by
  intro r d n M c hr hkn hc u hu hflat
  let b := EmbeddedChart.boundaryChart c hr hkn hc
  let v := flatProjection d u
  have hι : flatInclusion d v = u := flatInclusion_projection d u hflat
  have hv : v ∈ b.source := by change flatInclusion d v ∈ c.source; rwa [hι]
  have hb : b.toFun v = c.toFun u := by change c.toFun (flatInclusion d v) = c.toFun u; rw [hι]
  obtain ⟨W, g, hW, huW, he, hg, _⟩ := c.regular u hu
  have hdg := (hg.contDiffAt (hW.mem_nhds huW)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))
  have hdg' : HasFDerivAt g (fderiv ℝ g u) (flatInclusion d v) := by rw [hι]; exact hdg.hasFDerivAt
  have hd := hdg'.comp v (flatInclusion d).hasFDerivAt
  have he' : EqOn (g ∘ flatInclusion d) b.toFun
      (b.source ∩ flatInclusion d ⁻¹' W) := by
    intro w hw
    exact he ⟨hw.1, hw.2⟩
  have hdb : chartDifferential b v = (chartDifferential c u).comp (flatInclusion d) := by
    rw [EmbeddedChart.differential_extension b hv
      (hW.preimage (flatInclusion d).continuous) (by change flatInclusion d v ∈ W; rwa [hι])
      he' hd.differentiableAt, hd.fderiv,
      EmbeddedChart.differential_extension c hu hW huW he hdg]
  rw [← hb, tangentSpace_chart b hr ((Nat.le_succ d).trans hkn) v hv]
  change (LinearMap.range (chartDifferential b v).toLinearMap : Set (E n)) = _
  rw [hdb]
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨flatInclusion d z, flatInclusion_last d z, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨flatProjection d z, by
      change chartDifferential c u (flatInclusion d (flatProjection d z)) = _
      rw [flatInclusion_projection d z hz]⟩


namespace EmbeddedChart
variable {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}

/-- A chart extension composed with a parameter line gives a C¹ ambient curve
on an open interval. On the portion of the line in the chart it lies in M. -/
theorem parameter_curve (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r)
    {u : E k} (hu : u ∈ c.source) (w : E k) :
    ∃ (γ : ℝ → E n) (U : Set ℝ), IsOpen U ∧ 0 ∈ U ∧ ContDiffOn ℝ 1 γ U ∧
      γ 0 = c.toFun u ∧ HasDerivAt γ (chartDifferential c u w) 0 ∧
      ∀ t ∈ U, u + t • w ∈ c.source → γ t ∈ M := by
  obtain ⟨W, g, hW, huW, he, hg, _⟩ := c.regular u hu
  let l : ℝ → E k := fun t => u + t • w
  have hl : ContDiff ℝ r l := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hl0 : l 0 = u := by simp [l]
  have hdl : HasDerivAt l w 0 := by
    simpa only [l, one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add u
  have hdg := (hg.contDiffAt (hW.mem_nhds huW)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hr.1))
  have hdg' : HasFDerivAt g (fderiv ℝ g u) (l 0) := by rw [hl0]; exact hdg.hasFDerivAt
  refine ⟨g ∘ l, l ⁻¹' W, hW.preimage hl.continuous, ?_, ?_, ?_, ?_, ?_⟩
  · change l 0 ∈ W; rwa [hl0]
  · exact (hg.of_le hr.1).comp (hl.of_le hr.1).contDiffOn (fun _ ht => ht)
  · change g (l 0) = c.toFun u
    rw [hl0, he ⟨hu, huW⟩]
  · rw [c.differential_extension hu hW huW he hdg]
    exact hdg'.comp_hasDerivAt 0 hdl
  · intro t ht hts
    change g (l t) ∈ M
    rw [he ⟨hts, ht⟩]
    exact (c.map_source hts).1

/-- Inward parameter directions remain in the source for sufficiently small
nonnegative times. At an interior point every direction is permitted. -/
theorem ray_eventually_source (c : EmbeddedChart r k n M) {u : E k}
    (hu : u ∈ c.source) {w : E k} (hw : w ∈ inwardParameterCone c u) :
    ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0, u + t • w ∈ c.source := by
  classical
  have hl : Continuous (fun t : ℝ => u + t • w) := continuous_const.add (continuous_id.smul continuous_const)
  have hlim : Tendsto (fun t : ℝ => u + t • w) (𝓝 0) (𝓝 u) := by
    simpa only [ContinuousAt, zero_smul, add_zero] using (hl.continuousAt (x := 0))
  by_cases hb : IsBoundaryParameter c u
  · obtain ⟨W, hW, hsource⟩ := c.source_open
    have huW : u ∈ W := (hsource ▸ hu).2
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), u + t • w ∈ W := by
      exact hlim.eventually (hW.mem_nhds huW)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hev] with t ht htW
    rw [hsource]
    refine ⟨?_, htW⟩
    rw [hb.1]
    cases k with
    | zero => exact False.elim (Nat.lt_irrefl 0 (c.half_pos hb.1))
    | succ d =>
      have hwpos : 0 ≤ w (Fin.last d) := by
        change w ∈ (if IsBoundaryParameter c u then halfSpace (d+1) else univ) at hw
        rw [ite_eq_left hb] at hw
        exact hw
      change 0 ≤ u (Fin.last d) + t * w (Fin.last d)
      rw [show u (Fin.last d) = 0 from hb.2]
      simpa only [zero_add] using mul_nonneg ht hwpos
  · have hh : ∀ᶠ t in 𝓝 (0 : ℝ), u + t • w ∈ c.source := by
      exact hlim.eventually (c.source_mem_nhds hu hb)
    exact mem_nhdsWithin_of_mem_nhds hh

theorem inward_velocity (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r)
    {u : E k} (hu : u ∈ c.source) {w : E k} (hw : w ∈ inwardParameterCone c u) :
    chartDifferential c u w ∈ oneSidedVelocities M (c.toFun u) := by
  obtain ⟨γ, U, hU, h0U, hγ, hγ0, hdγ, hmaps⟩ := c.parameter_curve hr hu w
  have hev := inter_mem (c.ray_eventually_source hu hw)
    (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0U))
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
  refine ⟨γ, ε, hε, hγ0, hγ.mono (fun t ht => (hsub ht).2), ?_, hdγ.hasDerivWithinAt⟩
  intro t ht
  exact hmaps t (hsub ht).2 (hsub ht).1

theorem interior_velocity (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r)
    {u : E k} (hu : u ∈ c.source) (hi : ¬ IsBoundaryParameter c u) (w : E k) :
    chartDifferential c u w ∈ twoSidedVelocities M (c.toFun u) := by
  obtain ⟨γ, U, hU, h0U, hγ, hγ0, hdγ, hmaps⟩ := c.parameter_curve hr hu w
  have hl : Continuous (fun t : ℝ => u + t • w) := continuous_const.add (continuous_id.smul continuous_const)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), u + t • w ∈ c.source := by
    have hlim : Tendsto (fun t : ℝ => u + t • w) (𝓝 0) (𝓝 u) := by
      simpa only [ContinuousAt, zero_smul, add_zero] using (hl.continuousAt (x := 0))
    exact hlim.eventually (c.source_mem_nhds hu hi)
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem hev (hU.mem_nhds h0U))
  let ε := min (-a) b
  have hε : 0 < ε := lt_min (neg_pos.mpr hab.1) hab.2
  have hsub' : Ioo (-ε) ε ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_le_of_lt (by dsimp [ε]; linarith [min_le_left (-a) b]) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right (-a) b)⟩
  refine ⟨γ, ε, hε, hγ0, hγ.mono (fun t ht => (hsub (hsub' ht)).2), ?_, hdγ⟩
  intro t ht
  exact hmaps t (hsub (hsub' ht)).2 (hsub (hsub' ht)).1

end EmbeddedChart


/-- At an interior point the range consists of exactly the two-sided C¹
curve velocities; the assertion deliberately excludes boundary points. -/
theorem tangentSpace_interior_velocities :
    Specs.D04.C14.ChartIndependentTangentSpaces.tangentSpace_interior_velocitiesType := by
  intro r k n M hM x hx hnot
  obtain ⟨c, u, hu, hux⟩ := hM.2.2 x hx
  have hi : ¬ IsBoundaryParameter c u := by
    intro hb
    apply hnot
    rw [← hux]
    exact (chart_intrinsicBoundary c hM.1 hM.2.1 u hu.1).mpr hb
  rw [← hux, tangentSpace_chart c hM.1 hM.2.1 u hu.1]
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact EmbeddedChart.interior_velocity c hM.1 hu.1 hi w
  · rintro ⟨γ, ε, hε, hγ0, _, hmaps, hdγ⟩
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ M :=
      eventually_of_mem (Ioo_mem_nhds (neg_neg_of_pos hε) hε) hmaps
    exact curve_velocity_mem_range c hM.1 hM.2.1 hu.1
      (uniqueDiffOn_univ (0 : ℝ) (mem_univ _)) hdγ.hasDerivWithinAt hγ0
      (mem_nhdsWithin_of_mem_nhds hev)

/-- One-sided curve velocities always lie in a chart's tangent range. -/
theorem oneSidedVelocities_subset_chart {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    {u : E k} (hu : u ∈ c.source) :
    oneSidedVelocities M (c.toFun u) ⊆ LinearMap.range (chartDifferential c u).toLinearMap := by
  rintro v ⟨γ, ε, hε, hγ0, _, hmaps, hdγ⟩
  exact curve_velocity_mem_range c hr hkn hu (uniqueDiffWithinAt_Ici 0) hdγ hγ0
    (eventually_of_mem (Ico_mem_nhdsGE hε) hmaps)

/-- Inward directions span the entire parameter space: for each vector,
either it or its negative points into the half-space. -/
theorem chart_range_span_oneSided {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r) (hkn : k ≤ n)
    {u : E k} (hu : u ∈ c.source) :
    LinearMap.range (chartDifferential c u).toLinearMap =
      Submodule.span ℝ (oneSidedVelocities M (c.toFun u)) := by
  classical
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    change chartDifferential c u w ∈ Submodule.span ℝ (oneSidedVelocities M (c.toFun u))
    have hcone : w ∈ inwardParameterCone c u ∨ -w ∈ inwardParameterCone c u := by
      by_cases hb : IsBoundaryParameter c u
      · cases k with
        | zero => exact False.elim (Nat.lt_irrefl 0 (c.half_pos hb.1))
        | succ d =>
          change w ∈ (if IsBoundaryParameter c u then halfSpace (d+1) else univ) ∨
            -w ∈ (if IsBoundaryParameter c u then halfSpace (d+1) else univ)
          rw [ite_eq_left hb]
          change 0 ≤ w (Fin.last d) ∨ 0 ≤ -w (Fin.last d)
          exact (le_total 0 (w (Fin.last d))).imp_right neg_nonneg.mpr
      · left
        change w ∈ (if IsBoundaryParameter c u then halfSpace k else univ)
        rw [ite_eq_right hb]
        trivial
    rcases hcone with hw | hw
    · exact Submodule.subset_span (EmbeddedChart.inward_velocity c hr hu hw)
    · have hh := Submodule.neg_mem (Submodule.span ℝ (oneSidedVelocities M (c.toFun u)))
        (Submodule.subset_span (EmbeddedChart.inward_velocity c hr hu hw))
      simp only [map_neg, neg_neg] at hh
      exact hh
  · exact Submodule.span_le.mpr (oneSidedVelocities_subset_chart c hr hkn hu)

/-- At a boundary point the tangent space is the linear span of velocities
with time parameter t ≥ 0. No two-sided inward characterization is asserted. -/
theorem tangentSpace_boundary_velocities :
    Specs.D04.C14.ChartIndependentTangentSpaces.tangentSpace_boundary_velocitiesType := by
  intro r k n M hM x hx
  obtain ⟨_, c, u, _, hu, _, hux⟩ := hx
  rw [← hux, tangentSpace_chart c hM.1 hM.2.1 u hu]
  exact chart_range_span_oneSided c hM.1 hM.2.1 hu


/-- The same kernel formula for any local regular-level description, without
requiring a globally defined level-set presentation of M. -/
theorem tangentSpace_local_regular_level :
    Specs.D04.C14.ChartIndependentTangentSpaces.tangentSpace_local_regular_levelType := by
  intro r k n M hM O g hO hg heq x hx hsurj
  obtain ⟨c, u, hu, hux⟩ := hM.2.2 x hx.1
  let d := EmbeddedChart.restrict c O hO
  have hud : u ∈ d.source := ⟨hu.1, by change c.toFun u ∈ O; rw [hux]; exact hx.2⟩
  have hdux : d.toFun u = x := hux
  have hdg := (hg.contDiffAt (hO.mem_nhds hx.2)).differentiableAt
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hM.1.1))
  have hdg' : HasFDerivAt g (fderiv ℝ g x) (d.toFun u) := by
    rw [hdux]; exact hdg.hasFDerivAt
  have hdcomp := hdg'.comp_hasFDerivWithinAt u
    (EmbeddedChart.hasDifferential d hM.1 hud)
  have hz : ∀ v ∈ d.source, g (d.toFun v) = 0 := by
    intro v hv
    have hm : d.toFun v ∈ M ∩ O := ⟨(d.map_source hv).1, (d.map_source hv).2.2⟩
    rw [heq] at hm
    exact hm.2
  have hzero : (fderiv ℝ g x).comp (chartDifferential d u) = 0 := by
    apply (EmbeddedChart.source_uniqueDiff d u hud).eq hdcomp
    exact (hasFDerivWithinAt_const (0 : E (n-k)) u d.source).congr' hz hud
  have hle : Specs.D04.C14.ChartIndependentTangentSpaces.Model.tangentSpace r k M x ≤
      (fderiv ℝ g x).ker := by
    rw [← hdux, tangentSpace_chart d hM.1 hM.2.1 u hud]
    rintro v ⟨w, rfl⟩
    change (fderiv ℝ g (d.toFun u)) (chartDifferential d u w) = 0
    rw [hdux]
    exact DFunLike.congr_fun hzero w
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hdim := (fderiv ℝ g x).toLinearMap.finrank_range_add_finrank_ker
  rw [RegularLevels.range_finrank_of_surjective _ hsurj] at hdim
  simp only [finrank_euclideanSpace_fin] at hdim
  rw [tangentSpace_finrank hM x hx.1]
  have hkn := hM.2.1
  omega

end D04
