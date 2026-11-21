import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.IntrinsicExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C14.ChartIndependentTangentSpaces
import MathGenome.Internal.MultivariableAnalysis.D04.C13.DifferentialIdentities

noncomputable section
open Set Filter Topology
open scoped BigOperators Classical
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace D04.Intrinsic
open D04
open Specs.D04.C15.IntrinsicExteriorDerivative.Model

abbrev IntrinsicForm := @Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicForm
abbrev chartPullback := @Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback
abbrev IntrinsicContinuous := @Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicContinuous
abbrev IntrinsicC1 := @Specs.D04.C15.IntrinsicExteriorDerivative.Model.IntrinsicC1
abbrev withinExteriorDerivative := @Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative
abbrev HasIntrinsicExteriorDerivative :=
  @Specs.D04.C15.IntrinsicExteriorDerivative.Model.HasIntrinsicExteriorDerivative
abbrev ambientRestriction := @Specs.D04.C15.IntrinsicExteriorDerivative.Model.ambientRestriction
abbrev intrinsicExteriorDerivative := @Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative
abbrev intrinsicWedge := @Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicWedge

variable {k n p q : ℕ} {M : Set (E n)}

@[simp] theorem chartPullback_of_mem (c : EmbeddedChart 2 k n M)
    (ω : IntrinsicForm (k := k) M p) {u : E k} (hu : u ∈ c.source) :
    chartPullback c ω u =
      (ω ⟨c.toFun u, (c.map_source hu).1⟩).compLinearMap (chartTangentMap c u hu) := by
  simp only [chartPullback, Specs.D04.C15.IntrinsicExteriorDerivative.Model.chartPullback,
    dite_eq_left hu]

theorem chartTangentMap_surjective (hM : IsEmbeddedManifold 2 k M)
    (c : EmbeddedChart 2 k n M) {u : E k} (hu : u ∈ c.source) :
    Function.Surjective (chartTangentMap c u hu) := by
  intro v
  have hv : v.val ∈ LinearMap.range (chartDifferential c u).toLinearMap := by
    rw [← tangentSpace_chart c hM.1 hM.2.1 u hu]
    exact v.property
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, Subtype.ext hw⟩

/-- A genuine tangent field is determined by all its chart pullbacks. -/
theorem chartPullback_ext (hM : IsEmbeddedManifold 2 k M)
    (α β : IntrinsicForm (k := k) M p)
    (h : ∀ (c : EmbeddedChart 2 k n M) (u : E k), u ∈ c.source →
      chartPullback c α u = chartPullback c β u) : α = β := by
  funext x
  obtain ⟨c, u, hu, hux⟩ := hM.2.2 x x.property
  have he := h c u hu.1
  rw [chartPullback_of_mem c α hu.1, chartPullback_of_mem c β hu.1] at he
  have hh := AlternatingMap.compLinearMap_injective _ (chartTangentMap_surjective hM c hu.1) he
  have hx : (⟨c.toFun u, (c.map_source hu.1).1⟩ : M) = x := Subtype.ext hux
  rw [hx] at hh
  exact hh

theorem intrinsic_exteriorDerivative_unique :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsic_exteriorDerivative_uniqueType := by
  intro k n p M hM ω η ζ hη hζ
  exact chartPullback_ext hM η ζ (fun c u hu => (hη c u hu).trans (hζ c u hu).symm)

/-- The derivative of an extension is determined by its germ on the half-space.
This uses the actual unique-differentiability theorem for the chart source. -/
theorem withinExteriorDerivative_extension (c : EmbeddedChart 2 k n M)
    {u : E k} (hu : u ∈ c.source) {W : Set (E k)} (hW : IsOpen W) (huW : u ∈ W)
    (α β : FormField k p) (hα : IsCrForm (some 1) W α)
    (he : EqOn α β (c.source ∩ W)) :
    withinExteriorDerivative c.source β u = exteriorDerivative α u := by
  classical
  unfold withinExteriorDerivative Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative
  rw [exteriorDerivative_formula]
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro j _
  have hd := isCrForm_coefficient_differentiableAt W α hα u huW I
  have hd' : HasFDerivWithinAt (fun v => coefficient (standardBasis k) (β v) I)
      (fderiv ℝ (fun v => coefficient (standardBasis k) (α v) I) u) c.source u := by
    apply hd.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq
    · apply eventuallyEq_of_mem
        (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW)))
      intro v hv
      exact congrArg (fun a => coefficient (standardBasis k) a I) (he hv).symm
    · exact congrArg (fun a => coefficient (standardBasis k) a I) (he ⟨hu, huW⟩).symm
  erw [hd'.fderivWithin (c.source_uniqueDiff u hu),
    scalarPartialDerivative_eq_fderiv _ _ hd]
  rfl

theorem withinExteriorDerivative_top (S : Set (E k)) (ω : FormField k k) :
    withinExteriorDerivative S ω = 0 := by
  funext u
  apply covector_eq_zero_above_dimension
  simpa only [finrank_euclideanSpace_fin] using Nat.lt_succ_self k

theorem intrinsic_above_dimension :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsic_above_dimensionType := by
  intro k n p M hM hp ω x
  apply covector_eq_zero_above_dimension
  rw [tangentSpace_finrank hM x x.property]
  exact hp

theorem intrinsic_top_derivative :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsic_top_derivativeType := by
  intro k n M _ ω c u hu
  change chartPullback c (fun _ => 0) u = withinExteriorDerivative c.source (chartPullback c ω) u
  erw [chartPullback_of_mem c (fun _ => 0) hu, withinExteriorDerivative_top]
  exact AlternatingMap.zero_compLinearMap _

/-- C¹ intrinsic forms are continuous, also at genuine boundary points. -/
theorem intrinsicC1_continuous (ω : IntrinsicForm (k := k) M p) (hω : IntrinsicC1 ω) :
    IntrinsicContinuous ω := by
  intro c I
  apply continuousOn_of_locally_continuousOn
  intro u hu
  obtain ⟨W, α, hW, huW, hα, he⟩ := hω c u hu
  refine ⟨W, hW, huW, ?_⟩
  apply (((crOn_iff_contDiffOn 1 W _ hW).mp (hα.2 I)).continuousOn.mono inter_subset_right).congr
  intro v hv
  exact congrArg (fun a => coefficient (standardBasis k) a I) (he hv).symm

/-- Algebraic pullback commutes with the normalized wedge on the actual tangent spaces. -/
theorem chartPullback_wedge (c : EmbeddedChart 2 k n M)
    (α : IntrinsicForm (k := k) M p) (β : IntrinsicForm (k := k) M q)
    {u : E k} (hu : u ∈ c.source) :
    chartPullback c (intrinsicWedge α β) u =
      wedge (chartPullback c α u) (chartPullback c β u) := by
  rw [chartPullback_of_mem c _ hu, chartPullback_of_mem c α hu,
    chartPullback_of_mem c β hu]
  ext v
  simp only [intrinsicWedge, Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicWedge,
    AlternatingMap.compLinearMap_apply, wedge_apply]

theorem isCrForm_mono {a b : ℕ} (r : ℕ) {U V : Set (E a)}
    {α : FormField a b} (hα : IsCrForm (some r) U α) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsCrForm (some r) V α := by
  refine ⟨hV, fun I => ?_⟩
  exact (crOn_iff_contDiffOn r V _ hV).mpr
    (((crOn_iff_contDiffOn r U _ hα.1).mp (hα.2 I)).mono hVU)

theorem isCrForm_wedge {a b d : ℕ} (r : ℕ) (U : Set (E a))
    (α : FormField a b) (β : FormField a d)
    (hα : IsCrForm (some r) U α) (hβ : IsCrForm (some r) U β) :
    IsCrForm (some r) U (fun u => wedge (α u) (β u)) := by
  classical
  refine ⟨hα.1, fun I => ?_⟩
  change CrOn r U (fun u => wedge (α u) (β u)
    (fun j => standardBasis a (indexTuple I j)))
  simp_rw [wedge_apply]
  apply (crOn_iff_contDiffOn r U _ hα.1).mpr
  apply ContDiffOn.mul contDiffOn_const
  apply ContDiffOn.sum
  intro σ _
  apply ContDiffOn.const_smul
  apply ContDiffOn.mul
  · exact (crOn_iff_contDiffOn r U _ hα.1).mp
      (isCrForm_evaluation r U U id α
        (fun i _ => standardBasis a (indexTuple I (σ (Fin.castAdd d i))))
        hα.1 (fun _ hu => hu) ((crOn_iff_contDiffOn r U _ hα.1).mpr contDiffOn_id) hα
        (fun _ => (crOn_iff_contDiffOn r U _ hα.1).mpr contDiffOn_const))
  · exact (crOn_iff_contDiffOn r U _ hα.1).mp
      (isCrForm_evaluation r U U id β
        (fun i _ => standardBasis a (indexTuple I (σ (Fin.natAdd b i))))
        hα.1 (fun _ hu => hu) ((crOn_iff_contDiffOn r U _ hα.1).mpr contDiffOn_id) hβ
        (fun _ => (crOn_iff_contDiffOn r U _ hα.1).mpr contDiffOn_const))

theorem intrinsicC1_wedge (α : IntrinsicForm (k := k) M p)
    (β : IntrinsicForm (k := k) M q) (hα : IntrinsicC1 α) (hβ : IntrinsicC1 β) :
    IntrinsicC1 (intrinsicWedge α β) := by
  intro c u hu
  obtain ⟨U, a, hU, huU, ha, hea⟩ := hα c u hu
  obtain ⟨V, b, hV, huV, hb, heb⟩ := hβ c u hu
  refine ⟨U ∩ V, fun v => wedge (a v) (b v), hU.inter hV, ⟨huU, huV⟩,
    isCrForm_wedge 1 _ a b (isCrForm_mono 1 ha (hU.inter hV) inter_subset_left)
      (isCrForm_mono 1 hb (hU.inter hV) inter_subset_right), ?_⟩
  intro v hv
  change wedge (a v) (b v) = chartPullback c (intrinsicWedge α β) v
  erw [chartPullback_wedge c α β hv.1]
  exact congrArg₂ wedge (hea ⟨hv.1, hv.2.1⟩) (heb ⟨hv.1, hv.2.2⟩)

/-- A coordinate chart version of the intrinsic graded product rule. -/
theorem withinExteriorDerivative_wedge (c : EmbeddedChart 2 k n M)
    (α : IntrinsicForm (k := k) M p) (β : IntrinsicForm (k := k) M q)
    (hα : IntrinsicC1 α) (hβ : IntrinsicC1 β) {u : E k} (hu : u ∈ c.source) :
    withinExteriorDerivative c.source (chartPullback c (intrinsicWedge α β)) u =
      castCovector (by omega : (p+1)+q = p+q+1)
        (wedge (withinExteriorDerivative c.source (chartPullback c α) u) (chartPullback c β u)) +
      (-1 : ℝ)^p • castCovector (by omega : p+(q+1) = p+q+1)
        (wedge (chartPullback c α u) (withinExteriorDerivative c.source (chartPullback c β) u)) := by
  obtain ⟨U, a, hU, huU, ha, hea⟩ := hα c u hu
  obtain ⟨V, b, hV, huV, hb, heb⟩ := hβ c u hu
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have huW : u ∈ W := ⟨huU, huV⟩
  have haW := isCrForm_mono 1 ha hW inter_subset_left
  have hbW := isCrForm_mono 1 hb hW inter_subset_right
  have he : EqOn (fun v => wedge (a v) (b v))
      (chartPullback c (intrinsicWedge α β)) (c.source ∩ W) := by
    intro v hv
    change wedge (a v) (b v) = chartPullback c (intrinsicWedge α β) v
    erw [chartPullback_wedge c α β hv.1]
    exact congrArg₂ wedge (hea ⟨hv.1, hv.2.1⟩) (heb ⟨hv.1, hv.2.2⟩)
  rw [withinExteriorDerivative_extension c hu hW huW _ _ (isCrForm_wedge 1 W a b haW hbW) he,
    withinExteriorDerivative_extension c hu hU huU a _ ha hea,
    withinExteriorDerivative_extension c hu hV huV b _ hb heb,
    exteriorDerivative_wedge W a b haW hbW u huW, hea ⟨hu, huU⟩, heb ⟨hu, huV⟩]

/-- Arbitrary-degree forms on a discrete zero-manifold have zero differential. -/
theorem intrinsic_zero_dimension :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsic_zero_dimensionType := by
  intro n p M _ ω
  refine ⟨?_, ?_, ?_⟩
  · intro c u hu
    refine ⟨univ, fun _ => chartPullback c ω u, isOpen_univ, mem_univ _,
      isCrForm_const 1 univ isOpen_univ _, ?_⟩
    intro v _
    have hvu : v = u := Subsingleton.elim _ _
    subst v
    rfl
  · intro c I
    have hf : (fun u => coefficient (standardBasis 0) (chartPullback c ω u) I) =
        fun _ => coefficient (standardBasis 0) (chartPullback c ω 0) I :=
      funext (fun u => congrArg (fun v => coefficient (standardBasis 0) (chartPullback c ω v) I) (Subsingleton.elim u 0))
    erw [hf]
    exact continuous_const.continuousOn
  · intro c u hu
    change chartPullback c (fun _ => 0) u = withinExteriorDerivative c.source (chartPullback c ω) u
    rw [chartPullback_of_mem c _ hu]
    simp only [withinExteriorDerivative,
      Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative,
      Finset.univ_eq_empty, Finset.sum_empty, AlternatingMap.zero_compLinearMap, Finset.sum_const_zero]

/-- Restricting an ambient covector and then using a chart differentiates only
in tangent directions. The extension may be chosen locally and independently. -/
theorem chartPullback_ambient_extension (c : EmbeddedChart 2 k n M)
    (ω : FormField n p) {u : E k} (hu : u ∈ c.source)
    {W : Set (E k)} {g : E k → E n} (hW : IsOpen W) (huW : u ∈ W)
    (he : EqOn g c.toFun (c.source ∩ W)) (hg : DifferentiableAt ℝ g u) :
    chartPullback c (ambientRestriction (k := k) M ω) u = pullback g ω u := by
  rw [chartPullback_of_mem c _ hu]
  ext v
  change ω (c.toFun u) (fun i => chartDifferential c u (v i)) =
    ω (g u) (fun i => fderiv ℝ g u (v i))
  rw [he ⟨hu, huW⟩, EmbeddedChart.differential_extension c hu hW huW he hg]

/-- A single common open neighborhood on which chart pullbacks of every
ambient form agree with pullback by a genuine C² extension. -/
theorem chart_ambient_local (c : EmbeddedChart 2 k n M) {u : E k}
    (hu : u ∈ c.source) (O : Set (E n)) (hO : IsOpen O) (hxO : c.toFun u ∈ O) :
    ∃ (W : Set (E k)) (g : E k → E n), IsOpen W ∧ u ∈ W ∧
      MapsTo g W O ∧ CrOn 2 W g ∧
      ∀ (s : ℕ) (ω : FormField n s), EqOn (pullback g ω)
        (chartPullback c (ambientRestriction (k := k) M ω)) (c.source ∩ W) := by
  obtain ⟨V, g, hV, huV, he, hg, _⟩ := c.regular u hu
  let W := V ∩ g ⁻¹' O
  have hW : IsOpen W := hg.continuousOn.isOpen_inter_preimage hV hO
  have huW : u ∈ W := ⟨huV, by change g u ∈ O; rw [he ⟨hu, huV⟩]; exact hxO⟩
  have hgW : ContDiffOn ℝ 2 g W := hg.mono inter_subset_left
  refine ⟨W, g, hW, huW, fun _ hv => hv.2,
    (crOn_iff_contDiffOn 2 W g hW).mpr hgW, ?_⟩
  intro s ω v hv
  exact (chartPullback_ambient_extension c ω hv.1 hV hv.2.1 he
    ((hg.contDiffAt (hV.mem_nhds hv.2.1)).differentiableAt (by norm_num))).symm

theorem ambientRestriction_C1 (O : Set (E n)) (hO : IsOpen O) (hMO : M ⊆ O)
    (ω : FormField n p) (hω : IsCrForm (some 1) O ω) :
    IntrinsicC1 (ambientRestriction (k := k) M ω) := by
  intro c u hu
  obtain ⟨W, g, hW, huW, hmap, hg, he⟩ := chart_ambient_local c hu O hO (hMO (c.map_source hu).1)
  exact ⟨W, pullback g ω, hW, huW, pullback_C1 W O g ω hW hmap hg hω, he p ω⟩

theorem ambientRestriction_continuous (O : Set (E n)) (hO : IsOpen O) (hMO : M ⊆ O)
    (ω : FormField n p) (hω : IsCrForm (some 0) O ω) :
    IntrinsicContinuous (ambientRestriction (k := k) M ω) := by
  intro c I
  apply continuousOn_of_locally_continuousOn
  intro u hu
  obtain ⟨W, g, hW, huW, hmap, hg, he⟩ := chart_ambient_local c hu O hO (hMO (c.map_source hu).1)
  have hg1 : CrOn 1 W g := (crOn_iff_contDiffOn 1 W g hW).mpr
    (((crOn_iff_contDiffOn 2 W g hW).mp hg).of_le (by norm_num))
  have hc := (pullback_continuous W O g ω hW hmap hg1 hω).2 I
  refine ⟨W, hW, huW, ?_⟩
  apply (hc.mono inter_subset_right).congr
  intro v hv
  exact congrArg (fun a => coefficient (standardBasis k) a I) (he p ω hv).symm

theorem ambientRestriction_derivative (O : Set (E n)) (hO : IsOpen O) (hMO : M ⊆ O)
    (ω : FormField n p) (hω : IsCrForm (some 1) O ω) :
    HasIntrinsicExteriorDerivative (ambientRestriction (k := k) M ω)
      (ambientRestriction (k := k) M (exteriorDerivative ω)) := by
  intro c u hu
  obtain ⟨W, g, hW, huW, hmap, hg, he⟩ := chart_ambient_local c hu O hO (hMO (c.map_source hu).1)
  change chartPullback c (ambientRestriction M (exteriorDerivative ω)) u =
    withinExteriorDerivative c.source (chartPullback c (ambientRestriction M ω)) u
  erw [withinExteriorDerivative_extension c hu hW huW (pullback g ω) _
    (pullback_C1 W O g ω hW hmap hg hω) (he p ω),
    exteriorDerivative_pullback W O g ω hW hmap hg hω u huW]
  exact (he (p+1) (exteriorDerivative ω) ⟨hu, huW⟩).symm

theorem intrinsic_ambientRestriction :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsic_ambientRestrictionType := by
  intro k n p M _ O ω hMO hω
  exact ⟨ambientRestriction_C1 O hω.1 hMO ω hω,
    ambientRestriction_continuous O hω.1 hMO _ (exteriorDerivative_continuous O ω hω),
    ambientRestriction_derivative O hω.1 hMO ω hω⟩

theorem ambientRestriction_derivative_at (c : EmbeddedChart 2 k n M) {u : E k}
    (hu : u ∈ c.source) (O : Set (E n)) (hO : IsOpen O) (hxO : c.toFun u ∈ O)
    (ω : FormField n p) (hω : IsCrForm (some 1) O ω) :
    chartPullback c (ambientRestriction M (exteriorDerivative ω)) u =
      withinExteriorDerivative c.source (chartPullback c (ambientRestriction M ω)) u := by
  obtain ⟨W, g, hW, huW, hmap, hg, he⟩ := chart_ambient_local c hu O hO hxO
  erw [withinExteriorDerivative_extension c hu hW huW (pullback g ω) _
    (pullback_C1 W O g ω hW hmap hg hω) (he p ω),
    exteriorDerivative_pullback W O g ω hW hmap hg hω u huW]
  exact (he (p+1) (exteriorDerivative ω) ⟨hu, huW⟩).symm

theorem withinExteriorDerivative_congr {S : Set (E k)} {u : E k} (hu : u ∈ S)
    (α β : FormField k p) (he : α =ᶠ[𝓝[S] u] β) :
    withinExteriorDerivative S α u = withinExteriorDerivative S β u := by
  unfold withinExteriorDerivative Specs.D04.C15.IntrinsicExteriorDerivative.Model.withinExteriorDerivative
  apply Finset.sum_congr rfl
  intro I _
  have hc : (fun v => coefficient (standardBasis k) (α v) I) =ᶠ[𝓝[S] u]
      (fun v => coefficient (standardBasis k) (β v) I) := he.mono (fun v hv => congrArg (fun z => coefficient (standardBasis k) z I) hv)
  have hd := hc.fderivWithin_eq_of_mem hu (𝕜 := ℝ)
  apply Finset.sum_congr rfl
  intro j _
  erw [hd]
  rfl

theorem chartPullback_eventuallyEq (c : EmbeddedChart 2 k n M) {u : E k}
    (hu : u ∈ c.source) (α β : IntrinsicForm (k := k) M p)
    (O : Set (E n)) (hO : IsOpen O) (hxO : c.toFun u ∈ O)
    (he : ∀ y : M, y.val ∈ O → α y = β y) :
    chartPullback c α =ᶠ[𝓝[c.source] u] chartPullback c β := by
  have hnear : ∀ᶠ v in 𝓝[c.source] u, c.toFun v ∈ O :=
    (c.continuous_toFun u hu).eventually (hO.mem_nhds hxO)
  filter_upwards [self_mem_nhdsWithin, hnear] with v hv hvO
  rw [chartPullback_of_mem c α hv, chartPullback_of_mem c β hv,
    he ⟨c.toFun v, (c.map_source hv).1⟩ hvO]

/-- Local equality of ambient tangent restrictions implies equality of their
exterior derivatives at the marked point; there is no equality assumed off M. -/
theorem ambient_derivative_locality (hM : IsEmbeddedManifold 2 k M)
    (x : M) (O : Set (E n)) (hO : IsOpen O) (hxO : x.val ∈ O)
    (α β : FormField n p) (hα : IsCrForm (some 1) O α) (hβ : IsCrForm (some 1) O β)
    (he : ∀ y : M, y.val ∈ O → ambientRestriction (k := k) M α y = ambientRestriction (k := k) M β y) :
    ambientRestriction (k := k) M (exteriorDerivative α) x =
      ambientRestriction (k := k) M (exteriorDerivative β) x := by
  obtain ⟨c, u, hu, hux⟩ := hM.2.2 x x.property
  have huO : c.toFun u ∈ O := hux ▸ hxO
  have hd := withinExteriorDerivative_congr hu.1 _ _
    (chartPullback_eventuallyEq c hu.1 (ambientRestriction M α) (ambientRestriction M β) O hO huO he)
  rw [← ambientRestriction_derivative_at c hu.1 O hO huO α hα,
    ← ambientRestriction_derivative_at c hu.1 O hO huO β hβ] at hd
  rw [chartPullback_of_mem c _ hu.1, chartPullback_of_mem c _ hu.1] at hd
  have hh := AlternatingMap.compLinearMap_injective _ (chartTangentMap_surjective hM c hu.1) hd
  have hx : (⟨c.toFun u, (c.map_source hu.1).1⟩ : M) = x := Subtype.ext hux
  rw [hx] at hh
  exact hh

theorem cast_compLinearMap {V W : Type} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {a b : ℕ} (h : a = b)
    (α : Covector V a) (A : W →ₗ[ℝ] V) :
    (castCovector h α).compLinearMap A = castCovector h (α.compLinearMap A) := by
  subst b
  rfl

theorem wedge_compLinearMap {V W : Type} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (α : Covector V p) (β : Covector V q)
    (A : W →ₗ[ℝ] V) :
    (wedge α β).compLinearMap A = wedge (α.compLinearMap A) (β.compLinearMap A) := by
  ext v
  simp only [AlternatingMap.compLinearMap_apply, wedge_apply]

theorem smul_compLinearMap {V W : Type} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {a : ℕ} (r : ℝ) (α : Covector V a)
    (A : W →ₗ[ℝ] V) : (r • α).compLinearMap A = r • α.compLinearMap A := by
  rfl

theorem chartPullback_gradedProduct (c : EmbeddedChart 2 k n M)
    (α : IntrinsicForm (k := k) M p) (β : IntrinsicForm (k := k) M q)
    (dα : IntrinsicForm (k := k) M (p+1)) (dβ : IntrinsicForm (k := k) M (q+1))
    {u : E k} (hu : u ∈ c.source) :
    chartPullback c (gradedDerivativeProduct α β dα dβ) u =
      castCovector (by omega : (p+1)+q = p+q+1)
        (wedge (chartPullback c dα u) (chartPullback c β u)) +
      (-1 : ℝ)^p • castCovector (by omega : p+(q+1) = p+q+1)
        (wedge (chartPullback c α u) (chartPullback c dβ u)) := by
  simp only [chartPullback_of_mem c _ hu, gradedDerivativeProduct,
    AlternatingMap.add_compLinearMap, smul_compLinearMap,
    cast_compLinearMap, wedge_compLinearMap]

theorem intrinsic_product_rule :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsic_product_ruleType := by
  intro k n p q M _ α β dα dβ hα hβ hdα hdβ
  refine ⟨intrinsicC1_wedge α β hα hβ, ?_⟩
  intro c u hu
  change chartPullback c (gradedDerivativeProduct α β dα dβ) u =
    withinExteriorDerivative c.source (chartPullback c (intrinsicWedge α β)) u
  rw [chartPullback_gradedProduct c α β dα dβ hu,
    withinExteriorDerivative_wedge c α β hα hβ hu]
  have ha : chartPullback c dα u = withinExteriorDerivative c.source (chartPullback c α) u := hdα c u hu
  have hb : chartPullback c dβ u = withinExteriorDerivative c.source (chartPullback c β) u := hdβ c u hu
  rw [ha, hb]

/-- Differentiating a local ambient inverse on the full, uniquely differentiable
source gives a left inverse even at a flat boundary point. -/
theorem chart_inverse_differential (hM : IsEmbeddedManifold 2 k M)
    (c : EmbeddedChart 2 k n M) {u : E k} (hu : u ∈ c.source)
    (O : Set (E n)) (J : E n → E k) (hO : IsOpen O) (hxO : c.toFun u ∈ O)
    (hJ : ContDiffOn ℝ 2 J O) (he : EqOn J c.invFun ((M ∩ c.ambient) ∩ O)) :
    (fderiv ℝ J (c.toFun u)).comp (chartDifferential c u) = ContinuousLinearMap.id ℝ (E k) := by
  have hdJ := (hJ.contDiffAt (hO.mem_nhds hxO)).differentiableAt (by norm_num)
  have hcomp := hdJ.hasFDerivAt.comp_hasFDerivWithinAt u (c.hasDifferential hM.1 hu)
  have hval : J (c.toFun u) = u := by rw [he ⟨c.map_source hu, hxO⟩, c.left_inv _ hu]
  have heq : (fun v => J (c.toFun v)) =ᶠ[𝓝[c.source] u] id := by
    have hev := (c.continuous_toFun u hu).eventually (hO.mem_nhds hxO)
    filter_upwards [self_mem_nhdsWithin, hev] with v hv hvO
    exact (he ⟨c.map_source hv, hvO⟩).trans (c.left_inv _ hv)
  have hd : HasFDerivWithinAt id
      ((fderiv ℝ J (c.toFun u)).comp (chartDifferential c u)) c.source u :=
    hcomp.congr_of_eventuallyEq heq.symm hval.symm
  exact (c.source_uniqueDiff u hu).eq hd (hasFDerivWithinAt_id u c.source)

/-- The coordinate form pulled to ambient space by a chart inverse returns the
same coordinate covector when restricted to the tangent space. -/
theorem chartPullback_inverse (c : EmbeddedChart 2 k n M) {u : E k}
    (hu : u ∈ c.source) (J : E n → E k) (α : FormField k p)
    (hJu : J (c.toFun u) = u)
    (hd : (fderiv ℝ J (c.toFun u)).comp (chartDifferential c u) = ContinuousLinearMap.id ℝ (E k)) :
    chartPullback c (ambientRestriction M (pullback J α)) u = α u := by
  rw [chartPullback_of_mem c _ hu]
  ext v
  change α (J (c.toFun u)) (fun i => fderiv ℝ J (c.toFun u) (chartDifferential c u (v i))) = α u v
  rw [hJu]
  have ht : (fun i => fderiv ℝ J (c.toFun u) (chartDifferential c u (v i))) = v := by
    funext i
    exact DFunLike.congr_fun hd (v i)
  rw [ht]

/-- Every intrinsic C¹ form has local ambient C¹ representatives. This is a
consequence of chart regularity, rather than an added hypothesis on the form. -/
theorem intrinsic_local_ambient (hM : IsEmbeddedManifold 2 k M)
    (ω : IntrinsicForm (k := k) M p) (hω : IntrinsicC1 ω) (x : M) :
    ∃ (O : Set (E n)) (Ω : FormField n p), IsOpen O ∧ x.val ∈ O ∧
      IsCrForm (some 1) O Ω ∧ ∀ y : M, y.val ∈ O → ambientRestriction M Ω y = ω y := by
  obtain ⟨c, u, hu, hux⟩ := hM.2.2 x x.property
  obtain ⟨W, α, hW, huW, hα, heα⟩ := hω c u hu.1
  obtain ⟨V, J, hV, hxV, hJ, heJ⟩ := chart_inverse_extension c hM.1 hM.2.1 u hu.1
  have hJu : J (c.toFun u) = u := by rw [heJ ⟨c.map_source hu.1, hxV⟩, c.left_inv _ hu.1]
  let O := (V ∩ J ⁻¹' W) ∩ c.ambient
  have hO : IsOpen O := (hJ.continuousOn.isOpen_inter_preimage hV hW).inter c.ambient_open
  have hxO : x.val ∈ O := by
    rw [← hux]
    exact ⟨⟨hxV, by change J (c.toFun u) ∈ W; rwa [hJu]⟩, (c.map_source hu.1).2⟩
  have hJO : CrOn 2 O J := (crOn_iff_contDiffOn 2 O J hO).mpr
    (hJ.mono (inter_subset_left.trans inter_subset_left))
  refine ⟨O, pullback J α, hO, hxO,
    pullback_C1 O W J α hO (fun y hy => hy.1.2) hJO hα, ?_⟩
  intro y hy
  have hyc : y.val ∈ M ∩ c.ambient := ⟨y.property, hy.2⟩
  let v := c.invFun y
  have hv : v ∈ c.source := c.map_target hyc
  have hcv : c.toFun v = y.val := c.right_inv _ hyc
  have hvV : c.toFun v ∈ V := hcv ▸ hy.1.1
  have hJv : J (c.toFun v) = v := by rw [heJ ⟨c.map_source hv, hvV⟩, c.left_inv _ hv]
  have hvW : v ∈ W := by
    have hh : J y.val = v := heJ ⟨hyc, hy.1.1⟩
    exact hh ▸ hy.1.2
  have hd := chart_inverse_differential hM c hv V J hV hvV hJ heJ
  have he : chartPullback c (ambientRestriction M (pullback J α)) v = chartPullback c ω v :=
    (chartPullback_inverse c hv J α hJv hd).trans (heα ⟨hv, hvW⟩)
  rw [chartPullback_of_mem c _ hv, chartPullback_of_mem c _ hv] at he
  have hh := AlternatingMap.compLinearMap_injective _ (chartTangentMap_surjective hM c hv) he
  have hxy : (⟨c.toFun v, (c.map_source hv).1⟩ : M) = y := Subtype.ext hcv
  rw [hxy] at hh
  exact hh

/-- Data obtained from local C¹ extension, used only to construct the derivative. -/
structure LocalAmbientForm (ω : IntrinsicForm (k := k) M p) (x : M) where
  domain : Set (E n)
  form : FormField n p
  isOpen : IsOpen domain
  mem : x.val ∈ domain
  regular : IsCrForm (some 1) domain form
  agrees : ∀ y : M, y.val ∈ domain → ambientRestriction M form y = ω y

def localAmbientForm (hM : IsEmbeddedManifold 2 k M)
    (ω : IntrinsicForm (k := k) M p) (hω : IntrinsicC1 ω) (x : M) : LocalAmbientForm ω x :=
  Classical.choice (by
    obtain ⟨O, Ω, hO, hxO, hΩ, he⟩ := intrinsic_local_ambient hM ω hω x
    exact ⟨⟨O, Ω, hO, hxO, hΩ, he⟩⟩)

def localDerivative (hM : IsEmbeddedManifold 2 k M)
    (ω : IntrinsicForm (k := k) M p) (hω : IntrinsicC1 ω) : IntrinsicForm (k := k) M (p+1) :=
  fun x => ambientRestriction M (exteriorDerivative (localAmbientForm hM ω hω x).form) x

/-- All locally chosen representatives give the same derivative, throughout
any neighborhood on which that representative describes the original form. -/
theorem localDerivative_eq (hM : IsEmbeddedManifold 2 k M)
    (ω : IntrinsicForm (k := k) M p) (hω : IntrinsicC1 ω) (x : M)
    (a : LocalAmbientForm ω x) (y : M) (hy : y.val ∈ a.domain) :
    localDerivative hM ω hω y = ambientRestriction M (exteriorDerivative a.form) y := by
  let b := localAmbientForm hM ω hω y
  exact ambient_derivative_locality hM y (b.domain ∩ a.domain) (b.isOpen.inter a.isOpen)
    ⟨b.mem, hy⟩ b.form a.form
    (isCrForm_mono 1 b.regular (b.isOpen.inter a.isOpen) inter_subset_left)
    (isCrForm_mono 1 a.regular (b.isOpen.inter a.isOpen) inter_subset_right)
    (fun z hz => (b.agrees z hz.1).trans (a.agrees z hz.2).symm)

theorem localDerivative_hasDerivative (hM : IsEmbeddedManifold 2 k M)
    (ω : IntrinsicForm (k := k) M p) (hω : IntrinsicC1 ω) :
    HasIntrinsicExteriorDerivative ω (localDerivative hM ω hω) := by
  intro c u hu
  let x : M := ⟨c.toFun u, (c.map_source hu).1⟩
  let a := localAmbientForm hM ω hω x
  have heω := chartPullback_eventuallyEq c hu (ambientRestriction M a.form) ω a.domain
    a.isOpen a.mem a.agrees
  have hed := chartPullback_eventuallyEq c hu (localDerivative hM ω hω)
    (ambientRestriction M (exteriorDerivative a.form)) a.domain a.isOpen a.mem
    (localDerivative_eq hM ω hω x a)
  change chartPullback c (localDerivative hM ω hω) u = withinExteriorDerivative c.source (chartPullback c ω) u
  rw [hed.self_of_nhdsWithin hu,
    ambientRestriction_derivative_at c hu a.domain a.isOpen a.mem a.form a.regular,
    withinExteriorDerivative_congr hu _ _ heω]

/-- Continuity is local in chart coefficients. Near each point the constructed
field is the restriction of the continuous derivative of a C¹ ambient form. -/
theorem localDerivative_continuous (hM : IsEmbeddedManifold 2 k M)
    (ω : IntrinsicForm (k := k) M p) (hω : IntrinsicC1 ω) :
    IntrinsicContinuous (localDerivative hM ω hω) := by
  intro c I u hu
  let x : M := ⟨c.toFun u, (c.map_source hu).1⟩
  let a := localAmbientForm hM ω hω x
  obtain ⟨W, g, hW, huW, hmap, hg, he⟩ := chart_ambient_local c hu a.domain a.isOpen a.mem
  have hg1 : CrOn 1 W g := (crOn_iff_contDiffOn 1 W g hW).mpr
    (((crOn_iff_contDiffOn 2 W g hW).mp hg).of_le (by norm_num))
  have hc := (pullback_continuous W a.domain g (exteriorDerivative a.form) hW hmap hg1
    (exteriorDerivative_continuous a.domain a.form a.regular)).2 I
  have hca := (hc.continuousAt (hW.mem_nhds huW)).continuousWithinAt (s := c.source)
  have hed := chartPullback_eventuallyEq c hu (localDerivative hM ω hω)
    (ambientRestriction M (exteriorDerivative a.form)) a.domain a.isOpen a.mem
    (localDerivative_eq hM ω hω x a)
  have he' : pullback g (exteriorDerivative a.form) =ᶠ[𝓝[c.source] u]
      chartPullback c (ambientRestriction M (exteriorDerivative a.form)) :=
    eventuallyEq_of_mem (inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW))) (he (p+1) _)
  have ht := hed.trans he'.symm
  apply hca.congr_of_eventuallyEq
  · exact ht.mono (fun v hv => congrArg (fun z => coefficient (standardBasis k) z I) hv)
  · exact congrArg (fun z => coefficient (standardBasis k) z I) (ht.self_of_nhdsWithin hu)

theorem intrinsic_exteriorDerivative_exists_unique :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsic_exteriorDerivative_exists_uniqueType := by
  intro k n p M hM ω hω
  refine ⟨localDerivative hM ω hω,
    ⟨localDerivative_continuous hM ω hω, localDerivative_hasDerivative hM ω hω⟩, ?_⟩
  intro η hη
  exact intrinsic_exteriorDerivative_unique hM ω η _ hη.2 (localDerivative_hasDerivative hM ω hω)

theorem intrinsicExteriorDerivative_spec :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsicExteriorDerivative_specType := by
  intro k n p M hM ω hω
  have hex : ∃ η : IntrinsicForm (k := k) M (p+1),
      IntrinsicContinuous η ∧ HasIntrinsicExteriorDerivative ω η :=
    (intrinsic_exteriorDerivative_exists_unique hM ω hω).exists
  change IntrinsicContinuous (intrinsicExteriorDerivative ω) ∧
    HasIntrinsicExteriorDerivative ω (intrinsicExteriorDerivative ω)
  simp only [intrinsicExteriorDerivative,
    Specs.D04.C15.IntrinsicExteriorDerivative.Model.intrinsicExteriorDerivative, dite_eq_left hex]
  exact hex.choose_spec

theorem intrinsicExteriorDerivative_ambient :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsicExteriorDerivative_ambientType := by
  intro k n p M hM O ω hMO hω
  obtain ⟨hc, _, hd⟩ := intrinsic_ambientRestriction hM O ω hMO hω
  exact intrinsic_exteriorDerivative_unique hM _ _ _
    (intrinsicExteriorDerivative_spec hM _ hc).2 hd

theorem intrinsicExteriorDerivative_wedge :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsicExteriorDerivative_wedgeType := by
  intro k n p q M hM α β hα hβ
  have ha := intrinsicExteriorDerivative_spec hM α hα
  have hb := intrinsicExteriorDerivative_spec hM β hβ
  have hp := intrinsic_product_rule hM α β _ _ hα hβ ha.2 hb.2
  exact intrinsic_exteriorDerivative_unique hM _ _ _
    (intrinsicExteriorDerivative_spec hM _ hp.1).2 hp.2

theorem intrinsicExteriorDerivative_high_degree :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsicExteriorDerivative_high_degreeType := by
  intro k n p M hM hp ω x
  exact intrinsic_above_dimension hM (hp.trans_lt (Nat.lt_succ_self p))
    (intrinsicExteriorDerivative ω) x

theorem intrinsicExteriorDerivative_chart :
    Specs.D04.C15.IntrinsicExteriorDerivative.intrinsicExteriorDerivative_chartType := by
  intro k n p M hM ω hω c u hu W α hW huW hα he
  exact ((intrinsicExteriorDerivative_spec hM ω hω).2 c u hu).trans
    (withinExteriorDerivative_extension c hu hW huW α _ hα he)

end D04.Intrinsic
