import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.RegularPerturbation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.CkDependence
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace D13Unified.Ch06.RegularPerturbation
open C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A compact time fiber in an open set has one common parameter neighborhood. -/
lemma compact_fiber {V : Set (ℝ × ℝ)} (hV : IsOpen V) {a b : ℝ}
    (h0 : ∀ t ∈ Icc a b, (t,0) ∈ V) :
    ∃ r > (0 : ℝ), Icc a b ×ˢ Ioo (-r) r ⊆ V := by
  have h : V ∈ (𝓝ˢ (Icc a b)) ×ˢ 𝓝 (0 : ℝ) :=
    isCompact_Icc.mem_nhdsSet_prod_of_forall (fun t ht => by
      rw [← nhds_prod_eq]; exact hV.mem_nhds (h0 t ht))
  obtain ⟨U,hU,W,hW,hUW⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨r,hr,fun q hq => hUW ⟨subset_of_mem_nhdsSet hU hq.1,hrW ?_⟩⟩
  simpa [Real.dist_eq, abs_lt] using hq.2

/-- The derivative in the scalar parameter, assembled from the joint derivative. -/
def scalarPartial (g : ℝ × ℝ → E) (q : ℝ × ℝ) : E :=
  fderiv ℝ g q (0,1)

omit [FiniteDimensional ℝ E] in
lemma hasDerivAt_scalarPartial {g : ℝ × ℝ → E} {q : ℝ × ℝ}
    (hg : DifferentiableAt ℝ g q) :
    HasDerivAt (fun ε => g (q.1,ε)) (scalarPartial g q) q.2 := by
  simpa only [scalarPartial,Function.comp_def,id_eq] using
    hg.hasFDerivAt.comp_hasDerivAt q.2
      ((hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2))

omit [FiniteDimensional ℝ E] in
lemma contDiffOn_scalarPartial {g : ℝ × ℝ → E} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {k : ℕ∞ω} (hg : ContDiffOn ℝ (k+1) g V) :
    ContDiffOn ℝ k (scalarPartial g) V :=
  (hg.fderiv_of_isOpen hV le_rfl).clm_apply contDiffOn_const

/-- A joint C¹ map has a first-order Taylor estimate uniform over a compact
fiber. The estimate includes ε=0 and both signs of ε. -/
lemma uniform_first_order {g : ℝ × ℝ → E} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (hg : ContDiffOn ℝ 1 g V) {a b : ℝ}
    (h0 : ∀ t ∈ Icc a b, (t,0) ∈ V) :
    ∀ η > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ε, |ε| < δ → ∀ t ∈ Icc a b,
      ‖g (t,ε) - g (t,0) - ε • scalarPartial g (t,0)‖ ≤ η * |ε| := by
  obtain ⟨r,hr,hrV⟩ := compact_fiber hV h0
  have hdc : ContinuousOn (scalarPartial g) V :=
    (contDiffOn_scalarPartial hV (k := 0) hg).continuousOn
  intro η hη
  have hc : ContinuousOn (fun q : ℝ × ℝ => scalarPartial g (q.2,q.1))
      (Ioo (-r) r ×ˢ Icc a b) :=
    hdc.comp (continuousOn_snd.prodMk continuousOn_fst)
      (fun q hq => hrV ⟨hq.2,hq.1⟩)
  obtain ⟨W,hW,hsmall⟩ := isCompact_Icc.mem_uniformity_of_prod (f := fun ε t => scalarPartial g (t,ε)) hc
    (show (0 : ℝ) ∈ Ioo (-r) r from ⟨by linarith,hr⟩) (Metric.dist_mem_uniformity hη)
  rw [nhdsWithin_eq_nhds.mpr (Ioo_mem_nhds (by linarith) hr)] at hW
  obtain ⟨d,hd,hdW⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨min r d,lt_min hr hd,fun ε hε t ht => ?_⟩
  have hεr : |ε| < r := hε.trans_le (min_le_left _ _)
  have hεd : |ε| < d := hε.trans_le (min_le_right _ _)
  let S : Set ℝ := uIcc 0 ε
  have hS (v : ℝ) (hv : v ∈ S) : |v| ≤ |ε| := by
    have := norm_sub_le_of_mem_segment (show v ∈ segment ℝ 0 ε from by simpa [S,segment_eq_uIcc] using hv)
    simpa using this
  have hder (v : ℝ) (hv : v ∈ S) :
      HasDerivWithinAt (fun v => g (t,v) - g (t,0) - v • scalarPartial g (t,0))
        (scalarPartial g (t,v) - scalarPartial g (t,0)) S v := by
    have hvV : (t,v) ∈ V := hrV ⟨ht,abs_lt.mp ((hS v hv).trans_lt hεr)⟩
    have hdg := hasDerivAt_scalarPartial (hg.differentiableOn one_ne_zero _ hvV |>.differentiableAt (hV.mem_nhds hvV))
    simpa only [one_smul,id_eq] using
      ((hdg.sub_const (g (t,0))).fun_sub ((hasDerivAt_id v).smul_const (scalarPartial g (t,0)))).hasDerivWithinAt (s := S)
  have hbnd (v : ℝ) (hv : v ∈ S) :
      ‖scalarPartial g (t,v) - scalarPartial g (t,0)‖ ≤ η := by
    have hvW : v ∈ W := hdW (by simpa [Real.dist_eq] using (hS v hv).trans_lt hεd)
    exact (show ‖scalarPartial g (t,v) - scalarPartial g (t,0)‖ < η from
      by simpa only [Set.mem_ofPred_eq,dist_eq_norm] using hsmall v hvW t ht).le
  have hh := (convex_uIcc (0 : ℝ) ε).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbnd (left_mem_uIcc) (right_mem_uIcc)
  simpa only [zero_smul,sub_zero,sub_self,Real.norm_eq_abs] using hh

/-- Two applications of the mean value estimate give a uniform quadratic
bound. A sharp factor one-half is unnecessary for the stated O(ε²) claim. -/
lemma uniform_second_order {g : ℝ × ℝ → E} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (hg : ContDiffOn ℝ 2 g V) {a b : ℝ}
    (h0 : ∀ t ∈ Icc a b, (t,0) ∈ V) :
    ∃ C ≥ (0 : ℝ), ∃ δ > (0 : ℝ), ∀ ε, |ε| < δ → ∀ t ∈ Icc a b,
      ‖g (t,ε) - g (t,0) - ε • scalarPartial g (t,0)‖ ≤ C * ε^2 := by
  obtain ⟨r,hr,hrV⟩ := compact_fiber hV h0
  have hp : ContDiffOn ℝ 1 (scalarPartial g) V := contDiffOn_scalarPartial hV hg
  have hpp : ContinuousOn (scalarPartial (scalarPartial g)) V :=
    (contDiffOn_scalarPartial hV (k := 0) hp).continuousOn
  have hKV : Icc a b ×ˢ Icc (-r/2) (r/2) ⊆ V := by
    intro q hq
    apply hrV ⟨hq.1,?_⟩
    constructor <;> linarith [hq.2.1,hq.2.2]
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hpp.mono hKV)
  refine ⟨max M 0,le_max_right _ _,r/2,by positivity,fun ε hε t ht => ?_⟩
  let S : Set ℝ := uIcc 0 ε
  have hS (v : ℝ) (hv : v ∈ S) : |v| ≤ |ε| := by
    have := norm_sub_le_of_mem_segment (show v ∈ segment ℝ 0 ε from by
      simpa [S,segment_eq_uIcc] using hv)
    simpa using this
  have hvK (v : ℝ) (hv : v ∈ S) : (t,v) ∈ Icc a b ×ˢ Icc (-r/2) (r/2) :=
    ⟨ht,by have h := abs_le.mp ((hS v hv).trans hε.le); constructor <;> linarith [h.1,h.2]⟩
  have hpd (v : ℝ) (hv : v ∈ S) := hasDerivAt_scalarPartial
    (hp.differentiableOn one_ne_zero _ (hKV (hvK v hv)) |>.differentiableAt (hV.mem_nhds (hKV (hvK v hv))))
  have hgd (v : ℝ) (hv : v ∈ S) := hasDerivAt_scalarPartial
    ((hg.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).differentiableOn one_ne_zero _ (hKV (hvK v hv)) |>.differentiableAt (hV.mem_nhds (hKV (hvK v hv))))
  have hbnd (v : ℝ) (hv : v ∈ S) :
      ‖scalarPartial g (t,v) - scalarPartial g (t,0)‖ ≤ max M 0 * |ε| := by
    have h := (convex_uIcc (0 : ℝ) ε).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v hv => show HasDerivWithinAt (fun e => scalarPartial g (t,e)) _ S v from (hpd v hv).hasDerivWithinAt)
      (fun v hv => (hM (t,v) (hvK v hv)).trans (le_max_left M 0))
      left_mem_uIcc hv
    have hh : ‖scalarPartial g (t,v) - scalarPartial g (t,0)‖ ≤ max M 0 * |v| := by
      simpa using h
    exact hh.trans (mul_le_mul_of_nonneg_left (hS v hv) (le_max_right _ _))
  have h := (convex_uIcc (0 : ℝ) ε).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun v => g (t,v) - g (t,0) - v • scalarPartial g (t,0))
    (f' := fun v => scalarPartial g (t,v) - scalarPartial g (t,0))
    (fun v hv => by
      simpa only [one_smul,id_eq] using
        (((hgd v hv).sub_const (g (t,0))).fun_sub
          ((hasDerivAt_id v).smul_const (scalarPartial g (t,0)))).hasDerivWithinAt (s := S))
    hbnd left_mem_uIcc right_mem_uIcc
  simp only [zero_smul,sub_zero,sub_self,Real.norm_eq_abs] at h
  convert h using 1
  rw [mul_assoc,← sq_abs,pow_two]

/-- Local uniqueness also holds at the included endpoints of a compact
reference interval. The two half-interval uniqueness theorems retain the
one-sided derivatives; no differentiability outside [a,b] is used. -/
lemma compact_local_unique (G : ODE E) (hG : G.LocallyLipschitzInState)
    {a b t : ℝ} {x y : ℝ → E} {I : OpenTimeInterval}
    (hx : compactSolutionOnValue G a b x) (hy : classicalSolutionOnValue G I y)
    (ht : t ∈ Icc a b) (htI : t ∈ I.carrier) (heq : x t = y t) :
    ∀ᶠ u in 𝓝[Icc a b] t, x u = y u := by
  obtain ⟨A,B,L,hA,hB,hL,_,hLip⟩ := hG t (x t) (hx.2.2.1 t ht)
  have hgood : ∀ᶠ u in 𝓝[Icc a b] t,
      u ∈ I.carrier ∧ u ∈ ball t A ∧ x u ∈ ball (x t) B ∧ y u ∈ ball (x t) B := by
    have hyc := hy.1.continuousOn.continuousAt (I.isOpen.mem_nhds htI)
    filter_upwards [nhdsWithin_le_nhds (I.isOpen.mem_nhds htI),
      nhdsWithin_le_nhds (ball_mem_nhds t hA),
      (hx.2.1 t ht).eventually (ball_mem_nhds (x t) hB),
      nhdsWithin_le_nhds (hyc.eventually (show ball (x t) B ∈ 𝓝 (y t) from by rw [heq]; exact ball_mem_nhds (y t) hB))]
      with u hu htime hxu hyu
    exact ⟨hu,htime,hxu,hyu⟩
  obtain ⟨r,hr,hnear⟩ := Metric.mem_nhdsWithin_iff.mp hgood
  let c := max a (t-r/2)
  let d := min b (t+r/2)
  have hct : c ≤ t := max_le ht.1 (by linarith)
  have htd : t ≤ d := le_min ht.2 (by linarith)
  have hcdJ : Icc c d ⊆ Icc a b := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hcd (u : ℝ) (hu : u ∈ Icc c d) :
      u ∈ I.carrier ∧ u ∈ ball t A ∧ x u ∈ ball (x t) B ∧ y u ∈ ball (x t) B := by
    apply hnear
    refine ⟨?_,hcdJ hu⟩
    rw [mem_ball,Real.dist_eq,abs_lt]
    have hc := le_max_right a (t-r/2)
    have hd := min_le_right b (t+r/2)
    constructor <;> linarith [hu.1,hu.2]
  have hright : EqOn x y (Icc t d) := by
    have hsub : Icc t d ⊆ Icc c d := Icc_subset_Icc hct le_rfl
    apply ODE_solution_unique_of_mem_Icc_right (v := G.eval)
      (s := fun _ => ball (x t) B) (K := ⟨L,hL⟩)
      (fun u hu => Ch03.ControlledPicard.state_lipschitz hL hLip
        (hcd u (hsub (Ico_subset_Icc_self hu))).2.1)
      (hx.2.1.mono (hsub.trans hcdJ)) ?_
      (fun u hu => (hcd u (hsub (Ico_subset_Icc_self hu))).2.2.1)
      (hy.1.continuousOn.mono (fun u hu => (hcd u (hsub hu)).1)) ?_
      (fun u hu => (hcd u (hsub (Ico_subset_Icc_self hu))).2.2.2) heq
    · intro u hu
      exact (hx.2.2.2 u (hcdJ (hsub (Ico_subset_Icc_self hu)))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1.trans hu.1,hu.2.trans_le (min_le_left _ _)⟩)
    · intro u hu
      exact (hy.2.2 u (hcd u (hsub (Ico_subset_Icc_self hu))).1).hasDerivWithinAt
  have hleft : EqOn x y (Icc c t) := by
    have hsub : Icc c t ⊆ Icc c d := Icc_subset_Icc le_rfl htd
    apply ODE_solution_unique_of_mem_Icc_left (v := G.eval)
      (s := fun _ => ball (x t) B) (K := ⟨L,hL⟩)
      (fun u hu => Ch03.ControlledPicard.state_lipschitz hL hLip
        (hcd u (hsub (Ioc_subset_Icc_self hu))).2.1)
      (hx.2.1.mono (hsub.trans hcdJ)) ?_
      (fun u hu => (hcd u (hsub (Ioc_subset_Icc_self hu))).2.2.1)
      (hy.1.continuousOn.mono (fun u hu => (hcd u (hsub hu)).1)) ?_
      (fun u hu => (hcd u (hsub (Ioc_subset_Icc_self hu))).2.2.2) heq
    · intro u hu
      exact (hx.2.2.2 u (hcdJ (hsub (Ioc_subset_Icc_self hu)))).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨(le_max_left _ _).trans_lt hu.1,hu.2.trans ht.2⟩)
    · intro u hu
      exact (hy.2.2 u (hcd u (hsub (Ioc_subset_Icc_self hu))).1).hasDerivWithinAt
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds t (show 0 < r/2 by positivity))] with u hu hdist
  have hu' := abs_lt.mp (show |u-t| < r/2 from by simpa [Real.dist_eq] using hdist)
  rcases le_total u t with hut | htu
  · exact hleft ⟨max_le hu.1 (by linarith),hut⟩
  · exact hright ⟨htu,le_min hu.2 (by linarith)⟩

/-- Every compact reference solution is the restriction of the canonical
maximal one. Compact confinement supplies existence through both endpoints. -/
lemma compact_reference (G : ODE E) (hG : G.LocallyLipschitzInState)
    {a b s : ℝ} {x : ℝ → E} (hs : s ∈ Icc a b)
    (hx : compactSolutionOnValue G a b x) :
    Icc a b ⊆ (maximalIntervalValue G s (x s)).carrier ∧
      EqOn (solutionCurveValue G s (x s)) x (Icc a b) := by
  obtain ⟨hy,hsI,hys,hmax,_⟩ := ODE.canonical_solution G hG s (x s) (hx.2.2.1 s hs)
  let I := maximalIntervalValue G s (x s)
  let y := solutionCurveValue G s (x s)
  let S : Set ℝ := Icc a b ∩ I.carrier
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp
    (ordConnected_Icc.inter I.ordConnected).isPreconnected
  have hcl : IsClosed {t : S | x t = y t} :=
    isClosed_eq (hx.2.1.mono inter_subset_left).domRestrict
      (hy.1.continuousOn.mono inter_subset_right).domRestrict
  have hop : IsOpen {t : S | x t = y t} := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have h := compact_local_unique G hG hx hy t.2.1 t.2.2 ht
    exact (tendsto_nhdsWithin_iff.mpr ⟨continuous_subtype_val.tendsto t,
      Eventually.of_forall (fun u : S => u.property.1)⟩).eventually h
  have hall := (show IsClopen {t : S | x t = y t} from ⟨hcl,hop⟩).eq_univ
    ⟨⟨s,hs,hsI⟩,hys.symm⟩
  have heq : EqOn y x S := by
    intro t ht
    exact (show x t = y t from (show (⟨t,ht⟩ : S) ∈ {t : S | x t = y t} by
      rw [hall]; trivial)).symm
  let K := (fun t => (t,x t)) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    (continuousOn_id.prodMk hx.2.1)
  have hKU : K ⊆ G.domain := by
    rintro _ ⟨t,ht,rfl⟩; exact hx.2.2.1 t ht
  have hclosed : IsClosed (Icc a b ∩ I.carrier) :=
    Ch05.CommonInterval.closed_overlap_of_compact_confinement G hG
      (⟨I,y,hy⟩ : Solution G) hmax a b K hK hKU (fun t ht => by
        refine ⟨t,ht.1,?_⟩
        exact Prod.ext rfl (heq ht).symm)
  have hfull := Ch05.CommonInterval.interval_subset_of_closed_overlap I hs hsI hclosed
  exact ⟨hfull,fun t ht => heq ⟨ht,hfull ht⟩⟩

lemma reference_data (F : ParameterODE E ℝ) (hF : ContDiffOn ℝ 1 (field F) F.domain)
    {ξ : ℝ → E} {a b s : ℝ} {x₀ : ℝ → E} (hs : s ∈ Icc a b)
    (hx : compactSolutionOnValue (atParameterValue F 0) a b x₀) (hξ : ξ 0 = x₀ s) :
    (∀ t ∈ Icc a b, (t,((s,ξ 0),0)) ∈ parameterSolutionDomainValue F) ∧
      EqOn (trajectory F s ξ 0) x₀ (Icc a b) := by
  have hLip := F.locallyLipschitzInState_of_contDiffOn hF
  have hG := hLip.atParameter F 0
  obtain ⟨hI,heq⟩ := compact_reference (F.atParameter 0) hG hs hx
  have hinit : ((s,ξ 0),0) ∈ F.domain := by
    rw [hξ]; exact hx.2.2.1 s hs
  have hI' : Icc a b ⊆ (parameterMaximalIntervalValue F s (ξ 0) 0).carrier := by
    simpa only [parameterMaximalIntervalValue,hξ,ParameterODE.atParameter] using hI
  refine ⟨fun t ht => ⟨hinit,hI' ht⟩,?_⟩
  intro t ht
  have hv := (ParameterODE.solutionValue_on_domain F hLip t s (ξ 0) 0 ⟨hinit,hI' ht⟩).1
  change parameterSolutionValueValue F t s (ξ 0) 0 = x₀ t
  rw [hv]
  simpa only [parameterSolutionCurveValue,hξ,ParameterODE.atParameter] using heq ht

/-- Joint Cᵏ regularity pulls back to the actual domain of the perturbed
initial curve. The domain has a single neighborhood over the compact fiber. -/
lemma smooth_family (k : ℕ) (hk : 1 ≤ k) (F : ParameterODE E ℝ)
    (hF : ContDiffOn ℝ k (field F) F.domain) (ξ : ℝ → E)
    (hξ : ContDiffAt ℝ k ξ 0) {a b s : ℝ}
    (h0 : ∀ t ∈ Icc a b, (t,((s,ξ 0),0)) ∈ parameterSolutionDomainValue F) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧
      (∀ t ∈ Icc a b, (t,0) ∈ V) ∧
      ContDiffOn ℝ k (fun q : ℝ × ℝ => trajectory F s ξ q.2 q.1) V ∧
      ∀ q ∈ V, (q.1,((s,ξ q.2),q.2)) ∈ parameterSolutionDomainValue F := by
  obtain ⟨U,hU,hξU⟩ := hξ.contDiffOn le_rfl (by simp)
  let W : Set (ℝ × ℝ) := Prod.snd ⁻¹' interior U
  have hWo : IsOpen W := isOpen_interior.preimage continuous_snd
  let χ : ℝ × ℝ → ℝ × ((ℝ × E) × ℝ) := fun q => (q.1,((s,ξ q.2),q.2))
  have hχ : ContDiffOn ℝ k χ W :=
    contDiffOn_fst.prodMk ((contDiffOn_const.prodMk
      ((hξU.mono interior_subset).comp contDiffOn_snd (fun q hq => hq))).prodMk contDiffOn_snd)
  have hsol := CkDependence.joint_ck k hk F hF
  let V := W ∩ χ ⁻¹' parameterSolutionDomainValue F
  refine ⟨V,hχ.continuousOn.isOpen_inter_preimage hWo hsol.1,?_,?_,fun q hq => hq.2⟩
  · intro t ht
    exact ⟨mem_interior_iff_mem_nhds.mpr hU,h0 t ht⟩
  · exact hsol.2.comp (hχ.mono inter_subset_left) (fun q hq => hq.2)

/-- The chain rule gives the actual first parameter derivative, with the
initial-curve term as well as the direct field-parameter term. -/
lemma trajectory_derivative (F : ParameterODE E ℝ)
    (hF : ContDiffOn ℝ 1 (field F) F.domain) (s : ℝ) (ξ : ℝ → E)
    (hξ : HasDerivAt ξ (deriv ξ 0) 0) {t : ℝ}
    (hq : (t,((s,ξ 0),0)) ∈ parameterSolutionDomainValue F) :
    HasDerivAt (fun ε => trajectory F s ξ ε t) (variation F s ξ t) 0 := by
  have hc := joint_c1 F hF
  have hd := (hc.2.contDiffAt (hc.1.mem_nhds hq)).differentiableAt_one.hasFDerivAt
  let D := fderiv ℝ (solution F) (t,((s,ξ 0),0))
  have hx : stateVariation F s (ξ 0) 0 t (deriv ξ 0) = D (0,((0,deriv ξ 0),0)) := by
    have hh := (hd.comp (ξ 0) ((hasFDerivAt_const t (ξ 0)).prodMk
      (hasFDerivAt_state_insert s (0 : ℝ) (ξ 0)))).fderiv
    exact congrArg (fun L : E →L[ℝ] E => L (deriv ξ 0)) hh
  have hp : parameterVariation F s (ξ 0) 0 t 1 = D (0,((0,0),1)) := by
    have hh := (hd.comp (0 : ℝ) ((hasFDerivAt_const t (0 : ℝ)).prodMk
      (hasFDerivAt_parameter_insert s (ξ 0) (0 : ℝ)))).fderiv
    exact congrArg (fun L : ℝ →L[ℝ] E => L 1) hh
  have hcurve := ((hasDerivAt_const (0 : ℝ) t).prodMk
    (((hasDerivAt_const (0 : ℝ) s).prodMk hξ).prodMk (hasDerivAt_id (0 : ℝ))))
  have h := hd.comp_hasDerivAt (0 : ℝ) hcurve
  have he : variation F s ξ t = D (0,((0,deriv ξ 0),1)) := by
    rw [variation,hx,hp,← map_add]
    simp only [Prod.mk_add_mk,add_zero,zero_add]
  simpa only [trajectory,Function.comp_def,id_eq,he,D] using h

/-- The two variational equations combine to the uniquely characterizing
inhomogeneous equation, including the derivative of the initial curve. -/
lemma variation_equation (F : ParameterODE E ℝ)
    (hF : ContDiffOn ℝ 1 (field F) F.domain) (ξ : ℝ → E)
    {a b s : ℝ} {x₀ : ℝ → E} (hs : s ∈ Icc a b)
    (h0 : ∀ t ∈ Icc a b, (t,((s,ξ 0),0)) ∈ parameterSolutionDomainValue F)
    (heq : EqOn (trajectory F s ξ 0) x₀ (Icc a b)) :
    LinearVolterra.IsDifferentialSolution a b s (referenceCoefficient F x₀)
      (referenceForcing F x₀) (deriv ξ 0) (variation F s ξ) ∧
    ∀ z : ℝ → E,
      LinearVolterra.IsDifferentialSolution a b s (referenceCoefficient F x₀)
        (referenceForcing F x₀) (deriv ξ 0) z → EqOn z (variation F s ξ) (Icc a b) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hinit := (h0 s hs).1
  have hA (t : ℝ) (ht : t ∈ Icc a b) :
      referenceCoefficient F x₀ t = stateCoefficient F s (ξ 0) 0 t := by
    rw [referenceCoefficient,← heq ht]
    rfl
  have hB (t : ℝ) (ht : t ∈ Icc a b) :
      referenceForcing F x₀ t = parameterCoefficient F s (ξ 0) 0 t 1 := by
    rw [referenceForcing,← heq ht]
    rfl
  have hcoeff := continuousOn_coefficients F hF hinit
  have hI : Icc a b ⊆ (parameterMaximalIntervalValue F s (ξ 0) 0).carrier :=
    fun t ht => (h0 t ht).2
  have hAc : ContinuousOn (referenceCoefficient F x₀) (Icc a b) :=
    (hcoeff.1.mono hI).congr (fun t ht => hA t ht)
  have hBc : ContinuousOn (referenceForcing F x₀) (Icc a b) :=
    ((hcoeff.2.mono hI).clm_apply continuousOn_const).congr (fun t ht => hB t ht)
  have hz0 : variation F s ξ s = deriv ξ 0 := by
    have hh := variation_initial_values F hF hinit
    simp only [variation,hh.1,hh.2,ContinuousLinearMap.id_apply,
      zero_apply,add_zero]
  have hzd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (variation F s ξ)
        (referenceCoefficient F x₀ t (variation F s ξ t) + referenceForcing F x₀ t) t := by
    have hh := variational_derivatives F hF (h0 t ht)
    have hY := hh.1.clm_apply (hasDerivAt_const t (deriv ξ 0))
    have hZ := hh.2.clm_apply (hasDerivAt_const t (1 : ℝ))
    have h := hY.fun_add hZ
    simp only [ContinuousLinearMap.map_zero,add_zero,ContinuousLinearMap.comp_apply,
      add_apply] at h
    change HasDerivAt (fun i => stateVariation F s (ξ 0) 0 i (deriv ξ 0) +
      parameterVariation F s (ξ 0) 0 i 1) _ t
    simpa only [variation,hA t ht,hB t ht,map_add,add_assoc] using h
  have hz : LinearVolterra.IsDifferentialSolution a b s (referenceCoefficient F x₀)
      (referenceForcing F x₀) (deriv ξ 0) (variation F s ξ) :=
    ⟨fun t ht => (hzd t ht).continuousAt.continuousWithinAt,
      hz0,fun t ht => (hzd t ht).hasDerivWithinAt⟩
  refine ⟨hz,fun z hzz => ?_⟩
  have hiff := LinearVolterra.differential_equivalence a b s (referenceCoefficient F x₀)
    (referenceForcing F x₀) (deriv ξ 0)
  obtain ⟨Y,hY,hu⟩ := LinearVolterra.existence a b s (referenceCoefficient F x₀)
    (referenceForcing F x₀) (deriv ξ 0) hs hAc hBc
  intro t ht
  exact (hu z ((hiff z hs hAc hBc).mpr hzz) ht).trans
    (hu (variation F s ξ) ((hiff _ hs hAc hBc).mpr hz) ht).symm

lemma family_existence (F : ParameterODE E ℝ)
    (hF : ContDiffOn ℝ 1 (field F) F.domain) (ξ : ℝ → E) {a b s : ℝ}
    (hs : s ∈ Icc a b) {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h0 : ∀ t ∈ Icc a b, (t,0) ∈ V)
    (hdom : ∀ q ∈ V, (q.1,((s,ξ q.2),q.2)) ∈ parameterSolutionDomainValue F) :
    ∃ r > (0 : ℝ), ∀ ε, |ε| < r →
      ((s,ξ ε),ε) ∈ F.domain ∧
      Icc a b ⊆ (parameterMaximalIntervalValue F s (ξ ε) ε).carrier ∧
      compactSolutionOnValue (atParameterValue F ε) a b (trajectory F s ξ ε) ∧
      trajectory F s ξ ε s = ξ ε := by
  obtain ⟨r,hr,hrV⟩ := compact_fiber hV h0
  refine ⟨r,hr,fun ε hε => ?_⟩
  have hq (t : ℝ) (ht : t ∈ Icc a b) := hdom (t,ε) (hrV ⟨ht,abs_lt.mp hε⟩)
  have hinit := (hq s hs).1
  have hI : Icc a b ⊆ (parameterMaximalIntervalValue F s (ξ ε) ε).carrier :=
    fun t ht => (hq t ht).2
  have hx := ParameterODE.solutionValue_ivp F (F.locallyLipschitzInState_of_contDiffOn hF)
    s (ξ ε) ε hinit
  refine ⟨hinit,hI,⟨hs.1.trans hs.2,hx.1.1.continuousOn.mono hI,?_,?_⟩,hx.2.2⟩
  · intro t ht
    exact hx.1.2.1 t (hI ht)
  · intro t ht
    exact (hx.1.2.2 t (hI ht)).hasDerivWithinAt

lemma scalarPartial_trajectory (F : ParameterODE E ℝ)
    (hF : ContDiffOn ℝ 1 (field F) F.domain) (s : ℝ) (ξ : ℝ → E)
    (hξ : HasDerivAt ξ (deriv ξ 0) 0) {t : ℝ}
    (hq : (t,((s,ξ 0),0)) ∈ parameterSolutionDomainValue F)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => trajectory F s ξ q.2 q.1) V)
    (htV : (t,0) ∈ V) :
    scalarPartial (fun q : ℝ × ℝ => trajectory F s ξ q.2 q.1) (t,0) = variation F s ξ t := by
  have hdg := hasDerivAt_scalarPartial
    ((hg.contDiffAt (hV.mem_nhds htV)).differentiableAt_one)
  exact hdg.deriv.symm.trans (trajectory_derivative F hF s ξ hξ hq).deriv

theorem first_order : Specs.D13Unified.Ch06.RegularPerturbation.FirstOrder.{u} := by
  intro E _ _ _ F hF ξ hξ a b s x₀ hs hx hξ0
  obtain ⟨h0,heq⟩ := reference_data F hF hs hx hξ0
  obtain ⟨V,hV,hV0,hg,hdom⟩ := smooth_family 1 le_rfl F hF ξ hξ h0
  have hξd := hξ.differentiableAt_one.hasDerivAt
  have hz := variation_equation F hF ξ hs h0 heq
  refine ⟨family_existence F hF ξ hs hV hV0 hdom,heq,hξd,hz.1,hz.2,?_⟩
  intro η hη
  obtain ⟨δ,hδ,hbound⟩ := uniform_first_order hV hg hV0 η hη
  refine ⟨δ,hδ,fun ε hε t ht => ?_⟩
  have hh := hbound ε hε t ht
  rw [scalarPartial_trajectory F hF s ξ hξd (h0 t ht) hV hg (hV0 t ht),heq ht] at hh
  exact hh

theorem second_order : Specs.D13Unified.Ch06.RegularPerturbation.SecondOrder.{u} := by
  intro E _ _ _ F hF ξ hξ a b s x₀ hs hx hξ0
  have hF1 : ContDiffOn ℝ 1 (field F) F.domain := hF.of_le (by norm_num)
  have hξ1 : ContDiffAt ℝ 1 ξ 0 := hξ.of_le (by norm_num)
  obtain ⟨h0,heq⟩ := reference_data F hF1 hs hx hξ0
  obtain ⟨V,hV,hV0,hg,hdom⟩ := smooth_family 2 (by omega) F hF ξ hξ h0
  obtain ⟨C,hC,δ,hδ,hbound⟩ := uniform_second_order hV hg hV0
  obtain ⟨r,hr,hrV⟩ := compact_fiber hV hV0
  refine ⟨C,hC,min δ r,lt_min hδ hr,fun ε hε => ?_⟩
  have hq (t : ℝ) (ht : t ∈ Icc a b) :=
    hdom (t,ε) (hrV ⟨ht,abs_lt.mp (hε.trans_le (min_le_right _ _))⟩)
  refine ⟨⟨(hq s hs).1,fun t ht => (hq t ht).2⟩,fun t ht => ?_⟩
  have hh := hbound ε (hε.trans_le (min_le_left _ _)) t ht
  rw [scalarPartial_trajectory F hF1 s ξ hξ1.differentiableAt_one.hasDerivAt
    (h0 t ht) hV (hg.of_le (by norm_num)) (hV0 t ht),heq ht] at hh
  exact hh

end D13Unified.Ch06.RegularPerturbation
