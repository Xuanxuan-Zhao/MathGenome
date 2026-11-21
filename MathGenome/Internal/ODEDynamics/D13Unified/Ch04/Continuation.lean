import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.Continuation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalExistenceUniqueness
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.RestrictionPasting
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D13Unified.Ch04.Continuation
universe u
open Specs.D13Unified.Ch04.Continuation
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniform positive lifetime for data near an admissible point. In
particular all these local solutions are defined at the fixed central time.
The estimate is obtained by shrinking one compact controlled box. -/
lemma uniform_local_existence [FiniteDimensional ℝ E] (F : ODE E)
    (hF : F.LocallyLipschitzInState) (c : ℝ) (η : E) (hc : (c, η) ∈ F.domain) :
    ∃ d r : ℝ, 0 < d ∧ 0 < r ∧ ∀ s ∈ ball c d, ∀ ξ ∈ ball η r,
      ∃ (J : OpenTimeInterval) (y : ℝ → E),
        c ∈ J.carrier ∧ IsClassicalIVPOn F J y s ξ := by
  obtain ⟨a, b, L, ha, hb, hL, hdom, hlip⟩ := hF c η hc
  have htime : Icc (c - a / 2) (c + a / 2) ⊆ ball c a := by
    rw [Real.ball_eq_Ioo]
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hstate : closedBall η (b / 2) ⊆ ball η b :=
    closedBall_subset_ball (by linarith)
  have hbox : Icc (c - a / 2) (c + a / 2) ×ˢ closedBall η (b / 2) ⊆ F.domain :=
    fun _ h => hdom ⟨htime h.1, hstate h.2⟩
  have hcompact : IsCompact (Icc (c - a / 2) (c + a / 2) ×ˢ closedBall η (b / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall η (b / 2))
  obtain ⟨M, hbound⟩ := hcompact.exists_bound_of_continuousOn
    (F.continuousOn_eval.mono hbox)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound (c, η)
    ⟨⟨by linarith, by linarith⟩, mem_closedBall_self (by linarith)⟩)
  obtain ⟨h, hh, hha, hMh, hLh⟩ := Ch03.LocalExistenceUniqueness.exists_picard_time
    (a / 4) (b / 4) M L (by positivity) (by positivity) hM hL
  refine ⟨h / 2, b / 4, by positivity, by positivity, ?_⟩
  intro s hs ξ hξ
  have hs' : c - h / 2 < s ∧ s < c + h / 2 := by
    simpa only [Real.ball_eq_Ioo, mem_Ioo] using hs
  have hT : Icc (s - h) (s + h) ⊆ Icc (c - a / 2) (c + a / 2) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hB : closedBall ξ (b / 4) ⊆ closedBall η (b / 2) := by
    intro z hz
    apply mem_closedBall.mpr
    calc
      dist z η ≤ dist z ξ + dist ξ η := dist_triangle _ _ _
      _ ≤ b / 2 := by linarith [mem_closedBall.mp hz, mem_ball.mp hξ]
  obtain ⟨y, hy, _⟩ := Ch03.ControlledPicard.controlled_picard F s ξ h (b / 4) M L h
    hM hL hh le_rfl hMh hLh (fun _ ht => hbox ⟨hT ht.1, hB ht.2⟩)
    (fun t ht z hz => hbound (t, z) ⟨hT ht, hB hz⟩)
    (fun t ht z hz w hw => hlip t (htime (hT ht)) z (hstate (hB hz)) w (hstate (hB hw)))
  let J := OpenTimeInterval.bounded (s - h) (s + h) (by linarith)
  have hsub : J.carrier ⊆ (Specs.D13Unified.Ch03.ControlledPicard.controlledInterval s h hh).carrier :=
    Ioo_subset_Icc_self
  refine ⟨J, y, ⟨by linarith, by linarith⟩, ?_⟩
  refine ⟨(classical_iff_solutionOn F J y).mpr ?_, ⟨by linarith, by linarith⟩, hy.2.2⟩
  exact ⟨hy.1.1.mono hsub, fun t ht => hy.1.2.1 t (hsub ht),
    fun t ht => (hy.1.2.2 t (hsub ht)).mono hsub⟩


/-- Even a nonmonotone convergent sequence of graph points suffices to obtain
one genuine local solution across its limiting time, agreeing on the overlap. -/
lemma cluster_local_solution [FiniteDimensional ℝ E] (F : ODE E)
    (hF : F.LocallyLipschitzInState) (I : OpenTimeInterval) (x : ℝ → E)
    (hx : IsClassicalSolutionOn F I x) (c : ℝ) (η : E) (hc : (c, η) ∈ F.domain)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ I.carrier)
    (hconv : Tendsto (fun j => (t j, x (t j))) atTop (𝓝 (c, η))) :
    ∃ (J : OpenTimeInterval) (y : ℝ → E), c ∈ J.carrier ∧
      IsClassicalSolutionOn F J y ∧ EqOn x y (I.carrier ∩ J.carrier) ∧ y c = η := by
  obtain ⟨d, r, hd, hr, hloc⟩ := uniform_local_existence F hF c η hc
  have htlim : Tendsto t atTop (𝓝 c) := (continuous_fst.tendsto (c, η)).comp hconv
  have hxlim : Tendsto (fun j => x (t j)) atTop (𝓝 η) :=
    (continuous_snd.tendsto (c, η)).comp hconv
  obtain ⟨n, hn⟩ := ((htlim.eventually (ball_mem_nhds c hd)).and
    (hxlim.eventually (ball_mem_nhds η hr))).exists
  obtain ⟨J, y, hcJ, hy⟩ := hloc (t n) hn.1 (x (t n)) hn.2
  have heq : EqOn x y (I.carrier ∩ J.carrier) :=
    Ch03.LocalExistenceUniqueness.no_crossing F hF I J x y (t n) hx hy.1
      ⟨ht n, hy.2.1⟩ hy.2.2.symm
  have hycont : ContinuousAt y c := hy.1.1.continuousOn.continuousAt (J.isOpen.mem_nhds hcJ)
  have hevent : (fun j => x (t j)) =ᶠ[atTop] (fun j => y (t j)) := by
    filter_upwards [htlim.eventually (J.isOpen.mem_nhds hcJ)] with j hj
    exact heq ⟨ht j, hj⟩
  have hyconv : Tendsto (fun j => x (t j)) atTop (𝓝 (y c)) :=
    (hycont.tendsto.comp htlim).congr' hevent.symm
  exact ⟨J, y, hcJ, hy.1, heq, tendsto_nhds_unique hyconv hxlim⟩

/-- A sufficiently short terminal interval is in the recorded domain, even
when the opposite endpoint is minus infinity. -/
lemma right_eventually_mem (I : OpenTimeInterval) (a : EReal) (b : ℝ)
    (hI : I.carrier = {t : ℝ | a < (t : EReal) ∧ t < b}) :
    I.carrier ∈ 𝓝[<] b := by
  obtain ⟨s, hs⟩ := I.nonempty
  have hs' : a < (s : EReal) ∧ s < b := by simpa only [hI, mem_ofPred_eq] using hs
  apply mem_of_superset (Ioo_mem_nhdsLT hs'.2)
  intro t ht
  rw [hI]
  exact ⟨hs'.1.trans (EReal.coe_lt_coe_iff.mpr ht.1), ht.2⟩

lemma left_eventually_mem (I : OpenTimeInterval) (a : ℝ) (b : EReal)
    (hI : I.carrier = {t : ℝ | a < t ∧ (t : EReal) < b}) :
    I.carrier ∈ 𝓝[>] a := by
  obtain ⟨s, hs⟩ := I.nonempty
  have hs' : a < s ∧ (s : EReal) < b := by simpa only [hI, mem_ofPred_eq] using hs
  apply mem_of_superset (Ioo_mem_nhdsGT hs'.1)
  intro t ht
  rw [hI]
  exact ⟨ht.1, (EReal.coe_lt_coe_iff.mpr ht.2).trans hs'.2⟩

/-- Necessity uses continuity at the included interior endpoint of the
extension; all sequence times remain in the original actual interval. -/
lemma right_cluster_of_extension (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E)
    (a : EReal) (b : ℝ)
    (hI : I.carrier = {t : ℝ | a < (t : EReal) ∧ t < b})
    (J : OpenTimeInterval) (y : ℝ → E) (hb : b ∈ J.carrier)
    (hy : IsClassicalSolutionOn F J y) (heq : EqOn y x I.carrier) :
    RightCluster F I x b (y b) := by
  obtain ⟨s, hs⟩ := I.nonempty
  have hs' : a < (s : EReal) ∧ s < b := by simpa only [hI, mem_ofPred_eq] using hs
  obtain ⟨t, hmono, ht, hlim⟩ := exists_seq_strictMono_tendsto' hs'.2
  have htI : ∀ j, t j ∈ I.carrier := by
    intro j
    rw [hI]
    exact ⟨hs'.1.trans (EReal.coe_lt_coe_iff.mpr (ht j).1), (ht j).2⟩
  have hxlim : Tendsto (fun j => x (t j)) atTop (𝓝 (y b)) := by
    apply ((hy.1.continuousOn.continuousAt (J.isOpen.mem_nhds hb)).tendsto.comp hlim).congr'
    exact Filter.Eventually.of_forall (fun j => heq (htI j))
  exact ⟨hy.2.1 b hb, t, hmono, htI, hlim.prodMk_nhds hxlim⟩

lemma left_cluster_of_extension (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E)
    (a : ℝ) (b : EReal)
    (hI : I.carrier = {t : ℝ | a < t ∧ (t : EReal) < b})
    (J : OpenTimeInterval) (y : ℝ → E) (ha : a ∈ J.carrier)
    (hy : IsClassicalSolutionOn F J y) (heq : EqOn y x I.carrier) :
    LeftCluster F I x a (y a) := by
  obtain ⟨s, hs⟩ := I.nonempty
  have hs' : a < s ∧ (s : EReal) < b := by simpa only [hI, mem_ofPred_eq] using hs
  obtain ⟨t, hanti, ht, hlim⟩ := exists_seq_strictAnti_tendsto' hs'.1
  have htI : ∀ j, t j ∈ I.carrier := by
    intro j
    rw [hI]
    exact ⟨(ht j).1, (EReal.coe_lt_coe_iff.mpr (ht j).2).trans hs'.2⟩
  have hxlim : Tendsto (fun j => x (t j)) atTop (𝓝 (y a)) := by
    apply ((hy.1.continuousOn.continuousAt (J.isOpen.mem_nhds ha)).tendsto.comp hlim).congr'
    exact Filter.Eventually.of_forall (fun j => heq (htI j))
  exact ⟨hy.2.1 a ha, t, hanti, htI, hlim.prodMk_nhds hxlim⟩


/-- Pasting a solution across the endpoint and restricting the union leaves
the opposite endpoint fixed, including the case of an infinite endpoint. -/
lemma right_extend_of_local (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E)
    (a : EReal) (b : ℝ)
    (hI : I.carrier = {t : ℝ | a < (t : EReal) ∧ t < b})
    (hx : IsClassicalSolutionOn F I x) (J : OpenTimeInterval) (y : ℝ → E)
    (hbJ : b ∈ J.carrier) (hy : IsClassicalSolutionOn F J y)
    (heq : EqOn x y (I.carrier ∩ J.carrier)) : RightExtension F I x a b := by
  have hJmem : J.carrier ∈ 𝓝[<] b := mem_nhdsWithin_of_mem_nhds (J.isOpen.mem_nhds hbJ)
  obtain ⟨r, hrI, hrJ⟩ := Filter.nonempty_of_mem (inter_mem (right_eventually_mem I a b hI) hJmem)
  have hmeet : (I.carrier ∩ J.carrier).Nonempty := ⟨r, hrI, hrJ⟩
  obtain ⟨l, d, hbd, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (J.isOpen.mem_nhds hbJ)
  let D := (b + d) / 2
  have hbD : b < D := by dsimp [D]; linarith [hbd.2]
  have hDJ : D ∈ J.carrier := hsub ⟨by dsimp [D]; linarith [hbd.1, hbd.2],
    by dsimp [D]; linarith [hbd.2]⟩
  let K : OpenTimeInterval := {
    carrier := {t : ℝ | a < (t : EReal) ∧ t < D}
    nonempty := ⟨r, by
      have hr : a < (r : EReal) ∧ r < b := by simpa only [hI, mem_ofPred_eq] using hrI
      exact ⟨hr.1, hr.2.trans hbD⟩⟩
    ordConnected := ⟨by
      intro u hu v hv t ht
      exact ⟨hu.1.trans_le (EReal.coe_le_coe_iff.mpr ht.1), ht.2.trans_lt hv.2⟩⟩
    isOpen := (isOpen_lt continuous_const continuous_coe_real_ereal).inter isOpen_Iio }
  let U : OpenTimeInterval := ⟨I.toTimeInterval.union J.toTimeInterval hmeet,
    I.isOpen.union J.isOpen⟩
  have hKU : K.carrier ⊆ U.carrier := by
    intro t ht
    by_cases htb : t < b
    · exact Or.inl (by rw [hI]; exact ⟨ht.1, htb⟩)
    · exact Or.inr (J.ordConnected.out hbJ hDJ ⟨le_of_not_gt htb, ht.2.le⟩)
  have hsol := classical_pasting F I J x y hmeet hx hy heq
  refine ⟨D - b, sub_pos.mpr hbD, K, pasteCurves I.carrier x y, ?_,
    classicalSolutionOn_restrict F U K _ hKU hsol, (pasteCurves_eqOn heq).1⟩
  change {t : ℝ | a < (t : EReal) ∧ t < D} = _
  rw [show b + (D - b) = D by ring]

lemma left_extend_of_local (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E)
    (a : ℝ) (b : EReal)
    (hI : I.carrier = {t : ℝ | a < t ∧ (t : EReal) < b})
    (hx : IsClassicalSolutionOn F I x) (J : OpenTimeInterval) (y : ℝ → E)
    (haJ : a ∈ J.carrier) (hy : IsClassicalSolutionOn F J y)
    (heq : EqOn x y (I.carrier ∩ J.carrier)) : LeftExtension F I x a b := by
  have hJmem : J.carrier ∈ 𝓝[>] a := mem_nhdsWithin_of_mem_nhds (J.isOpen.mem_nhds haJ)
  obtain ⟨r, hrI, hrJ⟩ := Filter.nonempty_of_mem (inter_mem (left_eventually_mem I a b hI) hJmem)
  have hmeet : (I.carrier ∩ J.carrier).Nonempty := ⟨r, hrI, hrJ⟩
  obtain ⟨l, d, hal, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (J.isOpen.mem_nhds haJ)
  let A := (l + a) / 2
  have hAa : A < a := by dsimp [A]; linarith [hal.1]
  have hAJ : A ∈ J.carrier := hsub ⟨by dsimp [A]; linarith [hal.1],
    by dsimp [A]; linarith [hal.1, hal.2]⟩
  let K : OpenTimeInterval := {
    carrier := {t : ℝ | A < t ∧ (t : EReal) < b}
    nonempty := ⟨r, by
      have hr : a < r ∧ (r : EReal) < b := by simpa only [hI, mem_ofPred_eq] using hrI
      exact ⟨hAa.trans hr.1, hr.2⟩⟩
    ordConnected := ⟨by
      intro u hu v hv t ht
      exact ⟨hu.1.trans_le ht.1, (EReal.coe_le_coe_iff.mpr ht.2).trans_lt hv.2⟩⟩
    isOpen := isOpen_Ioi.inter (isOpen_lt continuous_coe_real_ereal continuous_const) }
  let U : OpenTimeInterval := ⟨I.toTimeInterval.union J.toTimeInterval hmeet,
    I.isOpen.union J.isOpen⟩
  have hKU : K.carrier ⊆ U.carrier := by
    intro t ht
    by_cases hat : a < t
    · exact Or.inl (by rw [hI]; exact ⟨hat, ht.2⟩)
    · exact Or.inr (J.ordConnected.out hAJ haJ ⟨ht.1.le, le_of_not_gt hat⟩)
  have hsol := classical_pasting F I J x y hmeet hx hy heq
  refine ⟨a - A, sub_pos.mpr hAa, K, pasteCurves I.carrier x y, ?_,
    classicalSolutionOn_restrict F U K _ hKU hsol, (pasteCurves_eqOn heq).1⟩
  change {t : ℝ | A < t ∧ (t : EReal) < b} = _
  rw [show a - (a - A) = A by ring]

/-- The finite right-endpoint criterion, on the original time-state domain. -/
theorem right_continuation : rightContinuationExpected.{u} := by
  intro E _ _ _ F hF I x a b hI hx
  constructor
  · rintro ⟨ε, hε, J, y, hJ, hy, heq⟩
    have hbJ : b ∈ J.carrier := by
      obtain ⟨s, hs⟩ := I.nonempty
      have hs' : a < (s : EReal) ∧ s < b := by simpa only [hI, mem_ofPred_eq] using hs
      rw [hJ]
      exact ⟨hs'.1.trans (EReal.coe_lt_coe_iff.mpr hs'.2), by linarith⟩
    exact ⟨y b, right_cluster_of_extension F I x a b hI J y hbJ hy heq⟩
  · rintro ⟨η, hc, t, _hmono, ht, hconv⟩
    obtain ⟨J, y, hbJ, hy, heq, _⟩ := cluster_local_solution F hF I x hx b η hc t ht hconv
    exact right_extend_of_local F I x a b hI hx J y hbJ hy heq

/-- The exact finite left-endpoint criterion, with decreasing interior times. -/
theorem left_continuation : leftContinuationExpected.{u} := by
  intro E _ _ _ F hF I x a b hI hx
  constructor
  · rintro ⟨ε, hε, J, y, hJ, hy, heq⟩
    have haJ : a ∈ J.carrier := by
      obtain ⟨s, hs⟩ := I.nonempty
      have hs' : a < s ∧ (s : EReal) < b := by simpa only [hI, mem_ofPred_eq] using hs
      rw [hJ]
      exact ⟨by linarith, (EReal.coe_lt_coe_iff.mpr hs'.1).trans hs'.2⟩
    exact ⟨y a, left_cluster_of_extension F I x a b hI J y haJ hy heq⟩
  · rintro ⟨η, hc, t, _hanti, ht, hconv⟩
    obtain ⟨J, y, haJ, hy, heq, _⟩ := cluster_local_solution F hF I x hx a η hc t ht hconv
    exact left_extend_of_local F I x a b hI hx J y haJ hy heq


omit [NormedSpace ℝ E] in
/-- A continuous extension's value is forced by any convergent graph
sequence, independently of which extension was selected. -/
lemma value_of_extension (I J : OpenTimeInterval) (x y : ℝ → E) (c : ℝ) (η : E)
    (hcJ : c ∈ J.carrier) (hy : ContinuousOn y J.carrier) (heq : EqOn y x I.carrier)
    (t : ℕ → ℝ) (ht : ∀ j, t j ∈ I.carrier)
    (hconv : Tendsto (fun j => (t j, x (t j))) atTop (𝓝 (c, η))) : y c = η := by
  have htlim : Tendsto t atTop (𝓝 c) := (continuous_fst.tendsto (c, η)).comp hconv
  have hxlim : Tendsto (fun j => x (t j)) atTop (𝓝 η) :=
    (continuous_snd.tendsto (c, η)).comp hconv
  have hyconv : Tendsto (fun j => x (t j)) atTop (𝓝 (y c)) := by
    apply ((hy.continuousAt (J.isOpen.mem_nhds hcJ)).tendsto.comp htlim).congr'
    exact Filter.Eventually.of_forall (fun j => heq (ht j))
  exact tendsto_nhds_unique hyconv hxlim

/-- Convergence of an admissible subsequence forces the full left-hand
limit. Every extension through the endpoint takes the limiting value. -/
theorem right_limit : rightLimitExpected.{u} := by
  intro E _ _ _ F hF I x a b hI hx η hcluster
  obtain ⟨hc, t, _hmono, ht, hconv⟩ := hcluster
  obtain ⟨J, y, hbJ, hy, heq, hyη⟩ := cluster_local_solution F hF I x hx b η hc t ht hconv
  have hevent : x =ᶠ[𝓝[<] b] y := by
    filter_upwards [right_eventually_mem I a b hI,
      mem_nhdsWithin_of_mem_nhds (J.isOpen.mem_nhds hbJ)] with r hrI hrJ
    exact heq ⟨hrI, hrJ⟩
  have hyconv : Tendsto y (𝓝[<] b) (𝓝 η) := by
    rw [← hyη]
    exact (hy.1.continuousOn.continuousAt (J.isOpen.mem_nhds hbJ)).tendsto.mono_left
      nhdsWithin_le_nhds
  refine ⟨hyconv.congr' hevent.symm, ?_⟩
  intro K z hbK hz hzx
  exact value_of_extension I K x z b η hbK hz.1.continuousOn hzx t ht hconv

/-- The full right-hand limit and the endpoint value at a finite left
endpoint, with precisely the reversed one-sided filter. -/
theorem left_limit : leftLimitExpected.{u} := by
  intro E _ _ _ F hF I x a b hI hx η hcluster
  obtain ⟨hc, t, _hanti, ht, hconv⟩ := hcluster
  obtain ⟨J, y, haJ, hy, heq, hyη⟩ := cluster_local_solution F hF I x hx a η hc t ht hconv
  have hevent : x =ᶠ[𝓝[>] a] y := by
    filter_upwards [left_eventually_mem I a b hI,
      mem_nhdsWithin_of_mem_nhds (J.isOpen.mem_nhds haJ)] with r hrI hrJ
    exact heq ⟨hrI, hrJ⟩
  have hyconv : Tendsto y (𝓝[>] a) (𝓝 η) := by
    rw [← hyη]
    exact (hy.1.continuousOn.continuousAt (J.isOpen.mem_nhds haJ)).tendsto.mono_left
      nhdsWithin_le_nhds
  refine ⟨hyconv.congr' hevent.symm, ?_⟩
  intro K z haK hz hzx
  exact value_of_extension I K x z a η haK hz.1.continuousOn hzx t ht hconv

end D13Unified.Ch04.Continuation
