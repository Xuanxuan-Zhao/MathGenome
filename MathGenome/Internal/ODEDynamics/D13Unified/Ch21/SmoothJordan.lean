import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.SmoothJordan
import MathGenome.Internal.ODEDynamics.D13Unified.Ch21.Collar
import MathGenome.Internal.ODEDynamics.D13Unified.Ch21.IndexJump
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace D13Unified.Ch21.SmoothJordan
noncomputable section
open Set Filter
open scoped Topology
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.SmoothJordan

/-- A nearest-point segment, except for its initial point, misses the compact
set. This argument needs no differentiability or separation theorem. -/
theorem nearest_segment_avoids {K : Set ℂ} {p q : ℂ}
    (hp : p ∉ K) (hq : q ∈ K) (hmin : ∀ z ∈ K, dist p q ≤ dist p z)
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) : q + t • (p - q) ∉ K := by
  intro hz
  have hd : 0 < dist p q := dist_pos.mpr (fun h => hp (h.symm ▸ hq))
  have he : p - (q + t • (p - q)) = (1 - t) • (p - q) := by
    simp only [sub_smul, one_smul]
    abel
  have hdist : dist p (q + t • (p - q)) = (1 - t) * dist p q := by
    rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht'),
      dist_eq_norm]
  have := hmin _ hz
  rw [hdist] at this
  nlinarith

/-- Every point outside a nonempty compact set can be joined in its complement
to any prescribed open neighborhood of that set. -/
theorem reaches_neighborhood {K N : Set ℂ} (hK : IsCompact K) (hKn : K.Nonempty)
    (hN : IsOpen N) (hKN : K ⊆ N) {p : ℂ} (hp : p ∉ K) :
    ∃ z ∈ N \ K, JoinedIn Kᶜ p z := by
  obtain ⟨q, hq, hmin⟩ := hK.exists_isMinOn hKn (continuous_const.dist continuous_id).continuousOn
  let f : ℝ → ℂ := fun t => q + t • (p - q)
  have hf : Continuous f := by fun_prop
  have h₀ : f 0 ∈ N := by simpa [f] using hKN hq
  have hpre : f ⁻¹' N ∈ 𝓝 (0 : ℝ) := hf.continuousAt.preimage_mem_nhds (hN.mem_nhds h₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := min (ε / 2) (1 / 2)
  have ht : 0 < t := lt_min (half_pos hε) (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have htε : t < ε := (min_le_left _ _).trans_lt (by linarith)
  have hft : f t ∈ N := hball (by simpa [Real.dist_eq, abs_of_pos ht] using htε)
  have havoid : ∀ r ∈ Icc t 1, f r ∉ K :=
    fun r hr => nearest_segment_avoids hp hq hmin (ht.trans_le hr.1) hr.2
  have hpath : IsPathConnected (f '' Icc t 1) :=
    ((convex_Icc t 1).isPathConnected ⟨t, le_rfl, ht1⟩).image hf
  have hsub : f '' Icc t 1 ⊆ Kᶜ := by
    rintro z ⟨r, hr, rfl⟩
    exact havoid r hr
  refine ⟨f t, ⟨hft, havoid t ⟨le_rfl, ht1⟩⟩, ?_⟩
  have hpim : p ∈ f '' Icc t 1 := ⟨1, ⟨ht1, le_rfl⟩, by simp [f]⟩
  exact (hpath.joinedIn p hpim (f t) ⟨t, ⟨le_rfl, ht1⟩, rfl⟩).mono hsub

/-- Every point of the collar off its zero section belongs to one of its two
specified sides. -/
theorem collar_target_off_trace {γ v : Circle → ℂ} {a : ℝ}
    (hc : IsCollar γ v a) :
    ∃ N : Set ℂ, IsOpen N ∧ range γ ⊆ N ∧
      N \ range γ = positiveSide γ v a ∪ negativeSide γ v a := by
  obtain ⟨ha, hv, ht, e, hs, he, htrace, hdiff, hinv, hdis, hpos, hneg, hpA, hnA⟩ := hc
  refine ⟨e.target, e.open_target, htrace, ?_⟩
  apply Subset.antisymm
  · rintro z ⟨hz, hzγ⟩
    have hsrc : e.symm z ∈ cylinder a := hs ▸ e.map_target hz
    have heq : collarMap γ v (e.symm z) = z := (he _).symm.trans (e.right_inv hz)
    have hne : (e.symm z).2 ≠ 0 := by
      intro hr
      apply hzγ
      exact ⟨(e.symm z).1, by simpa [collarMap, hr] using heq⟩
    rcases lt_or_gt_of_ne hne with hn | hp
    · exact Or.inr ⟨e.symm z, ⟨mem_univ _, hsrc.2.1, hn⟩, heq⟩
    · exact Or.inl ⟨e.symm z, ⟨mem_univ _, hp, hsrc.2.2⟩, heq⟩
  · rintro z (hz | hz)
    · refine ⟨?_, hpA hz⟩
      obtain ⟨p, hp, rfl⟩ := hz
      rw [← he]
      apply e.map_source
      rw [hs]
      exact ⟨mem_univ _, (neg_neg_of_pos ha).trans hp.2.1, hp.2.2⟩
    · refine ⟨?_, hnA hz⟩
      obtain ⟨p, hp, rfl⟩ := hz
      rw [← he]
      apply e.map_source
      rw [hs]
      exact ⟨mem_univ _, hp.2.1, hp.2.2.trans ha⟩

/-- The required at-most-two-components reachability statement. The compact
nearest-point argument and the actual collar suffice; normal derivatives are
unnecessary here. -/
theorem reaches_collar_side (γ : C(Circle, ℂ)) (v : Circle → ℂ) (a : ℝ)
    (hc : IsCollar γ v a) (p : ℂ) (hp : p ∉ range γ) :
    ∃ z ∈ positiveSide γ v a ∪ negativeSide γ v a, JoinedIn (range γ)ᶜ p z := by
  obtain ⟨N, hN, htrace, hNoff⟩ := collar_target_off_trace hc
  have hcompact : IsCompact (range γ) := isCompact_range γ.continuous
  obtain ⟨z, hz, hpath⟩ := reaches_neighborhood hcompact (range_nonempty γ) hN htrace hp
  exact ⟨z, hNoff ▸ hz, hpath⟩

/-- A path in a set puts its endpoints in the same connected component. -/
theorem joinedIn_component_eq {S : Set ℂ} {p z : ℂ} (h : JoinedIn S p z) :
    connectedComponentIn S p = connectedComponentIn S z := by
  apply connectedComponentIn_eq
  have hsub : pathComponentIn S p ⊆ connectedComponentIn S p :=
    (isPathConnected_pathComponentIn h.source_mem).isConnected.isPreconnected.subset_connectedComponentIn
      (mem_pathComponentIn_self h.source_mem) pathComponentIn_subset
  exact hsub h

/-- Two actual distinct components, containing the two collar sides, exhaust
the complement. This includes the at-most-two assertion rather than assuming it. -/
theorem collar_components (γ : C(Circle, ℂ)) (hγ : RegularEmbeddedLoop γ)
    (v : Circle → ℂ) (a : ℝ) (hc : IsCollar γ v a) :
    ∃ P M : Set ℂ,
      TwoComponents (range γ)ᶜ P M ∧
      IsOpen P ∧ IsOpen M ∧ IsPathConnected P ∧ IsPathConnected M ∧
      positiveSide γ v a ⊆ P ∧ negativeSide γ v a ⊆ M ∧
      ∀ p ∈ P, ∀ m ∈ M,
        Specs.D13Unified.Ch21.IndexProperties.index
          (Specs.D13Unified.Ch21.IndexProperties.circleLoop γ) p -
        Specs.D13Unified.Ch21.IndexProperties.index
          (Specs.D13Unified.Ch21.IndexProperties.circleLoop γ) m = 1 := by
  have hc0 := hc
  obtain ⟨ha, hv, ht, e, hs, he, htrace, hdiff, hinv, hdis, hpos, hneg, hpA, hnA⟩ := hc
  obtain ⟨p₀, hp₀⟩ := hpos.nonempty
  obtain ⟨m₀, hm₀⟩ := hneg.nonempty
  let S := (range γ)ᶜ
  let P := connectedComponentIn S p₀
  let M := connectedComponentIn S m₀
  have hpS : p₀ ∈ S := hpA hp₀
  have hmS : m₀ ∈ S := hnA hm₀
  have hpP : p₀ ∈ P := mem_connectedComponentIn hpS
  have hmM : m₀ ∈ M := mem_connectedComponentIn hmS
  have hPS : P ⊆ S := connectedComponentIn_subset _ _
  have hMS : M ⊆ S := connectedComponentIn_subset _ _
  have hsideP : positiveSide γ v a ⊆ P :=
    hpos.isConnected.isPreconnected.subset_connectedComponentIn hp₀ hpA
  have hsideM : negativeSide γ v a ⊆ M :=
    hneg.isConnected.isPreconnected.subset_connectedComponentIn hm₀ hnA
  have hall : ∀ z ∈ S, connectedComponentIn S z = P ∨ connectedComponentIn S z = M := by
    intro z hz
    obtain ⟨w, hw, hj⟩ := reaches_collar_side γ v a hc0 z hz
    rcases hw with hw | hw
    · exact Or.inl ((joinedIn_component_eq hj).trans (connectedComponentIn_eq (hsideP hw)).symm)
    · exact Or.inr ((joinedIn_component_eq hj).trans (connectedComponentIn_eq (hsideM hw)).symm)
  have hopen : IsOpen S := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hPo : IsOpen P := hopen.connectedComponentIn
  have hMo : IsOpen M := hopen.connectedComponentIn
  have hPc : IsConnected P := isConnected_connectedComponentIn_iff.mpr hpS
  have hMc : IsConnected M := isConnected_connectedComponentIn_iff.mpr hmS
  let α := Specs.D13Unified.Ch21.IndexProperties.circleLoop γ
  let ind := Specs.D13Unified.Ch21.IndexProperties.index α
  have hindexP : ∀ p ∈ P, ind p = ind p₀ := by
    intro p hp
    apply IndexJump.index_constant_on_preconnected α P hPc.isPreconnected _ p hp p₀ hpP
    simpa only [α, S, IndexProperties.circle_trace] using hPS
  have hindexM : ∀ m ∈ M, ind m = ind m₀ := by
    intro m hm
    apply IndexJump.index_constant_on_preconnected α M hMc.isPreconnected _ m hm m₀ hmM
    simpa only [α, S, IndexProperties.circle_trace] using hMS
  have hjump : ind p₀ - ind m₀ = 1 := IndexJump.index_jump γ hγ v a hc0 p₀ hp₀ m₀ hm₀
  have hdisPM : Disjoint P M := by
    apply Set.disjoint_left.mpr
    intro z hzP hzM
    have heq : ind p₀ = ind m₀ := (hindexP z hzP).symm.trans (hindexM z hzM)
    rw [heq, sub_self] at hjump
    exact zero_ne_one hjump
  refine ⟨P, M, ⟨⟨p₀, hpP⟩, ⟨m₀, hmM⟩, hdisPM, ?_, ?_, ?_⟩,
    hPo, hMo, hPo.isConnected_iff_isPathConnected.mp hPc,
    hMo.isConnected_iff_isPathConnected.mp hMc, hsideP, hsideM, ?_⟩
  · apply Subset.antisymm (union_subset hPS hMS)
    intro z hz
    rcases hall z hz with hp | hm
    · exact Or.inl (hp ▸ mem_connectedComponentIn hz)
    · exact Or.inr (hm ▸ mem_connectedComponentIn hz)
  · intro p hp
    exact (connectedComponentIn_eq hp).symm
  · intro m hm
    exact (connectedComponentIn_eq hm).symm
  · intro p hp m hm
    change ind p - ind m = 1
    rw [hindexP p hp, hindexM m hm]
    exact hjump

/-- Both half-cylinders approach every point of the zero section. -/
theorem trace_subset_closure_sides {γ v : Circle → ℂ} {a : ℝ} (ha : 0 < a) :
    range γ ⊆ closure (positiveSide γ v a) ∧
    range γ ⊆ closure (negativeSide γ v a) := by
  have hcont (t : Circle) : Continuous (fun r : ℝ => γ t + r • v t) := by fun_prop
  constructor
  · rintro z ⟨t, rfl⟩
    have h₀ : (0 : ℝ) ∈ closure (Ioo 0 a) := by
      rw [closure_Ioo (ne_of_lt ha)]
      exact ⟨le_rfl, ha.le⟩
    have hh := mem_closure_image (hcont t).continuousAt h₀
    have hsub : (fun r : ℝ => γ t + r • v t) '' Ioo 0 a ⊆ positiveSide γ v a := by
      rintro z ⟨r, hr, rfl⟩
      exact ⟨(t, r), ⟨mem_univ _, hr⟩, rfl⟩
    simpa only [zero_smul, add_zero] using closure_mono hsub hh
  · rintro z ⟨t, rfl⟩
    have h₀ : (0 : ℝ) ∈ closure (Ioo (-a) 0) := by
      rw [closure_Ioo (ne_of_lt (neg_neg_of_pos ha))]
      exact ⟨(neg_neg_of_pos ha).le, le_rfl⟩
    have hh := mem_closure_image (hcont t).continuousAt h₀
    have hsub : (fun r : ℝ => γ t + r • v t) '' Ioo (-a) 0 ⊆ negativeSide γ v a := by
      rintro z ⟨r, hr, rfl⟩
      exact ⟨(t, r), ⟨mem_univ _, hr⟩, rfl⟩
    simpa only [zero_smul, add_zero] using closure_mono hsub hh

/-- In a partition of the curve complement by two open sets containing the
respective collar sides, both frontiers are exactly the trace. -/
theorem collar_frontiers {γ v : Circle → ℂ} {a : ℝ} (hc : IsCollar γ v a)
    {P M : Set ℂ} (hPM : TwoComponents (range γ)ᶜ P M)
    (hPo : IsOpen P) (hMo : IsOpen M)
    (hp : positiveSide γ v a ⊆ P) (hm : negativeSide γ v a ⊆ M) :
    frontier P = range γ ∧ frontier M = range γ := by
  obtain ⟨hPn, hMn, hdis, hunion, hcompP, hcompM⟩ := hPM
  have hPS : P ⊆ (range γ)ᶜ := fun _ hx => hunion ▸ Or.inl hx
  have hMS : M ⊆ (range γ)ᶜ := fun _ hx => hunion ▸ Or.inr hx
  obtain ⟨hpcl, hmcl⟩ := trace_subset_closure_sides (γ := γ) (v := v) hc.1
  have htraceP : range γ ⊆ frontier P := by
    intro z hz
    rw [hPo.frontier_eq]
    exact ⟨closure_mono hp (hpcl hz), fun h => hPS h hz⟩
  have htraceM : range γ ⊆ frontier M := by
    intro z hz
    rw [hMo.frontier_eq]
    exact ⟨closure_mono hm (hmcl hz), fun h => hMS h hz⟩
  have hfrontP : frontier P ⊆ range γ := by
    intro z hz
    by_contra hnot
    have hzU : z ∈ P ∪ M := hunion.symm ▸ hnot
    rcases hzU with hzP | hzM
    · exact (hPo.frontier_eq ▸ hz).2 hzP
    · exact Set.disjoint_left.mp (hdis.frontier_left hMo) hz hzM
  have hfrontM : frontier M ⊆ range γ := by
    intro z hz
    by_contra hnot
    have hzU : z ∈ P ∪ M := hunion.symm ▸ hnot
    rcases hzU with hzP | hzM
    · exact Set.disjoint_left.mp (hdis.symm.frontier_left hPo) hz hzP
    · exact (hMo.frontier_eq ▸ hz).2 hzM
  exact ⟨Subset.antisymm hfrontP htraceP, Subset.antisymm hfrontM htraceM⟩

open Specs.D13Unified.Ch21.IndexProperties (index circleLoop)

/-- Nonzero index confines a set to a ball. -/
theorem bounded_of_index_ne_zero (γ : C(Circle, ℂ)) {A : Set ℂ}
    (hA : ∀ p ∈ A, index (circleLoop γ) p ≠ 0) : Bornology.IsBounded A := by
  obtain ⟨R, hR, hzero⟩ := IndexProperties.index_zero_outside_ball (circleLoop γ)
  apply (isBounded_iff_forall_norm_le).mpr
  refine ⟨R, fun p hp => le_of_not_gt fun h => hA p hp (hzero p h).2⟩

/-- A set containing all sufficiently distant points of the plane is unbounded. -/
theorem unbounded_of_contains_norm_gt {A : Set ℂ} {R : ℝ}
    (hA : ∀ p : ℂ, R < ‖p‖ → p ∈ A) : ¬ Bornology.IsBounded A := by
  intro hb
  obtain ⟨B, hB⟩ := (isBounded_iff_forall_norm_le).mp hb
  let T := max (max R B) 0 + 1
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right (max R B) 0]
  have hRT : R < T := by dsimp [T]; linarith [le_max_left R B, le_max_left (max R B) 0]
  have hBT : B < T := by dsimp [T]; linarith [le_max_right R B, le_max_left (max R B) 0]
  have hn : ‖(T : ℂ)‖ = T := by simp [Complex.norm_real, abs_of_pos hT]
  have := hB (T : ℂ) (hA (T : ℂ) (by rwa [hn]))
  rw [hn] at this
  exact (not_le_of_gt hBT) this

/-- The zero-at-infinity property and jump of one identify the bounded side,
including its signed index. No separate connectivity of a ball exterior is needed. -/
theorem order_components_by_index (γ : C(Circle, ℂ)) {P M : Set ℂ}
    (hPM : TwoComponents (range γ)ᶜ P M)
    (hjump : ∀ p ∈ P, ∀ m ∈ M, index (circleLoop γ) p - index (circleLoop γ) m = 1) :
    ∃ Ω E : Set ℂ, ∃ k : ℤ,
      ((Ω = P ∧ E = M ∧ k = 1) ∨ (Ω = M ∧ E = P ∧ k = -1)) ∧
      Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
      (∀ p ∈ E, index (circleLoop γ) p = 0) ∧
      (∀ p ∈ Ω, index (circleLoop γ) p = k) := by
  obtain ⟨hPn, hMn, hdis, hunion, hcompP, hcompM⟩ := hPM
  obtain ⟨p₀, hp₀⟩ := hPn
  obtain ⟨m₀, hm₀⟩ := hMn
  obtain ⟨R, hR, hzero⟩ := IndexProperties.index_zero_outside_ball (circleLoop γ)
  have hfar : ∀ z : ℂ, R < ‖z‖ → z ∈ P ∪ M ∧ index (circleLoop γ) z = 0 := by
    intro z hz
    refine ⟨hunion.symm ▸ ?_, (hzero z hz).2⟩
    rw [← IndexProperties.circle_trace]
    exact fun ⟨t, ht⟩ => (hzero z hz).1 t ht
  let z : ℂ := ((R + 1 : ℝ) : ℂ)
  have hz : R < ‖z‖ := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < R + 1)]
    linarith
  obtain ⟨hzPM, hz0⟩ := hfar z hz
  rcases hzPM with hzP | hzM
  · have hM : ∀ m ∈ M, index (circleLoop γ) m = -1 := by
      intro m hm
      have hh := hjump z hzP m hm
      rw [hz0] at hh
      omega
    have hP : ∀ p ∈ P, index (circleLoop γ) p = 0 := by
      intro p hp
      have hh := hjump p hp m₀ hm₀
      rw [hM m₀ hm₀] at hh
      omega
    refine ⟨M, P, -1, Or.inr ⟨rfl, rfl, rfl⟩,
      bounded_of_index_ne_zero γ (fun m hm => by rw [hM m hm]; norm_num),
      unbounded_of_contains_norm_gt (R := R) ?_, hP, hM⟩
    intro w hw
    rcases (hfar w hw).1 with hwP | hwM
    · exact hwP
    · have := hM w hwM
      rw [(hfar w hw).2] at this
      norm_num at this
  · have hP : ∀ p ∈ P, index (circleLoop γ) p = 1 := by
      intro p hp
      have hh := hjump p hp z hzM
      rwa [hz0, sub_zero] at hh
    have hM : ∀ m ∈ M, index (circleLoop γ) m = 0 := by
      intro m hm
      have hh := hjump p₀ hp₀ m hm
      rw [hP p₀ hp₀] at hh
      omega
    refine ⟨P, M, 1, Or.inl ⟨rfl, rfl, rfl⟩,
      bounded_of_index_ne_zero γ (fun p hp => by rw [hP p hp]; norm_num),
      unbounded_of_contains_norm_gt (R := R) ?_, hM, hP⟩
    intro w hw
    rcases (hfar w hw).1 with hwP | hwM
    · have := hP w hwP
      rw [(hfar w hw).2] at this
      norm_num at this
    · exact hwM

/-- Exchanging the labels leaves the assertion of exactly two components unchanged. -/
theorem twoComponents_swap {S P M : Set ℂ} (h : TwoComponents S P M) :
    TwoComponents S M P := by
  obtain ⟨hp, hm, hd, hu, hcp, hcm⟩ := h
  exact ⟨hm, hp, hd.symm, (union_comm _ _).trans hu, hcm, hcp⟩

/-- All separation, boundary, boundedness, and index conclusions. The additional
C¹ local graph conclusion is established below from the returned collar. -/
theorem topological_jordan (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ) :
    ∃ Ω E : Set ℂ,
      TwoComponents (range γ)ᶜ Ω E ∧
      IsOpen Ω ∧ IsOpen E ∧ IsPathConnected Ω ∧ IsPathConnected E ∧
      Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
      frontier Ω = range γ ∧ frontier E = range γ ∧
      closure Ω = Ω ∪ range γ ∧
      (∀ p ∈ E, index (circleLoop (regularLoopMap γ hγ)) p = 0) ∧
      (∃ k : ℤ, (k = 1 ∨ k = -1) ∧
        ∀ p ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) p = k) ∧
      (∃ v a, IsCollar γ v a ∧
        ((positiveSide γ v a ⊆ Ω ∧ negativeSide γ v a ⊆ E) ∨
          (positiveSide γ v a ⊆ E ∧ negativeSide γ v a ⊆ Ω))) := by
  let γc := regularLoopMap γ hγ
  obtain ⟨v, a, hc⟩ := Collar.collar_exists γ hγ
  obtain ⟨P, M, hPM, hPo, hMo, hPc, hMc, hp, hm, hjump⟩ := collar_components γc hγ v a hc
  obtain ⟨hPf, hMf⟩ := collar_frontiers hc hPM hPo hMo hp hm
  obtain ⟨Ω, E, k, horder, hΩb, hEb, hE0, hΩk⟩ := order_components_by_index γc hPM hjump
  rcases horder with ⟨hΩ, hE, hk⟩ | ⟨hΩ, hE, hk⟩
  · subst Ω E k
    exact ⟨P, M, hPM, hPo, hMo, hPc, hMc, hΩb, hEb, hPf, hMf,
      (closure_eq_self_union_frontier P).trans (congrArg (fun T => P ∪ T) hPf),
      hE0, ⟨1, Or.inl rfl, hΩk⟩, v, a, hc, Or.inl ⟨hp, hm⟩⟩
  · subst Ω E k
    exact ⟨M, P, twoComponents_swap hPM, hMo, hPo, hMc, hPc, hΩb, hEb, hMf, hPf,
      (closure_eq_self_union_frontier M).trans (congrArg (fun T => M ∪ T) hMf),
      hE0, ⟨-1, Or.inr rfl, hΩk⟩, v, a, hc, Or.inr ⟨hp, hm⟩⟩



theorem exists_rectangle_subset {S : Set (ℝ × ℝ)} (hS : S ∈ 𝓝 (0 : ℝ × ℝ)) :
    ∃ a : ℝ, 0 < a ∧ Ioo (-a) a ×ˢ Ioo (-a) a ⊆ S := by
  obtain ⟨a, ha, hsub⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨a, ha, fun z hz => hsub ?_⟩
  simpa [Metric.mem_ball, Prod.dist_eq, Prod.norm_def, Real.norm_eq_abs, Real.dist_eq, max_lt_iff, abs_lt] using hz

/-- The implicit function theorem plus the mean value theorem gives a one-sided
local graph, including the strict sublevel set. -/
theorem local_sublevel_graph (F : (ℝ × ℝ) → ℝ)
    (hF : ContDiffAt ℝ 1 F 0) (hzero : F 0 = 0)
    (hvert : fderiv ℝ F 0 (0, 1) = 1)
    {U : Set (ℝ × ℝ)} (hU : U ∈ 𝓝 (0 : ℝ × ℝ)) :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ ∃ f : ℝ → ℝ,
      ContDiffOn ℝ 1 f (Ioo (-b) b) ∧ f 0 = 0 ∧
      (∀ x ∈ Ioo (-b) b, f x ∈ Ioo (-c) c) ∧
      ∀ z ∈ Ioo (-b) b ×ˢ Ioo (-c) c,
        z ∈ U ∧ (F z = 0 ↔ z.2 = f z.1) ∧ (F z < 0 ↔ z.2 < f z.1) := by
  have hpartial : fderiv ℝ F 0 ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext_ring
    exact hvert
  have hinv : (fderiv ℝ F 0 ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hpartial]
    exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ ℝ)
  let f := hF.implicitFunction (by norm_num) hinv
  have hf0 : f 0 = 0 := hF.implicitFunction_apply_self (by norm_num) hinv
  have hfc : ContDiffAt ℝ 1 f 0 := hF.contDiffAt_implicitFunction (by norm_num) hinv
  have hfe : ∀ᶠ x in 𝓝 (0 : ℝ), F (x, f x) = 0 := by
    simpa only [hzero, Prod.fst_zero] using hF.eventually_apply_implicitFunction (by norm_num) hinv
  have hpos : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), 0 < fderiv ℝ F z (0, 1) := by
    have hh : ContinuousAt (fun z => fderiv ℝ F z (0, 1)) 0 :=
      (hF.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
    have h0 : 0 < fderiv ℝ F 0 (0, 1) := by rw [hvert]; norm_num
    exact hh.eventually (lt_mem_nhds h0)
  obtain ⟨a, ha, hrect⟩ := exists_rectangle_subset
    (inter_mem hU ((hF.eventually (by norm_num)).and hpos))
  have hfa : ∀ᶠ x in 𝓝 (0 : ℝ), f x ∈ Ioo (-a) a :=
    hfc.continuousAt.eventually (Ioo_mem_nhds (by simpa [hf0] using neg_neg_of_pos ha)
      (by simpa [hf0] using ha))
  obtain ⟨b', hb', hbsub⟩ := Metric.mem_nhds_iff.mp
    (hfa.and (hfe.and (hfc.eventually (by norm_num))))
  let b := min a b'
  have hb : 0 < b := lt_min ha hb'
  have hsmall (x : ℝ) (hx : x ∈ Ioo (-b) b) :
      f x ∈ Ioo (-a) a ∧ F (x, f x) = 0 ∧ ContDiffAt ℝ 1 f x := by
    apply hbsub
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    change -min a b' < x ∧ x < min a b' at hx
    constructor <;> linarith [hx.1, hx.2, min_le_right a b']
  refine ⟨b, a, hb, ha, f, (fun x hx => (hsmall x hx).2.2.contDiffWithinAt), hf0,
    (fun x hx => (hsmall x hx).1), ?_⟩
  intro z hz
  have hx : z.1 ∈ Ioo (-a) a := by
    constructor <;> linarith [hz.1.1, hz.1.2, min_le_left a b']
  have hmono : StrictMonoOn (fun y : ℝ => F (z.1, y)) (Ioo (-a) a) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro y hy
      exact ((hrect (a := (z.1, y)) ⟨hx, hy⟩).2.1.continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    · intro y hy
      have hy' : y ∈ Ioo (-a) a := interior_subset hy
      have hdiff := (hrect (a := (z.1, y)) ⟨hx, hy'⟩).2.1.differentiableAt (by norm_num)
      have hd := hdiff.hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y z.1).prodMk (hasDerivAt_id y))
      change 0 < deriv (F ∘ Prod.mk z.1) y
      rw [hd.deriv]
      exact (hrect (a := (z.1, y)) ⟨hx, hy'⟩).2.2
  have hgraph := (hsmall z.1 hz.1).2.1
  have hfy := (hsmall z.1 hz.1).1
  refine ⟨(hrect ⟨hx, hz.2⟩).1, ?_, ?_⟩
  · rw [← hgraph]
    exact hmono.injOn.eq_iff hz.2 hfy
  · rw [← hgraph]
    exact hmono.lt_iff_lt hz.2 hfy


/-- A defining function with unit transverse derivative gives the full local
one-sided graph boundary in affine linear coordinates. -/
theorem localGraphBoundary_of_coordinates {Ω : Set ℂ} {p : ℂ}
    (K : (ℝ × ℝ) ≃L[ℝ] ℂ) (r : ℂ → ℝ)
    (hr : ContDiffAt ℝ 1 r p) (hr0 : r p = 0)
    (hd : fderiv ℝ r p (K (0, 1)) = 1)
    (hlocal : ∀ᶠ z in 𝓝 p,
      (z ∈ frontier Ω ↔ r z = 0) ∧ (z ∈ Ω ↔ r z < 0)) :
    LocalGraphBoundary Ω p := by
  let A : (ℝ × ℝ) → ℂ := fun z => p + K z
  have hA : ContDiff ℝ 1 A := by dsimp [A]; fun_prop
  have hA0 : A 0 = p := by simp [A]
  let F := r ∘ A
  have hF : ContDiffAt ℝ 1 F 0 := (hA0 ▸ hr).comp 0 hA.contDiffAt
  have hzero : F 0 = 0 := by simp [F, hA0, hr0]
  have hderA : HasFDerivAt A (K : (ℝ × ℝ) →L[ℝ] ℂ) 0 := by
    simpa [A] using (K.hasFDerivAt (x := (0 : ℝ × ℝ))).const_add p
  have hdr : HasFDerivAt r (fderiv ℝ r p) (A 0) := hA0 ▸
    (hr.differentiableAt (by norm_num)).hasFDerivAt
  have hderF := hdr.comp 0
    (show HasFDerivAt A (K : (ℝ × ℝ) →L[ℝ] ℂ) 0 from hderA)
  have hvertical : fderiv ℝ F 0 (0, 1) = 1 := by
    change fderiv ℝ (r ∘ A) 0 (0, 1) = 1
    rw [hderF.fderiv]
    exact hd
  have hpre : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ),
      (A z ∈ frontier Ω ↔ r (A z) = 0) ∧ (A z ∈ Ω ↔ r (A z) < 0) := by
    have hh : Tendsto A (𝓝 0) (𝓝 p) := by
      simpa only [ContinuousAt, hA0] using hA.continuous.continuousAt (x := 0)
    exact hh.eventually hlocal
  obtain ⟨b, c, hb, hc, f, hfc, hf0, hfr, hfg⟩ := local_sublevel_graph F hF hzero hvertical hpre
  refine ⟨K.symm, b, c, hb, hc, f, hfc, hf0, hfr, ?_⟩
  intro z hz
  have heq : A (K.symm (z - p)) = z := by simp [A]
  obtain ⟨hlo, hzero', hneg⟩ := hfg (K.symm (z - p)) hz
  simpa only [heq, F, Function.comp_apply] using
    And.intro (hlo.1.trans hzero') (hlo.2.trans hneg)

/-- The genuine collar inverse supplies a C¹ defining function; its transverse
derivative is exactly one, obtained by differentiating the inverse identity. -/
theorem collar_defining_function {γ v : Circle → ℂ} {a : ℝ}
    (hc : IsCollar γ v a) (t : Circle) :
    ∃ r : ℂ → ℝ, ContDiffAt ℝ 1 r (γ t) ∧ r (γ t) = 0 ∧
      fderiv ℝ r (γ t) (v t) = 1 ∧
      ∀ᶠ z in 𝓝 (γ t),
        (z ∈ range γ ↔ r z = 0) ∧
        (z ∈ positiveSide γ v a ↔ 0 < r z) ∧
        (z ∈ negativeSide γ v a ↔ r z < 0) := by
  obtain ⟨ha, hv, ht, e, hs, he, htrace, hdiff, hinv, hdis, hpos, hneg, hpA, hnA⟩ := hc
  have hsrc (s : ℝ) (hsa : s ∈ Ioo (-a) a) : (t, s) ∈ e.source := by
    rw [hs]; exact ⟨mem_univ _, hsa⟩
  have htgt : γ t ∈ e.target := htrace ⟨t, rfl⟩
  have hzero : e.symm (γ t) = (t, 0) := by
    have hh := e.left_inv (hsrc 0 ⟨by linarith, ha⟩)
    simpa only [he, collarMap, zero_smul, add_zero] using hh
  let r : ℂ → ℝ := fun z => (e.symm z).2
  obtain ⟨g, hg, hge⟩ := hinv _ htgt
  have hr : ContDiffAt ℝ 1 r (γ t) := by
    apply hg.snd.congr_of_eventuallyEq
    filter_upwards [hge] with z hz
    exact (congrArg Prod.snd hz).symm
  have hr0 : r (γ t) = 0 := by simp [r, hzero]
  have hcurve : ∀ᶠ s in 𝓝 (0 : ℝ), r (γ t + s • v t) = s := by
    filter_upwards [Ioo_mem_nhds (by linarith : -a < (0 : ℝ)) ha] with s hs'
    have hh := e.left_inv (hsrc s hs')
    exact congrArg Prod.snd (by simpa only [he, collarMap] using hh)
  have hderline : HasDerivAt (fun s : ℝ => γ t + s • v t) (v t) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (v t)).const_add (γ t)
  have hderr : HasDerivAt (fun s : ℝ => r (γ t + s • v t))
      (fderiv ℝ r (γ t) (v t)) 0 := by
    have hh : HasFDerivAt r (fderiv ℝ r (γ t)) (γ t + (0 : ℝ) • v t) := by
      simpa using (hr.differentiableAt (by norm_num)).hasFDerivAt
    exact hh.comp_hasDerivAt 0 hderline
  have hder1 : HasDerivAt (fun s : ℝ => r (γ t + s • v t)) 1 0 :=
    (hasDerivAt_id 0).congr_of_eventuallyEq hcurve
  refine ⟨r, hr, hr0, hderr.unique hder1, ?_⟩
  filter_upwards [e.open_target.mem_nhds htgt] with z hz
  have hzsrc : e.symm z ∈ cylinder a := hs ▸ e.map_target hz
  have heq : collarMap γ v (e.symm z) = z := (he _).symm.trans (e.right_inv hz)
  have hpre (u : Circle × ℝ) (hu : u ∈ cylinder a) (hu' : collarMap γ v u = z) :
      e.symm z = u := by
    rw [← hu', ← he]
    exact e.left_inv (hs.symm ▸ hu)
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨u, rfl⟩
      have hh := hpre (u, 0) ⟨mem_univ _, by linarith, ha⟩ (by simp [collarMap])
      simp [r, hh]
    · intro hh
      exact ⟨(e.symm z).1, by simpa only [collarMap, show (e.symm z).2 = 0 from hh,
        zero_smul, add_zero] using heq⟩
  · constructor
    · rintro ⟨u, hu, hu'⟩
      have hh := hpre u ⟨mem_univ _, by linarith [hu.2.1], hu.2.2⟩ hu'
      simpa [r, hh] using hu.2.1
    · intro hh
      exact ⟨e.symm z, ⟨mem_univ _, hh, hzsrc.2.2⟩, heq⟩
  · constructor
    · rintro ⟨u, hu, hu'⟩
      have hh := hpre u ⟨mem_univ _, hu.2.1, by linarith [hu.2.2]⟩ hu'
      simpa [r, hh] using hu.2.2
    · intro hh
      exact ⟨e.symm z, ⟨mem_univ _, hzsrc.2.1, hh⟩, heq⟩


theorem hasC1Boundary_of_collar {γ v : Circle → ℂ} {a : ℝ}
    (hc : IsCollar γ v a) {Ω E : Set ℂ}
    (hcomp : TwoComponents (range γ)ᶜ Ω E)
    (hfront : frontier Ω = range γ)
    (hside : (positiveSide γ v a ⊆ Ω ∧ negativeSide γ v a ⊆ E) ∨
      (positiveSide γ v a ⊆ E ∧ negativeSide γ v a ⊆ Ω)) :
    HasC1Boundary Ω := by
  intro p hp
  obtain ⟨t, ht⟩ := hfront ▸ hp
  obtain ⟨u, hu⟩ := Ch15.CircleLift.quotientMap_surjective t
  subst t p
  obtain ⟨r, hr, hr0, hdr, hlocal⟩ := collar_defining_function hc (q u)
  have hΩoff : Ω ⊆ (range γ)ᶜ := fun z hz => hcomp.2.2.2.1 ▸ Or.inl hz
  have hd : det (deriv (realLift γ) u) (v (q u)) ≠ 0 := (hc.2.2.1 u).ne'
  rcases hside with ⟨hplus, hminus⟩ | ⟨hplus, hminus⟩
  · let K := Collar.columnEquiv (deriv (realLift γ) u) (-v (q u)) (show
        det (deriv (realLift γ) u) (-v (q u)) ≠ 0 by
          have he : det (deriv (realLift γ) u) (-v (q u)) =
              -det (deriv (realLift γ) u) (v (q u)) := by simp [det]; ring
          rw [he]; exact neg_ne_zero.mpr hd)
    apply localGraphBoundary_of_coordinates K (fun z => -r z) hr.neg (by simp [hr0])
    · have hk : K (0, 1) = -v (q u) := by
        change Collar.columnMap _ _ (0, 1) = -v (q u)
        simp
      rw [hk]
      change fderiv ℝ (-r) (γ (q u)) (-v (q u)) = 1
      rw [(hr.differentiableAt (by norm_num)).hasFDerivAt.neg.fderiv]
      simp [hdr]
    · filter_upwards [hlocal] with z hz
      refine ⟨?_, ?_⟩
      · rw [hfront, hz.1, neg_eq_zero]
      · have hmem : z ∈ Ω ↔ 0 < r z := by
          constructor
          · intro hΩ
            have hne : r z ≠ 0 := fun hh => hΩoff hΩ (hz.1.mpr hh)
            have hnonneg : ¬ r z < 0 := fun hh =>
              Set.disjoint_left.mp hcomp.2.2.1 hΩ (hminus (hz.2.2.mpr hh))
            exact lt_of_le_of_ne (le_of_not_gt hnonneg) hne.symm
          · intro hh
            exact hplus (hz.2.1.mpr hh)
        simpa only [neg_lt_zero] using hmem
  · let K := Collar.columnEquiv (deriv (realLift γ) u) (v (q u)) hd
    apply localGraphBoundary_of_coordinates K r hr hr0
    · have hk : K (0, 1) = v (q u) := by
        change Collar.columnMap _ _ (0, 1) = v (q u)
        simp
      rw [hk]
      exact hdr
    · filter_upwards [hlocal] with z hz
      refine ⟨by rw [hfront]; exact hz.1, ?_⟩
      constructor
      · intro hΩ
        have hne : r z ≠ 0 := fun hh => hΩoff hΩ (hz.1.mpr hh)
        have hnonpos : ¬ 0 < r z := fun hh =>
          Set.disjoint_left.mp hcomp.2.2.1 hΩ (hplus (hz.2.1.mpr hh))
        exact lt_of_le_of_ne (le_of_not_gt hnonpos) hne
      · intro hh
        exact hminus (hz.2.2.mpr hh)

/-- Jordan separation with the C¹ one-sided local graph boundary, under exactly
merely C¹ injectivity and regularity of the original parametrization. -/
theorem smooth_jordan : Specs.D13Unified.Ch21.SmoothJordan.smooth_jordanStatement := by
  intro γ hγ
  obtain ⟨Ω, E, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf, hcl, hiE, hiΩ,
    v, a, hc, hside⟩ := topological_jordan γ hγ
  exact ⟨Ω, E, hcomp, hΩo, hEo, hΩp, hEp, hΩb, hEb, hΩf, hEf, hcl,
    hasC1Boundary_of_collar hc hcomp hΩf hside, hiE, hiΩ⟩
end
end D13Unified.Ch21.SmoothJordan
