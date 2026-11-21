import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.ReturnMap
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.ReturnBranch
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Orbits

/-! The near-period implicit branch is upstream. Here compactness excludes
all middle hits, and the time-zero implicit branch excludes early hits.
Together with near-period uniqueness these give a genuine first return. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch14.ReturnMap
open Ch06.StateDerivative Ch06.C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Leastness of the period rules out every intermediate return to p. -/
lemma no_intermediate_return (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    (hc : Ch11.Orbits.IsComplete F p) {T : ℝ}
    (hmin : ∀ R : ℝ, 0 < R → Function.Periodic (fun t => flow F t p) R → T ≤ R)
    {t : ℝ} (ht : 0 < t) (htT : t < T) : flow F t p ≠ p := by
  intro he
  have hti : t ∈ (flowInterval F p).carrier := by rw [hc]; trivial
  have hper := (Ch11.Orbits.complete_of_positive_return F hF hp ht hti he).2
  exact (not_le_of_gt htT) (hmin t ht hper)

/-- Uniform short-time exclusion on the specified affine transverse section.
The scalar implicit function theorem at time zero is an alternative proof
of the flowbox's one-crossing property. -/
lemma early_crossings (k : ℕ) (hk : 1 ≤ k) (F : AutonomousODE E)
    (hF : ContDiffOn ℝ k F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    (ℓ : E →L[ℝ] ℝ) (ha : ℓ (F.eval p) ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∃ A : Set ℓ.ker, IsOpen A ∧ (0 : ℓ.ker) ∈ A ∧
      ∀ v ∈ A, ∀ t ∈ Ioo (-a) a,
        (t, p + (v : E)) ∈ flowDomain F ∧
        (ℓ (flow F t (p + (v : E)) - p) = 0 ↔ t = 0) := by
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hzero := Ch11.Flow.flow_zero F hF1 p hp
  obtain ⟨τ, _, _, hpair, _, _⟩ :=
    ReturnBranch.implicit_return_time k hk F hF hp hzero.1.2 hzero.2 ℓ ha
  rw [nhds_prod_eq] at hpair
  obtain ⟨V,hV,J,hJ,hVJ⟩ := Filter.mem_prod_iff.mp hpair
  obtain ⟨A,hAV,hAo,h0A⟩ := mem_nhds_iff.mp hV
  obtain ⟨a,ha0,haJ⟩ := Metric.mem_nhds_iff.mp hJ
  have htime {t : ℝ} (ht : t ∈ Ioo (-a) a) : t ∈ J := by
    apply haJ
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using abs_lt.mpr ht
  refine ⟨a,ha0,A,hAo,h0A,?_⟩
  intro v hv t ht
  have h0 := hVJ (show (v,0) ∈ V ×ˢ J from ⟨hAV hv, htime ⟨by linarith,ha0⟩⟩)
  have hz : τ v = 0 := by
    have he := (Ch11.Flow.flow_zero F hF1 (p + (v : E)) h0.1.1).2
    apply Eq.symm
    apply h0.2.mp
    simp [he, show ℓ (v : E) = 0 from v.property]
  have h := hVJ (show (v,t) ∈ V ×ˢ J from ⟨hAV hv,htime ht⟩)
  exact ⟨h.1, by simpa only [hz] using h.2⟩

/-- Every nearby initial state has the whole given compact time interval in
its actual flow domain. This is the compact form of openness of the domain. -/
lemma compact_domain (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    (hc : Ch11.Orbits.IsComplete F p) (ℓ : E →L[ℝ] ℝ)
    {K : Set ℝ} (hK : IsCompact K) :
    ∀ᶠ v : ℓ.ker in 𝓝 0, ∀ t ∈ K, (t, p + (v : E)) ∈ flowDomain F := by
  apply hK.eventually_forall_of_forall_eventually
  intro t ht
  have hdom : (t,p) ∈ flowDomain F := ⟨hp,by rw [hc]; trivial⟩
  have hreg := Ch11.Flow.flow_regularity 1 (by omega) F hF
  have hc' : Continuous (fun q : ℓ.ker × ℝ => (q.2,p + (q.1 : E))) :=
    continuous_snd.prodMk (continuous_const.add (ℓ.ker.subtypeL.continuous.comp continuous_fst))
  have he := (hc'.continuousAt (x := ((0 : ℓ.ker),t))).preimage_mem_nhds
    (hreg.1.mem_nhds (by simpa using hdom))
  exact he

/-- A compact orbit arc avoiding p stays away from a fixed small section for
all nearby initial states. Both the starting and section points vary. -/
lemma compact_no_crossings (F : AutonomousODE E)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {p : E} (hp : p ∈ F.domain)
    (hc : Ch11.Orbits.IsComplete F p) (ℓ : E →L[ℝ] ℝ)
    {K : Set ℝ} (hK : IsCompact K) (havoid : ∀ t ∈ K, flow F t p ≠ p) :
    ∃ V W : Set ℓ.ker, IsOpen V ∧ IsOpen W ∧ (0 : ℓ.ker) ∈ V ∧
      (0 : ℓ.ker) ∈ W ∧ ∀ v ∈ V, ∀ w ∈ W, ∀ t ∈ K,
        flow F t (p + (v : E)) ≠ p + (w : E) := by
  have hreg := Ch11.Flow.flow_regularity 1 (by omega) F hF
  have he : ∀ᶠ q : ℓ.ker × ℓ.ker in 𝓝 (0,0),
      ∀ t ∈ K, flow F t (p + (q.1 : E)) ≠ p + (q.2 : E) := by
    apply hK.eventually_forall_of_forall_eventually
    intro t ht
    have hdom : (t,p) ∈ flowDomain F := ⟨hp,by rw [hc]; trivial⟩
    have hg : ContinuousAt (fun q : (ℓ.ker × ℓ.ker) × ℝ =>
        flow F q.2 (p + (q.1.1 : E))) ((0,0),t) := by
      have hi : ContinuousAt (fun q : (ℓ.ker × ℓ.ker) × ℝ =>
          (q.2,p + (q.1.1 : E))) ((0,0),t) :=
        continuous_snd.continuousAt.prodMk (continuous_const.add
          (ℓ.ker.subtypeL.continuous.comp (continuous_fst.comp continuous_fst))).continuousAt
      have hf : ContinuousAt (fun q : ℝ × E => flow F q.1 q.2)
          (t,p + ((0 : ℓ.ker) : E)) := by
        simpa only [ZeroMemClass.coe_zero, add_zero] using
          hreg.2.1.continuousOn.continuousAt (hreg.1.mem_nhds hdom)
      exact hf.comp (f := fun q : (ℓ.ker × ℓ.ker) × ℝ =>
        (q.2,p + (q.1.1 : E))) hi
    have hh : ContinuousAt (fun q : (ℓ.ker × ℓ.ker) × ℝ =>
        p + (q.1.2 : E)) ((0,0),t) :=
      (continuous_const.add
        (ℓ.ker.subtypeL.continuous.comp (continuous_snd.comp continuous_fst))).continuousAt
    have hne : flow F t (p + ((0 : ℓ.ker) : E)) ≠ p + ((0 : ℓ.ker) : E) :=
      by simpa using havoid t ht
    simpa only [Pi.sub_apply, sub_ne_zero] using (hg.sub hh).eventually_ne (sub_ne_zero.mpr hne)
  rw [nhds_prod_eq] at he
  obtain ⟨V',hV',W',hW',hVW⟩ := Filter.mem_prod_iff.mp he
  obtain ⟨V,hVV,hVo,h0V⟩ := mem_nhds_iff.mp hV'
  obtain ⟨W,hWW,hWo,h0W⟩ := mem_nhds_iff.mp hW'
  exact ⟨V,W,hVo,hWo,h0V,h0W,fun v hv w hw t ht =>
    hVW (show (v,w) ∈ V' ×ˢ W' from ⟨hVV hv,hWW hw⟩) t ht⟩

/-- The complete local first-return theorem. Restrictions of the upstream
partial homeomorphism preserve its actual representatives and derivatives. -/
theorem return_map : Specs.D13Unified.Ch14.ReturnMap.ReturnMapExpected.{u} := by
  intro E _ _ _ k hk F hF p hp T hT hc hperiod hmin _ ℓ ha S₀ hS₀ h0S₀ ε hε
  have hF1 : ContDiffOn ℝ 1 F.eval F.domain := hF.of_le (by exact_mod_cast hk)
  have hTI : T ∈ (flowInterval F p).carrier := by rw [hc]; trivial
  have hr : flow F T p = p := by
    simpa only [zero_add] using
      (hperiod 0).trans (Ch11.Flow.flow_zero F hF1 p hp).2
  let ε' := min ε (min (T/4) 1)
  have hε' : 0 < ε' := lt_min hε (lt_min (by positivity) zero_lt_one)
  obtain ⟨δ,hδ,hδε,τ,P,h0P,h0Pt,_,_,_,_,hτ0,hP0,hτcd,hPcd,hPicd,
      hτnear,_,hformula,hunique,hτder,hPder⟩ :=
    ReturnBranch.return_branch k hk F hF p hp T hTI hr ℓ ha univ isOpen_univ
      (mem_univ _) ε' hε'
  have hδε₀ : δ < ε := hδε.trans_le (min_le_left _ _)
  have hδquarter : δ < T/4 := hδε.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδT : δ < T := by linarith
  have hδone : δ < 1 := hδε.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨a,ha0,A,hAo,h0A,hearly⟩ := early_crossings k hk F hF hp ℓ ha
  let K := Icc (a/2) (T-δ/2)
  have havoid : ∀ t ∈ K, flow F t p ≠ p := by
    intro t ht
    exact no_intermediate_return F hF1 hp hc hmin (by linarith [ht.1]) (by linarith [ht.2])
  obtain ⟨V,W,hVo,hWo,h0V,h0W,hmiddle⟩ :=
    compact_no_crossings F hF1 hp hc ℓ isCompact_Icc havoid
  obtain ⟨B,hBsub,hBo,h0B⟩ := mem_nhds_iff.mp
    (compact_domain F hF1 hp hc ℓ (K := Icc 0 (T+1)) isCompact_Icc)
  let D : Set ℓ.ker := {v | p + (v : E) ∈ F.domain}
  have hDo : IsOpen D := F.isOpen_domain.preimage
    (continuous_const.add ℓ.ker.subtypeL.continuous)
  have h0D : (0 : ℓ.ker) ∈ D := by simpa [D] using hp
  have heval : ContinuousAt (fun v : ℓ.ker => F.eval (p + (v : E))) 0 := by
    have hf : ContinuousAt F.eval p := hF1.continuousOn.continuousAt
      (F.isOpen_domain.mem_nhds hp)
    exact hf.comp_of_eq (continuous_const.add ℓ.ker.subtypeL.continuous).continuousAt
      (by simp)
  have hvel : ContinuousAt (fun v : ℓ.ker => ℓ (F.eval (p + (v : E)))) 0 :=
    ℓ.continuous.continuousAt.comp (f := fun v : ℓ.ker => F.eval (p + (v : E))) heval
  obtain ⟨C,hCsub,hCo,h0C⟩ := mem_nhds_iff.mp
    (hvel.eventually_ne (show ℓ (F.eval (p + ((0 : ℓ.ker) : E))) ≠ 0 by simpa [AutonomousODE.eval] using ha))
  let S := S₀ ∩ W ∩ (D ∩ C)
  have hSo : IsOpen S := (hS₀.inter hWo).inter (hDo.inter hCo)
  have h0S : (0 : ℓ.ker) ∈ S := ⟨⟨h0S₀,h0W⟩,h0D,h0C⟩
  let U := S ∩ A ∩ V ∩ B
  have hUo : IsOpen U := ((hSo.inter hAo).inter hVo).inter hBo
  have h0U : (0 : ℓ.ker) ∈ U := ⟨⟨⟨h0S,h0A⟩,h0V⟩,h0B⟩
  let Q := (P.symm.restrOpen S hSo).symm
  let P' := Q.restrOpen U hUo
  have hP'eq : (P' : ℓ.ker → ℓ.ker) = P := rfl
  have hP'ieq : (P'.symm : ℓ.ker → ℓ.ker) = P.symm := rfl
  have h0P' : (0 : ℓ.ker) ∈ P'.source := by
    change 0 ∈ (P.source ∩ P ⁻¹' S) ∩ U
    exact ⟨⟨h0P,by change P 0 ∈ S; rw [hP0]; exact h0S⟩,h0U⟩
  have hP'0 : P' 0 = 0 := hP0
  have h0P't : (0 : ℓ.ker) ∈ P'.target := hP'0 ▸ P'.map_source h0P'
  have hsrc : P'.source ⊆ P.source := fun v hv => hv.1.1
  have htgt : P'.target ⊆ P.target := fun v hv => hv.1.1
  have hsrcU : P'.source ⊆ U := fun v hv => hv.2
  have hsrcS : P'.source ⊆ S := fun v hv => (hsrcU hv).1.1.1
  have htgtS : P'.target ⊆ S := fun v hv => hv.1.2
  refine ⟨{
    sectionSet := S
    section_open := hSo
    section_zero := h0S
    section_domain := fun v hv => hv.2.1
    section_transverse := fun v hv => hCsub hv.2.2
    δ := δ
    δ_pos := hδ
    δ_lt_period := hδT
    τ := τ
    P := P'
    source_zero := h0P'
    target_zero := h0P't
    source_section := hsrcS
    target_section := htgtS
    time_zero := hτ0
    map_zero := hP'0
    time_regular := hτcd.mono hsrc
    map_regular := by rw [hP'eq]; exact hPcd.mono hsrc
    inverse_regular := by rw [hP'ieq]; exact hPicd.mono htgt
    time_positive := fun v hv => (sub_pos.mpr hδT).trans (hτnear v (hsrc hv)).1
    time_near := fun v hv => hτnear v (hsrc hv)
    flow_domain := ?_
    map_formula := ?_
    unique_near := fun v hv t ht => hunique v (hsrc hv) t ht
    first_return := ?_
    time_derivative := hτder
    map_derivative := by rw [hP'eq]; exact hPder
  },fun v hv => hv.1.1,hδε₀⟩
  · intro v hv t ht
    exact hBsub (hsrcU hv).2 t ⟨ht.1,by linarith [ht.2]⟩
  · intro v hv
    exact hformula v (hsrc hv)
  · intro v hv t ht0 htt hhit
    obtain ⟨w,hw,he⟩ := hhit
    have hroot : ℓ (flow F t (p + (v : E)) - p) = 0 := by
      rw [← he]
      simp [show ℓ (w : E) = 0 from w.property]
    by_cases hta : t < a
    · have he0 := (hearly v (hsrcU hv).1.1.2 t ⟨by linarith,hta⟩).2.mp hroot
      linarith
    · by_cases htend : T-δ < t
      · have heτ := (hunique v (hsrc hv) t ⟨htend,
          htt.trans (hτnear v (hsrc hv)).2⟩).mp hroot
        exact (ne_of_lt htt) heτ
      · apply hmiddle v (hsrcU hv).1.2 w hw.1.2 t
          (show t ∈ K from ⟨by linarith,by linarith⟩)
        exact he.symm

end D13Unified.Ch14.ReturnMap
