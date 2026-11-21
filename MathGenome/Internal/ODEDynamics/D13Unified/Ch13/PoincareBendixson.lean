import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.PoincareBendixson
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Omega
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Orbits
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flowbox
import Mathlib.Tactic.LinearCombination

import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.OmegaSection
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch13.PoincareBendixson
open Ch11 Ch13.Nullclines Ch06.StateDerivative Ch06.C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch13.Nullclines Specs.D13Unified.Ch13.OmegaSection
open Specs.D13Unified.Ch11.OmegaTopology Specs.D13Unified.Ch11.Flow
open Ch11.Orbits

/-- The time and segment directions form a genuine linear coordinate system. -/
lemma transverse_frame (v d : Plane) (h : d.1 * v.2 - d.2 * v.1 ≠ 0) :
    ∃ A : Plane ≃L[ℝ] Plane, ∀ q, A q = q.1 • v + q.2 • d := by
  let L : Plane →ₗ[ℝ] Plane :=
    { toFun := fun q => q.1 • v + q.2 • d
      map_add' := by intros; simp [add_smul]; abel
      map_smul' := by intros; simp [smul_add, smul_smul] }
  have hi : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm ?_ bot_le
    intro q hq
    have he : q.1 • v + q.2 • d = 0 := hq
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change q.1 * v.1 + q.2 * d.1 = 0 at h₁
    change q.1 * v.2 + q.2 * d.2 = 0 at h₂
    have hq₁ : q.1 = 0 := by
      apply (mul_eq_zero.mp (show q.1 * (d.1 * v.2 - d.2 * v.1) = 0 by
        linear_combination d.1 * h₂ - d.2 * h₁)).resolve_right h
    have hq₂ : q.2 = 0 := by
      apply (mul_eq_zero.mp (show q.2 * (d.1 * v.2 - d.2 * v.1) = 0 by
        linear_combination v.2 * h₁ - v.1 * h₂)).resolve_right h
    exact Prod.ext hq₁ hq₂
  exact ⟨(LinearEquiv.ofBijective L
    ⟨hi, (LinearMap.injective_iff_surjective).mp hi⟩).toContinuousLinearEquiv,
    fun _ => rfl⟩

/-- A flowbox based on the prescribed straight section. Its inverse gives
a continuous small time that moves a nearby point onto that section. -/
lemma section_projection (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) (S : TransverseSegment F) :
    ∃ (U : Set Plane) (τ : Plane → ℝ),
      IsOpen U ∧ S.center ∈ U ∧ ContinuousAt τ S.center ∧ τ S.center = 0 ∧
      ∀ y ∈ U, (τ y, y) ∈ flowDomain F ∧
        flow F (τ y) y ∈ sectionInteriorValue S.toStraightSegment := by
  have hcenter : S.center ∈ segmentCarrierValue S.toStraightSegment := by
    exact ⟨0, ⟨by linarith [S.radius_pos], S.radius_pos.le⟩, by simp [segmentPointValue]⟩
  have hp := S.transverse.1 hcenter
  obtain ⟨A, hA⟩ := transverse_frame (F.eval S.center) S.direction
    (S.transverse.2 S.center hcenter)
  let J : ℝ →L[ℝ] Plane := (ContinuousLinearMap.id ℝ ℝ).smulRight S.direction
  let c : Plane → ℝ × Plane := fun q => (q.1, S.center + J q.2)
  let g : Plane → Plane := fun q => flow F q.1 (S.center + J q.2)
  let D : Set Plane := c ⁻¹' flowDomain F
  have hc : ContDiff ℝ 1 c :=
    contDiff_fst.prodMk (contDiff_const.add (J.contDiff.comp contDiff_snd))
  have hD : IsOpen D := (Flow.flow_regularity 1 le_rfl F hF).1.preimage hc.continuous
  have hD0 : (0,0) ∈ D := by simpa [D,c] using (Flow.flow_zero F hF _ hp).1
  have hg : ContDiffOn ℝ 1 g D :=
    (Flow.flow_regularity 1 le_rfl F hF).2.1.comp hc.contDiffOn (fun _ hq => hq)
  have hg0 : g (0,0) = S.center := by simpa [g] using (Flow.flow_zero F hF _ hp).2
  have hga := hg.contDiffAt (hD.mem_nhds hD0)
  have hcin : HasFDerivAt c
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (J.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))) (0,0) := by
    convert (hasFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ),(0 : ℝ)))).prodMk
      ((hasFDerivAt_const S.center ((0 : ℝ),(0 : ℝ))).add
        (J.hasFDerivAt.comp ((0 : ℝ),(0 : ℝ))
          (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0 : ℝ),(0 : ℝ)))))) using 1 <;> simp [c]
  have hgd : HasFDerivAt g (A : Plane →L[ℝ] Plane) (0,0) := by
    have hder := Flowbox.flow_derivative_zero F hF hp
    rw [show (0,S.center) = c (0,0) by simp [c]] at hder
    have hh := hder.comp ((0 : ℝ),(0 : ℝ)) hcin
    convert hh using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      change A q = q.1 • F.eval S.center + q.2 • S.direction
      exact hA q
  let e := hga.toOpenPartialHomeomorph g hgd (by norm_num)
  have he0 : (0,0) ∈ e.source := hga.mem_toOpenPartialHomeomorph_source hgd (by norm_num)
  let V : Set Plane := D ∩ {q | q.2 ∈ Ioo (-S.radius) S.radius}
  have hV : IsOpen V := hD.inter (isOpen_Ioo.preimage continuous_snd)
  have hV0 : (0,0) ∈ V := ⟨hD0, by exact ⟨by linarith [S.radius_pos], S.radius_pos⟩⟩
  let b := e.restrOpen V hV
  have hb0 : (0,0) ∈ b.source := ⟨he0,hV0⟩
  have hbp : S.center ∈ b.target := by rw [← hg0]; exact b.map_source hb0
  have hbinv : b.symm S.center = (0,0) := by
    rw [← hg0]; exact b.left_inv hb0
  refine ⟨b.target, (fun y => -(b.symm y).1), b.open_target, hbp, ?_, ?_, ?_⟩
  · exact ((b.continuousOn_symm.continuousAt (b.open_target.mem_nhds hbp)).fst).neg
  · simp [hbinv]
  · intro y hy
    have hq := b.map_target hy
    have hqd : c (b.symm y) ∈ flowDomain F := hq.2.1
    have hpoint : flow F (b.symm y).1 (S.center + J (b.symm y).2) = y :=
      b.right_inv hy
    have hrev := Flow.reverse_flow F hF hqd
    rw [hpoint] at hrev
    exact ⟨hrev.1, (by
      rw [hrev.2]
      exact ⟨(b.symm y).2, hq.2.2, rfl⟩)⟩

/-- A section containing only its center in an invariant set forces every
nearby point of that set onto the center's orbit. -/
lemma local_orbit (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K : Set Plane}
    (hK : Specs.D13Unified.Ch11.Invariant.invariantValue F K)
    (S : TransverseSegment F) (hS : K ∩ sectionInteriorValue S.toStraightSegment = {S.center}) :
    ∃ U : Set Plane, IsOpen U ∧ S.center ∈ U ∧
      ∀ y ∈ K ∩ U, y ∈ orbit F S.center := by
  obtain ⟨U, τ, hU, hpU, _, _, hproj⟩ := section_projection F hF S
  refine ⟨U,hU,hpU,?_⟩
  intro y hy
  obtain ⟨ht, hs⟩ := hproj y hy.2
  have he : flow F (τ y) y = S.center := by
    have hm : flow F (τ y) y ∈ K ∩ sectionInteriorValue S.toStraightSegment :=
      ⟨hK.2 y hy.1 _ ht.2,hs⟩
    simpa only [hS, mem_singleton_iff] using hm
  have hr := Flow.reverse_flow F hF ht
  rw [he] at hr
  exact ⟨-τ y, hr.1.2, hr.2⟩

/-- Late points converging to the center give arbitrarily late exact hits
when projection onto the section is confined to that center. -/
lemma late_hits (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {K : Set Plane}
    (hK : Specs.D13Unified.Ch11.Invariant.invariantValue F K)
    {y : Plane} (hy : y ∈ K)
    (S : TransverseSegment F) (hz : S.center ∈ omegaValue F y)
    (hS : K ∩ sectionInteriorValue S.toStraightSegment = {S.center}) :
    ∀ T : ℝ, ∃ t ∈ (flowInterval F y).carrier, T < t ∧ flow F t y = S.center := by
  obtain ⟨U, τ, hU, hpU, hτ, hτ0, hproj⟩ := section_projection F hF S
  obtain ⟨s, hs, hsTop, hsz⟩ := (Ch11.OmegaTopology.sequence_characterization F y S.center).mp hz
  have hnear : ∀ᶠ j in atTop, flow F (s j) y ∈ U := hsz (hU.mem_nhds hpU)
  have hsmall : ∀ᶠ j in atTop, τ (flow F (s j) y) ∈ Ioo (-1 : ℝ) 1 := by
    have hl := hτ.tendsto.comp hsz
    rw [hτ0] at hl
    exact hl (Ioo_mem_nhds (by norm_num) (by norm_num))
  intro T
  obtain ⟨j, hjU, hjτ, hjlate⟩ :=
    (hnear.and (hsmall.and (hsTop (eventually_ge_atTop (T+2))))).exists
  have ht := (hproj _ hjU).1
  have he : flow F (τ (flow F (s j) y)) (flow F (s j) y) = S.center := by
    have hyj : flow F (s j) y ∈ K := hK.2 y hy _ (hs j).1
    have hm : flow F (τ (flow F (s j) y)) (flow F (s j) y) ∈
        K ∩ sectionInteriorValue S.toStraightSegment :=
      ⟨hK.2 _ hyj _ ht.2, (hproj _ hjU).2⟩
    simpa only [hS,mem_singleton_iff] using hm
  have htr := Flow.flow_translation F hF y (hK.1 hy) (s j) (hs j).1
  have htime : τ (flow F (s j) y) + s j ∈ (flowInterval F y).carrier := by
    have hh := ht.2
    rw [htr.1] at hh
    exact hh
  refine ⟨_,htime,?_,(htr.2 _ htime).symm.trans he⟩
  change T+2 ≤ s j at hjlate
  linarith [hjτ.1]

/-- The image of a complete periodic trajectory is compact. -/
lemma compact_orbit (F : AutonomousODE Plane)
    (hF : ContDiffOn ℝ 1 F.eval F.domain) {y : Plane} (hy : y ∈ F.domain)
    (hp : HasLeastPeriod F y) : IsCompact (orbit F y) := by
  obtain ⟨hc,T,hT,hper,_⟩ := hp
  have heq : orbit F y = (fun t => flow F t y) '' Icc 0 T := by
    apply Subset.antisymm
    · rintro _ ⟨t,_,rfl⟩
      obtain ⟨r,hr,he⟩ := hper.exists_mem_Ico₀ hT t
      exact ⟨r,⟨hr.1,hr.2.le⟩,he.symm⟩
    · exact image_mono (by rw [hc]; exact subset_univ _)
  rw [heq]
  exact isCompact_Icc.image_of_continuousOn ((flow_ivp F hF hy).1.1.continuousOn.mono
    (by rw [hc]; exact subset_univ _))

/-- Conditional derivation only. The original closed target is deliberately
not declared until the two genuine upstream obligations have been closed. -/
theorem poincare_bendixson_conditional
    (_omega_section : Specs.D13Unified.Ch13.OmegaSection.OmegaSection)
    (regular_section : Specs.D13Unified.Ch13.OmegaSection.RegularSection) :
    Specs.D13Unified.Ch13.PoincareBendixson.PoincareBendixson := by
  intro F hF x hx hcompact hdomain hregular
  obtain ⟨hforward,hne,hKcompact,hKconn,hKsub,hKinv,hKcomplete,_⟩ :=
    Ch11.Omega.compact_omega F hF x hx hcompact hdomain
  let K := omegaValue F x
  obtain ⟨y,hy⟩ := hne
  have hyD := hKinv.1 hy
  have hpos : positiveOrbit F y ⊆ K := by
    rintro _ ⟨t,ht,rfl⟩
    exact (hKcomplete y hy).2 t
  have hcl : closure (positiveOrbit F y) ⊆ K :=
    closure_minimal hpos hKcompact.isClosed
  obtain ⟨_,hynonempty,_,_,hyomegaSub,_⟩ :=
    Ch11.Omega.compact_omega F hF y hyD
      (hKcompact.of_isClosed_subset isClosed_closure hcl) (hcl.trans hKinv.1)
  obtain ⟨z,hz⟩ := hynonempty
  have hzK : z ∈ K := hcl (hyomegaSub hz)
  obtain ⟨S,hSc,_,_,hS⟩ := regular_section F hF x hx hforward z (hKinv.1 hzK)
    (hregular z hzK) 1 (by norm_num)
  have hScenter : K ∩ sectionInteriorValue S.toStraightSegment = {S.center} := by
    simpa only [hSc] using hS hzK
  have hlate := late_hits F hF hKinv hy S (hSc.symm ▸ hz) hScenter
  obtain ⟨a,ha,_,hazeq⟩ := hlate 0
  obtain ⟨b,hb,hab,hbzeq⟩ := hlate a
  have hynotconstant : ¬ IsConstant F y := by
    intro he
    exact hregular y hy ((Ch11.Orbits.equilibrium_characterization F hF y hyD).mpr he)
  have hyperiod := Ch11.Orbits.self_intersection_least_period F hF y hyD hynotconstant
    a ha b hb hab.ne (hazeq.trans hbzeq.symm)
  have hΓcompact := compact_orbit F hF hyD hyperiod
  have hΓsub : orbit F y ⊆ K := by
    rintro _ ⟨t,ht,rfl⟩
    exact (hKcomplete y hy).2 t
  have hlocal : ∀ p ∈ orbit F y, ∃ U : Set Plane, IsOpen U ∧ p ∈ U ∧
      K ∩ U ⊆ orbit F y := by
    intro p hpΓ
    have hpK := hΓsub hpΓ
    obtain ⟨S,hSc,_,_,hS⟩ := regular_section F hF x hx hforward p (hKinv.1 hpK)
      (hregular p hpK) 1 (by norm_num)
    obtain ⟨U,hU,hpU,hsub⟩ := local_orbit F hF hKinv S
      (by simpa only [hSc] using hS hpK)
    have horbit : orbit F S.center = orbit F y := by
      obtain ⟨t,ht,he⟩ := hpΓ
      rw [hSc,← he]
      exact Ch11.Orbits.orbit_rebase F hF hyD ht
    exact ⟨U,hU,hSc ▸ hpU, fun q hq => horbit ▸ hsub q hq⟩
  let A : Set K := Subtype.val ⁻¹' orbit F y
  have hAclosed : IsClosed A := hΓcompact.isClosed.preimage continuous_subtype_val
  have hAopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    obtain ⟨U,hU,hpU,hsub⟩ := hlocal p.val hp
    apply Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hpU)
    intro q hq
    exact hsub ⟨q.property,hq⟩
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp hKconn
  have hyΓ : y ∈ orbit F y :=
    ⟨0,(Flow.flow_zero F hF y hyD).1.2,(Flow.flow_zero F hF y hyD).2⟩
  have hAuniv : A = univ := IsClopen.eq_univ ⟨hAclosed,hAopen⟩ ⟨⟨y,hy⟩,hyΓ⟩
  refine ⟨y,hy,hynotconstant,hyperiod,Subset.antisymm ?_ hΓsub⟩
  intro p hp
  have hm : (⟨p,hp⟩ : K) ∈ A := hAuniv.symm ▸ mem_univ _
  exact hm

end D13Unified.Ch13.PoincareBendixson

theorem _root_.«D13Unified».«Ch13».«PoincareBendixson».«poincare_bendixson» : _root_.«Specs».«D13Unified».«Ch13».«PoincareBendixson».«PoincareBendixson» :=
  @_root_.«D13Unified».«Ch13».«PoincareBendixson».«poincare_bendixson_conditional» (@_root_.«D13Unified».«Ch13».«OmegaSection».«omega_section») (@_root_.«D13Unified».«Ch13».«OmegaSection».«regular_section»)
