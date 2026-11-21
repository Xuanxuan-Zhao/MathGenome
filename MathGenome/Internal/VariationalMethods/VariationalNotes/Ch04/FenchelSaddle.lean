import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.FenchelSaddle
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Subgradients
import Mathlib.Tactic.Linarith

noncomputable section
universe u v
namespace VariationalNotes.Ch04
open VariationalNotes.ConvexAnalysis
open VariationalNotes.Ch04.Specs (fenchelPrimalObjective fenchelDualObjective finiteConjugateDomain
  fenchelLagrangian FenchelSaddle)

section
variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]

/-- Weak duality with all infinite competitors retained. -/
theorem fenchel_weak_duality (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (A : X →L[ℝ] Y) (hf : Proper f) (hg : Proper g)
    (z : X) (w : Y →L[ℝ] ℝ) :
    fenchelDualObjective f g A w ≤ fenchelPrimalObjective f g A z := by
  have hnf := conjugate_ne_bot f hf (-(w.comp A))
  have hng := conjugate_ne_bot g hg w
  cases hfw : conjugate f (-(w.comp A)) with
  | bot => exact (hnf hfw).elim
  | top =>
    change -conjugate f (-(w.comp A)) - conjugate g w ≤ _
    rw [hfw, EReal.neg_top, EReal.bot_sub]
    exact bot_le
  | coe a =>
    cases hgw : conjugate g w with
    | bot => exact (hng hgw).elim
    | top =>
      change -conjugate f (-(w.comp A)) - conjugate g w ≤ _
      rw [hgw, EReal.sub_top]
      exact bot_le
    | coe b =>
      have hd : fenchelDualObjective f g A w = ((-a - b : ℝ) : EReal) := by
        change -conjugate f (-(w.comp A)) - conjugate g w = _
        rw [hfw, hgw, ← EReal.coe_neg, ← EReal.coe_sub]
      rw [hd]
      induction hfz : f z using WithTop.recTopCoe with
      | top =>
        change _ ≤ ConvexAnalysis.Specs.toEReal (f z) + ConvexAnalysis.Specs.toEReal (g (A z))
        rw [hfz]
        change _ ≤ ⊤ + ConvexAnalysis.Specs.toEReal (g (A z))
        rw [EReal.top_add_of_ne_bot (toEReal_conventions.2.2.1 _)]
        exact le_top
      | coe r =>
        induction hgz : g (A z) using WithTop.recTopCoe with
        | top =>
          change _ ≤ ConvexAnalysis.Specs.toEReal (f z) + ConvexAnalysis.Specs.toEReal (g (A z))
          rw [hfz, hgz]
          change _ ≤ (r : EReal) + ⊤
          simp
        | coe s =>
          have h1 := conjugate_finite_lower_bound f z r hfz (-(w.comp A))
          have h2 := conjugate_finite_lower_bound g (A z) s hgz w
          rw [show ConvexAnalysis.Specs.conjugate f (-(w.comp A)) = (a : EReal) from hfw] at h1
          rw [show ConvexAnalysis.Specs.conjugate g w = (b : EReal) from hgw] at h2
          have h1' : -w (A z) - r ≤ a := EReal.coe_le_coe_iff.mp h1
          have h2' := EReal.coe_le_coe_iff.mp h2
          change _ ≤ ConvexAnalysis.Specs.toEReal (f z) + ConvexAnalysis.Specs.toEReal (g (A z))
          rw [hfz, hgz]
          change _ ≤ (r : EReal) + (s : EReal)
          rw [← EReal.coe_add]
          exact EReal.coe_le_coe_iff.mpr (by linarith)

end

/-- The certificate, saddle, and attainment theorem in the original setting. -/
theorem fenchel_certificate_saddle :
    VariationalNotes.Ch04.Specs.fenchel_certificate_saddle.{u,v} := by
  intro X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g A hfp _ _ hgp hgc hgl
    x hx hgx y hfy hgy
  obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hx
  obtain ⟨s, hs⟩ := (mem_domain_iff g (A x)).mp hgx
  obtain ⟨a, ha⟩ := hfy
  obtain ⟨b, hb⟩ := hgy
  have hyDom : y ∈ finiteConjugateDomain g := ⟨b, hb⟩
  have hP : fenchelPrimalObjective f g A x = ((r + s : ℝ) : EReal) := by
    change ConvexAnalysis.Specs.toEReal (f x) + ConvexAnalysis.Specs.toEReal (g (A x)) = _
    rw [hr, hs]
    exact (EReal.coe_add r s).symm
  have hD : fenchelDualObjective f g A y = ((-a - b : ℝ) : EReal) := by
    change -ConvexAnalysis.Specs.conjugate f (-(y.comp A)) - ConvexAnalysis.Specs.conjugate g y = _
    rw [ha, hb, ← EReal.coe_neg, ← EReal.coe_sub]
  have h1 : -y (A x) - r ≤ a := by
    have h := conjugate_finite_lower_bound f x r hr (-(y.comp A))
    rw [ha] at h
    exact EReal.coe_le_coe_iff.mp h
  have h2 : y (A x) - s ≤ b := by
    have h := conjugate_finite_lower_bound g (A x) s hs y
    rw [hb] at h
    exact EReal.coe_le_coe_iff.mp h
  have hF : (-(y.comp A)) ∈ subdifferential f x ↔ a = -y (A x) - r := by
    rw [subgradient_iff_conjugate_eq hr]
    change ConvexAnalysis.Specs.conjugate f (-(y.comp A)) = ((-y (A x) - r : ℝ) : EReal) ↔ _
    rw [ha, EReal.coe_eq_coe_iff]
  have hG : y ∈ subdifferential g (A x) ↔ b = y (A x) - s := by
    rw [subgradient_iff_conjugate_eq hs]
    change ConvexAnalysis.Specs.conjugate g y = ((y (A x) - s : ℝ) : EReal) ↔ _
    rw [hb, EReal.coe_eq_coe_iff]
  have gap_iff :
      (fenchelPrimalObjective f g A x = fenchelDualObjective f g A y) ↔
      ((-(y.comp A)) ∈ subdifferential f x ∧ y ∈ subdifferential g (A x)) := by
    rw [hP, hD, EReal.coe_eq_coe_iff, hF, hG]
    constructor
    · intro h
      constructor <;> linarith
    · rintro ⟨h, k⟩
      linarith
  have lag_value (z : X) (w : Y →L[ℝ] ℝ) (t c : ℝ)
      (hz : f z = (t : WithTop ℝ)) (hw : conjugate g w = (c : EReal)) :
      fenchelLagrangian f g A z w = t + w (A z) - c := by
    change (f z).untopD 0 + w (A z) - (conjugate g w).toReal = _
    rw [hz, hw, WithTop.untopD_coe, EReal.toReal_coe]
  have saddle_iff :
      ((-(y.comp A)) ∈ subdifferential f x ∧ y ∈ subdifferential g (A x)) ↔
      FenchelSaddle f g A x y := by
    constructor
    · rintro ⟨hfsub, hgsub⟩ z hz w hw
      obtain ⟨t, ht⟩ := (mem_domain_iff f z).mp hz
      obtain ⟨c, hc⟩ := hw
      have hfs := (mem_subdifferential_iff hr (-(y.comp A))).mp hfsub z
      have hfs' : r + (-y (A z) + y (A x)) ≤ t := by
        rw [ht] at hfs
        simpa only [neg_apply, ContinuousLinearMap.comp_apply,
          map_sub, neg_sub, sub_neg_eq_add] using WithTop.coe_le_coe.mp hfs
      have hgs := (subgradient_iff_pairing_subgradient g hgp hgc hgl (A x) hgx y).mp hgsub
      obtain ⟨d, hd, hsupport⟩ := hgs
      have hdb : d = b := EReal.coe_injective (hd.symm.trans hb)
      have hsup := hsupport w
      rw [hc] at hsup
      have hsup' : b + (w (A x) - y (A x)) ≤ c := by
        simpa only [hdb, sub_apply] using EReal.coe_le_coe_iff.mp hsup
      rw [lag_value x w r c hr hc, lag_value x y r b hr hb, lag_value z y t b ht hb]
      constructor <;> linarith
    · intro h
      constructor
      · apply (mem_subdifferential_iff hr (-(y.comp A))).mpr
        intro z
        induction hz : f z using WithTop.recTopCoe with
        | top => exact le_top
        | coe t =>
          have hzDom := (mem_domain_iff f z).mpr ⟨t, hz⟩
          have hright := (h z hzDom y hyDom).2
          rw [lag_value x y r b hr hb, lag_value z y t b hz hb] at hright
          apply WithTop.coe_le_coe.mpr
          change r + (-(y.comp A)) (z - x) ≤ t
          simp only [neg_apply, ContinuousLinearMap.comp_apply,
            map_sub]
          linarith
      · apply (subgradient_iff_pairing_subgradient g hgp hgc hgl (A x) hgx y).mpr
        refine ⟨b, hb, ?_⟩
        intro w
        have hn := conjugate_ne_bot g hgp w
        cases hw : conjugate g w with
        | bot => exact (hn hw).elim
        | top =>
          change _ ≤ conjugate g w
          rw [hw]
          exact le_top
        | coe c =>
          have hleft := (h x hx w ⟨c, hw⟩).1
          rw [lag_value x w r c hr hw, lag_value x y r b hr hb] at hleft
          change _ ≤ conjugate g w
          rw [hw]
          apply EReal.coe_le_coe_iff.mpr
          rw [sub_apply]
          linarith
  refine ⟨gap_iff, saddle_iff, ?_⟩
  intro h
  have hgap : fenchelPrimalObjective f g A x = fenchelDualObjective f g A y := by
    rcases h with h | h | h
    · exact h
    · exact gap_iff.mpr h
    · exact gap_iff.mpr (saddle_iff.mpr h)
  have hmin : ∀ z, fenchelPrimalObjective f g A x ≤ fenchelPrimalObjective f g A z := by
    intro z
    rw [hgap]
    exact fenchel_weak_duality f g A hfp hgp z y
  have hmax : ∀ w, fenchelDualObjective f g A w ≤ fenchelDualObjective f g A y := by
    intro w
    rw [← hgap]
    exact fenchel_weak_duality f g A hfp hgp x w
  exact ⟨hmin, hmax, le_antisymm (iInf_le _ x) (le_iInf hmin),
    le_antisymm (iSup_le hmax) (le_iSup _ y)⟩

end VariationalNotes.Ch04
