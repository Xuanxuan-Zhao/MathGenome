import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.SubdifferentialSum
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.BanachFenchel
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.FiniteFenchel
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Subgradients
import Mathlib.Tactic.Linarith

noncomputable section
open Set Topology
open scoped Pointwise
universe u
namespace VariationalNotes.Ch04
open VariationalNotes.ConvexAnalysis
open VariationalNotes.ConvexGeometry

section Algebra
variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

/-- Subtract a finite continuous linear functional, preserving infinite values. -/
def linearTilt (f : X → WithTop ℝ) (l : X →L[ℝ] ℝ) (z : X) : WithTop ℝ :=
  f z + ((-l z : ℝ) : WithTop ℝ)

lemma linearTilt_value (f : X → WithTop ℝ) (l : X →L[ℝ] ℝ)
    {x : X} {r : ℝ} (hx : f x = (r : WithTop ℝ)) :
    linearTilt f l x = ((r - l x : ℝ) : WithTop ℝ) := by
  simp only [linearTilt, hx, ← WithTop.coe_add, sub_eq_add_neg]

lemma effectiveDomain_linearTilt (f : X → WithTop ℝ) (l : X →L[ℝ] ℝ) :
    effectiveDomain (linearTilt f l) = effectiveDomain f := by
  ext z
  change f z + ((-l z : ℝ) : WithTop ℝ) < ⊤ ↔ f z < ⊤
  simp only [WithTop.add_lt_top, WithTop.coe_lt_top, and_true]

lemma convex_linearTilt (f : X → WithTop ℝ) (l : X →L[ℝ] ℝ)
    (hf : IsConvex f) : IsConvex (linearTilt f l) := by
  apply (convex_iff_twoPoint _).mpr
  intro x z r s hx hz a b ha hb hab
  obtain ⟨r₀, r₁, hr₀, hr₁, hr⟩ := WithTop.add_eq_coe.mp hx
  obtain ⟨s₀, s₁, hs₀, hs₁, hs⟩ := WithTop.add_eq_coe.mp hz
  have h := (convex_iff_twoPoint f).mp hf x z r₀ s₀ hr₀.symm hs₀.symm a b ha hb hab
  have hr₁' : r₁ = -l x := WithTop.coe_injective hr₁
  have hs₁' : s₁ = -l z := WithTop.coe_injective hs₁
  change f (a • x + b • z) + _ ≤ _
  apply (add_le_add h (le_refl ((-l (a • x + b • z) : ℝ) : WithTop ℝ))).trans_eq
  rw [← WithTop.coe_add]
  congr 1
  simp only [map_add, map_smul, smul_eq_mul]
  rw [← hr, ← hs, hr₁', hs₁']
  ring

lemma subdifferential_add_subset (f g : X → WithTop ℝ) (x : X) :
    subdifferential f x + subdifferential g x ⊆
      subdifferential (fun z => f z + g z) x := by
  rintro l ⟨a, ⟨r, hr, ha⟩, b, ⟨s, hs, hb⟩, rfl⟩
  refine ⟨r+s, by simp only [hr, hs, WithTop.coe_add], fun z => ?_⟩
  convert add_le_add (ha z) (hb z) using 1
  rw [← WithTop.coe_add]
  congr 1
  change r + s + (a (z-x) + b (z-x)) = _
  ring

/-- A subgradient turns the tilted primal problem into an attained finite minimum. -/
lemma linearTilt_primal_minimum (f g : X → WithTop ℝ) (x : X)
    (l : X →L[ℝ] ℝ) {r s : ℝ} (hr : f x = (r : WithTop ℝ))
    (hs : g x = (s : WithTop ℝ))
    (hl : l ∈ subdifferential (fun z => f z + g z) x) :
    (⨅ z, toEReal (linearTilt f l z + g z)) = ((r+s-l x : ℝ) : EReal) := by
  have hx : f x + g x = ((r+s : ℝ) : WithTop ℝ) := by
    simp only [hr, hs, WithTop.coe_add]
  have h := (mem_subdifferential_iff (f := fun z : X => f z + g z) (x := x) hx l).mp hl
  apply le_antisymm
  · apply iInf_le_of_le x
    rw [linearTilt_value f l hr, hs, ← WithTop.coe_add]
    exact le_of_eq (congrArg (fun t : ℝ => (t : EReal)) (by ring))
  · apply le_iInf
    intro z
    have hz := add_le_add (h z) (le_refl ((-l z : ℝ) : WithTop ℝ))
    have hz' : ((r+s-l x : ℝ) : WithTop ℝ) ≤ linearTilt f l z + g z := by
      convert hz using 1
      · rw [← WithTop.coe_add, map_sub]
        congr 1
        ring
      · simp only [linearTilt]
        ac_rfl
    exact (toEReal_conventions.2.2.2.2 _ _).mpr hz'

/-- Dual equality forces both conjugates to be finite and both Young gaps to vanish. -/
lemma subdifferential_decomposition_of_dual (f g : X → WithTop ℝ) (x : X)
    (l y : X →L[ℝ] ℝ) {r s : ℝ} (hr : f x = (r : WithTop ℝ))
    (hs : g x = (s : WithTop ℝ))
    (heq : -conjugate (linearTilt f l) (-y) - conjugate g y =
      ((r+s-l x : ℝ) : EReal)) :
    l ∈ subdifferential f x + subdifferential g x := by
  have ht := linearTilt_value f l hr
  have hflo : ((-y x - (r-l x) : ℝ) : EReal) ≤ conjugate (linearTilt f l) (-y) :=
    conjugate_finite_lower_bound (linearTilt f l) x (r-l x) ht (-y)
  have hglo : ((y x - s : ℝ) : EReal) ≤ conjugate g y :=
    conjugate_finite_lower_bound g x s hs y
  have hfbot : conjugate (linearTilt f l) (-y) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hflo
  have hgbot : conjugate g y ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hglo
  obtain ⟨a, ha⟩ : ∃ a : ℝ, conjugate (linearTilt f l) (-y) = (a : EReal) := by
    cases h : conjugate (linearTilt f l) (-y) using EReal.rec with
    | bot => exact (hfbot h).elim
    | coe a => exact ⟨a, rfl⟩
    | top =>
      have hh : (⊥ : EReal) = ((r+s-l x : ℝ) : EReal) := by
        simpa only [h, sub_eq_add_neg, EReal.neg_top, EReal.bot_add] using heq
      exact (EReal.coe_ne_bot _ hh.symm).elim
  obtain ⟨b, hb⟩ : ∃ b : ℝ, conjugate g y = (b : EReal) := by
    cases h : conjugate g y using EReal.rec with
    | bot => exact (hgbot h).elim
    | coe b => exact ⟨b, rfl⟩
    | top =>
      have hh : (⊥ : EReal) = ((r+s-l x : ℝ) : EReal) := by
        simpa only [h, sub_eq_add_neg, EReal.neg_top, EReal.add_bot] using heq
      exact (EReal.coe_ne_bot _ hh.symm).elim
  rw [ha, hb, ← EReal.coe_neg, ← EReal.coe_sub] at heq
  have hab := EReal.coe_injective heq
  rw [ha] at hflo
  rw [hb] at hglo
  have hfa := EReal.coe_le_coe_iff.mp hflo
  have hgb := EReal.coe_le_coe_iff.mp hglo
  have hae : a = -y x - (r-l x) := by linarith
  have hbe : b = y x - s := by linarith
  have hys : y ∈ subdifferential g x :=
    (subgradient_iff_conjugate_eq hs y).mpr (hb.trans (congrArg (fun t : ℝ => (t : EReal)) hbe))
  have hts : -y ∈ subdifferential (linearTilt f l) x := by
    apply (subgradient_iff_conjugate_eq ht (-y)).mpr
    simpa only [neg_apply, hae] using ha
  refine ⟨l-y, ?_, y, hys, sub_add_cancel l y⟩
  apply (mem_subdifferential_iff hr (l-y)).mpr
  intro z
  have hz := (mem_subdifferential_iff ht (-y)).mp hts z
  cases h : f z using WithTop.recTopCoe with
  | top => exact le_top
  | coe t =>
    rw [linearTilt_value f l h] at hz
    have hh := WithTop.coe_le_coe.mp hz
    apply WithTop.coe_le_coe.mpr
    simp only [neg_apply, sub_apply, map_sub] at hh ⊢
    linarith

end Algebra

/-- The Banach sum rule, using ambient norm continuity at one common finite point. -/
theorem subdifferential_sum_banach : Specs.subdifferential_sum_banach.{u} := by
  intro X _ _ _ f g hf hfc hg hgc hqual x hxf hxg
  change subdifferential (fun z => f z + g z) x = subdifferential f x + subdifferential g x
  apply Set.Subset.antisymm ?_ (subdifferential_add_subset f g x)
  intro l hl
  obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hxf
  obtain ⟨s, hs⟩ := (mem_domain_iff g x).mp hxg
  have htp : Proper (linearTilt f l) := by
    obtain ⟨z,hz⟩ := hf
    exact ⟨z, by change z ∈ effectiveDomain (linearTilt f l); rw [effectiveDomain_linearTilt]; exact hz⟩
  have htq : ∃ z : X, z ∈ effectiveDomain (linearTilt f l) ∧
      (ContinuousLinearMap.id ℝ X) z ∈ effectiveDomain g ∧
      ContinuousAt g ((ContinuousLinearMap.id ℝ X) z) := by
    change ∃ z : X, z ∈ effectiveDomain f ∧ z ∈ effectiveDomain g ∧ ContinuousAt g z at hqual
    simpa only [effectiveDomain_linearTilt, ContinuousLinearMap.id_apply] using hqual
  have hp := linearTilt_primal_minimum f g x l hr hs hl
  obtain ⟨⟨y, heq, _⟩, _⟩ := banach_fenchel (ContinuousLinearMap.id ℝ X)
    (linearTilt f l) g htp (convex_linearTilt f l hfc) hg hgc htq (r+s-l x) hp
  apply subdifferential_decomposition_of_dual f g x l y hr hs
  change -conjugate (linearTilt f l) (-(y.comp (ContinuousLinearMap.id ℝ X))) - conjugate g y = _ at heq
  simpa only [ContinuousLinearMap.comp_id] using heq

/-- Relative interiors replace ambient continuity in finite dimension. -/
theorem subdifferential_sum_finite : Specs.subdifferential_sum_finite.{u} := by
  intro X _ _ _ _ _ _ _ f g hf hfc hg hgc hqual x hxf hxg
  change subdifferential (fun z => f z + g z) x = subdifferential f x + subdifferential g x
  apply Set.Subset.antisymm ?_ (subdifferential_add_subset f g x)
  intro l hl
  obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hxf
  obtain ⟨s, hs⟩ := (mem_domain_iff g x).mp hxg
  have htp : Proper (linearTilt f l) := by
    obtain ⟨z,hz⟩ := hf
    exact ⟨z, by change z ∈ effectiveDomain (linearTilt f l); rw [effectiveDomain_linearTilt]; exact hz⟩
  have htq : ((LinearMap.id : X →ₗ[ℝ] X) '' relativeInterior (effectiveDomain (linearTilt f l)) ∩
      relativeInterior (effectiveDomain g)).Nonempty := by
    change (relativeInterior (effectiveDomain f) ∩ relativeInterior (effectiveDomain g)).Nonempty at hqual
    simpa only [effectiveDomain_linearTilt, LinearMap.id_coe, Set.image_id] using hqual
  have hp := linearTilt_primal_minimum f g x l hr hs hl
  obtain ⟨y, heq, _⟩ := finite_fenchel (LinearMap.id : X →ₗ[ℝ] X)
    (linearTilt f l) g htp (convex_linearTilt f l hfc) hg hgc htq (r+s-l x) hp
  apply subdifferential_decomposition_of_dual f g x l y hr hs
  exact heq.symm

section Indicators
variable {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]

omit [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] in
lemma effectiveDomain_indicator (C : Set X) : effectiveDomain (indicator C) = C := by
  classical
  ext z
  by_cases hz : z ∈ C <;>
    simp [effectiveDomain, ConvexAnalysis.Specs.effectiveDomain, ConvexAnalysis.indicator,
      ConvexAnalysis.Specs.indicator, hz]

omit [TopologicalSpace X] in
lemma convex_indicator (C : Set X) (hC : Convex ℝ C) : IsConvex (indicator C) := by
  classical
  apply (convex_iff_twoPoint _).mpr
  intro x z r s hx hz a b ha hb hab
  have hxi : x ∈ C := by
    by_contra hh
    simp [ConvexAnalysis.indicator, ConvexAnalysis.Specs.indicator, hh] at hx
  have hzi : z ∈ C := by
    by_contra hh
    simp [ConvexAnalysis.indicator, ConvexAnalysis.Specs.indicator, hh] at hz
  have hr : r = 0 := by
    simpa [ConvexAnalysis.indicator, ConvexAnalysis.Specs.indicator, hxi] using hx.symm
  have hs : s = 0 := by
    simpa [ConvexAnalysis.indicator, ConvexAnalysis.Specs.indicator, hzi] using hz.symm
  simp [ConvexAnalysis.indicator, ConvexAnalysis.Specs.indicator, hC hxi hzi ha hb hab, hr, hs]

omit [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] in
lemma indicator_inter (C D : Set X) :
    indicator (C ∩ D) = fun z => indicator C z + indicator D z := by
  classical
  funext z
  by_cases hc : z ∈ C <;> by_cases hd : z ∈ D <;>
    simp [ConvexAnalysis.indicator, ConvexAnalysis.Specs.indicator, hc, hd]

omit [AddCommGroup X] [Module ℝ X] in
lemma continuousAt_indicator_of_mem_nhds (D : Set X) (z : X) (hz : D ∈ 𝓝 z) :
    ContinuousAt (indicator D) z := by
  classical
  apply (continuousAt_const : ContinuousAt (fun _ : X => (0 : WithTop ℝ)) z).congr
  filter_upwards [hz] with w hw
  simp [ConvexAnalysis.indicator, ConvexAnalysis.Specs.indicator, hw]

end Indicators

/-- The indicator specialization under an ambient neighborhood qualification. -/
theorem normalCone_inter_banach : Specs.normalCone_inter_banach.{u} := by
  intro X _ _ _ C D hCn hC hDn hD hqual x hx
  have hq : ∃ z : X, z ∈ effectiveDomain (indicator C) ∧
      z ∈ effectiveDomain (indicator D) ∧ ContinuousAt (indicator D) z := by
    obtain ⟨z,hzC,hzD⟩ := hqual
    refine ⟨z, ?_, ?_, continuousAt_indicator_of_mem_nhds D z hzD⟩
    · rwa [effectiveDomain_indicator]
    · rw [effectiveDomain_indicator]
      exact mem_of_mem_nhds hzD
  have hh := subdifferential_sum_banach (indicator C) (indicator D)
    ((indicator_values C).2.2.mpr hCn) (convex_indicator C hC)
    ((indicator_values D).2.2.mpr hDn) (convex_indicator D hD) hq x
    (by change x ∈ effectiveDomain (indicator C); rw [effectiveDomain_indicator]; exact hx.1)
    (by change x ∈ effectiveDomain (indicator D); rw [effectiveDomain_indicator]; exact hx.2)
  change subdifferential (fun z => indicator C z + indicator D z) x =
    subdifferential (indicator C) x + subdifferential (indicator D) x at hh
  rw [← indicator_inter] at hh
  calc
    normalCone (C ∩ D) x = subdifferential (indicator (C ∩ D)) x :=
      (subdifferential_indicator (C ∩ D) ⟨x,hx⟩ (hC.inter hD) x hx).symm
    _ = subdifferential (indicator C) x + subdifferential (indicator D) x := hh
    _ = normalCone C x + normalCone D x :=
      congrArg₂ (fun S T : Set (X →L[ℝ] ℝ) => S + T)
        (subdifferential_indicator C hCn hC x hx.1)
        (subdifferential_indicator D hDn hD x hx.2)

/-- The indicator specialization under a relative-interior qualification. -/
theorem normalCone_inter_finite : Specs.normalCone_inter_finite.{u} := by
  intro X _ _ _ _ _ _ _ C D hCn hC hDn hD hqual x hx
  have hq : (relativeInterior (effectiveDomain (indicator C)) ∩
      relativeInterior (effectiveDomain (indicator D))).Nonempty := by
    change (relativeInterior C ∩ relativeInterior D).Nonempty at hqual
    simpa only [effectiveDomain_indicator] using hqual
  have hh := subdifferential_sum_finite (indicator C) (indicator D)
    ((indicator_values C).2.2.mpr hCn) (convex_indicator C hC)
    ((indicator_values D).2.2.mpr hDn) (convex_indicator D hD) hq x
    (by change x ∈ effectiveDomain (indicator C); rw [effectiveDomain_indicator]; exact hx.1)
    (by change x ∈ effectiveDomain (indicator D); rw [effectiveDomain_indicator]; exact hx.2)
  change subdifferential (fun z => indicator C z + indicator D z) x =
    subdifferential (indicator C) x + subdifferential (indicator D) x at hh
  rw [← indicator_inter] at hh
  calc
    normalCone (C ∩ D) x = subdifferential (indicator (C ∩ D)) x :=
      (subdifferential_indicator (C ∩ D) ⟨x,hx⟩ (hC.inter hD) x hx).symm
    _ = subdifferential (indicator C) x + subdifferential (indicator D) x := hh
    _ = normalCone C x + normalCone D x :=
      congrArg₂ (fun S T : Set (X →L[ℝ] ℝ) => S + T)
        (subdifferential_indicator C hCn hC x hx.1)
        (subdifferential_indicator D hDn hD x hx.2)

end VariationalNotes.Ch04
