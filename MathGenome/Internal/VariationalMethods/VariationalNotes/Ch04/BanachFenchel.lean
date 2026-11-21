import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.BanachFenchel
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.PerturbationAlgebra
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.LocalValueSupport

noncomputable section
open Set Topology
universe u v
namespace VariationalNotes.Ch04
open VariationalNotes.ConvexAnalysis

section Perturbation
variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Convexity of the actual composition perturbation, with no finiteness
assumption away from the two candidates. -/
theorem fenchelPerturbation_convex (A : X →L[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (hf : IsConvex f) (hg : IsConvex g) :
    IsConvex (fun q : X × Y => f q.1 + g (A q.1 + q.2)) := by
  apply (convex_iff_twoPoint _).mpr
  intro q w r s hq hw a b ha hb hab
  obtain ⟨r₁, r₂, hr₁, hr₂, hr⟩ := WithTop.add_eq_coe.mp hq
  obtain ⟨s₁, s₂, hs₁, hs₂, hs⟩ := WithTop.add_eq_coe.mp hw
  have h₁ := (convex_iff_twoPoint f).mp hf q.1 w.1 r₁ s₁
    hr₁.symm hs₁.symm a b ha hb hab
  have h₂ := (convex_iff_twoPoint g).mp hg (A q.1 + q.2) (A w.1 + w.2)
    r₂ s₂ hr₂.symm hs₂.symm a b ha hb hab
  have heq : A (a • q.1 + b • w.1) + (a • q.2 + b • w.2) =
      a • (A q.1 + q.2) + b • (A w.1 + w.2) := by
    simp only [map_add, map_smul, smul_add]
    abel
  change f (a • q.1 + b • w.1) +
    g (A (a • q.1 + b • w.1) + (a • q.2 + b • w.2)) ≤ _
  rw [heq]
  convert add_le_add h₁ h₂ using 1
  rw [← WithTop.coe_add]
  congr 1
  rw [← hr, ← hs]
  ring

/-- Changing variables to `z = Ax + u` separates the two conjugate suprema.
The proof compares finite candidates, so no ambiguous arithmetic with
opposite infinities is used. -/
theorem fenchelPerturbation_conjugate (A : X →L[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ) (y : Y →L[ℝ] ℝ) :
    conjugate (fun q : X × Y => f q.1 + g (A q.1 + q.2))
      (y.comp (ContinuousLinearMap.snd ℝ X Y)) =
      conjugate f (-(y.comp A)) + conjugate g y := by
  apply le_antisymm
  · apply iSup₂_le
    intro q hq
    have hfin : f q.1 < ⊤ ∧ g (A q.1 + q.2) < ⊤ := WithTop.add_lt_top.mp hq
    obtain ⟨r, hr⟩ := (mem_domain_iff f q.1).mp hfin.1
    obtain ⟨s, hs⟩ := (mem_domain_iff g (A q.1 + q.2)).mp hfin.2
    have h₁ := conjugate_finite_lower_bound f q.1 r hr (-(y.comp A))
    have h₂ := conjugate_finite_lower_bound g (A q.1 + q.2) s hs y
    convert add_le_add h₁ h₂ using 1
    · simp only [hr, hs, ← WithTop.coe_add, WithTop.untopD_coe,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
        neg_apply, map_add, ← EReal.coe_add]
      congr 1
      ring
    · rfl
  · apply EReal.add_le_of_forall_lt
    intro a ha b hb
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp ha
    obtain ⟨hxf, hxa⟩ := lt_iSup_iff.mp hx
    obtain ⟨z, hz⟩ := lt_iSup_iff.mp hb
    obtain ⟨hzg, hzb⟩ := lt_iSup_iff.mp hz
    obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hxf
    obtain ⟨s, hs⟩ := (mem_domain_iff g z).mp hzg
    have hval : (fun q : X × Y => f q.1 + g (A q.1 + q.2)) (x, z - A x) =
        ((r + s : ℝ) : WithTop ℝ) := by
      simp only [add_sub_cancel, hr, hs, ← WithTop.coe_add]
    have h := conjugate_finite_lower_bound
      (fun q : X × Y => f q.1 + g (A q.1 + q.2)) (x, z - A x) (r + s) hval
      (y.comp (ContinuousLinearMap.snd ℝ X Y))
    apply (add_le_add hxa.le hzb.le).trans
    convert h using 1
    · simp only [hr, hs, WithTop.untopD_coe, neg_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
        map_sub, ← EReal.coe_add]
      congr 1
      ring
    · rfl

/-- Ambient continuity at a common finite candidate bounds the value
function on a full ball of perturbations. -/
theorem fenchelPerturbation_local_bound (A : X →L[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (x₀ : X) (hxf : x₀ ∈ effectiveDomain f)
    (hxg : A x₀ ∈ effectiveDomain g) (hcont : ContinuousAt g (A x₀)) :
    ∃ r M : ℝ, 0 < r ∧ ∀ u : Y, ‖u‖ < r →
      marginal (fun q : X × Y => f q.1 + g (A q.1 + q.2)) u ≤ (M : EReal) := by
  obtain ⟨a, ha⟩ := (mem_domain_iff f x₀).mp hxf
  obtain ⟨b, hb⟩ := (mem_domain_iff g (A x₀)).mp hxg
  have hU : {z : Y | g z < ((b + 1 : ℝ) : WithTop ℝ)} ∈ 𝓝 (A x₀) :=
    hcont.preimage_mem_nhds (Iio_mem_nhds (by
      rw [hb]
      exact WithTop.coe_lt_coe.mpr (by linarith)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r, a + (b + 1), hr, fun u hu => ?_⟩
  have hgu : g (A x₀ + u) ≤ ((b + 1 : ℝ) : WithTop ℝ) :=
    (hball (by simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hu)).le
  apply (marginal_le_candidate _ x₀ u).trans
  apply (toEReal_conventions.2.2.2.2 _ _).mpr
  change f x₀ + g (A x₀ + u) ≤ _
  rw [ha, WithTop.coe_add]
  exact add_le_add le_rfl hgu

/-- The sign and adjoint conventions in the manuscript's dual objective. -/
theorem fenchelPerturbation_dualObjective (A : X →L[ℝ] Y)
    (f : X → WithTop ℝ) (g : Y → WithTop ℝ)
    (hf : Proper f) (hg : Proper g) (y : Y →L[ℝ] ℝ) :
    perturbationDualObjective (fun q : X × Y => f q.1 + g (A q.1 + q.2)) y =
      -conjugate f (-(y.comp A)) - conjugate g y := by
  change -conjugate (fun q : X × Y => f q.1 + g (A q.1 + q.2))
    (y.comp (ContinuousLinearMap.snd ℝ X Y)) = _
  have hfb : conjugate f (-(y.comp A)) ≠ ⊥ := conjugate_ne_bot f hf _
  have hgb : conjugate g y ≠ ⊥ := conjugate_ne_bot g hg _
  rw [fenchelPerturbation_conjugate, EReal.neg_add (Or.inl hfb) (Or.inr hgb)]

end Perturbation

/-- Banach-space Fenchel duality with a maximizing continuous functional.
Only the primal infimum, rather than a minimizing point, is assumed finite. -/
theorem banach_fenchel : Specs.banach_fenchel.{u,v} := by
  intro X Y _ _ _ _ _ _ A f g hf hfc hg hgc hqual p hp
  obtain ⟨x₀, hxf, hxg, hcont⟩ := hqual
  let Φ : X × Y → WithTop ℝ := fun q => f q.1 + g (A q.1 + q.2)
  have hΦc : IsConvex Φ := fenchelPerturbation_convex A f g hfc hgc
  have hΦp : Proper Φ := by
    refine ⟨(x₀, 0), ?_⟩
    change f x₀ + g (A x₀ + 0) < ⊤
    rw [add_zero, WithTop.add_lt_top]
    exact ⟨hxf, hxg⟩
  have h0 : marginal Φ 0 = (p : EReal) := by
    change (⨅ x : X, ConvexAnalysis.Specs.toEReal (f x + g (A x + 0))) = _
    simpa only [add_zero] using hp
  obtain ⟨r, M, hr, hM⟩ := fenchelPerturbation_local_bound A f g x₀ hxf hxg hcont
  obtain ⟨hnb, _, y, hy⟩ := local_value_support Φ hΦp hΦc p r M h0 hr hM
  have hatt := perturbation_attainment Φ p hnb h0 y
  have heq : perturbationDualObjective Φ y = (p : EReal) :=
    (hatt.1.mpr (hatt.2.mpr hy)).1
  have hbound : ∀ z : Y →L[ℝ] ℝ,
      -conjugate f (-(z.comp A)) - conjugate g z ≤ (p : EReal) := by
    intro z
    rw [← fenchelPerturbation_dualObjective A f g hf hg z]
    exact (perturbation_dual_bound Φ p h0).2.2.2 z
  have hyval : -conjugate f (-(y.comp A)) - conjugate g y = (p : EReal) := by
    rw [← fenchelPerturbation_dualObjective A f g hf hg y]
    exact heq
  refine ⟨⟨y, hyval, hbound⟩, le_antisymm (iSup_le hbound) ?_⟩
  rw [← hyval]
  exact le_iSup (fun z : Y →L[ℝ] ℝ => -conjugate f (-(z.comp A)) - conjugate g z) y

end VariationalNotes.Ch04
