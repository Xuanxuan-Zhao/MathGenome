import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Conjugates
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.Separation
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ConjugateSetNorm

noncomputable section
open Set
universe u
namespace VariationalNotes.ConvexAnalysis

theorem conjugate_indicator : Specs.conjugate_indicator.{u} := by
  intro X _ _ _ C hC y
  classical
  apply le_antisymm
  · apply iSup₂_le
    intro x hx
    have hmem : x ∈ C := by
      by_contra hn
      simp [Specs.effectiveDomain, Specs.indicator, hn] at hx
    simpa [Specs.indicator, hmem, ConvexGeometry.Specs.supportFunction] using
      (le_iSup₂ (f := fun x (_ : x ∈ C) => (y x : EReal)) x hmem)
  · apply iSup₂_le
    intro x hx
    have hdom : x ∈ Specs.effectiveDomain (Specs.indicator C) := by
      simp [Specs.effectiveDomain, Specs.indicator, hx]
    simpa [Specs.indicator, hx, Specs.conjugate] using
      (le_iSup₂ (f := fun x (_ : x ∈ Specs.effectiveDomain (Specs.indicator C)) =>
        ((y x - (Specs.indicator C x).untopD 0 : ℝ) : EReal)) x hdom)

private theorem supportFunction_zero {X : Type u} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] (C : Set X) (hC : C.Nonempty) :
    ConvexGeometry.Specs.supportFunction C (0 : X →L[ℝ] ℝ) = 0 := by
  apply le_antisymm
  · apply iSup₂_le
    intro x hx
    simp
  · obtain ⟨x, hx⟩ := hC
    simpa [ConvexGeometry.Specs.supportFunction] using (le_iSup₂ (f := fun x (_ : x ∈ C) =>
      (((0 : X →L[ℝ] ℝ) x) : EReal)) x hx)

theorem conjugate_supportFunction : Specs.conjugate_supportFunction.{u} := by
  intro X _ _ _ _ _ _ _ C hC hclosed hconv x
  classical
  by_cases hx : x ∈ C
  · simp only [Specs.indicator, ite_eq_left hx, Specs.toEReal]
    change (⨆ y : X →L[ℝ] ℝ,
      (y x : EReal) - ConvexGeometry.Specs.supportFunction C y) = 0
    apply le_antisymm
    · apply iSup_le
      intro y
      apply EReal.sub_nonpos.mpr
      exact le_iSup₂ (f := fun z (_ : z ∈ C) => (y z : EReal)) x hx
    · apply le_iSup_of_le (0 : X →L[ℝ] ℝ)
      simp [supportFunction_zero C hC]
  · simp only [Specs.indicator, ite_eq_right hx, Specs.toEReal]
    change (⨆ y : X →L[ℝ] ℝ,
      (y x : EReal) - ConvexGeometry.Specs.supportFunction C y) = ⊤
    apply (EReal.eq_top_iff_forall_lt _).mpr
    intro r
    obtain ⟨l, a, hlC, hlx⟩ := geometric_hahn_banach_closed_point hconv hclosed hx
    obtain ⟨t, ht, hrt⟩ := exists_pos_lt_mul (sub_pos.mpr hlx) r
    have hsupport : ConvexGeometry.Specs.supportFunction C (t • l) ≤
        ((t * a : ℝ) : EReal) := by
      apply iSup₂_le
      intro z hz
      apply EReal.coe_le_coe_iff.mpr
      change t * l z ≤ t * a
      exact mul_le_mul_of_nonneg_left (hlC z hz).le ht.le
    have hterm : ((t * (l x - a) : ℝ) : EReal) ≤
        (((t • l) x : ℝ) : EReal) - ConvexGeometry.Specs.supportFunction C (t • l) := by
      have h := EReal.sub_le_sub (le_refl (((t • l) x : ℝ) : EReal)) hsupport
      simpa only [smul_apply, smul_eq_mul, ← EReal.coe_sub,
        ← mul_sub] using h
    exact (EReal.coe_lt_coe_iff.mpr hrt).trans_le
      (hterm.trans (le_iSup (fun y : X →L[ℝ] ℝ =>
        (y x : EReal) - ConvexGeometry.Specs.supportFunction C y) (t • l)))

theorem conjugate_norm : Specs.conjugate_norm.{u} := by
  intro X _ _ y
  classical
  rw [conjugate_eq_iSup_sub]
  by_cases hy : ‖y‖ ≤ 1
  · simp only [Specs.indicator, Set.mem_ofPred_eq, ite_eq_left hy, Specs.toEReal]
    change (⨆ x : X, (y x : EReal) - (‖x‖ : EReal)) = 0
    apply le_antisymm
    · apply iSup_le
      intro x
      apply EReal.sub_nonpos.mpr
      apply EReal.coe_le_coe_iff.mpr
      exact (le_abs_self (y x)).trans (by
        simpa only [Real.norm_eq_abs, one_mul] using y.le_of_opNorm_le hy x)
    · apply le_iSup_of_le (0 : X)
      simp
  · simp only [Specs.indicator, Set.mem_ofPred_eq, ite_eq_right hy, Specs.toEReal]
    change (⨆ x : X, (y x : EReal) - (‖x‖ : EReal)) = ⊤
    have hex : ∃ x : X, ‖x‖ < y x := by
      by_contra h
      have hall : ∀ x : X, y x ≤ ‖x‖ := by
        intro x
        exact le_of_not_gt (fun hx => h ⟨x, hx⟩)
      apply hy
      apply (ContinuousLinearMap.opNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro x
      rw [one_mul, Real.norm_eq_abs, abs_le]
      refine ⟨?_, hall x⟩
      have hn := hall (-x)
      have hn' : -y x ≤ ‖x‖ := by simpa using hn
      linarith
    obtain ⟨x, hx⟩ := hex
    apply (EReal.eq_top_iff_forall_lt _).mpr
    intro r
    obtain ⟨t, ht, hrt⟩ := exists_pos_lt_mul (sub_pos.mpr hx) r
    have heq : (y (t • x) : EReal) - (‖t • x‖ : EReal) =
        ((t * (y x - ‖x‖) : ℝ) : EReal) := by
      rw [← EReal.coe_sub, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      congr 1
      simp only [smul_eq_mul]
      ring
    exact (EReal.coe_lt_coe_iff.mpr hrt).trans_le
      (heq ▸ le_iSup (fun z : X => (y z : EReal) - (‖z‖ : EReal)) (t • x))

end VariationalNotes.ConvexAnalysis
