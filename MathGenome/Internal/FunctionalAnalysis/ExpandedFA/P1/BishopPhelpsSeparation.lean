import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BishopPhelpsSeparation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BishopPhelps
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Ekeland
import Mathlib.Tactic.Positivity

namespace ExpandedFA.P1.BishopPhelpsSeparation
open Set Metric
universe u

/-- A norm-one vector is within twice the original error of the normalization
of a nonzero approximant. -/
lemma normalization_error {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f h : V) (hf : ‖f‖ = 1) (hh : h ≠ 0) :
    ‖‖h‖⁻¹ • h - f‖ ≤ 2 * ‖h - f‖ := by
  let g : V := ‖h‖⁻¹ • h
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hg : ‖g‖ = 1 := by
    dsimp [g]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hsc : ‖h‖ • g = h := by
    dsimp [g]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hdist : ‖g - h‖ = |1 - ‖h‖| := by
    calc
      _ = ‖(1 - ‖h‖) • g‖ := by rw [sub_smul, one_smul, hsc]
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, hg, mul_one]
  have he : |1 - ‖h‖| ≤ ‖h - f‖ := by
    rw [abs_sub_comm, ← hf]
    exact abs_norm_sub_norm_le h f
  calc
    _ = ‖(g - h) + (h - f)‖ := by congr 1; dsimp [g]; abel
    _ ≤ ‖g-h‖ + ‖h-f‖ := norm_add_le _ _
    _ ≤ 2 * ‖h-f‖ := by rw [hdist]; linarith

/-- Ekeland's descent bound controls the support point even when C is unbounded. -/
theorem real_separation : Spec.RealSeparation.{u} := by
  intro E _ _ _ C A hne hc hv hA f hf hgap ε hε
  obtain ⟨M, d, hd, hM, hMd⟩ := hgap
  have hb : BddAbove (f '' C) := ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact hM y hy⟩
  let S : ℝ := sSup (f '' C)
  have hS (y : E) (hy : y ∈ C) : f y ≤ S := le_csSup hb ⟨y, hy, rfl⟩
  have hSM : S ≤ M := csSup_le (hne.image f) (by rintro _ ⟨y,hy,rfl⟩; exact hM y hy)
  obtain ⟨v, ⟨c, hcC, rfl⟩, hnear⟩ := exists_lt_of_lt_csSup (hne.image f)
    (show S - d/4 < sSup (f '' C) by dsimp [S]; linarith)
  obtain ⟨R, hR, hRA⟩ := hA.exists_pos_norm_le
  obtain ⟨α, hα, hαsmall⟩ := exists_between
    (show 0 < min (min (ε/2) (1/2)) (d / (4 * (R + ‖c‖ + 1))) by positivity)
  have hαε : 2 * α < ε := by have := (lt_min_iff.mp (lt_min_iff.mp hαsmall).1).1; linarith
  have hα1 : α < 1/2 := (lt_min_iff.mp (lt_min_iff.mp hαsmall).1).2
  have hαd : α * (R + ‖c‖ + 1) < d/4 := by
    have ht := (lt_div_iff₀ (show 0 < 4 * (R + ‖c‖ + 1) by positivity)).mp
      (lt_min_iff.mp hαsmall).2
    nlinarith
  let : CompleteSpace C := hc.isComplete.completeSpace_coe
  let F : C → ℝ := fun y => -f y
  have hF : LowerSemicontinuous F :=
    (f.continuous.comp continuous_subtype_val).neg.lowerSemicontinuous
  have hFb : BddBelow (range F) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨y,rfl⟩
    exact neg_le_neg (hM y y.property)
  obtain ⟨x, hxdes, hxterm⟩ := exists_terminal_descent hF hFb hα (⟨c,hcC⟩ : C)
  have hxmove : α * ‖(x : E) - c‖ < d/4 := by
    change -f (x : E) + α * dist (x : E) c ≤ -f c at hxdes
    rw [dist_eq_norm] at hxdes
    have := hS x x.property
    linarith
  have hmax : ∀ y ∈ C, f (y-(x : E)) ≤ α * ‖y-(x : E)‖ := by
    intro y hy
    by_contra hh
    have hdesc : Descent F α x (⟨y,hy⟩ : C) := by
      dsimp [Descent, F]
      change -f y + α * dist y (x : E) ≤ -f (x : E)
      rw [dist_eq_norm]
      rw [map_sub] at hh
      linarith
    have hey : y = (x : E) := congrArg Subtype.val (hxterm ⟨y,hy⟩ hdesc)
    simp [hey] at hh
  obtain ⟨h, hh, hs⟩ := BishopPhelps.support_of_approximate_maximum hv x.property f hα hmax
  have hhn : 0 < ‖h‖ := by
    have ht := norm_sub_norm_le f h
    rw [hf, norm_sub_rev] at ht
    linarith
  have hhn0 : h ≠ 0 := norm_pos_iff.mp hhn
  have hxb : α * ‖(x : E)‖ ≤ α * ‖c‖ + α * ‖(x : E)-c‖ := by
    have ht : ‖(x : E)‖ ≤ ‖c‖ + ‖(x : E)-c‖ := by
      simpa [add_comm] using norm_add_le ((x : E)-c) c
    nlinarith
  have he (z : E) : |h z - f z| ≤ α * ‖z‖ := by
    have ht := (h-f).le_opNorm z
    change ‖h z - f z‖ ≤ ‖h-f‖ * ‖z‖ at ht
    rw [Real.norm_eq_abs] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right hh (norm_nonneg z))
  have hsep (a : E) (ha : a ∈ A) : h (x : E) + d/2 ≤ h a := by
    have hxerr := (abs_le.mp (he x)).2
    have haerr := (abs_le.mp (he a)).1
    have hgap := hMd a ha
    have hxM := hM x x.property
    have hRa : α * ‖a‖ ≤ α * R := mul_le_mul_of_nonneg_left (hRA a ha) hα.le
    nlinarith
  let g : E →L[ℝ] ℝ := ‖h‖⁻¹ • h
  have hg : ‖g‖ = 1 := by
    dsimp [g]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hhn), inv_mul_cancel₀ hhn.ne']
  refine ⟨x, x.property, g, hg, ?_, ?_, ‖h‖⁻¹ * (d/2), by positivity, ?_⟩
  · exact (normalization_error f h hf hhn0).trans_lt (by nlinarith)
  · intro y hy
    change ‖h‖⁻¹ * h y ≤ ‖h‖⁻¹ * h (x : E)
    exact mul_le_mul_of_nonneg_left (hs y hy) (inv_nonneg.mpr hhn.le)
  · intro a ha
    change ‖h‖⁻¹ * h (x : E) + ‖h‖⁻¹ * (d/2) ≤ ‖h‖⁻¹ * h a
    simpa [mul_add] using mul_le_mul_of_nonneg_left (hsep a ha) (inv_nonneg.mpr hhn.le)

/-- Real-part restriction and complex extension are inverse norm isometries;
therefore the real theorem gives the complex scalar-linear theorem. -/
theorem complex_separation : Spec.ComplexSeparation.{u} := by
  intro E _ _ _ C A hne hc hv hA f hf hgap ε hε
  let e := StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)
  let fr : E →L[ℝ] ℝ := e.symm f
  have hfr : ‖fr‖ = 1 := by dsimp [fr]; rw [e.symm.norm_map, hf]
  have hgapr : ∃ M d : ℝ, 0 < d ∧ (∀ y ∈ C, fr y ≤ M) ∧
      (∀ a ∈ A, M+d ≤ fr a) := hgap
  obtain ⟨x, hx, h, hn, hh, hs, η, hη, hsep⟩ :=
    real_separation E C A hne hc hv hA fr hfr hgapr ε hε
  refine ⟨x, hx, e h, ?_, ?_, ?_, η, hη, ?_⟩
  · rw [e.norm_map, hn]
  · have he : e h - f = e (h-fr) := by simp [fr, map_sub]
    rw [he, e.norm_map]
    exact hh
  · intro y hy
    change ((StrongDual.extendRCLike h : E →L[ℂ] ℂ) y).re ≤
      ((StrongDual.extendRCLike h : E →L[ℂ] ℂ) x).re
    calc
      _ = h y := StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h y
      _ ≤ h x := hs y hy
      _ = _ := (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x).symm
  · intro a ha
    change ((StrongDual.extendRCLike h : E →L[ℂ] ℂ) x).re + η ≤
      ((StrongDual.extendRCLike h : E →L[ℂ] ℂ) a).re
    calc
      _ = h x + η := congrArg (fun t : ℝ => t + η)
        (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h x)
      _ ≤ h a := hsep a ha
      _ = _ := (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) h a).symm

end ExpandedFA.P1.BishopPhelpsSeparation
