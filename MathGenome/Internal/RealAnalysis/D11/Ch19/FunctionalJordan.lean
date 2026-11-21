import MathGenome.Internal.RealAnalysis.D11.Ch19.CzeroBanachDensity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.FunctionalJordan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! The Riesz–Kantorovich positive-cone construction, followed by its
well-defined extension by differences of nonnegative functions. -/
noncomputable section

namespace D11.Ch19
universe u
open scoped Topology

noncomputable def functionalPositiveSup :
    Specs.D11.Ch19.FunctionalJordan.positiveSupType.{u} :=
  Specs.D11.Ch19.FunctionalJordan.positiveSupValue

namespace FunctionalJordan
variable {X : Type u} [TopologicalSpace X]
local notation "E" => Czero X ℝ

/-- Pointwise positive part, still in the native C₀ space. -/
private def pos (f : E) : E where
  toFun x := max (f x) 0
  continuous_toFun := f.continuous.max continuous_const
  zero_at_infty' := by
    simpa using (zero_at_infty f).max (tendsto_const_nhds (x := (0 : ℝ)))

private def minimum (f g : E) : E where
  toFun x := min (f x) (g x)
  continuous_toFun := f.continuous.min g.continuous
  zero_at_infty' := by
    simpa using (zero_at_infty f).min (zero_at_infty g)

private lemma pos_nonneg (f : E) : ∀ x, 0 ≤ pos f x := fun _ => le_max_right _ _

private lemma norm_le_of_between {f g : E} (hf : ∀ x, 0 ≤ f x)
    (hfg : ∀ x, f x ≤ g x) : ‖f‖ ≤ ‖g‖ := by
  apply (czero_norm_le_iff X ℝ f ‖g‖ (norm_nonneg _)).mpr
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (hf x)]
  exact (hfg x).trans ((le_abs_self _).trans (g.toBCF.norm_coe_le_norm x))

private lemma norm_pos_le (f : E) : ‖pos f‖ ≤ ‖f‖ := by
  apply (czero_norm_le_iff X ℝ _ ‖f‖ (norm_nonneg _)).mpr
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (pos_nonneg f x)]
  exact max_le ((le_abs_self _).trans (f.toBCF.norm_coe_le_norm x)) (norm_nonneg _)

private lemma sup_bdd (I : E →L[ℝ] ℝ) (f : E) :
    BddAbove {r : ℝ | ∃ g : E, (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ f x) ∧ I g = r} := by
  refine ⟨‖I‖ * ‖f‖, ?_⟩
  rintro r ⟨g, hg, hgf, rfl⟩
  exact (le_abs_self _).trans ((I.le_opNorm g).trans
    (mul_le_mul_of_nonneg_left (norm_le_of_between hg hgf) (norm_nonneg _)))

private lemma sup_nonempty (I : E →L[ℝ] ℝ) {f : E} (hf : ∀ x, 0 ≤ f x) :
    {r : ℝ | ∃ g : E, (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ f x) ∧ I g = r}.Nonempty :=
  ⟨0, 0, fun _ => le_rfl, hf, map_zero I⟩

private lemma le_sup (I : E →L[ℝ] ℝ) {f g : E}
    (hg : ∀ x, 0 ≤ g x) (hgf : ∀ x, g x ≤ f x) : I g ≤ functionalPositiveSup X I f :=
  le_csSup (sup_bdd I f) ⟨g, hg, hgf, rfl⟩

private lemma sup_le (I : E →L[ℝ] ℝ) {f : E} (hf : ∀ x, 0 ≤ f x) {b : ℝ}
    (hb : ∀ g : E, (∀ x, 0 ≤ g x) → (∀ x, g x ≤ f x) → I g ≤ b) :
    functionalPositiveSup X I f ≤ b := by
  apply csSup_le (sup_nonempty I hf)
  rintro _ ⟨g, hg, hgf, rfl⟩
  exact hb g hg hgf

private lemma sup_nonneg (I : E →L[ℝ] ℝ) {f : E} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ functionalPositiveSup X I f := by
  simpa using le_sup I (g := 0) (fun _ => le_rfl) hf

private lemma sup_bound (I : E →L[ℝ] ℝ) {f : E} (hf : ∀ x, 0 ≤ f x) :
    functionalPositiveSup X I f ≤ ‖I‖ * ‖f‖ :=
  sup_le I hf (fun g hg hgf => (le_abs_self _).trans ((I.le_opNorm g).trans
    (mul_le_mul_of_nonneg_left (norm_le_of_between hg hgf) (norm_nonneg _))))

private lemma sup_zero (I : E →L[ℝ] ℝ) : functionalPositiveSup X I 0 = 0 := by
  exact le_antisymm (by simpa using sup_bound I (f := 0) (fun _ => le_rfl))
    (sup_nonneg I (fun _ => le_rfl))

private lemma sup_add (I : E →L[ℝ] ℝ) {f h : E}
    (hf : ∀ x, 0 ≤ f x) (hh : ∀ x, 0 ≤ h x) :
    functionalPositiveSup X I (f + h) =
      functionalPositiveSup X I f + functionalPositiveSup X I h := by
  apply le_antisymm
  · apply sup_le I (fun x => add_nonneg (hf x) (hh x))
    intro g hg hgf
    let g₁ := minimum g f
    let g₂ := g - g₁
    have h₁ : ∀ x, 0 ≤ g₁ x := fun x => le_min (hg x) (hf x)
    have h₁f : ∀ x, g₁ x ≤ f x := fun x => min_le_right _ _
    have h₂ : ∀ x, 0 ≤ g₂ x := fun x => sub_nonneg.mpr (min_le_left _ _)
    have h₂h : ∀ x, g₂ x ≤ h x := by
      intro x
      change g x - min (g x) (f x) ≤ h x
      have := hgf x
      change g x ≤ f x + h x at this
      rcases le_total (g x) (f x) with hx | hx
      · rw [min_eq_left hx, sub_self]; exact hh x
      · rw [min_eq_right hx]; linarith
    have heq : g = g₁ + g₂ := by dsimp [g₂]; abel
    rw [heq, map_add]
    exact add_le_add (le_sup I h₁ h₁f) (le_sup I h₂ h₂h)
  · apply (le_sub_iff_add_le).mp
    apply sup_le I hf
    intro g hg hgf
    apply (le_sub_iff_add_le).mpr
    rw [add_comm]
    apply (le_sub_iff_add_le).mp
    apply sup_le I hh
    intro k hk hkf
    apply (le_sub_iff_add_le).mpr
    simpa only [map_add] using le_sup I (g := k + g)
      (fun x => add_nonneg (hk x) (hg x))
      (fun x => by change k x + g x ≤ f x + h x; linarith [hkf x, hgf x])


private lemma sup_smul (I : E →L[ℝ] ℝ) {f : E} (hf : ∀ x, 0 ≤ f x)
    {a : ℝ} (ha : 0 ≤ a) :
    functionalPositiveSup X I (a • f) = a * functionalPositiveSup X I f := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [sup_zero]
  apply le_antisymm
  · apply sup_le I (fun x => mul_nonneg ha.le (hf x))
    intro g hg hgf
    have hscaled : I (a⁻¹ • g) ≤ functionalPositiveSup X I f := by
      apply le_sup I
      · intro x; exact mul_nonneg (inv_nonneg.mpr ha.le) (hg x)
      · intro x
        change a⁻¹ * g x ≤ f x
        have := hgf x
        change g x ≤ a * f x at this
        calc
          a⁻¹ * g x ≤ a⁻¹ * (a * f x) := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr ha.le)
          _ = f x := by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
    have := mul_le_mul_of_nonneg_left hscaled ha.le
    simpa [map_smul, smul_eq_mul, ← mul_assoc, ha.ne'] using this
  · rw [mul_comm]
    apply (le_div_iff₀ ha).mp
    apply sup_le I hf
    intro g hg hgf
    apply (le_div_iff₀ ha).mpr
    have := le_sup I (f := a • f) (g := a • g)
      (fun x => mul_nonneg ha.le (hg x))
      (fun x => mul_le_mul_of_nonneg_left (hgf x) ha.le)
    simpa [map_smul, smul_eq_mul, mul_comm] using this

private def extension (I : E →L[ℝ] ℝ) (f : E) : ℝ :=
  functionalPositiveSup X I (pos f) - functionalPositiveSup X I (pos (-f))

private lemma pos_sub_pos (f : E) : pos f - pos (-f) = f := by
  ext x
  change max (f x) 0 - max (-f x) 0 = f x
  rcases le_total 0 (f x) with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring

/-- Independence of the chosen difference of positive functions. -/
private lemma extension_diff (I : E →L[ℝ] ℝ) {f u v : E}
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x) (heq : f = u - v) :
    extension I f = functionalPositiveSup X I u - functionalPositiveSup X I v := by
  have he : pos f + v = pos (-f) + u := by
    ext x
    have h := congrArg (fun k : E => k x) (pos_sub_pos f)
    have h' := congrArg (fun k : E => k x) heq
    change pos f x - pos (-f) x = f x at h
    change f x = u x - v x at h'
    change pos f x + v x = pos (-f) x + u x
    linarith
  have h := congrArg (functionalPositiveSup X I) he
  rw [sup_add I (pos_nonneg f) hv, sup_add I (pos_nonneg (-f)) hu] at h
  dsimp [extension]
  linarith

private lemma extension_of_nonneg (I : E →L[ℝ] ℝ) {f : E}
    (hf : ∀ x, 0 ≤ f x) : extension I f = functionalPositiveSup X I f := by
  rw [extension_diff I hf (fun _ => le_rfl) (show f = f - 0 by simp), sup_zero, sub_zero]

private lemma extension_add (I : E →L[ℝ] ℝ) (f g : E) :
    extension I (f + g) = extension I f + extension I g := by
  rw [extension_diff I
    (fun x => add_nonneg (pos_nonneg f x) (pos_nonneg g x))
    (fun x => add_nonneg (pos_nonneg (-f) x) (pos_nonneg (-g) x))
    (show f + g = (pos f + pos g) - (pos (-f) + pos (-g)) by
      rw [add_sub_add_comm, pos_sub_pos, pos_sub_pos])]
  rw [sup_add I (pos_nonneg f) (pos_nonneg g),
    sup_add I (pos_nonneg (-f)) (pos_nonneg (-g))]
  dsimp [extension]
  ring

private lemma extension_neg (I : E →L[ℝ] ℝ) (f : E) :
    extension I (-f) = -extension I f := by simp [extension]

private lemma extension_smul_nonneg (I : E →L[ℝ] ℝ) (f : E) {a : ℝ} (ha : 0 ≤ a) :
    extension I (a • f) = a * extension I f := by
  rw [extension_diff I
    (fun x => mul_nonneg ha (pos_nonneg f x))
    (fun x => mul_nonneg ha (pos_nonneg (-f) x))
    (show a • f = a • pos f - a • pos (-f) by
      ext x
      have h := congrArg (fun k : E => k x) (pos_sub_pos f)
      change max (f x) 0 - max (-f x) 0 = f x at h
      change a * f x = a * max (f x) 0 - a * max (-f x) 0
      rw [← mul_sub, h])]
  rw [sup_smul I (pos_nonneg f) ha, sup_smul I (pos_nonneg (-f)) ha]
  dsimp [extension]
  ring

private def extensionLinear (I : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ where
  toFun := extension I
  map_add' := extension_add I
  map_smul' a f := by
    change extension I (a • f) = a * extension I f
    rcases le_total 0 a with ha | ha
    · exact extension_smul_nonneg I f ha
    · have h : a • f = -((-a) • f) := by
        ext x
        change a * f x = -((-a) * f x)
        ring
      rw [h, extension_neg, extension_smul_nonneg I f (neg_nonneg.mpr ha)]
      ring

private lemma extension_bound (I : E →L[ℝ] ℝ) (f : E) :
    ‖extension I f‖ ≤ ‖I‖ * ‖f‖ := by
  have hp := sup_nonneg I (pos_nonneg f)
  have hn := sup_nonneg I (pos_nonneg (-f))
  have hp' := (sup_bound I (pos_nonneg f)).trans
    (mul_le_mul_of_nonneg_left (norm_pos_le f) (norm_nonneg I))
  have hn' := (sup_bound I (pos_nonneg (-f))).trans
    (mul_le_mul_of_nonneg_left (norm_pos_le (-f)) (norm_nonneg I))
  rw [norm_neg] at hn'
  rw [Real.norm_eq_abs, abs_le]
  dsimp [extension]
  constructor <;> linarith

private def positiveExtension (I : E →L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (extensionLinear I).mkContinuous ‖I‖ (extension_bound I)

end FunctionalJordan

/-- The positive-cone supremum extends to a bounded positive functional.
Its difference with I is bounded positive, giving the stated decomposition. -/
theorem functional_jordan : Specs.D11.Ch19.FunctionalJordan.functional_jordan.{u} := by
  intro X _ _ _ I
  let P := FunctionalJordan.positiveExtension I
  have hP : ∀ f : Czero X ℝ, (∀ x, 0 ≤ f x) →
      P f = functionalPositiveSup X I f := by
    intro f hf
    exact FunctionalJordan.extension_of_nonneg I hf
  refine ⟨P, hP, ?_, ?_, ?_, ?_⟩
  · intro f hf
    rw [hP f hf]
    exact FunctionalJordan.sup_nonneg I hf
  · intro f hf
    change 0 ≤ P f - I f
    rw [hP f hf]
    exact sub_nonneg.mpr (FunctionalJordan.le_sup I hf (fun _ => le_rfl))
  · abel
  · exact LinearMap.mkContinuous_norm_le (FunctionalJordan.extensionLinear I)
      (norm_nonneg I) (FunctionalJordan.extension_bound I)

end D11.Ch19
