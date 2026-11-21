import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Conjugates
import Mathlib.Tactic.Linarith

noncomputable section
open Set
universe u
namespace VariationalNotes.ConvexAnalysis

def conjugate {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (y : X →L[ℝ] ℝ) : EReal := Specs.conjugate f y

def indicator {X : Type u} (C : Set X) (x : X) : WithTop ℝ := Specs.indicator C x

def biconjugate {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    (f : X → WithTop ℝ) (x : X) : EReal := Specs.biconjugate f x

theorem indicator_values : Specs.indicator_values.{u} := by
  intro X C
  classical
  refine ⟨fun x hx => ite_eq_left hx, fun x hx => ite_eq_right hx, ?_⟩
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    by_contra hnot
    simp [Specs.indicator, hnot] at hx
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp [Specs.indicator, hx]

theorem conjugate_finite_lower_bound : Specs.conjugate_finite_lower_bound.{u} := by
  intro X _ _ _ f x r hx y
  have hdom : x ∈ Specs.effectiveDomain f := by
    change f x < ⊤
    rw [hx]
    exact WithTop.coe_lt_top r
  have h := le_iSup₂ (f := fun x (_ : x ∈ Specs.effectiveDomain f) =>
    ((y x - (f x).untopD 0 : ℝ) : EReal)) x hdom
  change ((y x - (f x).untopD 0 : ℝ) : EReal) ≤ Specs.conjugate f y at h
  rw [hx, WithTop.untopD_coe] at h
  exact h

theorem conjugate_ne_bot : Specs.conjugate_ne_bot.{u} := by
  intro X _ _ _ f hf y
  obtain ⟨x, r, hr⟩ := (proper_iff_exists_real f).mp hf
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (conjugate_finite_lower_bound f x r hr y)

theorem conjugate_term_conventions : Specs.conjugate_term_conventions.{u} := by
  intro X _ _ _ f x y
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rw [hr]
    rfl
  · intro h
    rw [h]
    exact EReal.sub_top _
  · intro h
    rw [h]
    exact EReal.sub_top _

theorem conjugate_eq_iSup_sub : Specs.conjugate_eq_iSup_sub.{u} := by
  intro X _ _ _ f y
  apply le_antisymm
  · apply iSup₂_le
    intro x hx
    obtain ⟨r, hr⟩ := (mem_domain_iff f x).mp hx
    apply le_iSup_of_le x
    simp only [hr, WithTop.untopD_coe, Specs.toEReal, EReal.coe_sub]
    exact le_rfl
  · apply iSup_le
    intro x
    induction hfx : f x using WithTop.recTopCoe with
    | top =>
      change (y x : EReal) - ⊤ ≤ _
      rw [EReal.sub_top]
      exact bot_le
    | coe r =>
      have h := conjugate_finite_lower_bound f x r hfx y
      exact h

theorem conjugate_convex : Specs.conjugate_convex.{u} := by
  intro X _ _ _ f p hp q hq a b ha hb hab
  change Specs.conjugate f (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
  apply iSup₂_le
  intro x hx
  have hp' := (le_iSup₂ (f := fun x (_ : x ∈ Specs.effectiveDomain f) =>
    ((p.1 x - (f x).untopD 0 : ℝ) : EReal)) x hx).trans hp
  have hq' := (le_iSup₂ (f := fun x (_ : x ∈ Specs.effectiveDomain f) =>
    ((q.1 x - (f x).untopD 0 : ℝ) : EReal)) x hx).trans hq
  have hp'' : p.1 x - (f x).untopD 0 ≤ p.2 := EReal.coe_le_coe_iff.mp hp'
  have hq'' : q.1 x - (f x).untopD 0 ≤ q.2 := EReal.coe_le_coe_iff.mp hq'
  apply EReal.coe_le_coe_iff.mpr
  change a * p.1 x + b * q.1 x - (f x).untopD 0 ≤ a * p.2 + b * q.2
  have h := add_le_add (mul_le_mul_of_nonneg_left hp'' ha)
    (mul_le_mul_of_nonneg_left hq'' hb)
  have hab' := congrArg (fun t : ℝ => t * (f x).untopD 0) hab
  nlinarith only [h, hab']

theorem conjugate_weakStar_lowerSemicontinuous :
    Specs.conjugate_weakStar_lowerSemicontinuous.{u} := by
  intro X _ _ _ f
  apply lowerSemicontinuous_biSup
  intro x hx
  exact (continuous_coe_real_ereal.comp
    ((WeakDual.eval_continuous x).sub continuous_const)).lowerSemicontinuous

theorem fenchel_young : Specs.fenchel_young.{u} := by
  intro X _ _ _ f hf x y
  induction hfx : f x using WithTop.recTopCoe with
  | top =>
    change (y x : EReal) ≤ ⊤ + Specs.conjugate f y
    rw [EReal.top_add_of_ne_bot (conjugate_ne_bot f hf y)]
    exact le_top
  | coe r =>
    have h := conjugate_finite_lower_bound f x r hfx y
    have h' := add_le_add_right h (r : EReal)
    rw [← EReal.coe_add, show r + (y x - r) = y x by ring] at h'
    exact h' 

end VariationalNotes.ConvexAnalysis
