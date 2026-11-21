import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.PerturbationModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Conjugates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
universe u v
namespace VariationalNotes.Ch04

open VariationalNotes.ConvexAnalysis

def marginal {X : Type u} {Y : Type v} (Φ : X × Y → WithTop ℝ) (u : Y) : EReal :=
  Specs.marginal Φ u

def primalValue {X : Type u} {Y : Type v} [Zero Y]
    (Φ : X × Y → WithTop ℝ) : EReal := Specs.primalValue Φ

def extendedConjugate {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (f : Y → EReal) (y : Y →L[ℝ] ℝ) : EReal := Specs.extendedConjugate f y

def marginalConjugate {X : Type u} {Y : Type v}
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) (y : Y →L[ℝ] ℝ) : EReal := Specs.marginalConjugate Φ y

def perturbationDualObjective {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) (y : Y →L[ℝ] ℝ) : EReal :=
  Specs.perturbationDualObjective Φ y

theorem marginal_le_candidate : Specs.marginal_le_candidate.{u,v} := by
  intro X Y Φ x u
  exact iInf_le _ x

theorem marginal_empty : Specs.marginal_empty.{u,v} := by
  intro X Y _ Φ u
  change (⨅ x : X, ConvexAnalysis.Specs.toEReal (Φ (x, u))) = ⊤
  simp

theorem extendedConjugate_toEReal : Specs.extendedConjugate_toEReal.{v} := by
  intro Y _ _ _ f y
  exact (conjugate_eq_iSup_sub f y).symm

/-- A strict real upper bound on the infimum supplies a genuinely finite
candidate. In particular no minimizer is selected here. -/
theorem exists_candidate_lt {X : Type u} {Y : Type v}
    (Φ : X × Y → WithTop ℝ) (u : Y) (c : ℝ)
    (h : marginal Φ u < (c : EReal)) :
    ∃ x : X, ∃ r : ℝ, Φ (x, u) = (r : WithTop ℝ) ∧ r < c := by
  obtain ⟨x, hx⟩ := iInf_lt_iff.mp h
  induction hval : Φ (x, u) using WithTop.recTopCoe with
  | top =>
    simp only [hval, ConvexAnalysis.Specs.toEReal] at hx
    exact (not_top_lt hx).elim
  | coe r =>
    refine ⟨x, r, hval, ?_⟩
    rw [hval] at hx
    exact EReal.coe_lt_coe_iff.mp hx

/-- Convexity applied to two finite candidates and then to the infimum. -/
theorem marginal_le_combination {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (Φ : X × Y → WithTop ℝ) (hΦ : IsConvex Φ)
    (x z : X) (u v : Y) (r s : ℝ)
    (hx : Φ (x, u) = (r : WithTop ℝ)) (hz : Φ (z, v) = (s : WithTop ℝ))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    marginal Φ (a • u + b • v) ≤ ((a * r + b * s : ℝ) : EReal) := by
  have hc := (convex_iff_twoPoint Φ).mp hΦ (x, u) (z, v) r s hx hz a b ha hb hab
  exact (marginal_le_candidate Φ (a • x + b • z) (a • u + b • v)).trans
    ((toEReal_conventions.2.2.2.2 _ _).mpr hc)

theorem marginal_convex_finite : Specs.marginal_convex_finite.{u,v} := by
  intro X Y _ _ _ _ Φ hΦ u v r s hu hv a b ha hb hab
  apply EReal.le_of_forall_lt_iff_le.mp
  intro t ht
  have ht' : a * r + b * s < t := EReal.coe_lt_coe_iff.mp ht
  let ε : ℝ := (t - (a * r + b * s)) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨x, r', hx, hr⟩ := exists_candidate_lt Φ u (r + ε) (by
    change Specs.marginal Φ u < _
    rw [hu]
    exact EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨z, s', hz, hs⟩ := exists_candidate_lt Φ v (s + ε) (by
    change Specs.marginal Φ v < _
    rw [hv]
    exact EReal.coe_lt_coe_iff.mpr (by linarith))
  apply (marginal_le_combination Φ hΦ x z u v r' s' hx hz a b ha hb hab).trans
  apply EReal.coe_le_coe_iff.mpr
  have h := add_le_add (mul_le_mul_of_nonneg_left hr.le ha)
    (mul_le_mul_of_nonneg_left hs.le hb)
  have hsum : a * (r + ε) + b * (s + ε) = a * r + b * s + ε := by
    nlinarith only [congrArg (fun k : ℝ => k * ε) hab]
  rw [hsum] at h
  dsimp [ε] at h
  linarith

theorem marginal_eq_bot_of_left {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (Φ : X × Y → WithTop ℝ) (hΦ : IsConvex Φ) (u v : Y)
    (hu : marginal Φ u = ⊥) (z : X) (s : ℝ) (hz : Φ (z, v) = (s : WithTop ℝ))
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    marginal Φ (a • u + b • v) = ⊥ := by
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro t
  obtain ⟨x, r, hx, hr⟩ := exists_candidate_lt Φ u ((t - b * s) / a) (by
    rw [hu]
    exact EReal.bot_lt_coe _)
  apply (marginal_le_combination Φ hΦ x z u v r s hx hz a b ha.le hb hab).trans_lt
  apply EReal.coe_lt_coe_iff.mpr
  have h := (lt_div_iff₀ ha).mp hr
  nlinarith

theorem marginal_eq_bot_of_endpoint : Specs.marginal_eq_bot_of_endpoint.{u,v} := by
  intro X Y _ _ _ _ Φ hΦ u v h a b ha hb hab
  change marginal Φ (a • u + b • v) = ⊥
  rcases h with ⟨hu, z, s, hz⟩ | ⟨hv, x, r, hx⟩
  · exact marginal_eq_bot_of_left Φ hΦ u v hu z s hz a b ha hb.le hab
  · simpa only [add_comm] using
      marginal_eq_bot_of_left Φ hΦ v u hv x r hx b a hb ha.le (by rw [add_comm]; exact hab)

end VariationalNotes.Ch04
