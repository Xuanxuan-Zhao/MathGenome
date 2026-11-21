import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.PerturbationAlgebra
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.PerturbationModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.Subgradients
import Mathlib.Tactic.Linarith

noncomputable section
universe u v
namespace VariationalNotes.Ch04
open VariationalNotes.ConvexAnalysis

def ExtendedProper {Y : Type v} (f : Y → EReal) : Prop := Specs.ExtendedProper f

def marginalFunction {X : Type u} {Y : Type v} (Φ : X × Y → WithTop ℝ)
    (u : Y) : WithTop ℝ := Specs.marginalFunction Φ u

def extendedBiconjugate {Y : Type v} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (f : Y → EReal) (u : Y) : EReal := Specs.extendedBiconjugate f u

def perturbationDualValue {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) : EReal := Specs.perturbationDualValue Φ

/-- Subtracting an arbitrary extended value from a finite real reverses order,
including both infinite boundary cases. -/
theorem real_sub_le_real_iff (a b : ℝ) (z : EReal) :
    (a : EReal) - z ≤ (b : EReal) ↔ ((a - b : ℝ) : EReal) ≤ z := by
  cases z with
  | bot => simp [-EReal.coe_sub]
  | top => simp [-EReal.coe_sub]
  | coe z =>
    simp only [← EReal.coe_sub, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

/-- No attainment of the infimum, nor a lower bound on the family, is used. -/
theorem real_sub_iInf {ι : Sort*} (a : ℝ) (f : ι → EReal) :
    (a : EReal) - (⨅ i, f i) = ⨆ i, (a : EReal) - f i := by
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro t ht
    apply (real_sub_le_real_iff a t _).mpr
    apply le_iInf
    intro i
    exact (real_sub_le_real_iff a t _).mp ((le_iSup (fun i => (a : EReal) - f i) i).trans ht.le)
  · exact iSup_le fun i => EReal.sub_le_sub le_rfl (iInf_le f i)

theorem marginalFunction_representation : Specs.marginalFunction_representation.{u,v} := by
  intro X Y Φ h u
  obtain ⟨r, hr⟩ := (toEReal_conventions.2.2.2.1 (Specs.marginal Φ u)).mp (h u)
  change ConvexAnalysis.Specs.toEReal ((Specs.marginal Φ u).unbotD ⊤) = _
  rw [← hr]
  rfl

theorem marginal_conjugate_identity : Specs.marginal_conjugate_identity.{u,v} := by
  intro X Y _ _ _ _ _ _ Φ y
  rw [conjugate_eq_iSup_sub]
  change (⨆ u : Y, (y u : EReal) - ⨅ x : X, ConvexAnalysis.Specs.toEReal (Φ (x, u))) =
    ⨆ z : X × Y, (y z.2 : EReal) - ConvexAnalysis.Specs.toEReal (Φ z)
  simp_rw [real_sub_iInf]
  rw [iSup_prod, iSup_comm]

theorem marginal_biconjugate_bridge : Specs.marginal_biconjugate_bridge.{u,v} := by
  intro X Y _ _ _ Φ h u
  have hrep : (fun u => ConvexAnalysis.Specs.toEReal (Specs.marginalFunction Φ u)) =
      Specs.marginal Φ := funext (marginalFunction_representation Φ h)
  change (⨆ y : Y →L[ℝ] ℝ, (y u : EReal) - Specs.extendedConjugate (Specs.marginal Φ) y) =
    ⨆ y : Y →L[ℝ] ℝ, (y u : EReal) - ConvexAnalysis.Specs.conjugate (Specs.marginalFunction Φ) y
  congr 1
  funext y
  rw [← hrep, extendedConjugate_toEReal]

section Algebra
variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]

/-- The (0,y) product functional is the composition with the second projection. -/
theorem perturbationDualObjective_eq_neg_marginalConjugate
    (Φ : X × Y → WithTop ℝ) (y : Y →L[ℝ] ℝ) :
    perturbationDualObjective Φ y = -marginalConjugate Φ y := by
  change -ConvexAnalysis.Specs.conjugate Φ (y.comp (ContinuousLinearMap.snd ℝ X Y)) = _
  rw [← marginal_conjugate_identity]
  rfl

end Algebra

theorem perturbation_dual_bound : Specs.perturbation_dual_bound.{u,v} := by
  intro X Y _ _ _ _ _ _ Φ p hp
  have hobj (y : Y →L[ℝ] ℝ) : Specs.perturbationDualObjective Φ y ≤ (p : EReal) := by
    have h := le_iSup (fun u : Y => (y u : EReal) - Specs.marginal Φ u) 0
    change (y 0 : EReal) - Specs.marginal Φ 0 ≤ marginalConjugate Φ y at h
    have hlower : ((-p : ℝ) : EReal) ≤ marginalConjugate Φ y := by
      simpa only [hp, map_zero, EReal.coe_zero, zero_sub, EReal.coe_neg] using h
    have hn := EReal.neg_le_neg_iff.mpr hlower
    change perturbationDualObjective Φ y ≤ (p : EReal)
    rw [perturbationDualObjective_eq_neg_marginalConjugate]
    simpa only [EReal.coe_neg, neg_neg] using hn
  have hid : Specs.perturbationDualValue Φ = Specs.extendedBiconjugate (Specs.marginal Φ) 0 := by
    unfold Specs.perturbationDualValue Specs.extendedBiconjugate
    apply iSup_congr
    intro y
    change perturbationDualObjective Φ y = (y 0 : EReal) - marginalConjugate Φ y
    simpa only [map_zero, EReal.coe_zero, zero_sub] using
      perturbationDualObjective_eq_neg_marginalConjugate Φ y
  have hbound : Specs.perturbationDualValue Φ ≤ (p : EReal) := iSup_le hobj
  exact ⟨hid, hid ▸ hbound, hbound, hobj⟩

theorem perturbation_attainment : Specs.perturbation_attainment.{u,v} := by
  intro X Y _ _ _ _ _ _ Φ p hbot hp y
  have hrep (u : Y) : ConvexAnalysis.Specs.toEReal (marginalFunction Φ u) =
      Specs.marginal Φ u := marginalFunction_representation Φ hbot u
  have hf0 : marginalFunction Φ 0 = (p : WithTop ℝ) := by
    change (Specs.marginal Φ 0).unbotD ⊤ = _
    rw [hp]
    rfl
  have hc : conjugate (marginalFunction Φ) y = marginalConjugate Φ y := by
    change ConvexAnalysis.Specs.conjugate (Specs.marginalFunction Φ) y = Specs.marginalConjugate Φ y
    rw [← extendedConjugate_toEReal]
    have hr : (fun u => ConvexAnalysis.Specs.toEReal (Specs.marginalFunction Φ u)) =
        Specs.marginal Φ := funext hrep
    rw [hr]
    rfl
  have hsub : y ∈ subdifferential (marginalFunction Φ) 0 ↔
      marginalConjugate Φ y = ((-p : ℝ) : EReal) := by
    rw [subgradient_iff_conjugate_eq hf0, hc]
    simp only [map_zero, zero_sub]
  have hval : perturbationDualObjective Φ y = (p : EReal) ↔
      marginalConjugate Φ y = ((-p : ℝ) : EReal) := by
    rw [perturbationDualObjective_eq_neg_marginalConjugate]
    constructor
    · intro h
      have hh := congrArg Neg.neg h
      simpa only [neg_neg, EReal.coe_neg] using hh
    · intro h
      rw [h, EReal.coe_neg, neg_neg]
  constructor
  · constructor
    · intro h
      exact hsub.mpr (hval.mp h.1)
    · intro h
      have hy := hval.mpr (hsub.mp h)
      refine ⟨hy, le_antisymm (perturbation_dual_bound Φ p hp).2.2.1 ?_⟩
      exact hy ▸ le_iSup (Specs.perturbationDualObjective Φ) y
  · change y ∈ subdifferential (marginalFunction Φ) 0 ↔ _
    rw [mem_subdifferential_iff hf0]
    simp only [sub_zero]
    constructor
    · intro h u
      have hh := (toEReal_conventions.2.2.2.2 _ _).mpr (h u)
      rw [hrep u] at hh
      exact hh
    · intro h u
      apply (toEReal_conventions.2.2.2.2 _ _).mp
      rw [hrep u]
      exact h u

theorem perturbation_duality_algebra : Specs.perturbation_duality_algebra.{u,v} := by
  intro X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ Φ _ _ hv p hp
  exact ⟨marginal_conjugate_identity Φ,
    (perturbation_dual_bound Φ p hp).1,
    (perturbation_dual_bound Φ p hp).2.1,
    perturbation_attainment Φ p hv.1 hp⟩

end VariationalNotes.Ch04
