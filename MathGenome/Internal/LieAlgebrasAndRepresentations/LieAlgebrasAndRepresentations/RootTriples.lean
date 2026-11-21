import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootForm
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootTriples
import Mathlib.Algebra.Lie.Weights.RootSystem
import Batteries.Tactic.OpenPrivate

/-! Root triples and reducedness (LA-D03). We bridge ordinary root spaces to
Mathlib's generalized root spaces and identify its coroot with the source's
Killing-normalized coroot before applying the library root theorems. -/

universe u
namespace LieAlgebrasAndRepresentations

open private maximal_toral_centralizer_cartan toral_genWeightSpace_eq_weightSpace
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.MaximalTori

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

private theorem maximalToral_isCartan (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H) : H.IsCartanSubalgebra := by
  have hc := maximal_toral_centralizer_cartan hss H hH
  rwa [maximal_toral_centralizer hss H hH] at hc

private theorem rootSpace_eq_generalized (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    [H.IsCartanSubalgebra] (α : H → ℂ) :
    (LieModule.genWeightSpace L α).toSubmodule =
      (LieModule.weightSpace L α).toSubmodule := by
  let : IsLieAbelian H := hH.1.1
  exact congrArg LieSubmodule.toSubmodule (toral_genWeightSpace_eq_weightSpace H hH.1 α)

private def rootWeight (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    [H.IsCartanSubalgebra]
    (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) : LieModule.Weight ℂ H L :=
  ⟨α, by
    intro hz
    apply hα.2
    change (LieModule.weightSpace L (α : H → ℂ)).toSubmodule = ⊥
    rw [← rootSpace_eq_generalized H hH α, hz]
    rfl⟩

private theorem rootWeight_nonzero (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    [H.IsCartanSubalgebra]
    (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) :
    (rootWeight H hH α hα).IsNonZero := by
  intro hz
  exact hα.1 (LinearMap.ext fun h => congrFun hz h)

private theorem cartanDual_symm_eq_tAlpha (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    [H.IsCartanSubalgebra] [LieAlgebra.IsKilling ℂ L] (α : Module.Dual ℂ H) :
    (LieAlgebra.IsKilling.cartanEquivDual H).symm α = tAlpha H α := by
  apply tAlpha_unique hss H hH
  intro h
  change (LieAlgebra.IsKilling.cartanEquivDual H)
    ((LieAlgebra.IsKilling.cartanEquivDual H).symm α) h = α h
  rw [LinearEquiv.apply_symm_apply]

private theorem rootWeight_toLinear (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    [H.IsCartanSubalgebra] (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) :
    ((rootWeight H hH α hα) : Module.Dual ℂ H) = α := by
  ext h
  rfl

private theorem coroot_rootWeight (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    [H.IsCartanSubalgebra] [LieAlgebra.IsKilling ℂ L]
    (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) :
    LieAlgebra.IsKilling.coroot (rootWeight H hH α hα) = killingCoroot H α := by
  rw [LieAlgebra.IsKilling.coroot, rootWeight_toLinear,
    cartanDual_symm_eq_tAlpha hss H hH, killingCoroot_eq,
    rootForm_eq_apply hss H hH]
  simp only [rootWeight, two_smul, ← add_smul, div_eq_mul_inv, two_mul]
  rfl

theorem rootForm_self_ne_zero (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) : rootForm H α α ≠ 0 := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  have hn := LieAlgebra.IsKilling.root_apply_cartanEquivDual_symm_ne_zero
    (rootWeight_nonzero H hH α hα)
  rw [rootWeight_toLinear, cartanDual_symm_eq_tAlpha hss H hH] at hn
  exact (rootForm_eq_apply hss H hH α α) ▸ hn

theorem exists_root_triple (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) :
    ∃ e f : L, e ∈ rootSpace H α ∧ f ∈ rootSpace H (-α) ∧
      e ≠ 0 ∧ f ≠ 0 ∧ ⁅e, f⁆ = (killingCoroot H α : L) ∧
      ⁅(killingCoroot H α : L), e⁆ = (2 : ℂ) • e ∧
      ⁅(killingCoroot H α : L), f⁆ = (-2 : ℂ) • f := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  let a := rootWeight H hH α hα
  have ha := rootWeight_nonzero H hH α hα
  obtain ⟨h, e, f, ht, he, hf⟩ :=
    LieAlgebra.IsKilling.exists_isSl2Triple_of_weight_isNonZero ha
  have hh : h = (killingCoroot H α : L) :=
    (ht.h_eq_coroot ha he hf).trans (congrArg Subtype.val (coroot_rootWeight hss H hH α hα))
  refine ⟨e, f, ?_, ?_, ht.e_ne_zero, ht.f_ne_zero, ht.lie_e_f.trans hh, ?_, ?_⟩
  · change e ∈ (LieModule.weightSpace L (α : H → ℂ)).toSubmodule
    rw [← rootSpace_eq_generalized H hH]
    exact he
  · change f ∈ (LieModule.weightSpace L ((-α) : H → ℂ)).toSubmodule
    rw [← rootSpace_eq_generalized H hH]
    exact hf
  · rw [← hh]
    exact ht.lie_h_e_smul ℂ
  · rw [← hh]
    simpa only [neg_smul] using ht.lie_lie_smul_f ℂ

theorem finrank_rootSpace_eq_one (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α : Module.Dual ℂ H) (hα : α ∈ rootSet H) :
    Module.finrank ℂ (rootSpace H α) = 1 := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  have hn := LieAlgebra.IsKilling.finrank_rootSpace_eq_one (rootWeight H hH α hα)
    (rootWeight_nonzero H hH α hα)
  change Module.finrank ℂ (LieModule.genWeightSpace L (α : H → ℂ)).toSubmodule = 1 at hn
  rwa [rootSpace_eq_generalized H hH] at hn

theorem proportional_root_eq (hss : IsSemisimple ℂ L)
    (H : LieSubalgebra ℂ L) (hH : IsMaximalToral H)
    (α β : Module.Dual ℂ H) (hα : α ∈ rootSet H) (hβ : β ∈ rootSet H)
    (c : ℂ) (hc : β = c • α) : β = α ∨ β = -α := by
  let : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  let : H.IsCartanSubalgebra := maximalToral_isCartan hss H hH
  have hr := LieAlgebra.IsKilling.eq_neg_or_eq_of_eq_smul
    (rootWeight H hH α hα) (rootWeight H hH β hβ)
    (rootWeight_nonzero H hH β hβ) c (congrArg DFunLike.coe hc)
  rcases hr with hr | hr
  · right
    exact LinearMap.ext fun h => congrArg (fun w : LieModule.Weight ℂ H L => w h) hr
  · left
    exact LinearMap.ext fun h => congrArg (fun w : LieModule.Weight ℂ H L => w h) hr

end LieAlgebrasAndRepresentations
