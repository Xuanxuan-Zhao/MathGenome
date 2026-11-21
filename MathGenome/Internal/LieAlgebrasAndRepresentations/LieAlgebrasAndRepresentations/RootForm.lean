import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootDecomposition
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RootForm

/-! LA-U07: the Killing identification of the Cartan subalgebra with its dual,
the induced root form, and the opposite-root bracket formula (4.1). -/

universe u
namespace LieAlgebrasAndRepresentations

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

noncomputable abbrev rootDualMap (H : LieSubalgebra ℂ L) : Module.Dual ℂ H →ₗ[ℂ] H :=
  Specs.LieAlgebrasAndRepresentations.RootForm.rootDualMap_value H

noncomputable abbrev tAlpha (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) : H :=
  Specs.LieAlgebrasAndRepresentations.RootForm.tAlpha_value H α

noncomputable abbrev rootForm (H : LieSubalgebra ℂ L) :
    LinearMap.BilinForm ℂ (Module.Dual ℂ H) :=
  Specs.LieAlgebrasAndRepresentations.RootForm.rootForm_value H

/-- The coroot in the Cartan subalgebra, normalized using the complex Killing form. -/
noncomputable abbrev killingCoroot (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) : H :=
  Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H α

theorem tAlpha_pairing (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (α : Module.Dual ℂ H) (h : H) :
    killingForm ℂ L (tAlpha H α : L) (h : L) = α h := by
  have hB := killingForm_restrict_toral_nondegenerate hss H hH
  change ((killingForm ℂ L).restrict H.toSubmodule) (rootDualMap H α) h = α h
  unfold rootDualMap Specs.LieAlgebrasAndRepresentations.RootForm.rootDualMap_value
  dsimp only [killingForm,
    Specs.LieAlgebrasAndRepresentations.TraceCriterion.killingForm_value] at hB ⊢
  rw [dite_eq_left hB]
  exact LinearMap.BilinForm.apply_toDual_symm_apply α h

theorem tAlpha_unique (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (α : Module.Dual ℂ H) (t : H)
    (ht : ∀ h : H, killingForm ℂ L (t : L) (h : L) = α h) : t = tAlpha H α := by
  apply eq_of_sub_eq_zero
  apply (killingForm_restrict_toral_nondegenerate hss H hH).1
  intro h
  change killingForm ℂ L ((t : L) - (tAlpha H α : L)) (h : L) = 0
  rw [map_sub, LinearMap.sub_apply, ht h, tAlpha_pairing hss H hH, sub_self]

@[simp] theorem rootForm_apply (H : LieSubalgebra ℂ L) (α β : Module.Dual ℂ H) :
    rootForm H α β = killingForm ℂ L (tAlpha H α : L) (tAlpha H β : L) := rfl

theorem rootForm_eq_apply (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (α β : Module.Dual ℂ H) :
    rootForm H α β = α (tAlpha H β) :=
  tAlpha_pairing hss H hH α (tAlpha H β)

theorem opposite_root_bracket (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (α : Module.Dual ℂ H) (e f : L)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (-α)) :
    ⁅e, f⁆ = killingForm ℂ L e f • (tAlpha H α : L) := by
  have hef : ⁅e, f⁆ ∈ H := by
    have hm := rootSpace_bracket H α (-α) e f he hf
    change ⁅e, f⁆ ∈ H.toSubmodule
    simpa only [add_neg_cancel, rootSpace_zero hss H hH] using hm
  let z : H := ⟨⁅e, f⁆, hef⟩
  have hz : z = killingForm ℂ L e f • tAlpha H α := by
    apply eq_of_sub_eq_zero
    apply (killingForm_restrict_toral_nondegenerate hss H hH).1
    intro h
    have hfh : ⁅f, (h : L)⁆ = α h • f := by
      rw [← lie_skew f (h : L), (mem_rootSpace H (-α) f).mp hf h]
      simp
    change killingForm ℂ L (⁅e, f⁆ - killingForm ℂ L e f • (tAlpha H α : L)) (h : L) = 0
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      tAlpha_pairing hss H hH, killingForm_invariant, hfh, map_smul, smul_eq_mul,
      smul_eq_mul, mul_comm, sub_self]
  exact congrArg (fun x : H => (x : L)) hz

@[simp] theorem killingCoroot_eq (H : LieSubalgebra ℂ L) (α : Module.Dual ℂ H) :
    killingCoroot H α = (2 / rootForm H α α) • tAlpha H α := rfl

theorem killingCoroot_pairing (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L)
    (hH : IsMaximalToral H) (α β : Module.Dual ℂ H) :
    β (killingCoroot H α) = 2 * rootForm H β α / rootForm H α α := by
  rw [killingCoroot_eq, map_smul, smul_eq_mul, ← rootForm_eq_apply hss H hH β α,
    div_mul_eq_mul_div]

end LieAlgebrasAndRepresentations
