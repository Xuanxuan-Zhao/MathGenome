import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.Maschke
import MathGenome.Internal.AlgebraCore.P103.Ch03.Semisimple
import Mathlib.RepresentationTheory.Maschke

noncomputable section
namespace P103.Ch08.Maschke
open scoped MonoidAlgebra

/-- A simple group-algebra module restricts to an irreducible representation,
including the nonzero requirement. -/
theorem irreducible_of_simple_module {k G M : Type*} [Field k] [Group G]
    [AddCommGroup M] [Module k[G] M] [IsSimpleModule k[G] M] :
    @Irreducible k G (RestrictScalars k k[G] M) _ _ _
      (RestrictScalars.module k k[G] M) (Representation.ofModule (k := k) (G := G) M) := by
  constructor
  · exact IsSimpleModule.nontrivial k[G] M
  · intro U
    let E := Subrepresentation.submoduleSubrepresentationOrderIso
      (A := k) (G := G) (M := M)
    have h := eq_bot_or_eq_top (E.symm U)
    rcases h with h | h
    · left
      exact E.symm.injective (h.trans E.symm.map_bot.symm)
    · right
      exact E.symm.injective (h.trans E.symm.map_top.symm)

theorem semisimple : MaschkeSpecs.semisimpleType := by
  intro k G V _ _ _ _ _ ρ h
  have : NeZero (Nat.card G : k) := ⟨h⟩
  infer_instance

theorem invariant_complement : MaschkeSpecs.invariantComplementType := by
  intro k G V _ _ _ _ _ ρ h U
  have := semisimple ρ h
  obtain ⟨N, hN⟩ := exists_isCompl U.asSubmodule
  refine ⟨Subrepresentation.ofSubmodule' N, ?_⟩
  have hrestrict := (Submodule.isCompl_restrictScalars_iff k).mpr hN
  exact hrestrict

theorem direct_sum : MaschkeSpecs.directSumType := by
  intro k G V _ _ _ _ _ ρ h
  have := semisimple ρ h
  obtain ⟨s, e, hs⟩ :=
    (P103.Ch03.Semisimple.semisimple_iff_directSum k[G] ρ.asModule).mp inferInstance
  refine ⟨s, e, fun U => ?_⟩
  have := hs U
  exact ⟨hs U, irreducible_of_simple_module⟩

theorem finite_direct_sum : MaschkeSpecs.finiteDirectSumType := by
  intro k G V _ _ _ _ _ _ ρ h
  have := semisimple ρ h
  have : Module.Finite k ρ.asModule := Module.Finite.equiv ρ.asModuleEquiv.symm
  have : Module.Finite k[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] ρ.asModule
  obtain ⟨n, S, e, hs⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp k[G] ρ.asModule
  refine ⟨n, S, e, fun i => ?_⟩
  have := hs i
  exact ⟨hs i, irreducible_of_simple_module⟩

end P103.Ch08.Maschke
