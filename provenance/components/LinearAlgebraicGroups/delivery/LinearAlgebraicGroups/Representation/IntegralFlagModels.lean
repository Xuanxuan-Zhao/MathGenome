import Specs.LinearAlgebraicGroups.Representation.IntegralFlagModels
import LinearAlgebraicGroups.Representation.IntegralFlagGeometry
import LinearAlgebraicGroups.Representation.FlagCohomology
import LinearAlgebraicGroups.Cohomology.ArithmeticProjectiveFiniteness
import LinearAlgebraicGroups.Cohomology.ArithmeticCohomologyBaseChange
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Representation.IntegralFlagModels

open Specs.IntegralFlagModels (Statement)
open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticProjectiveFiniteness (IsLineBundleOn)
open Specs.ArithmeticCohomologyBaseChange (IsLocallyFree)
open Cohomology.ArithmeticCohomologyBaseChange (arithmeticBaseChange finiteAffineCover)
open private freeSingletonIso from LinearAlgebraicGroups.Representation.FlagCohomology

private theorem isLocallyFree_of_isLineBundleOn {A : Type u} [CommRing A]
    {X : SchemeOverRing A} {F : X.left.Modules} (h : IsLineBundleOn A X F) :
    IsLocallyFree F := by
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := h.2 x
  exact ⟨U, hx, PUnit.{u + 1}, ⟨e ≪≫ (freeSingletonIso U.toScheme.ringCatSheaf).symm⟩⟩

/-- Arithmetic cohomology of the equivariant line on the marked flag model. -/
theorem integralFlagModel : Statement.{u} := by
  intro D hss hspan weight
  obtain ⟨M⟩ := IntegralFlagGeometry.integralFlagGeometry D hss hspan weight
  obtain ⟨n, j, hj⟩ := M.model.projective
  have hFinite := Cohomology.ArithmeticProjectiveFiniteness.arithmeticProjectiveFiniteness
    M.m M.nonzero M.model.flag n j hj M.model.line M.lineBundle
  let : IsProper M.model.flag.hom :=
    IntegralFlagGeometry.proper_of_projectiveOver M.model.flag M.model.projective
  let : Flat M.model.flag.hom := M.model.flat
  let : CompactSpace M.model.flag.left :=
    QuasiCompact.compactSpace_of_compactSpace M.model.flag.hom
  let : IsSeparated (terminal.from M.model.flag.left) := by
    rw [← terminal.comp_from M.model.flag.hom]
    infer_instance
  have hm : (M.m : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr M.nonzero
  have hChange := arithmeticBaseChange (M.m : ℤ) hm
    M.model.flag M.model.line M.lineBundle.1 (isLocallyFree_of_isLineBundleOn M.lineBundle)
  refine ⟨M, hFinite, hChange.1, finiteAffineCover (X := M.model.flag.left), ?_⟩
  intro p _ hp
  have hp' : ¬ (p : ℤ) ∣ (M.m : ℤ) := by exact_mod_cast hp
  exact hChange.2 p hp'

end LinearAlgebraicGroups.Representation.IntegralFlagModels
