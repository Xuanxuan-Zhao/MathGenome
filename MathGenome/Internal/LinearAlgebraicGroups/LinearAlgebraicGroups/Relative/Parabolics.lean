import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.Parabolics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalFlagLifting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.SplitContractingRadical
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.SemiCartesianMonoidalCategory

universe u

namespace LinearAlgebraicGroups.Relative.Parabolics

open LinearAlgebraicGroups.Specs (IsSchemeKernel)
open Specs.Relative.Parabolics
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private pushSubgroup pushRadical subgroup_iso transported_kernel
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy
open private restrictSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

private theorem cocharacterLeviDecomposition : CocharacterLeviDecomposition.{u} := by
  intro k _ G P hP
  obtain ⟨c, D, hsame, hcentralizer, hradical⟩ :=
    RationalCocharacter.rationalParabolic G P hP
  obtain ⟨e, he⟩ := subgroup_iso hsame.1 hsame.2
  let U := pushSubgroup (contractingSubgroup D) e.symm
  have hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U :=
    pushRadical (A := closedSubgroupAlgebraicGroup D.parabolic)
      (B := closedSubgroupAlgebraicGroup P) e.symm hradical.1
  have hi : (Iso.refl U.group).hom ≫ D.contractingToParabolic = U.inclusion ≫ e.hom := by
    change 𝟙 _ ≫ D.contractingToParabolic = (D.contractingToParabolic ≫ e.inv) ≫ e.hom
    simp
  have hker : IsSchemeKernel (e.hom ≫ D.limit) U :=
    transported_kernel (B := contractingSubgroup D) e (Iso.refl _) hi D.isKernel
  let s := D.sectionMap ≫ e.inv
  have hs : s ≫ P.inclusion = D.centralizer.inclusion := by
    change (D.sectionMap ≫ e.inv) ≫ P.inclusion = _
    rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, D.section_in_G]
  let L := restrictSubgroup D.centralizer P s hs
  have hj : (Iso.refl L.group).hom ≫ D.sectionMap = L.inclusion ≫ e.hom := by
    change 𝟙 _ ≫ D.sectionMap = (D.sectionMap ≫ e.inv) ≫ e.hom
    simp
  have hLevi : IsIso (L.inclusion ≫ (e.hom ≫ D.limit)) := by
    change IsIso ((D.sectionMap ≫ e.inv) ≫ (e.hom ≫ D.limit))
    rw [Category.assoc, Iso.inv_hom_id_assoc, D.section_limit]
    infer_instance
  exact ⟨c, D, e, U, Iso.refl _, L, Iso.refl _, he, hi, hj, hker, hLevi,
    hcentralizer, hradical, hU, SplitContractingRadical.splitContractingSubgroup G hP.1 c D⟩

private theorem rationalLeviConjugacy : RationalLeviConjugacy.{u} := by
  intro k _ G P hP U hU Q q hq L L' hL hL'
  obtain ⟨a, ha⟩ := LeviConjugacy.leviConjugacy G P hP U hU Q q hq L L' hL hL'
  refine ⟨a, (ha _ a).2 ?_, fun b hb ↦ ?_⟩
  · simp only [toUnit_unit, Category.id_comp]
  · simpa only [toUnit_unit, Category.id_comp] using (ha _ b).1 hb

private theorem rationalFlagCosets : RationalFlagCosets.{u} := by
  intro k _ G P hP D
  obtain ⟨e, he, _⟩ := TorsorObstruction.rationalPointsOfPresentation D
  let cosetEquiv := Equiv.ofBijective (Specs.TorsorObstruction.rationalCosetMap P)
    (RationalFlagLifting.rationalFlagLifting G P hP)
  exact ⟨cosetEquiv.trans e, fun g ↦ he g⟩

/-- Rational parabolics, Levis, rational flag cosets, and the classification
of parabolic families by the flag scheme. -/
theorem rationalParabolics : Statement.{u} :=
  ⟨cocharacterLeviDecomposition, rationalLeviConjugacy, rationalFlagCosets,
    MaximalSplitTori.minimalParabolicsConjugate, MaximalSplitTori.maximalSplitToriConjugate,
    ParabolicFamilyTransporter.parabolicFamilyRepresentability,
    ParabolicFamilyTransporter.classifies_baseChange⟩

end LinearAlgebraicGroups.Relative.Parabolics
