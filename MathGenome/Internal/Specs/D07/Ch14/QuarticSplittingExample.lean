import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! Independent specification for K07.14.quartic_splitting_example.
All fields use the displayed inclusions in ℂ. The nested definition of L
records the tower ℚ ⊆ ℚ(a) ⊆ ℚ(a)(i); FieldData also requires that this is
exactly ℚ(a,i). Automorphisms multiply by left function composition.
-/
noncomputable section
namespace Specs.D07.Ch14.QuarticSplittingExample
open Polynomial IntermediateField

def aReal : ℝ := Real.sqrt (Real.sqrt 2)
def aComplex : ℂ := aReal

def realRootField : IntermediateField ℚ ℂ := adjoin ℚ {aComplex}
def splittingField : IntermediateField ℚ ℂ :=
  (adjoin realRootField ({Complex.I} : Set ℂ)).restrictScalars ℚ

abbrev L := splittingField

def a : L := ⟨aComplex, (adjoin realRootField {Complex.I}).algebraMap_mem
  ⟨aComplex, mem_adjoin_simple_self ℚ aComplex⟩⟩
def i : L := ⟨Complex.I, mem_adjoin_simple_self realRootField Complex.I⟩

def polynomial : ℚ[X] := X ^ 4 - C 2

def rationalI : IntermediateField ℚ L := adjoin ℚ {i}
def rationalA : IntermediateField ℚ L := adjoin ℚ {a}

def rotations (r : L ≃ₐ[ℚ] L) : Subgroup (L ≃ₐ[ℚ] L) := Subgroup.zpowers r
def reflection (s : L ≃ₐ[ℚ] L) : Subgroup (L ≃ₐ[ℚ] L) := Subgroup.zpowers s

/-- Positivity selects the positive real fourth root, rather than a conjugate. -/
def RootData : Prop := 0 < aReal ∧ aReal ^ 4 = 2 ∧ (a : ℂ) = aComplex ∧ (i : ℂ) = Complex.I

def FieldData : Prop :=
  splittingField = adjoin ℚ ({aComplex, Complex.I} : Set ℂ) ∧
  FiniteDimensional ℚ L ∧ Module.finrank ℚ L = 8 ∧
  Polynomial.IsSplittingField ℚ L polynomial ∧ IsGalois ℚ L ∧
  Module.finrank ℚ rationalA = 4 ∧ Module.finrank ℚ rationalI = 2

/-- The isomorphism identifies the specified automorphisms with the rotation
and reflection in the dihedral group of order eight. -/
def AutomorphismData (r s : L ≃ₐ[ℚ] L) : Prop :=
  r a = i * a ∧ r i = i ∧ s a = a ∧ s i = -i ∧
  r ^ 4 = 1 ∧ s ^ 2 = 1 ∧ s * r * s = r⁻¹ ∧
  Subgroup.closure ({r, s} : Set (L ≃ₐ[ℚ] L)) = ⊤ ∧
  Nat.card (L ≃ₐ[ℚ] L) = 8 ∧
  ∃ e : DihedralGroup 4 ≃* (L ≃ₐ[ℚ] L),
    e (DihedralGroup.r 1) = r ∧ e (DihedralGroup.sr 0) = s

/-- Actual equality of intermediate fields of the same L, using the same r,s. -/
def SubgroupData (r s : L ≃ₐ[ℚ] L) : Prop :=
  Nat.card (rotations r) = 4 ∧ (rotations r).index = 2 ∧
  Nat.card (reflection s) = 2 ∧ (reflection s).index = 4 ∧
  IntermediateField.fixedField (rotations r) = rationalI ∧
  IntermediateField.fixedField (reflection s) = rationalA ∧
  (rotations r).Normal ∧ ¬ (reflection s).Normal ∧
  IsGalois ℚ rationalI ∧ ¬ Normal ℚ rationalA

def Example : Prop := RootData ∧ FieldData ∧
  ∃ r s : L ≃ₐ[ℚ] L, AutomorphismData r s ∧ SubgroupData r s

end Specs.D07.Ch14.QuarticSplittingExample
