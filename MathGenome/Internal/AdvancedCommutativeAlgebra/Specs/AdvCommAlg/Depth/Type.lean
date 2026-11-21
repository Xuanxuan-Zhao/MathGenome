import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.FirstSurvivingExt
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! DP-05, paper.tex:2791–2795, 2805–2815. Canonical residue-field
structures descend the usual R-actions. The socle means 0 : maximalIdeal,
not a choice of a semisimple decomposition. -/
universe u
open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise
namespace AdvCommAlg.Depth

variable {R : Type u} [CommRing R] [IsLocalRing R]

abbrev ResidueExt (M : ModuleCat.{u} R) (n : ℕ) :=
  Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) M n

/-- The maximal ideal acts trivially on Ext from the residue field. -/
lemma residueExt_torsion (M : ModuleCat.{u} R) (n : ℕ) :
    Module.IsTorsionBySet R (ResidueExt M n) (IsLocalRing.maximalIdeal R) := by
  intro x a
  have hz : a.val • 𝟙 (ModuleCat.of R (IsLocalRing.ResidueField R)) = 0 := by
    ext z
    change (IsLocalRing.residue R a.val) * z = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr a.property, zero_mul]
  have hs : a.val • x = (Ext.mk₀ (a.val • 𝟙 (ModuleCat.of R
      (IsLocalRing.ResidueField R)))).comp x (zero_add n) := by
    simp [Ext.mk₀_smul]
  rw [hs, hz]
  simp

noncomputable instance residueExtModule (M : ModuleCat.{u} R) (n : ℕ) :
    Module (IsLocalRing.ResidueField R) (ResidueExt M n) :=
  (residueExt_torsion M n).module

instance residueExtTower (M : ModuleCat.{u} R) (n : ℕ) :
    IsScalarTower R (IsLocalRing.ResidueField R) (ResidueExt M n) :=
  (residueExt_torsion M n).isScalarTower

abbrev ResidueHom (R : Type u) [CommRing R] [IsLocalRing R] (U : Type u) [AddCommGroup U] [Module R U] :=
  IsLocalRing.ResidueField R →ₗ[R] U

lemma residueHom_torsion (U : Type u) [AddCommGroup U] [Module R U] :
    Module.IsTorsionBySet R (ResidueHom R U) (IsLocalRing.maximalIdeal R) := by
  intro f a
  ext z
  change a.val • f z = 0
  rw [← f.map_smul]
  have hz : a.val • z = 0 := by
    change (IsLocalRing.residue R a.val) * z = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr a.property, zero_mul]
  rw [hz, f.map_zero]

noncomputable instance residueHomModule (U : Type u) [AddCommGroup U] [Module R U] :
    Module (IsLocalRing.ResidueField R) (ResidueHom R U) :=
  (residueHom_torsion U).module

instance residueHomTower (U : Type u) [AddCommGroup U] [Module R U] :
    IsScalarTower R (IsLocalRing.ResidueField R) (ResidueHom R U) :=
  (residueHom_torsion U).isScalarTower

abbrev Socle (R : Type u) [CommRing R] [IsLocalRing R]
    (U : Type u) [AddCommGroup U] [Module R U] :=
  Submodule.torsionBySet R U (IsLocalRing.maximalIdeal R)

noncomputable instance socleResidueModule (U : Type u) [AddCommGroup U] [Module R U] :
    Module (IsLocalRing.ResidueField R) (Socle R U) :=
  inferInstanceAs (Module (R ⧸ IsLocalRing.maximalIdeal R) (Socle R U))

instance socleResidueTower (U : Type u) [AddCommGroup U] [Module R U] :
    IsScalarTower R (IsLocalRing.ResidueField R) (Socle R U) :=
  inferInstanceAs (IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) (Socle R U))

namespace Specs

noncomputable def depthDegreeValue (R : Type u) [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) : ℕ := (depthValue R M).toNat

def depthDegreeType := ∀ (R : Type u) [CommRing R] [IsLocalRing R], ModuleCat.{u} R → ℕ

noncomputable def moduleTypeValue (R : Type u) [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField R) (ResidueExt M (depthDegreeValue R M))

def moduleTypeType := ∀ (R : Type u) [CommRing R] [IsLocalRing R], ModuleCat.{u} R → ℕ

def depth_finiteType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
    depthValue R M ≠ ⊤ ∧ (depthDegreeValue R M : ℕ∞) = depthValue R M

def maximalRegular_length_eq_depthDegreeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M] (xs : List R),
    MaximalRegular (IsLocalRing.maximalIdeal R) M xs → xs.length = depthDegreeValue R M

/-- The second comparison is evaluation at the residue class of 1. -/
def homSocleEquivType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (U : Type u) [AddCommGroup U] [Module R U],
    ∃ e : ResidueHom R U ≃ₗ[IsLocalRing.ResidueField R] Socle R U,
      ∀ f, (e f).val = f 1

/-- All scalar structures here are the descended R-actions specified above. -/
def typeComparisonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M] (xs : List R),
    MaximalRegular (IsLocalRing.maximalIdeal R) M xs →
    ∃ e : ResidueExt M (depthDegreeValue R M) ≃ₗ[IsLocalRing.ResidueField R]
      ResidueHom R (FirstSurvivingExt.Quotient M xs),
    ∃ s : ResidueHom R (FirstSurvivingExt.Quotient M xs) ≃ₗ[IsLocalRing.ResidueField R]
      Socle R (FirstSurvivingExt.Quotient M xs), ∀ f, (s f).val = f 1

def typeExt_finiteType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M],
    FiniteDimensional (IsLocalRing.ResidueField R) (ResidueExt M (depthDegreeValue R M))

def moduleType_eq_socleType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M] (xs : List R),
    MaximalRegular (IsLocalRing.maximalIdeal R) M xs →
    moduleTypeValue R M = Module.finrank (IsLocalRing.ResidueField R)
      (Socle R (FirstSurvivingExt.Quotient M xs))

def socle_dimension_independentType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M] (xs ys : List R),
    MaximalRegular (IsLocalRing.maximalIdeal R) M xs →
    MaximalRegular (IsLocalRing.maximalIdeal R) M ys →
    Module.finrank (IsLocalRing.ResidueField R) (Socle R (FirstSurvivingExt.Quotient M xs)) =
    Module.finrank (IsLocalRing.ResidueField R) (Socle R (FirstSurvivingExt.Quotient M ys))

end Specs
end AdvCommAlg.Depth
