import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.RegularGlobalDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Homological.ExtProjectivityTest
import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-! CM-19: the global dimension of a regular local ring.
Every cyclic quotient is finite, so CM-12 bounds its projective dimension.
Baer's criterion with dimension shifting then bounds the injective dimension
of every module. The general Ext projectivity test converts this to a bound
on the projective dimension of every module. The residue field attains it. -/

universe u v
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.CohenMacaulay

/-- The supremum over all modules, including modules that are not finite. -/
noncomputable def globalDimension (R : Type u) [CommRing R] : WithBot ℕ∞ :=
  ⨆ M : ModuleCat.{u} R, projectiveDimension M

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- The Baer/dimension-shifting step applies to an arbitrary target module. -/
theorem regularLocal_injectiveDimension_le_all [Small.{v} R]
    (T : ModuleCat.{v} R) (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    injectiveDimension T ≤ (d : WithBot ℕ∞) := by
  apply (injectiveDimension_le_iff T d).mpr
  apply ModuleCat.hasInjectiveDimensionLE_of_quotients T d
  intro I
  let Q := ModuleCat.of R (R ⧸ I)
  have hQ : HasProjectiveDimensionLE Q d := (projectiveDimension_le_iff Q d).mp
    (regularLocal_projectiveDimension_le R Q d hd)
  let := hQ
  let : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ I))) d :=
    ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
      (M := Q) (Shrink.linearEquiv R (R ⧸ I)).symm d
  exact HasProjectiveDimensionLT.subsingleton _ (d + 1) (d + 1) le_rfl T

/-- There is no finite-generation restriction on `T`. -/
theorem regularLocal_projectiveDimension_le_all [Small.{v} R]
    (T : ModuleCat.{v} R) (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    projectiveDimension T ≤ (d : WithBot ℕ∞) := by
  apply AdvCommAlg.projectiveDimension_le_of_ext_vanishes T d
  intro V
  let : HasInjectiveDimensionLE V d := (injectiveDimension_le_iff V d).mp
    (regularLocal_injectiveDimension_le_all R V d hd)
  exact HasInjectiveDimensionLT.subsingleton V (d + 1) (d + 1) le_rfl T

/-- The residue field witnesses sharpness of the arbitrary-module bound. -/
theorem regularLocal_residueField_attains_globalDimension (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (d : WithBot ℕ∞) :=
  regularLocal_residueField_projectiveDimension R d hd

/-- The global dimension equals the Krull dimension, including dimension zero. -/
theorem regularLocal_globalDimension_eq (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) :
    globalDimension R = (d : WithBot ℕ∞) := by
  apply le_antisymm
  · exact iSup_le fun T => regularLocal_projectiveDimension_le_all R T d hd
  · rw [← regularLocal_residueField_attains_globalDimension R d hd]
    exact le_iSup (fun T : ModuleCat.{u} R => projectiveDimension T)
      (ModuleCat.of R (IsLocalRing.ResidueField R))

end AdvCommAlg.CohenMacaulay
