import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! Independent statements for CM-19, paper.tex:3956–3958 and 4014–4025.
The global dimension is the supremum of the actual projective dimensions of
all modules in the chosen universe. The arbitrary-module bounds also allow
a separate module universe, assuming only that the scalar ring fits in it.
No finite-generation or nonzero hypothesis is imposed on these modules. -/

universe u v
open CategoryTheory
namespace AdvCommAlg.CohenMacaulay.Specs

def globalDimensionType := (R : Type u) → [CommRing R] → WithBot ℕ∞

noncomputable def globalDimensionValue (R : Type u) [CommRing R] : WithBot ℕ∞ :=
  ⨆ M : ModuleCat.{u} R, projectiveDimension M

def regularLocal_injectiveDimension_le_allType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [Small.{v} R]
    (T : ModuleCat.{v} R) (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) →
      injectiveDimension T ≤ (d : WithBot ℕ∞)

def regularLocal_projectiveDimension_le_allType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [Small.{v} R]
    (T : ModuleCat.{v} R) (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) →
      projectiveDimension T ≤ (d : WithBot ℕ∞)

def regularLocal_residueField_attains_globalDimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) →
      projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (d : WithBot ℕ∞)

def regularLocal_globalDimension_eqType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) →
      globalDimensionValue R = (d : WithBot ℕ∞)

end AdvCommAlg.CohenMacaulay.Specs
