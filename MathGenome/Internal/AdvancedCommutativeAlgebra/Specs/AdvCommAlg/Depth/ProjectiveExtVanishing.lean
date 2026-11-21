import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-! Independent statements for the projective-dimension assertions of DP-11.
`HasProjectiveDimensionLE N ℓ` permits any finite upper bound on projective
 dimension, and in particular the actual finite dimension ℓ. Subtraction is
in ℕ∞, so infinite grade gives vanishing in every natural degree.
Projective dimension is in `WithBot ℕ∞`, with the zero module at bottom. -/

universe u
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Depth.Specs

def ext_vanishes_below_grade_sub_projectiveDimensionType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E N : ModuleCat.{u} R) [Module.Finite R E] [Module.Finite R N]
    (ℓ : ℕ) [HasProjectiveDimensionLE N ℓ] (i : ℕ),
    (i : ℕ∞) < gradeValue (Module.annihilator R E) R - (ℓ : ℕ∞) →
      Subsingleton (Ext E N i)

def grade_annihilator_le_projectiveDimensionType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (E : ModuleCat.{u} R) [Module.Finite R E] [Nontrivial E],
    (gradeValue (Module.annihilator R E) R : WithBot ℕ∞) ≤ projectiveDimension E

end AdvCommAlg.Depth.Specs
