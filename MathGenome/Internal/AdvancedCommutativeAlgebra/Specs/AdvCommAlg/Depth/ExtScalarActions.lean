import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.Ideal.Maps

/-!
Independent statements for the scalar-action part of paper.tex, Lemma DP-03.
`Ext` is Mathlib's Ext group in the category of all modules, and `mk₀` sends
an ordinary module homomorphism to degree-zero Ext. The morphism `a • 𝟙 N`
is multiplication by `a` (definitionally `ModuleCat.ofHom (LinearMap.lsmul R N a)`).
No Noetherian, finiteness, local-ring or nonzero hypotheses are imposed.
-/

universe u

open CategoryTheory CategoryTheory.Abelian

namespace Specs.AdvCommAlg.Depth.ExtScalarActions

/-- The scalar action equals the contravariant action of multiplication on the first module. -/
def scalar_eq_precomposition : Prop :=
  ∀ (R : Type u) [CommRing R] (N M : ModuleCat.{u} R)
    (a : R) (i : ℕ) (x : Ext N M i),
    a • x = (Ext.mk₀ (a • 𝟙 N)).comp x (zero_add i)

/-- The scalar action equals the covariant action of multiplication on the second module. -/
def scalar_eq_postcomposition : Prop :=
  ∀ (R : Type u) [CommRing R] (N M : ModuleCat.{u} R)
    (a : R) (i : ℕ) (x : Ext N M i),
    a • x = x.comp (Ext.mk₀ (a • 𝟙 M)) (add_zero i)

/-- Every element of the annihilator of the first module kills each Ext group. -/
def annihilator_smul_eq_zero : Prop :=
  ∀ (R : Type u) [CommRing R] (N M : ModuleCat.{u} R)
    (a : R) (_ : a ∈ Module.annihilator R N) (i : ℕ) (x : Ext N M i),
    a • x = 0

end Specs.AdvCommAlg.Depth.ExtScalarActions
