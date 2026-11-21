import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ExtScalarActions

/-!
The two scalar actions on Ext and annihilation by the first module's annihilator
(paper.tex, Lemma DP-03, scalar-action part).

Ext composition is bilinear. Composing with the degree-zero class of a scalar
multiple of the identity therefore gives that scalar multiple of the Ext class,
on either side. If the scalar annihilates the first module, its multiplication
morphism is zero, so its action on Ext is zero as well.
-/

universe u

open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Depth.ExtScalarActions

/-- Multiplication on the first module computes the scalar action on Ext. -/
theorem scalar_eq_precomposition (R : Type u) [CommRing R] (N M : ModuleCat.{u} R)
    (a : R) (i : ℕ) (x : Ext N M i) :
    a • x = (Ext.mk₀ (a • 𝟙 N)).comp x (zero_add i) := by
  simp [Ext.mk₀_smul]

/-- Multiplication on the second module computes the same scalar action. -/
theorem scalar_eq_postcomposition (R : Type u) [CommRing R] (N M : ModuleCat.{u} R)
    (a : R) (i : ℕ) (x : Ext N M i) :
    a • x = x.comp (Ext.mk₀ (a • 𝟙 M)) (add_zero i) := by
  exact Ext.smul_eq_comp_mk₀ x a

/-- The annihilator of the first module acts by zero on Ext in every degree. -/
theorem annihilator_smul_eq_zero (R : Type u) [CommRing R] (N M : ModuleCat.{u} R)
    (a : R) (ha : a ∈ Module.annihilator R N) (i : ℕ) (x : Ext N M i) :
    a • x = 0 := by
  have hzero : a • 𝟙 N = 0 := by
    rw [← ModuleCat.lsmul_eq_smul_id,
      Module.mem_annihilator_iff_lsmul_eq_zero.mp ha]
    rfl
  rw [scalar_eq_precomposition R N M a i x, hzero]
  simp

end AdvCommAlg.Depth.ExtScalarActions
