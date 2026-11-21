import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Depth.Basic

/-! Independent specifications for DP-07 (paper.tex:2847–2884).
A short exact complex represents 0 → L → M → N → 0. No term is assumed
nonzero. Values lie in ℕ∞, with truncated subtraction and ⊤ ± 1 = ⊤. -/

universe u
open CategoryTheory
namespace AdvCommAlg.Depth.Specs

def grade_min_le_middleType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    min (gradeValue I S.X₁) (gradeValue I S.X₃) ≤ gradeValue I S.X₂

def grade_min_add_one_le_leftType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    min (gradeValue I S.X₂) (gradeValue I S.X₃ + 1) ≤ gradeValue I S.X₁

def grade_min_sub_one_le_rightType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    min (gradeValue I S.X₂) (gradeValue I S.X₁ - 1) ≤ gradeValue I S.X₃

def grade_middle_eq_left_of_left_lt_rightType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    gradeValue I S.X₁ < gradeValue I S.X₃ → gradeValue I S.X₂ = gradeValue I S.X₁

def grade_middle_eq_right_of_right_add_one_lt_leftType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    gradeValue I S.X₃ + 1 < gradeValue I S.X₁ → gradeValue I S.X₂ = gradeValue I S.X₃

def grade_right_eq_sub_one_of_left_lt_middleType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    gradeValue I S.X₁ < gradeValue I S.X₂ → 1 ≤ gradeValue I S.X₁ ∧ gradeValue I S.X₃ = gradeValue I S.X₁ - 1

def depth_min_le_middleType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    min (depthValue R S.X₁) (depthValue R S.X₃) ≤ depthValue R S.X₂

def depth_min_add_one_le_leftType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    min (depthValue R S.X₂) (depthValue R S.X₃ + 1) ≤ depthValue R S.X₁

def depth_min_sub_one_le_rightType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    min (depthValue R S.X₂) (depthValue R S.X₁ - 1) ≤ depthValue R S.X₃

def depth_middle_eq_left_of_left_lt_rightType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    depthValue R S.X₁ < depthValue R S.X₃ → depthValue R S.X₂ = depthValue R S.X₁

def depth_middle_eq_right_of_right_add_one_lt_leftType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    depthValue R S.X₃ + 1 < depthValue R S.X₁ → depthValue R S.X₂ = depthValue R S.X₃

def depth_right_eq_sub_one_of_left_lt_middleType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₁]
    [Module.Finite R S.X₂] [Module.Finite R S.X₃], S.ShortExact →
    depthValue R S.X₁ < depthValue R S.X₂ → 1 ≤ depthValue R S.X₁ ∧ depthValue R S.X₃ = depthValue R S.X₁ - 1

end AdvCommAlg.Depth.Specs
