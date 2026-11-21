import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Depth.Basic

/-! Independent specifications for DP-04, paper.tex:2721–2766.
Ext is taken in the category of all R-modules. Subsingleton means vanishing,
and the infimum in ℕ∞ of the empty family is infinity. Maximality means that
no further element of I can be appended to the ordered regular list.
All module types may be placed in one common universe, with no nonzero
hypotheses on either module. -/

universe u
open scoped Pointwise
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Depth

/-- A proper regular list in I which cannot be extended by one element of I. -/
def MaximalRegular {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type u) [AddCommGroup M] [Module R M] (xs : List R) : Prop :=
  RingTheory.Sequence.IsRegular M xs ∧ (∀ a ∈ xs, a ∈ I) ∧
    ∀ a ∈ I, ¬ RingTheory.Sequence.IsRegular M (xs ++ [a])

namespace Specs

def grade_eq_extDepthType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (N M : ModuleCat.{u} R) [Module.Finite R N] [Module.Finite R M],
    gradeValue (Module.annihilator R N) M = N.depth M

def grade_eq_iInf_extType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (N M : ModuleCat.{u} R) [Module.Finite R N] [Module.Finite R M],
    gradeValue (Module.annihilator R N) M =
      ⨅ (i : ℕ) (_ : Nontrivial (Ext N M i)), (i : ℕ∞)

def grade_eq_idealDepthType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M],
    gradeValue I M = I.depth M

def grade_eq_quotient_extType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M],
    gradeValue I M =
      ⨅ (i : ℕ) (_ : Nontrivial (Ext (ModuleCat.of R (R ⧸ I)) M i)), (i : ℕ∞)

def depth_eq_libraryDepthType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M],
    depthValue R M = IsLocalRing.depth M

def depth_eq_residue_extType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M],
    depthValue R M =
      ⨅ (i : ℕ) (_ : Nontrivial (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) M i)),
        (i : ℕ∞)

def grade_eq_nat_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (N M : ModuleCat.{u} R) [Module.Finite R N] [Module.Finite R M] (n : ℕ),
    gradeValue (Module.annihilator R N) M = n ↔
      Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i)

def grade_eq_top_iff_ext_zeroType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (N M : ModuleCat.{u} R) [Module.Finite R N] [Module.Finite R M],
    gradeValue (Module.annihilator R N) M = ⊤ ↔
      ∀ i : ℕ, Subsingleton (Ext N M i)

def maximalRegular_length_eq_gradeType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    I • (⊤ : Submodule R M) ≠ ⊤ → ∀ xs : List R,
      MaximalRegular I M xs → (xs.length : ℕ∞) = gradeValue I M

def exists_maximalRegular_extensionType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    I • (⊤ : Submodule R M) ≠ ⊤ → ∀ xs : List R,
      RingTheory.Sequence.IsRegular M xs → (∀ a ∈ xs, a ∈ I) →
      ∃ ys : List R, MaximalRegular I M (xs ++ ys)

end Specs
end AdvCommAlg.Depth
