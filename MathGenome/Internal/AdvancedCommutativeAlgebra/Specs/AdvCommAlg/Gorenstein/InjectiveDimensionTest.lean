import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Noetherian.Defs

/-! Independent statements for GC-02, paper.tex:4410–4452.
The dimension is the categorical injective dimension in `WithBot ℕ∞`,
with value `⊥` on the zero module. The bound statement includes that case.
Ext is computed in the category of all modules, and `Subsingleton` means
vanishing of its additive group. All types may live in a common universe.
-/

universe u
open CategoryTheory CategoryTheory.Abelian

namespace AdvCommAlg.Gorenstein.InjectiveDimensionTest.Specs

def injectiveDimension_le_iff_residue_extType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (N : ModuleCat.{u} R) [Module.Finite R N] (n : ℕ),
    injectiveDimension N ≤ (n : WithBot ℕ∞) ↔
      ∀ i : ℕ, n < i →
        Subsingleton (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i)

def injectiveDimension_eq_iff_residue_extType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (N : ModuleCat.{u} R) [Module.Finite R N] [Nontrivial N] (n : ℕ),
    injectiveDimension N = (n : WithBot ℕ∞) ↔
      Nontrivial (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N n) ∧
      ∀ i : ℕ, n < i →
        Subsingleton (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i)

def injectiveDimension_eq_iff_isGreatest_residue_extType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (N : ModuleCat.{u} R) [Module.Finite R N] [Nontrivial N] (n : ℕ),
    injectiveDimension N = (n : WithBot ℕ∞) ↔
      IsGreatest {i : ℕ | Nontrivial
        (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i)} n

def finite_injectiveDimension_eq_greatestType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (N : ModuleCat.{u} R) [Module.Finite R N] [Nontrivial N],
    injectiveDimension N ≠ ⊤ →
      ∃ n : ℕ, injectiveDimension N = (n : WithBot ℕ∞) ∧
        IsGreatest {i : ℕ | Nontrivial
          (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) N i)} n

end AdvCommAlg.Gorenstein.InjectiveDimensionTest.Specs
