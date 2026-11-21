import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.Existence
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The two series in (A_4) from Example GR02-C02.05. -/

namespace Specs.ALG02GroupTheory.Chief.AlternatingFour

open Specs.ALG02GroupTheory.Chief.Series
open Specs.ALG02GroupTheory.Chief.Existence

abbrev A4 := alternatingGroup (Fin 4)

/- The letters 1, 2, 3, 4 are 0, 1, 2, 3 in Lean.
Permutation products are composed rightmost first. -/

def double12_34 : A4 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

def double13_24 : A4 :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

def double14_23 : A4 :=
  ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

def cycle123 : A4 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

abbrev VType : Type := Subgroup A4
abbrev vValue : VType := alternatingGroup.kleinFour (Fin 4)

abbrev UType : Type := Subgroup A4
abbrev uValue : UType := Subgroup.zpowers double12_34

instance vNormal : vValue.Normal :=
  alternatingGroup.normal_kleinFour (by simp : Nat.card (Fin 4) = 4)

def SubgroupCarriers : Prop :=
  (vValue : Set A4) = {1, double12_34, double13_24, double14_23} ∧
  (uValue : Set A4) = {1, double12_34}

def ElementaryAbelian : Prop :=
  IsKleinFour vValue ∧ Nonempty (vValue ≃* Multiplicative (ZMod 2 × ZMod 2))

def ConjugationCycle : Prop :=
  cycle123 * double12_34 * cycle123⁻¹ = double14_23 ∧
  cycle123 * double14_23 * cycle123⁻¹ = double13_24 ∧
  cycle123 * double13_24 * cycle123⁻¹ = double12_34

def MinimalNormal : Prop := isMinimalNormalValue vValue

abbrev chiefTerms : Fin 3 → Subgroup A4 := ![⊥, vValue, ⊤]

def ChiefChain : Prop := isChiefSeriesValue 2 chiefTerms

/-- The lower chief factor is canonically (V), with conjugation induced
by a homomorphism out of (A_4/V). -/
def FirstFactorAndAction : Prop :=
  ∃ (e : factorValue ⊥ vValue ≃* vValue) (ρ : (A4 ⧸ vValue) →* MulAut vValue),
    (∀ x : vValue, e (factorMkValue ⊥ vValue x) = x) ∧
    (∀ (g : A4) (x : vValue),
      (ρ (QuotientGroup.mk' vValue g) x : A4) = g * (x : A4) * g⁻¹) ∧
    (∀ (g : A4) (z : factorValue ⊥ vValue),
      e (g • z) = ρ (QuotientGroup.mk' vValue g) (e z)) ∧
    ∀ x : vValue,
      let y : A4 := ρ (QuotientGroup.mk' vValue cycle123) x
      ((x : A4) = double12_34 → y = double14_23) ∧
      ((x : A4) = double14_23 → y = double13_24) ∧
      ((x : A4) = double13_24 → y = double12_34)

/-- The upper chief factor is canonically (A_4/V), a cyclic group
of order three, with trivial ambient action. -/
def SecondFactorAndAction : Prop :=
  (∃ e : factorValue vValue ⊤ ≃* A4 ⧸ vValue,
    ∀ x : (⊤ : Subgroup A4),
      e (factorMkValue vValue ⊤ x) = QuotientGroup.mk' vValue (x : A4)) ∧
  Nat.card (A4 ⧸ vValue) = 3 ∧
  Nonempty ((A4 ⧸ vValue) ≃* Multiplicative (ZMod 3)) ∧
  ∀ (g : A4) (z : factorValue vValue (⊤ : Subgroup A4)), g • z = z

abbrev compositionTerms : Fin 4 → Subgroup A4 := ![⊥, uValue, vValue, ⊤]

/-- Adjacent normality supplies the group structure on each composition
factor, including the quotient (V/U). -/
def CompositionChain : Prop :=
  compositionTerms 0 = ⊥ ∧ compositionTerms (Fin.last 3) = ⊤ ∧
  StrictMono compositionTerms ∧
  ∀ i : Fin 3,
    ∃ hn : ((compositionTerms i.castSucc).subgroupOf (compositionTerms i.succ)).Normal,
      letI := hn
      IsSimpleGroup (factorValue (compositionTerms i.castSucc) (compositionTerms i.succ)) ∧
      Nat.card (factorValue (compositionTerms i.castSucc) (compositionTerms i.succ)) =
        (![2, 2, 3] : Fin 3 → ℕ) i

def MovedSubgroup : Prop :=
  uValue.map (MulAut.conj cycle123).toMonoidHom = Subgroup.zpowers double14_23 ∧
  uValue.map (MulAut.conj cycle123).toMonoidHom ≠ uValue ∧
  ¬ uValue.Normal ∧ ¬ isChiefSeriesValue 3 compositionTerms

end Specs.ALG02GroupTheory.Chief.AlternatingFour
