import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation
import Mathlib.Algebra.Field.ZMod

namespace FiniteCombinatorics.Matroid.Expected
open Set
universe v w

/-- Four labelled elements, independent exactly up to cardinality two. -/
def uniformTwoFourSystem : IndependenceSystem (univ : Set (Fin 4)) where
  finite_ground := finite_univ
  Indep I := I.ncard ≤ 2
  empty_indep := by simp
  hereditary := fun {_ _} h hsub => (ncard_le_ncard hsub).trans h
  subset_ground := fun {_} _ => subset_univ _

theorem uniformTwoFourAugmentation : Augmentation uniformTwoFourSystem := by
  intro I J hI hJ hlt
  obtain ⟨e, heJ, heI⟩ := exists_mem_notMem_of_ncard_lt_ncard hlt
  refine ⟨e, ⟨heJ, heI⟩, ?_⟩
  change (insert e I).ncard ≤ 2
  have hi : I.ncard < 2 := lt_of_lt_of_le hlt hJ
  exact (ncard_insert_le e I).trans (by omega)

def uniformTwoFour : _root_.Matroid (Fin 4) :=
  ofAugmentation uniformTwoFourSystem uniformTwoFourAugmentation

instance : uniformTwoFour.Finite := ⟨finite_univ⟩

/-- The four columns in the order specified in W73. -/
def uniformTwoFourColumns (K : Type v) [Field K] (t : K) : Fin 4 → K × K :=
  ![(1,0), (0,1), (1,1), (1,t)]

def uniformTwoFourType := _root_.Matroid (Fin 4)
def uniformTwoFourColumnsType := ∀ (K : Type v) [Field K], K → Fin 4 → K × K

def uniformTwoFourGround : Prop := uniformTwoFour.E = univ

def uniformTwoFourIndep : Prop := ∀ I : Set (Fin 4),
  uniformTwoFour.Indep I ↔ I.ncard ≤ 2

def uniformTwoFourColumnsIndep : Prop := ∀ (K : Type v) [Field K] (t : K),
  t ≠ 0 → t ≠ 1 → ∀ I : Set (Fin 4),
    LinearIndepOn K (uniformTwoFourColumns K t) I ↔ I.ncard ≤ 2

def uniformTwoFourRepresents : Prop := ∀ (K : Type v) [Field K] (t : K),
  t ≠ 0 → t ≠ 1 → Represents K uniformTwoFour (uniformTwoFourColumns K t)

def uniformTwoFourNecessary : Prop := ∀ (K : Type v) [Field K],
  Representable.{0,v,w} K uniformTwoFour → ∃ t : K, t ≠ 0 ∧ t ≠ 1

def uniformTwoFourRepresentable : Prop := ∀ (K : Type v) [Field K],
  Representable.{0,v,v} K uniformTwoFour ↔ ∃ t : K, t ≠ 0 ∧ t ≠ 1

def fieldThreeElements : Prop := ∀ (K : Type v) [Field K],
  (∃ t : K, t ≠ 0 ∧ t ≠ 1) ↔ ∃ a b c : K, a ≠ b ∧ a ≠ c ∧ b ≠ c

def uniformTwoFourRepresentableIffThree : Prop := ∀ (K : Type v) [Field K],
  Representable.{0,v,v} K uniformTwoFour ↔ ∃ a b c : K, a ≠ b ∧ a ≠ c ∧ b ≠ c

def uniformTwoFourNotBinary : Prop := ∀ (K : Type v) [Field K] [Finite K],
  Nat.card K = 2 → ¬ Representable.{0,v,w} K uniformTwoFour

def uniformTwoFourNotRepresentableF2 : Prop :=
  ¬ Representable.{0,0,w} (ZMod 2) uniformTwoFour

end FiniteCombinatorics.Matroid.Expected
