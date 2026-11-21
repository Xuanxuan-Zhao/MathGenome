import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Concatenation

/-! Concatenation of weak and proper regular sequences (RK-02).
The proper case uses the canonical linear equivalence between successive
quotients, so all module actions agree with those in the definitions. -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.RegularSequence

variable {R : Type u} [CommRing R]

theorem weaklyRegular_append_iff (M : Type v) [AddCommGroup M] [Module R M]
    (x y : List R) :
    WeaklyRegular M (x ++ y) ↔
      WeaklyRegular M x ∧
      WeaklyRegular (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M)) y :=
  RingTheory.Sequence.isWeaklyRegular_append_iff M x y

theorem regular_append_iff (M : Type v) [AddCommGroup M] [Module R M]
    (x y : List R) :
    Regular M (x ++ y) ↔
      Regular M x ∧
      Regular (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M)) y := by
  change RingTheory.Sequence.IsRegular M (x ++ y) ↔
    RingTheory.Sequence.IsRegular M x ∧
    RingTheory.Sequence.IsRegular (M ⧸ (Ideal.ofList x • ⊤ : Submodule R M)) y
  induction x generalizing M with
  | nil =>
    let e := Submodule.quotEquivOfEqBot
      (Ideal.ofList ([] : List R) • ⊤ : Submodule R M) (by simp)
    rw [List.nil_append, e.isRegular_congr y]
    constructor
    · intro h
      exact ⟨(regular_nil_iff M).mpr h.nontrivial, h⟩
    · exact fun h => h.2
  | cons a x ih =>
    let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a x
    rw [List.cons_append, RingTheory.Sequence.isRegular_cons_iff,
      RingTheory.Sequence.isRegular_cons_iff, ih, ← and_assoc,
      ← e.isRegular_congr y]

end AdvCommAlg.RegularSequence
