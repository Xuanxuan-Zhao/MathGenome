import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
Independent statements for K07.08.field_embedding, paper.tex:1421–1429.
The source field is commutative and nontrivial. Target rings are associative
and unital, with no commutativity assumption. Only the unital embedding
theorem requires target nontriviality. A nonunital map preserves addition
and multiplication but need not preserve one; its nonzero hypothesis is
stated for the actual bundled map. The final statement includes existence
of a unital map to every zero ring and its failure to be injective.
-/

universe u v

namespace Specs.D07.Ch08.FieldEmbedding

/-- The field kernel is two-sided, proper, and consequently zero. -/
def UnitalKernel : Prop :=
  ∀ (F : Type u) (R : Type v) [Field F] [Ring R] [Nontrivial R]
    (f : F →+* R),
    (RingHom.ker f).IsTwoSided ∧ RingHom.ker f ≠ ⊤ ∧ RingHom.ker f = ⊥

def UnitalInjective : Prop :=
  ∀ (F : Type u) (R : Type v) [Field F] [Ring R] [Nontrivial R]
    (f : F →+* R), Function.Injective f

/-- Nonzeroness replaces preservation of one and target nontriviality. -/
def NonunitalKernel : Prop :=
  ∀ (F : Type u) (R : Type v) [Field F] [Ring R]
    (f : F →ₙ+* R), f ≠ 0 →
    TwoSidedIdeal.ker f ≠ ⊤ ∧ TwoSidedIdeal.ker f = ⊥

def NonunitalInjective : Prop :=
  ∀ (F : Type u) (R : Type v) [Field F] [Ring R]
    (f : F →ₙ+* R), f ≠ 0 → Function.Injective f

/-- A zero-ring target admits a unital zero map, which is not injective. -/
def ZeroRingCounterexample : Prop :=
  ∀ (F : Type u) (R : Type v) [Field F] [Ring R] [Subsingleton R],
    ∃ f : F →+* R, (∀ a : F, f a = 0) ∧ ¬ Function.Injective f

end Specs.D07.Ch08.FieldEmbedding
