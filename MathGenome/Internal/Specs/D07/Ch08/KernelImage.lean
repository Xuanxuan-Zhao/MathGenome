import MathGenome.Internal.Specs.D07.Ch08.IdealDefinition
import MathGenome.Internal.Specs.D07.Ch08.RingHomomorphism
import MathGenome.Internal.Specs.D07.Ch08.Subring
import MathGenome.Internal.Specs.D07.Ch09.QuotientProjection
import Mathlib.Algebra.Ring.Subring.Basic

/-!
Independent specification for K07.08.kernel_image, paper.tex:1311–1325.
Rings are associative and unital, with no commutativity or nontriviality
assumption. The kernel is the zero fibre and the image is the actual set
range. Mathlib's `Ideal` is a left ideal, so two-sidedness is a separate
conclusion, also expressed using the source's two absorption conditions.
The image contains the ambient identity. The ideal in the last statement
need not be proper, and its quotient target may be the zero ring.
-/

universe u v

namespace Specs.D07.Ch08.KernelImage

def KernelCarrier : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    (RingHom.ker f : Set R) = {a : R | f a = 0}

def ImageCarrier : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    (f.range : Set S) = Set.range f

def KernelTwoSided : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    (RingHom.ker f).IsTwoSided

def KernelAbsorption : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    Specs.D07.Ch08.IdealDefinition.IsTwoSidedIdeal (RingHom.ker f).toAddSubgroup

def ImageIsUnitalSubring : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    ∃ U : Subring S, (U : Set S) = Set.range f

def ImageClosure : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    Specs.D07.Ch08.Subring.UnitalConditions (Set.range f)

/-- The canonical quotient projection realizes every two-sided ideal
as a kernel, even for a noncommutative ring or the whole ideal. -/
def EveryTwoSidedIdealIsKernel : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R) [I.IsTwoSided],
    ∃ (S : Type u) (_ : Ring S) (f : R →+* S),
      Function.Surjective f ∧ RingHom.ker f = I

end Specs.D07.Ch08.KernelImage
