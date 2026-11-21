import MathGenome.Internal.D05.M03.Image
import MathGenome.Internal.D05.M03.Kernel
import MathGenome.Internal.D05.M03.Isomorphism
import MathGenome.Internal.D05.M06.QuotientLift
import Mathlib.LinearAlgebra.Isomorphisms
import MathGenome.Internal.Specs.D05.M03.FirstIso

/-! K05.03.first_iso: the canonical isomorphism from the kernel quotient to the image. -/

namespace D05.M03.FirstIso

theorem representative_independence :
    Specs.D05.M03.FirstIso.representative_independence := by
  intro K V W _ _ _ _ _ T v w h
  exact D05.M06.QuotientLift.representative_independence T.ker T le_rfl v w h

theorem first_iso : Specs.D05.M03.FirstIso.first_iso := by
  intro K V W _ _ _ _ _ T
  -- Mathlib constructs this equivalence by lifting T through its kernel,
  -- proving the lift injective, and identifying its range with T's image.
  -- Its hypotheses require no finite-dimensional structure.
  refine ⟨T.quotKerEquivRange, ?_, ?_⟩
  · intro v
    apply Subtype.ext
    exact T.quotKerEquivRange_apply_mk v
  · intro e he
    apply LinearEquiv.ext
    intro x
    obtain ⟨v, rfl⟩ := D05.M06.Quotient.every_class_representative T.ker x
    apply Subtype.ext
    exact (congrArg Subtype.val (he v)).trans (T.quotKerEquivRange_apply_mk v).symm

end D05.M03.FirstIso
