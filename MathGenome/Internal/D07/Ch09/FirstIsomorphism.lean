import MathGenome.Internal.Specs.D07.Ch09.FirstIsomorphism
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
K07.09.first_isomorphism, paper.tex:1569–1583.
Mathlib's kernel-quotient equivalences are available for arbitrary rings,
despite the older commutative-ring wording in their documentation. We check
their values on representatives explicitly. No properness, commutativity,
or nontriviality assumption is needed.
-/

universe u v

namespace D07.Ch09.FirstIsomorphism

open Specs.D07.Ch09.FirstIsomorphism

theorem first_isomorphism : FirstIsomorphism.{u, v} := by
  intro R S _ _ f
  refine ⟨RingHom.quotientKerEquivRange f, ?_⟩
  intro a
  simp only [RingHom.quotientKerEquivRange, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

theorem first_isomorphism_of_surjective : FirstIsomorphismOfSurjective.{u, v} := by
  intro R S _ _ f hf
  exact ⟨RingHom.quotientKerEquivOfSurjective hf,
    RingHom.quotientKerEquivOfSurjective_apply_mk hf⟩

end D07.Ch09.FirstIsomorphism
