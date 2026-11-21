import MathGenome.Internal.Specs.D07.Ch09.QuotientProjection
import MathGenome.Internal.D07.Ch09.QuotientConstruction

/-!
K07.09.quotient_projection (paper.tex:1534–1545).
The canonical quotient map sends a ring element to its additive coset.
The accepted construction identifies these classes with the source's
set-valued cosets, so their equality is precisely difference membership.
No properness, nontriviality, or commutativity is required.
-/

universe u

namespace D07.Ch09.QuotientProjection

open Specs.D07.Ch09.QuotientProjection

theorem projection_homomorphism : ProjectionHomomorphism.{u} := by
  intro R _ I _
  exact ⟨map_add (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I),
    map_one (Ideal.Quotient.mk I), map_zero (Ideal.Quotient.mk I),
    map_neg (Ideal.Quotient.mk I)⟩

theorem projection_surjective : ProjectionSurjective.{u} := by
  intro R _ I _
  exact Ideal.Quotient.mk_surjective

theorem quotient_eq_iff_sub_mem : QuotientEqIffSubMem.{u} := by
  intro R _ I _ a b
  exact (D07.Ch09.QuotientConstruction.quotient_eq_iff_coset_eq R I a b).trans
    (D07.Ch09.QuotientConstruction.additive_coset_eq_iff_sub_mem
      R I.toAddSubgroup a b)

theorem quotient_zero_iff_mem : QuotientZeroIffMem.{u} := by
  intro R _ I _ a
  simpa only [map_zero, sub_zero] using quotient_eq_iff_sub_mem R I a 0

theorem projection_kernel : ProjectionKernel.{u} := by
  intro R _ I _
  apply Ideal.ext
  intro a
  exact RingHom.mem_ker.trans (quotient_zero_iff_mem R I a)

theorem every_two_sided_ideal_is_kernel : EveryTwoSidedIdealIsKernel.{u} := by
  intro R _ I _
  exact ⟨R ⧸ I, inferInstance, Ideal.Quotient.mk I,
    projection_surjective R I, projection_kernel R I⟩

end D07.Ch09.QuotientProjection
