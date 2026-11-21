import MathGenome.Internal.Specs.D07.Ch09.ThirdIsomorphism
import MathGenome.Internal.D07.Ch09.FirstIsomorphism
import MathGenome.Internal.D07.Ch09.QuotientProjection

/-!
K07.09.third_isomorphism, paper.tex:1598–1608.
The class map is onto, so the ideal image has exactly the displayed image
carrier and remains two-sided. For the natural map `R/I → R/J`, vanishing
of an `I`-class is equivalent to its representative lying in `J`. This
identifies its kernel with `J/I`. The accepted first isomorphism theorem
then gives the desired equivalence, with the representative formula.
-/

universe u

namespace D07.Ch09.ThirdIsomorphism

open Specs.D07.Ch09.ThirdIsomorphism

theorem quotient_ideal_carrier : QuotientIdealCarrier.{u} := by
  intro R _ I J _ _ _ x
  exact Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk I)
    (D07.Ch09.QuotientProjection.projection_surjective R I)

theorem quotient_ideal_two_sided : QuotientIdealTwoSided.{u} := by
  intro R _ I J _ _ _
  infer_instance

theorem representative_independence : RepresentativeIndependence.{u} := by
  intro R _ I J _ _ h a b hab
  apply (D07.Ch09.QuotientProjection.quotient_eq_iff_sub_mem R J a b).mpr
  exact h ((D07.Ch09.QuotientProjection.quotient_eq_iff_sub_mem R I a b).mp hab)

theorem natural_map_on_classes : NaturalMapOnClasses.{u} := by
  intro R _ I J _ _ h a
  exact Ideal.Quotient.factor_mk h a

theorem natural_map_surjective : NaturalMapSurjective.{u} := by
  intro R _ I J _ _ h y
  obtain ⟨a, rfl⟩ := D07.Ch09.QuotientProjection.projection_surjective R J y
  exact ⟨Ideal.Quotient.mk I a, natural_map_on_classes R I J h a⟩

theorem natural_map_kernel : NaturalMapKernel.{u} := by
  intro R _ I J _ _ h
  apply Ideal.ext
  intro x
  obtain ⟨a, rfl⟩ := D07.Ch09.QuotientProjection.projection_surjective R I x
  rw [RingHom.mem_ker, natural_map_on_classes R I J h a,
    D07.Ch09.QuotientProjection.quotient_zero_iff_mem R J a,
    quotient_ideal_carrier R I J h]
  constructor
  · intro ha
    exact ⟨a, ha, rfl⟩
  · rintro ⟨j, hj, hja⟩
    have hsub : j - a ∈ I :=
      (D07.Ch09.QuotientProjection.quotient_eq_iff_sub_mem R I j a).mp hja
    have ha : j - (j - a) ∈ J := J.sub_mem hj (h hsub)
    simpa only [sub_sub_cancel] using ha

theorem third_isomorphism : ThirdIsomorphismTheorem.{u} := by
  intro R _ I J _ _ h
  obtain ⟨e, he⟩ := D07.Ch09.FirstIsomorphism.first_isomorphism_of_surjective
    (R ⧸ I) (R ⧸ J) (Ideal.Quotient.factor h) (natural_map_surjective R I J h)
  refine ⟨(Ideal.quotEquivOfEq (natural_map_kernel R I J h).symm).trans e, ?_⟩
  intro a
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, he,
    natural_map_on_classes R I J h a]

end D07.Ch09.ThirdIsomorphism
