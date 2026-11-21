import MathGenome.Internal.Specs.D07.Ch09.QuotientLift
import MathGenome.Internal.D07.Ch09.QuotientProjection

/-!
K07.09.quotient_lift, paper.tex:1556–1569.
Necessity follows because the projection kills the ideal. For sufficiency,
the kernel containment supplies the vanishing hypothesis of the canonical
quotient lift. Surjectivity of the projection then forces uniqueness.
No properness, commutativity, or nontriviality is assumed.
-/

universe u v

namespace D07.Ch09.QuotientLift

open Specs.D07.Ch09.QuotientLift

theorem factorization_iff : FactorizationIff.{u, v} := by
  intro R S _ _ I _ f
  constructor
  · rintro ⟨g, hg⟩ a ha
    apply RingHom.mem_ker.mpr
    have hzero :=
      (D07.Ch09.QuotientProjection.quotient_zero_iff_mem R I a).mpr ha
    calc
      f a = g (Ideal.Quotient.mk I a) := (RingHom.congr_fun hg a).symm
      _ = g 0 := congrArg g hzero
      _ = 0 := map_zero g
  · intro h
    let H : ∀ a : R, a ∈ I → f a = 0 :=
      fun _ ha => RingHom.mem_ker.mp (h ha)
    exact ⟨Ideal.Quotient.lift I f H, Ideal.Quotient.lift_comp_mk I f H⟩

theorem factorization_unique : FactorizationUnique.{u, v} := by
  intro R S _ _ I _ f g h hg hh
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := D07.Ch09.QuotientProjection.projection_surjective R I x
  exact (RingHom.congr_fun hg a).trans (RingHom.congr_fun hh a).symm

theorem factorization_on_classes : FactorizationOnClasses.{u, v} := by
  intro R S _ _ I _ f g hg a
  exact RingHom.congr_fun hg a

end D07.Ch09.QuotientLift
