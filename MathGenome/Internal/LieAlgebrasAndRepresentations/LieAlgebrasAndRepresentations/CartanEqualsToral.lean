import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.MaximalTori
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanEqualsToral
import Batteries.Tactic.OpenPrivate

/-! LA-D07: Cartan subalgebras are precisely maximal toral subalgebras.
The definition retains nilpotence and self-normalization literally.
The accepted maximal-torus argument shows its centralizer is Cartan;
the Killing-form Cartan theorem makes every Cartan toral. -/

universe u
namespace LieAlgebrasAndRepresentations

open private cartan_toral cartan_centralizer self_centralizing_maximal
  maximal_toral_centralizer_cartan from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.MaximalTori

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- A Cartan subalgebra is nilpotent and equals its normalizer. -/
def IsCartan (H : LieSubalgebra ℂ L) : Prop :=
  LieRing.IsNilpotent H ∧ H.normalizer = H

theorem isCartan_iff_isCartanSubalgebra (H : LieSubalgebra ℂ L) :
    IsCartan H ↔ H.IsCartanSubalgebra := by
  constructor
  · rintro ⟨hn, hs⟩
    exact ⟨hn, hs⟩
  · intro h
    exact ⟨h.nilpotent, h.self_normalizing⟩

/-- The characterization includes the zero algebra and imposes no splitting
condition on the nilpotent self-normalizing subalgebra. -/
theorem isCartan_iff_maximal_toral [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (H : LieSubalgebra ℂ L) :
    IsCartan H ↔ IsMaximalToral H := by
  haveI : LieAlgebra.HasTrivialRadical ℂ L := ⟨hss⟩
  constructor
  · intro hH
    haveI : H.IsCartanSubalgebra := (isCartan_iff_isCartanSubalgebra H).mp hH
    have ht : IsToral H := cartan_toral H
    exact self_centralizing_maximal H ht (cartan_centralizer H ht)
  · intro hH
    have hc := maximal_toral_centralizer_cartan hss H hH
    rw [maximal_toral_centralizer hss H hH] at hc
    exact (isCartan_iff_isCartanSubalgebra H).mpr hc

theorem zero_algebra_cartan (L : Type u) [LieRing L] [LieAlgebra ℂ L]
    [FiniteDimensional ℂ L] [Subsingleton L] :
    IsCartan (⊥ : LieSubalgebra ℂ L) :=
  (isCartan_iff_maximal_toral (semisimple_of_subsingleton ℂ L) ⊥).mpr
    (zero_algebra_toral L).1

end LieAlgebrasAndRepresentations
