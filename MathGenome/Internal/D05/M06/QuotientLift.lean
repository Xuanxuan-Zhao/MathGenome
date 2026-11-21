import MathGenome.Internal.D05.M06.QuotientMap
import MathGenome.Internal.D05.M03.LinearMap
import Mathlib.LinearAlgebra.Quotient.Basic
import MathGenome.Internal.Specs.D05.M06.QuotientLift

/-! K05.06.quotient_lift: unique linear descent to an algebraic quotient. -/

namespace D05.M06.QuotientLift

theorem representative_independence :
    Specs.D05.M06.QuotientLift.representative_independence := by
  intro K V W _ _ _ _ _ U T h v w hvw
  have hz : T (v - w) = 0 := LinearMap.mem_ker.mp (h hvw)
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

theorem factorization_apply : Specs.D05.M06.QuotientLift.factorization_apply := by
  intro K V W _ _ _ _ _ U T Tbar h v
  exact (congrArg (fun f : V →ₗ[K] W => f v) h).symm

theorem quotient_lift : Specs.D05.M06.QuotientLift.quotient_lift := by
  intro K V W _ _ _ _ _ U T
  constructor
  · rintro ⟨Tbar, hfac, _⟩
    intro u hu
    change T u = 0
    have hq : D05.M06.QuotientMap.quotientMap K V U u = 0 :=
      (D05.M06.QuotientMap.eq_zero_iff U u).mpr hu
    calc
      T u = Tbar (D05.M06.QuotientMap.quotientMap K V U u) :=
        congrArg (fun f : V →ₗ[K] W => f u) hfac
      _ = Tbar 0 := congrArg Tbar hq
      _ = 0 := D05.M03.LinearMap.map_zero Tbar
  · intro h
    refine ⟨U.liftQ T h, (U.liftQ_mkQ T h).symm, ?_⟩
    intro S hS
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := D05.M06.QuotientMap.surjective U x
    calc
      S (D05.M06.QuotientMap.quotientMap K V U v) = T v :=
        factorization_apply U T S hS v
      _ = U.liftQ T h (D05.M06.QuotientMap.quotientMap K V U v) :=
        (U.liftQ_apply T v).symm

end D05.M06.QuotientLift
