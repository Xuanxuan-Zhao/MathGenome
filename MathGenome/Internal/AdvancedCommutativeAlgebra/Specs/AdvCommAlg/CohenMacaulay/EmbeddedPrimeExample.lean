import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SerreDepthConditions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.ZeroTest
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

/-! The second example in CM-14, paper.tex:3744–3751.
We write k[x,y] as k[y][x]. All objects below are shared canonical
objects; the expected results are Prop definitions, with no assumed proofs. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace AdvCommAlg.CohenMacaulay.EmbeddedPrimeExample
open Polynomial

section Ring
variable (k : Type u) [CommRing k]
abbrev Ambient := Polynomial (Polynomial k)
noncomputable instance ambient_commRing : CommRing (Ambient k) := inferInstance
noncomputable def relations : Ideal (Ambient k) :=
  Ideal.span {X ^ 2, X * C (X : Polynomial k)}
abbrev CoordinateRing := Ambient k ⧸ relations k
noncomputable instance coordinateRing_commRing : CommRing (CoordinateRing k) := inferInstance

noncomputable def ambientOrigin : Ideal (Ambient k) :=
  RingHom.ker ((evalRingHom (0 : k)).comp (evalRingHom (0 : Polynomial k)))

lemma relations_le_ambientOrigin : relations k ≤ ambientOrigin k := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with rfl | ⟨rfl⟩ <;> simp [ambientOrigin, RingHom.mem_ker]

noncomputable def origin : Ideal (CoordinateRing k) :=
  (ambientOrigin k).map (Ideal.Quotient.mk (relations k))

noncomputable def xBar : CoordinateRing k := Ideal.Quotient.mk (relations k) X
noncomputable def yBar : CoordinateRing k := Ideal.Quotient.mk (relations k) (C X)
end Ring
variable (k : Type u) [Field k]

instance ambientOrigin_isMaximal : (ambientOrigin k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C (C a), by simp⟩)

instance origin_isMaximal : (origin k).IsMaximal :=
  Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using relations_le_ambientOrigin k)

instance origin_isPrime : (origin k).IsPrime :=
  @Ideal.IsMaximal.isPrime (CoordinateRing k) inferInstance (origin k) (origin_isMaximal k)

abbrev LocalRing : Type u := Localization.AtPrime (R := CoordinateRing k) (origin k)
noncomputable def x : LocalRing k := algebraMap (CoordinateRing k) (LocalRing k) (xBar k)
noncomputable def y : LocalRing k := algebraMap (CoordinateRing k) (LocalRing k) (yBar k)

end AdvCommAlg.CohenMacaulay.EmbeddedPrimeExample

namespace AdvCommAlg.CohenMacaulay.Specs
open EmbeddedPrimeExample

/-- The full result, including the strict containment that makes the
associated maximal ideal an embedded prime. -/
def embeddedPrimeExampleType : Prop :=
  ∀ (k : Type u) [Field k],
    IsNoetherianRing (LocalRing k) ∧ IsLocalRing (LocalRing k) ∧
    ringKrullDim (LocalRing k) = 1 ∧
    AdvCommAlg.Depth.Specs.depthValue (LocalRing k) (LocalRing k) = 0 ∧
    x k ≠ 0 ∧
    (⊥ : Submodule (LocalRing k) (LocalRing k)).colon {x k} =
      IsLocalRing.maximalIdeal (LocalRing k) ∧
    minimalPrimes (LocalRing k) = {Ideal.span {x k}} ∧
    IsLocalRing.maximalIdeal (LocalRing k) ∈ associatedPrimes (LocalRing k) (LocalRing k) ∧
    Ideal.span {x k} < IsLocalRing.maximalIdeal (LocalRing k) ∧
    ¬ RingSerreConditionValue (LocalRing k) 1

end AdvCommAlg.CohenMacaulay.Specs
