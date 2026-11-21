import MathGenome.Internal.Specs.D07.Ch13.Frobenius
import MathGenome.Internal.D07.Ch12.SimpleDegree
import MathGenome.Internal.D07.Ch13.PowerIdentity
import MathGenome.Internal.D07.Ch13.PrimePowerCardinality
import Mathlib.FieldTheory.Finite.Basic

/-!
Absolute and relative Frobenius, K07.13.frobenius.
Surjectivity on an arbitrary algebraic extension is proved locally in K(a):
the upstream simple-degree theorem makes this extension finite-dimensional,
and the upstream coordinate count makes its underlying set finite. An
injective endomorphism of this finite field is surjective. The resulting
preimage maps into L through the canonical intermediate-field inclusion.
-/

universe u v

namespace D07.Ch13.Frobenius

open Specs.D07.Ch13.Frobenius

theorem absolute_endomorphism : AbsoluteEndomorphism.{u} := by
  intro F _ p _ _
  exact ⟨frobenius F p, fun _ => rfl, (frobenius F p).injective⟩

theorem absolute_finite_bijective : AbsoluteFiniteBijective.{u} := by
  intro F _ _ p _ _
  obtain ⟨φ, hφ, hinj⟩ := absolute_endomorphism F p
  have hfun : (fun x : F => x ^ p) = φ := (funext hφ).symm
  rw [hfun]
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem relative_endomorphism : RelativeEndomorphism.{u, v} := by
  intro K L _ _ _ _ q hq
  let := Fintype.ofFinite K
  refine ⟨FiniteField.frobeniusAlgHom K L, ?_⟩
  intro x
  change x ^ Fintype.card K = x ^ q
  rw [← Nat.card_eq_fintype_card, hq]

theorem relative_base_fixation : RelativeBaseFixation.{u, v} := by
  intro K L _ _ _ _ q hq c
  let := Fintype.ofFinite K
  have hc := PowerIdentity.power_identity K q
    ((Nat.card_eq_fintype_card).symm.trans hq) c
  rw [← map_pow, hc]

theorem finite_simple_preimages : FiniteSimplePreimages.{u, v} := by
  intro K L _ _ _ _ q hq a ha
  let E := IntermediateField.adjoin K {a}
  have hdegree :=
    (D07.Ch12.SimpleDegree.algebraic_iff_finite_simple_extension K L a).mp ha
  have : FiniteDimensional K E :=
    (D07.Ch12.DegreeDefinition.finite_iff_finiteDimensional K E).mp hdegree
  obtain ⟨hfinite, _, _⟩ := PrimePowerCardinality.extension_cardinality K E
  let : Finite E := hfinite
  obtain ⟨Φ, hΦ⟩ := relative_endomorphism K E q hq
  have hsurj : Function.Surjective Φ := Finite.surjective_of_injective Φ.injective
  let aE : E := ⟨a, IntermediateField.mem_adjoin_simple_self K a⟩
  obtain ⟨b, hb⟩ := hsurj aE
  refine ⟨hfinite, b, ?_⟩
  have hpow : b ^ q = aE := (hΦ b).symm.trans hb
  exact congrArg (fun z : E => (z : L)) hpow

theorem relative_surjective : RelativeSurjective.{u, v} := by
  intro K L _ _ _ _ _ q hq a
  obtain ⟨_, b, hb⟩ := finite_simple_preimages K L q hq a
    (Algebra.IsAlgebraic.isAlgebraic a)
  exact ⟨(b : L), hb⟩

theorem relative_automorphism : RelativeAutomorphism.{u, v} := by
  intro K L _ _ _ _ _ q hq
  obtain ⟨Φ, hΦ⟩ := relative_endomorphism K L q hq
  have hsurj : Function.Surjective Φ := by
    intro a
    obtain ⟨b, hb⟩ := relative_surjective K L q hq a
    exact ⟨b, (hΦ b).trans hb⟩
  exact ⟨AlgEquiv.ofBijective Φ ⟨Φ.injective, hsurj⟩, hΦ⟩

end D07.Ch13.Frobenius
