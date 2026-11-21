import MathGenome.Internal.Specs.D07.Ch02.CyclicAutomorphisms
import MathGenome.Internal.D07.Ch01.ArithmeticExamples
import MathGenome.Internal.D07.Ch01.HomOnGenerators
import MathGenome.Internal.D07.Ch02.FiniteCyclicSubgroupClassification
import MathGenome.Internal.D07.Ch02.SubgroupsOfIntegerGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Ring.Int.Units

namespace D07.Ch02.CyclicAutomorphisms

universe u v

open Specs.D07.Ch02.CyclicAutomorphisms

theorem hom_determined_by_generator : HomDeterminedByGenerator.{u,v} := by
  intro G H _ _ x hx f g
  constructor
  · rintro rfl
    rfl
  · intro h
    apply MonoidHom.ext
    intro y
    have hy : y ∈ Subgroup.zpowers x := hx ▸ Subgroup.mem_top y
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    simp only [map_zpow, h]

theorem finite_automorphism_equivalence : FiniteAutomorphismEquivalence.{u} := by
  intro G _ x n hx _hn hcard
  have hgen : ∀ y : G, y ∈ Subgroup.zpowers x := fun y => hx ▸ Subgroup.mem_top y
  let e : Multiplicative (ZMod n) ≃* G := zmodMulEquivOfGenerator hgen hcard
  let E : MulAut G ≃* (ZMod n)ˣ :=
    ((MulAut.congr e).symm.trans (MulAutMultiplicative (ZMod n))).trans
      (ZMod.AddAutEquivUnits n).toMultiplicative
  refine ⟨E, ?_⟩
  intro f a
  change Multiplicative.toAdd (e.symm (f (e (Multiplicative.ofAdd 1)))) =
    (a : ZMod n) ↔ f x = x ^ a
  rw [show e (Multiplicative.ofAdd 1) = x from
    zmodMulEquivOfGenerator_apply_ofAdd_one hgen hcard]
  change e.symm (f x) = Multiplicative.ofAdd (a : ZMod n) ↔ f x = x ^ a
  rw [e.symm_apply_eq]
  rw [show e (Multiplicative.ofAdd (a : ZMod n)) = x ^ a from
    zmodMulEquivOfGenerator_apply_ofAdd_intCast hgen hcard a]

theorem finite_automorphism_form : FiniteAutomorphismForm.{u} := by
  intro G _ x n hx hn hcard f
  obtain ⟨E, hE⟩ := finite_automorphism_equivalence G x n hx hn hcard
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective (E f : ZMod n)
  have hax : f x = x ^ a := (hE f a).mp ha.symm
  have hu : IsUnit (a : ZMod n) := ha.symm ▸ (E f).isUnit
  refine ⟨a, (D07.Ch01.ArithmeticExamples.residue_unit_criterion n hn a).mp hu, ?_⟩
  intro k
  rw [map_zpow, hax, ← zpow_mul]

theorem power_automorphism_iff : PowerAutomorphismIff.{u} := by
  intro G _ x n hx hn hcard a
  obtain ⟨E, hE⟩ := finite_automorphism_equivalence G x n hx hn hcard
  constructor
  · rintro ⟨f, hf, _⟩
    have hax : f x = x ^ a := by simpa only [zpow_one, mul_one] using hf 1
    have hres := (hE f a).mpr hax
    apply (D07.Ch01.ArithmeticExamples.residue_unit_criterion n hn a).mp
    exact hres ▸ (E f).isUnit
  · intro ha
    obtain ⟨u, hu⟩ := (D07.Ch01.ArithmeticExamples.residue_unit_criterion n hn a).mpr ha
    let f : MulAut G := E.symm u
    have hax : f x = x ^ a := (hE f a).mp (by simpa only [f, E.apply_symm_apply] using hu)
    refine ⟨f, ?_, ?_⟩
    · intro k
      rw [map_zpow, hax, ← zpow_mul]
    · intro g hg
      have hga : g x = x ^ a := by simpa only [zpow_one, mul_one] using hg 1
      apply MulEquiv.toMonoidHom_injective
      exact (hom_determined_by_generator G G x hx g.toMonoidHom f.toMonoidHom).mpr
        (hga.trans hax.symm)

theorem integer_endomorphism_form : IntegerEndomorphismForm := by
  intro f k
  calc
    f k = k * f 1 := by
      simpa only [zsmul_eq_mul, mul_one, Int.cast_id] using (map_zsmul f k (1 : ℤ))
    _ = f 1 * k := mul_comm _ _

theorem integer_automorphisms : IntegerAutomorphisms := by
  refine ⟨AddEquiv.refl ℤ, AddEquiv.neg ℤ, (fun _ => rfl), (fun _ => rfl), ?_, ?_⟩
  · intro h
    have := DFunLike.congr_fun h 1
    norm_num at this
  · intro f
    obtain ⟨k, hk⟩ := f.surjective 1
    have hf : ∀ k : ℤ, f k = f 1 * k := integer_endomorphism_form f.toAddMonoidHom
    have hu : IsUnit (f 1) := IsUnit.of_mul_eq_one k ((hf k).symm.trans hk)
    rcases Int.isUnit_eq_one_or hu with h | h
    · left
      apply AddEquiv.ext
      intro k
      change f k = k
      simpa only [h, one_mul] using hf k
    · right
      apply AddEquiv.ext
      intro k
      change f k = -k
      simpa only [h, neg_one_mul] using hf k

end D07.Ch02.CyclicAutomorphisms
