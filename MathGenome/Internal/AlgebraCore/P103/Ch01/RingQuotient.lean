import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.RingQuotient
import Mathlib.Algebra.Ring.Ext

namespace P103.Ch01.RingQuotient

universe u v

theorem classes : Specs.Classes.{u} := by
  intro R _ I
  exact ⟨I.ringCon.mk'_surjective, fun x y => I.ringCon.eq.trans (I.rel_iff x y),
    (projection I).map_add⟩

theorem ringStructure : Specs.RingStructure.{u} := by
  intro R _ I
  refine ⟨inferInstance, ⟨projection I, fun _ => rfl⟩, ?_⟩
  intro A hA
  obtain ⟨p, hp⟩ := hA
  apply Ring.ext
  · funext x y
    obtain ⟨r, rfl⟩ := I.ringCon.mk'_surjective x
    obtain ⟨s, rfl⟩ := I.ringCon.mk'_surjective y
    exact (congrArg₂ (fun a b => A.toAdd.add a b) (hp r).symm (hp s).symm).trans
      ((p.map_add r s).symm.trans ((hp (r + s)).trans ((projection I).map_add r s)))
  · funext x y
    obtain ⟨r, rfl⟩ := I.ringCon.mk'_surjective x
    obtain ⟨s, rfl⟩ := I.ringCon.mk'_surjective y
    exact (congrArg₂ (fun a b => A.toMul.mul a b) (hp r).symm (hp s).symm).trans
      ((p.map_mul r s).symm.trans ((hp (r * s)).trans ((projection I).map_mul r s)))

theorem factorization : Specs.Factorization.{u,v} := by
  intro R _ S _ I f
  constructor
  · rintro ⟨g, hg, _⟩ x hx
    apply (TwoSidedIdeal.mem_ker f).mpr
    have hx0 : projection I x = 0 := by
      exact I.ringCon.eq.mpr hx
    calc
      f x = g (projection I x) := (RingHom.congr_fun hg x).symm
      _ = 0 := by rw [hx0, map_zero]
  · intro h
    have hc : I.ringCon ≤ RingCon.ker f := by
      intro x y hxy
      apply (RingCon.ker_apply f).mpr
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact (TwoSidedIdeal.mem_ker f).mp (h ((I.rel_iff x y).mp hxy))
    exact ⟨I.ringCon.lift f hc, rfl,
      fun g hg => I.ringCon.lift_unique hc g hg⟩

theorem fullIdealQuotient : Specs.FullIdealQuotient.{u} := by
  intro R _
  constructor
  intro x y
  obtain ⟨r, rfl⟩ := (⊤ : TwoSidedIdeal R).ringCon.mk'_surjective x
  obtain ⟨s, rfl⟩ := (⊤ : TwoSidedIdeal R).ringCon.mk'_surjective y
  exact (⊤ : TwoSidedIdeal R).ringCon.eq.mpr trivial

theorem fullIdealFactorization : Specs.FullIdealFactorization.{u,v} := by
  intro R _ S _ f
  rw [factorization R S (⊤ : TwoSidedIdeal R) f]
  constructor
  · intro h
    apply subsingleton_of_zero_eq_one
    have hf : f 1 = 0 := (TwoSidedIdeal.mem_ker f).mp (h (TwoSidedIdeal.mem_top (x := (1 : R))))
    simpa only [map_one] using hf.symm
  · intro h x _
    exact (TwoSidedIdeal.mem_ker f).mpr (h.elim _ _)

end P103.Ch01.RingQuotient
