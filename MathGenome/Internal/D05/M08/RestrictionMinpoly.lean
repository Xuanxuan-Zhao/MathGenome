import MathGenome.Internal.D05.M06.Invariant
import MathGenome.Internal.D05.M08.Minpoly
import MathGenome.Internal.Specs.D05.M08.RestrictionMinpoly

/-! Powers, polynomial evaluation, annihilators and minimal polynomials under
restriction to an invariant subspace and passage to its quotient. -/

noncomputable section

namespace D05.M08.RestrictionMinpoly

open D05.M06.Invariant

theorem restriction_pow_apply : Specs.D05.M08.RestrictionMinpoly.restriction_pow_apply := by
  intro K V _ _ _ U T h j x
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply]
    exact congrArg T ih

theorem quotient_pow_apply : Specs.D05.M08.RestrictionMinpoly.quotient_pow_apply := by
  intro K V _ _ _ U T h j x
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply, ih]
    rfl

theorem restriction_eval_apply : Specs.D05.M08.RestrictionMinpoly.restriction_eval_apply := by
  intro K V _ _ _ U T h p x
  rw [Evaluation.eval_apply, Evaluation.eval_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [restriction_pow_apply U T h j x]

theorem quotient_eval_apply : Specs.D05.M08.RestrictionMinpoly.quotient_eval_apply := by
  intro K V _ _ _ U T h p x
  rw [Evaluation.eval_apply, Evaluation.eval_apply]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [quotient_pow_apply U T h j x]

theorem restriction_annihilates : Specs.D05.M08.RestrictionMinpoly.restriction_annihilates := by
  intro K V _ _ _ U T h p hp
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [restriction_eval_apply, hp]
  rfl

theorem quotient_annihilates : Specs.D05.M08.RestrictionMinpoly.quotient_annihilates := by
  intro K V _ _ _ U T h p hp
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := U.mkQ_surjective x
  rw [quotient_eval_apply, hp]
  exact map_zero U.mkQ

theorem restriction_minpoly_dvd : Specs.D05.M08.RestrictionMinpoly.restriction_minpoly_dvd := by
  intro K V _ _ _ _ U T h
  apply (Minpoly.divides_iff_annihilates (restriction K V U T h) _).mpr
  apply restriction_annihilates U T h
  exact Minpoly.annihilates T

theorem quotient_minpoly_dvd : Specs.D05.M08.RestrictionMinpoly.quotient_minpoly_dvd := by
  intro K V _ _ _ _ U T h
  apply (Minpoly.divides_iff_annihilates (inducedMap K V U T h) _).mpr
  apply quotient_annihilates U T h
  exact Minpoly.annihilates T

end D05.M08.RestrictionMinpoly
