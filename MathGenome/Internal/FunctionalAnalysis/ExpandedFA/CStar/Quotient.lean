import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Quotient
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CStar.IdealApproximateIdentities
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.UnitizationQuotient
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

noncomputable section
namespace ExpandedFA.CStar.Quotient
universe u
open private quotientNormedRing from MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.UnitizationQuotient

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- Removing a positive contraction contracts on both sides, in the C*-unitization. -/
lemma cut_contractive (e : A) (he : Conventions.Spec.PositiveValue A e) (he1 : ‖e‖ ≤ 1) :
    ‖(1 : Unitization ℂ A) - (e : Unitization ℂ A)‖ ≤ 1 := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  have he0 : 0 ≤ (e : Unitization ℂ A) :=
    Unitization.inr_nonneg_iff.mpr ((PositiveConeSquareRoots.positive_iff_nonneg e).mp he)
  have he1' : ‖(e : Unitization ℂ A)‖ ≤ 1 := by simpa only [Unitization.norm_inr] using he1
  have hle : (e : Unitization ℂ A) ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ he0).mp he1'
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (sub_nonneg.mpr hle)).mpr
    (sub_le_self _ he0)

/-- The compression estimate uses the original C*-norm on the unitization. -/
lemma compression_bound (b j e : A)
    (hc : ‖(1 : Unitization ℂ A) - (e : Unitization ℂ A)‖ ≤ 1) :
    ‖((1 : Unitization ℂ A) - (e : Unitization ℂ A)) * (b : Unitization ℂ A) *
      (1 - (e : Unitization ℂ A))‖ ≤ ‖b - j‖ + ‖j - j * e‖ := by
  let c : Unitization ℂ A := 1 - (e : Unitization ℂ A)
  have hdecomp : c * (b : Unitization ℂ A) * c =
      c * ((b - j : A) : Unitization ℂ A) * c +
        c * ((j - j * e : A) : Unitization ℂ A) := by
    simp only [Unitization.inr_sub, Unitization.inr_mul]
    dsimp [c]
    noncomm_ring
  change ‖c * (b : Unitization ℂ A) * c‖ ≤ _
  rw [hdecomp]
  calc
    _ ≤ ‖c * ((b - j : A) : Unitization ℂ A) * c‖ +
        ‖c * ((j - j * e : A) : Unitization ℂ A)‖ := norm_add_le _ _
    _ ≤ ‖b - j‖ + ‖j - j * e‖ := by
      apply add_le_add
      · calc
          _ ≤ ‖c‖ * ‖((b - j : A) : Unitization ℂ A)‖ * ‖c‖ :=
            (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ 1 * ‖((b - j : A) : Unitization ℂ A)‖ * 1 := by
            gcongr
          _ = _ := by simp only [one_mul, mul_one, Unitization.norm_inr]
      · calc
          _ ≤ ‖c‖ * ‖((j - j * e : A) : Unitization ℂ A)‖ := norm_mul_le _ _
          _ ≤ 1 * ‖((j - j * e : A) : Unitization ℂ A)‖ :=
            mul_le_mul_of_nonneg_right hc (norm_nonneg _)
          _ = _ := by simp only [one_mul, Unitization.norm_inr]

/-- The hard C*-inequality for the actual distance quotient norm. Positive
contractive ideal approximants make the error of any representative vanish. -/
lemma quotient_norm_sq_le (I : Spec.ClosedTwoSidedIdeal A) (a : A) :
    ‖I.toSubmodule.mkQ a‖ * ‖I.toSubmodule.mkQ a‖ ≤
      ‖I.toSubmodule.mkQ (star a * a)‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hb, hbε⟩ := Submodule.Quotient.norm_mk_lt
    (I.toSubmodule.mkQ (star a * a)) (half_pos hε)
  have hj : star a * a - b ∈ I := by
    exact (Submodule.Quotient.eq I.toSubmodule).mp hb.symm
  let j : I := ⟨star a * a - b, hj⟩
  obtain ⟨e, heI, he0, he1, heF⟩ :=
    IdealApproximateIdentities.finite_approximation A I {j} (ε / 2) (half_pos hε)
  have heErr : ‖(j : A) - (j : A) * e‖ < ε / 2 := by
    simpa only [norm_sub_rev] using (heF j (Finset.mem_singleton_self j)).2
  have heStar : star e = e := he0.1
  have hc := cut_contractive e he0 he1
  have hq : I.toSubmodule.mkQ (a - a * e) = I.toSubmodule.mkQ a := by
    have hz : I.toSubmodule.mkQ (a * e) = 0 :=
      (Submodule.Quotient.mk_eq_zero I.toSubmodule).mpr (I.mul_mem_left a e heI)
    rw [map_sub, hz, sub_zero]
  have hle : ‖I.toSubmodule.mkQ a‖ ≤ ‖a - a * e‖ := by
    rw [← hq]
    exact Submodule.Quotient.norm_mk_le I.toSubmodule _
  have hid : ‖a - a * e‖ * ‖a - a * e‖ =
      ‖((1 : Unitization ℂ A) - (e : Unitization ℂ A)) *
        ((star a * a : A) : Unitization ℂ A) * (1 - (e : Unitization ℂ A))‖ := by
    rw [← CStarRing.norm_star_mul_self]
    rw [← Unitization.norm_inr (𝕜 := ℂ)]
    congr 1
    simp only [star_sub, star_mul, heStar, Unitization.inr_mul, Unitization.inr_sub,
      Unitization.inr_star]
    noncomm_ring
  calc
    _ ≤ ‖a - a * e‖ * ‖a - a * e‖ := mul_self_le_mul_self (norm_nonneg _) hle
    _ = _ := hid
    _ ≤ ‖star a * a - (j : A)‖ + ‖(j : A) - (j : A) * e‖ :=
      compression_bound _ _ _ hc
    _ ≤ ‖I.toSubmodule.mkQ (star a * a)‖ + ε := by
      have hbj : star a * a - (j : A) = b := sub_sub_cancel _ _
      rw [hbj]
      linarith

/-- The involution descends along the star-invariant closed ideal. -/
def quotientStar (I : Spec.ClosedTwoSidedIdeal A) (x : A ⧸ I.toSubmodule) :
    A ⧸ I.toSubmodule :=
  Quotient.liftOn x (fun a => I.toSubmodule.mkQ (star a)) (by
    intro a b hab
    apply (Submodule.Quotient.eq I.toSubmodule).mpr
    rw [← star_sub]
    exact IdealApproximateIdentities.star_invariant A I (a - b)
      (I.toSubmodule.quotientRel_def.mp hab))

@[simp] lemma quotientStar_mk (I : Spec.ClosedTwoSidedIdeal A) (a : A) :
    quotientStar I (I.toSubmodule.mkQ a) = I.toSubmodule.mkQ (star a) := rfl

section Structure
variable (I : Spec.ClosedTwoSidedIdeal A)
local instance quotientRing : NonUnitalNormedRing (A ⧸ I.toSubmodule) :=
  quotientNormedRing I.toSubmodule I.isTwoSided I.isClosed
local instance quotientInvolution : Star (A ⧸ I.toSubmodule) := ⟨quotientStar I⟩

@[simp] lemma quotient_mul_mk (a b : A) :
    I.toSubmodule.mkQ a * I.toSubmodule.mkQ b = I.toSubmodule.mkQ (a * b) := rfl

@[simp] lemma quotient_star_mk (a : A) :
    star (I.toSubmodule.mkQ a) = I.toSubmodule.mkQ (star a) := rfl

local instance quotientStarRing : StarRing (A ⧸ I.toSubmodule) where
  star_involutive := by
    intro x
    obtain ⟨a, rfl⟩ := I.toSubmodule.mkQ_surjective x
    change I.toSubmodule.mkQ (star (star a)) = I.toSubmodule.mkQ a
    rw [star_star]
  star_mul := by
    intro x y
    obtain ⟨a, rfl⟩ := I.toSubmodule.mkQ_surjective x
    obtain ⟨b, rfl⟩ := I.toSubmodule.mkQ_surjective y
    change I.toSubmodule.mkQ (star (a * b)) = I.toSubmodule.mkQ (star b * star a)
    rw [star_mul]
  star_add := by
    intro x y
    obtain ⟨a, rfl⟩ := I.toSubmodule.mkQ_surjective x
    obtain ⟨b, rfl⟩ := I.toSubmodule.mkQ_surjective y
    rw [← map_add, quotient_star_mk, star_add, map_add]
    rfl

local instance quotientStarModule : StarModule ℂ (A ⧸ I.toSubmodule) where
  star_smul := by
    intro z x
    obtain ⟨a, rfl⟩ := I.toSubmodule.mkQ_surjective x
    rw [← map_smul, quotient_star_mk, star_smul, map_smul]
    rfl

local instance quotientScalarTower : IsScalarTower ℂ (A ⧸ I.toSubmodule) (A ⧸ I.toSubmodule) where
  smul_assoc := by
    intro z x y
    obtain ⟨a, rfl⟩ := I.toSubmodule.mkQ_surjective x
    obtain ⟨b, rfl⟩ := I.toSubmodule.mkQ_surjective y
    change I.toSubmodule.mkQ (z • a * b) = I.toSubmodule.mkQ (z • (a * b))
    rw [smul_mul_assoc]

local instance quotientSMulComm : SMulCommClass ℂ (A ⧸ I.toSubmodule) (A ⧸ I.toSubmodule) where
  smul_comm := by
    intro z x y
    obtain ⟨a, rfl⟩ := I.toSubmodule.mkQ_surjective x
    obtain ⟨b, rfl⟩ := I.toSubmodule.mkQ_surjective y
    change I.toSubmodule.mkQ (z • (a * b)) = I.toSubmodule.mkQ (a * (z • b))
    rw [mul_smul_comm]

/-- All inherited operations and the metric are retained definitionally. -/
@[instance_reducible] def quotientCStarAlgebra : NonUnitalCStarAlgebra (A ⧸ I.toSubmodule) where
  toNonUnitalNormedRing := quotientRing I
  toStarRing := quotientStarRing I
  toIsScalarTower := quotientScalarTower I
  toSMulCommClass := quotientSMulComm I
  toStarModule := quotientStarModule I
  toNormedSpace := inferInstance
  toCompleteSpace := Submodule.Quotient.completeSpace I.toSubmodule
  norm_mul_self_le := by
    intro x
    obtain ⟨a, rfl⟩ := I.toSubmodule.mkQ_surjective x
    exact quotient_norm_sq_le I a

end Structure

theorem quotient_cstar : Spec.QuotientCStar.{u} := by
  intro A _ I
  refine ⟨?_, quotientCStarAlgebra I, rfl, rfl, rfl, rfl, ?_⟩
  · intro a
    exact (P1.C02QuotientNorm.distanceSeminorm_mk ℂ A I.toSubmodule a).1
  · let := quotientCStarAlgebra I
    exact ⟨fun _ _ => rfl, fun _ => rfl, fun x => by
      simpa only [pow_two] using CStarRing.norm_star_mul_self (x := x)⟩

end ExpandedFA.CStar.Quotient
