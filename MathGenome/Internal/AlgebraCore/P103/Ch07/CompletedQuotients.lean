import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletedQuotients
import MathGenome.Internal.AlgebraCore.P103.Ch07.ReesGradedConstruction
import Mathlib.RingTheory.AdicCompletion.Completeness

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u
/-! Quotient comparison, its grading, and completeness in Theorem 7.5
(paper.tex:1229–1238). The finite-generation completion lemmas in Mathlib
implement Stacks 05GG; Noetherianness supplies their finite-generation
hypothesis. The graded map below uses the actual shared Rees quotients. -/

namespace P103.Ch07.CompletedQuotients
noncomputable section
open P103.Adic P103.Rees P103.Specs.Ch07.CompletedQuotients

variable {R : Type u} [CommRing R] (I : Ideal R)

lemma eval_compatible {m n : ℕ} (h : m ≤ n) (x : Completion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  simp only [AdicCompletion.evalₐ, AlgHom.comp_apply]
  change Ideal.Quotient.factorPow I h
    (Ideal.quotientEquivAlgOfEq R _ (x.val n)) =
      Ideal.quotientEquivAlgOfEq R _ (x.val m)
  rw [← x.property h]
  induction x.val n using Quotient.inductionOn with
  | h r => rfl

theorem projection_kernel : projection_kernelType.{u} := by
  intro R _ _ I n
  ext x
  have hi : (I ^ n • ⊤ : Ideal R) = I ^ n := by simp
  have hk := AdicCompletion.pow_smul_top_eq_ker_eval (M := R) (n := n)
    I.fg_of_isNoetherianRing
  have hx : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I R n x = 0 := by
    exact (map_eq_zero_iff (Ideal.quotientEquivAlgOfEq R hi)
      (Ideal.quotientEquivAlgOfEq R hi).injective)
  change AdicCompletion.evalₐ I n x = 0 ↔ _
  rw [hx, ← LinearMap.mem_ker, ← hk]
  simp [extendedIdeal, ← Ideal.map_pow]

theorem quotient_comparison : quotient_comparisonType.{u} := by
  intro R _ _ I
  let e (n : ℕ) : (Completion I R ⧸ extendedIdeal I ^ n) ≃+* (R ⧸ I ^ n) :=
    (Ideal.quotEquivOfEq (projection_kernel R I n).symm).trans
      (RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ I n))
  refine ⟨e, ?_, ?_⟩
  · intro n x
    rfl
  · intro m n h x
    induction x using Quotient.inductionOn with
    | h x => exact eval_compatible I h x

theorem complete_separated : complete_separatedType.{u} := by
  intro R _ _ I
  have hI : IsAdicComplete I (Completion I R) :=
    AdicCompletion.isAdicComplete (M := R) I.fg_of_isNoetherianRing
  have hJ : IsAdicComplete (extendedIdeal I) (Completion I R) :=
    (IsAdicComplete.map_algebraMap_iff I (Completion I R)
      (S := Completion I R)).mpr hI
  let := hJ
  refine ⟨?_, ⟨(AdicCompletion.ofAlgEquiv (extendedIdeal I)).toRingEquiv, fun _ => rfl⟩⟩
  apply le_antisymm _ bot_le
  intro x hx
  have hx' : ∀ n, x ∈ extendedIdeal I ^ n := by simpa using hx
  have hz : x = 0 := IsHausdorff.haus (inferInstance : IsHausdorff (extendedIdeal I)
    (Completion I R)) x (fun n => by simpa [SModEq.sub_mem] using hx' n)
  simpa using hz


section GradedMap
variable {S : Type u} [CommRing S] (J : Ideal S) (f : R →+* S)
  (hf : I.map f ≤ J)

include hf in
lemma map_power_mem (n : ℕ) {r : R} (hr : r ∈ I ^ n) : f r ∈ J ^ n :=
  (Ideal.pow_right_mono hf n) (by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hr)

/-- Apply a filtered ring map coefficientwise to a Rees polynomial. -/
def reesMap : ReesAlgebra I →+* ReesAlgebra J where
  toFun p := ⟨Polynomial.map f p.val, fun n => by
    rw [Polynomial.coeff_map]
    exact map_power_mem I J f hf n (p.property n)⟩
  map_zero' := Subtype.ext (Polynomial.map_zero f)
  map_one' := Subtype.ext (Polynomial.map_one f)
  map_add' p q := Subtype.ext (Polynomial.map_add f)
  map_mul' p q := Subtype.ext (Polynomial.map_mul f)

/-- The induced map on the canonical associated graded quotient rings. -/
def associatedMap : AssociatedRing I →+* AssociatedRing J :=
  Ideal.Quotient.lift (quotientIdeal I)
    ((Ideal.Quotient.mk (quotientIdeal J)).comp (reesMap I J f hf)) (by
      intro p hp
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply (quotient_ideal_membership J _).mpr
      intro n
      change (Polynomial.map f p.val).coeff n ∈ J ^ (n + 1)
      rw [Polynomial.coeff_map]
      exact map_power_mem I J f hf (n + 1)
        ((quotient_ideal_membership I p).mp hp n))

lemma associatedMap_class (n : ℕ) (a : (I ^ n : Ideal R)) :
    associatedMap I J f hf (ringClass I n a) =
      ringClass J n ⟨f a.val, map_power_mem I J f hf n a.property⟩ := by
  change Ideal.Quotient.mk _ (reesMap I J f hf (ringTerm I n a)) =
    Ideal.Quotient.mk _ (ringTerm J n ⟨f a.val, map_power_mem I J f hf n a.property⟩)
  congr 1
  apply Subtype.ext
  exact Polynomial.map_monomial f

lemma associatedMap_injective
    (hreflect : ∀ n r, f r ∈ J ^ n → r ∈ I ^ n) :
    Function.Injective (associatedMap I J f hf) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  induction x using Quotient.inductionOn with
  | h p =>
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (quotient_ideal_membership I p).mpr
    have hp : reesMap I J f hf p ∈ quotientIdeal J :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    intro n
    apply hreflect (n + 1)
    simpa [reesMap, Polynomial.coeff_map] using
      (quotient_ideal_membership J _).mp hp n

lemma class_lift
    (hlift : ∀ n (b : (J ^ n : Ideal S)),
      ∃ a : (I ^ n : Ideal R), b.val - f a.val ∈ J ^ (n + 1))
    (n : ℕ) (b : (J ^ n : Ideal S)) :
    ∃ a : (I ^ n : Ideal R),
      associatedMap I J f hf (ringClass I n a) = ringClass J n b := by
  obtain ⟨a, ha⟩ := hlift n b
  refine ⟨a, ?_⟩
  rw [associatedMap_class]
  apply sub_eq_zero.mp
  rw [← map_sub, ringClass_eq_zero_iff]
  change f a.val - b.val ∈ J ^ (n + 1)
  simpa only [neg_sub] using (J ^ (n + 1)).neg_mem ha

lemma associatedMap_surjective
    (hlift : ∀ n (b : (J ^ n : Ideal S)),
      ∃ a : (I ^ n : Ideal R), b.val - f a.val ∈ J ^ (n + 1)) :
    Function.Surjective (associatedMap I J f hf) := by
  intro x
  induction x using Quotient.inductionOn with
  | h p =>
    classical
    have he (n : ℕ) := class_lift I J f hf hlift n (ringCoefficient J n p)
    choose a ha using he
    refine ⟨∑ n ∈ p.val.support, ringClass I n (a n), ?_⟩
    rw [map_sum]
    simp_rw [ha]
    change ∑ n ∈ p.val.support, ringClass J n (ringCoefficient J n p) =
      Ideal.Quotient.mk (quotientIdeal J) p
    conv_rhs => rw [reesAlgebra.as_sum_support p, map_sum]
    rfl

end GradedMap


section CompletedGrading
variable [IsNoetherianRing R]

lemma of_mem_power_iff (n : ℕ) (r : R) :
    algebraMap R (Completion I R) r ∈ extendedIdeal I ^ n ↔ r ∈ I ^ n := by
  rw [← projection_kernel R I n, RingHom.mem_ker]
  change AdicCompletion.evalₐ I n (AdicCompletion.of I R r) = 0 ↔ _
  rw [AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]

/-- A coefficient in J^n lifts to I^n modulo J^(n+1). -/
lemma lift_power (n : ℕ) (b : (extendedIdeal I ^ n : Ideal (Completion I R))) :
    ∃ a : (I ^ n : Ideal R),
      b.val - algebraMap R (Completion I R) a.val ∈ extendedIdeal I ^ (n + 1) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) b.val)
  have hb : AdicCompletion.evalₐ I n b.val = 0 := by
    have hb := b.property
    exact (show b.val ∈ RingHom.ker (AdicCompletion.evalₐ I n).toRingHom from
      (projection_kernel R I n).symm ▸ hb)
  have hrn : Ideal.Quotient.mk (I ^ n) r = 0 := by
    calc
      Ideal.Quotient.mk (I ^ n) r =
          Ideal.Quotient.factorPow I (Nat.le_succ n)
            (Ideal.Quotient.mk (I ^ (n + 1)) r) := rfl
      _ = Ideal.Quotient.factorPow I (Nat.le_succ n)
            (AdicCompletion.evalₐ I (n + 1) b.val) := congrArg _ hr
      _ = AdicCompletion.evalₐ I n b.val := eval_compatible I _ _
      _ = 0 := hb
  refine ⟨⟨r, Ideal.Quotient.eq_zero_iff_mem.mp hrn⟩, ?_⟩
  rw [← projection_kernel R I (n + 1), RingHom.mem_ker, map_sub]
  change AdicCompletion.evalₐ I (n + 1) b.val -
    AdicCompletion.evalₐ I (n + 1) (AdicCompletion.of I R r) = 0
  rw [AdicCompletion.evalₐ_of, hr, sub_self]

theorem graded_comparison : graded_comparisonType.{u} := by
  intro R _ _ I
  let f := algebraMap R (Completion I R)
  have hf : I.map f ≤ extendedIdeal I := le_rfl
  let g := associatedMap I (extendedIdeal I) f hf
  have hg : Function.Bijective g := ⟨
    associatedMap_injective I (extendedIdeal I) f hf
      (fun n r h => (of_mem_power_iff I n r).mp h),
    associatedMap_surjective I (extendedIdeal I) f hf (lift_power I)⟩
  let e := RingEquiv.ofBijective g hg
  refine ⟨e.symm, ?_, ?_⟩
  · intro n
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨b, rfl⟩ := hy
      obtain ⟨a, ha⟩ := class_lift I (extendedIdeal I) f hf (lift_power I) n b
      refine ⟨a, ?_⟩
      apply e.injective
      change g (ringClass I n a) = e (e.symm (ringClass (extendedIdeal I) n b))
      rw [e.apply_symm_apply]
      exact ha
    · rintro ⟨a, rfl⟩
      refine ⟨g (ringClass I n a), ?_, ?_⟩
      · rw [show g (ringClass I n a) = _ from associatedMap_class I (extendedIdeal I) f hf n a]
        exact ⟨_, rfl⟩
      · change e.symm (e (ringClass I n a)) = _
        exact e.symm_apply_apply _
  · intro n a b hb
    apply e.injective
    rw [e.apply_symm_apply]
    change ringClass (extendedIdeal I) n b = g (ringClass I n a)
    rw [associatedMap_class]
    congr 1
    exact Subtype.ext hb

end CompletedGrading

end
end P103.Ch07.CompletedQuotients
