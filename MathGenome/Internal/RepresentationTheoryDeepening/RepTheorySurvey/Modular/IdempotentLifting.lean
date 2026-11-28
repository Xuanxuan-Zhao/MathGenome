import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.IdempotentLifting
import Mathlib.RingTheory.Idempotents

namespace RepTheorySurvey.Modular

open Ideal.Quotient

section Ring

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

private theorem nilpotent_quotient_kernel (h : ∃ n : ℕ, I ^ n = ⊥)
    (x : R) (hx : x ∈ RingHom.ker (mk I)) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, Ideal.pow_eq_zero_of_mem hn le_rfl (eq_zero_iff_mem.mp (RingHom.mem_ker.mp hx))⟩

private theorem nilpotent_transition_kernel (n : ℕ) (x : R ⧸ (I ^ (n + 2)))
    (hx : x ∈ RingHom.ker (factorPowSucc I (n + 1))) : IsNilpotent x := by
  obtain ⟨r, rfl⟩ := mk_surjective x
  have hr : r ∈ I ^ (n + 1) :=
    eq_zero_iff_mem.mp (RingHom.mem_ker.mp hx)
  refine ⟨2, ?_⟩
  rw [← map_pow, eq_zero_iff_mem, pow_two]
  apply Ideal.pow_le_pow_right (show n + 2 ≤ (n + 1) + (n + 1) by omega)
  rw [Ideal.IsTwoSided.pow_add]
  exact Ideal.mul_mem_mul hr hr

private theorem compatible_of_successor
    (a : (n : ℕ) → R ⧸ (I ^ (n + 1)))
    (ha : ∀ n : ℕ, factorPowSucc I (n + 1) (a (n + 1)) = a n) :
    ∀ ⦃n m : ℕ⦄ (h : n ≤ m), factorPow I (Nat.succ_le_succ h) (a m) = a n := by
  intro n m h
  induction h with
  | refl => simp [factorPow]
  | @step m h ih =>
    calc
      _ = factorPow I (Nat.succ_le_succ h) (factorPowSucc I (m + 1) (a (m + 1))) := by
        simp only [factorPow, factorPowSucc, factor_comp_apply]
      _ = _ := by rw [ha m, ih]

private theorem idempotent_lift_of_adic (h : IsAdicCompleteSeparated I)
    (e : R ⧸ I) (he : IsIdempotentElem e) :
    ∃ a : R, IsIdempotentElem a ∧ mk I a = e := by
  classical
  let toBase : R ⧸ (I ^ (0 + 1)) ≃+* R ⧸ I := Ideal.quotEquivOfEq (Submodule.pow_one I)
  let initial : R ⧸ (I ^ (0 + 1)) := toBase.symm e
  have hInitial : IsIdempotentElem initial := he.map toBase.symm
  have step (n : ℕ) (x : {a : R ⧸ (I ^ (n + 1)) // IsIdempotentElem a}) :
      ∃ y : {a : R ⧸ (I ^ (n + 2)) // IsIdempotentElem a},
        factorPowSucc I (n + 1) y.1 = x.1 := by
    obtain ⟨y, hy, hyx⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
      (factorPowSucc I (n + 1)) (nilpotent_transition_kernel I n) x.1
      (factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) x.1) x.2
    exact ⟨⟨y, hy⟩, hyx⟩
  let lifts : (n : ℕ) → {a : R ⧸ (I ^ (n + 1)) // IsIdempotentElem a} :=
    Nat.rec ⟨initial, hInitial⟩ (fun n x => Classical.choose (step n x))
  let residues : AdicLimit I :=
    ⟨fun n => (lifts n).1, compatible_of_successor I _ fun n =>
      Classical.choose_spec (step n (lifts n))⟩
  obtain ⟨a, ha⟩ := h.2 residues
  have hResidue (n : ℕ) : mk (I ^ (n + 1)) a = (lifts n).1 :=
    congrArg (fun r : AdicLimit I => r.1 n) ha
  refine ⟨a, ?_, ?_⟩
  · apply h.1
    apply Subtype.ext
    funext n
    change mk (I ^ (n + 1)) (a * a) = mk (I ^ (n + 1)) a
    rw [map_mul, hResidue n]
    exact (lifts n).2.eq
  · calc
      mk I a = toBase (mk (I ^ (0 + 1)) a) :=
        (Ideal.quotEquivOfEq_mk (Submodule.pow_one I) a).symm
      _ = toBase (toBase.symm e) := congrArg toBase (hResidue 0)
      _ = e := toBase.apply_symm_apply e

/-- An idempotent lifts through a nilpotent ideal or an adically complete separated ring. -/
theorem exists_idempotent_lift
    (h : (∃ n : ℕ, I ^ n = ⊥) ∨ IsAdicCompleteSeparated I)
    (e : R ⧸ I) (he : IsIdempotentElem e) :
    ∃ a : R, IsIdempotentElem a ∧ mk I a = e := by
  rcases h with h | h
  · exact exists_isIdempotentElem_eq_of_ker_isNilpotent
      (mk I) (nilpotent_quotient_kernel I h) e (mk_surjective e) he
  · exact idempotent_lift_of_adic I h e he

end Ring

section CommRing

variable {R : Type*} [CommRing R] (I : Ideal R)

private theorem eq_zero_of_idempotent_mem (h : IsAdicCompleteSeparated I)
    {x : R} (hx : IsIdempotentElem x) (hxI : x ∈ I) : x = 0 := by
  apply h.1
  apply Subtype.ext
  funext n
  change mk (I ^ (n + 1)) x = mk (I ^ (n + 1)) 0
  rw [map_zero, eq_zero_iff_mem, ← hx.pow_succ_eq n]
  exact Ideal.pow_mem_pow hxI (n + 1)

private theorem mul_eq_left_of_same_residue (h : IsAdicCompleteSeparated I)
    {x y : R} (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
    (hxy : mk I x = mk I y) : x * y = x := by
  have hmem : x * (1 - y) ∈ I := eq_zero_iff_mem.mp (by
    rw [map_mul, map_sub, map_one, ← hxy, mul_sub, mul_one, (hx.map (mk I)).eq, sub_self])
  have hz := eq_zero_of_idempotent_mem I h (hx.mul hy.one_sub) hmem
  rw [mul_sub, mul_one, sub_eq_zero] at hz
  exact hz.symm

/-- The idempotent lift in a commutative ring is unique. -/
theorem existsUnique_idempotent_lift
    (h : (∃ n : ℕ, I ^ n = ⊥) ∨ IsAdicCompleteSeparated I)
    (e : R ⧸ I) (he : IsIdempotentElem e) :
    ∃! a : R, IsIdempotentElem a ∧ mk I a = e := by
  rcases h with h | h
  · exact existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
      (mk I) (nilpotent_quotient_kernel I h) e (mk_surjective e) he
  · obtain ⟨a, ha, hared⟩ := idempotent_lift_of_adic I h e he
    refine ⟨a, ⟨ha, hared⟩, fun b ⟨hb, hbred⟩ => ?_⟩
    have hab := hared.trans hbred.symm
    calc
      b = b * a := (mul_eq_left_of_same_residue I h hb ha hab.symm).symm
      _ = a * b := mul_comm b a
      _ = a := mul_eq_left_of_same_residue I h ha hb hab

end CommRing

end RepTheorySurvey.Modular
