import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.SuperLie
import Mathlib.Algebra.CharP.Basic

namespace LieNotes.SuperRestricted

namespace SuperLie

abbrev paritySign := _root_.LieNotes.SuperRestricted.paritySign
abbrev Grading := @_root_.LieNotes.SuperRestricted.Grading
abbrev LieSuperalgebra := @_root_.LieNotes.SuperRestricted.LieSuperalgebra
abbrev GradedModule := @_root_.LieNotes.SuperRestricted.GradedModule
abbrev GradedModuleHom := @_root_.LieNotes.SuperRestricted.GradedModule.Hom

end SuperLie

@[simp] theorem paritySign_zero_left (k : Type*) [Field k] (j : ZMod 2) :
    paritySign k 0 j = 1 := by
  simp [paritySign, ZMod.val_zero]

@[simp] theorem paritySign_zero_right (k : Type*) [Field k] (i : ZMod 2) :
    paritySign k i 0 = 1 := by
  simp [paritySign, ZMod.val_zero]

@[simp] theorem paritySign_one_one (k : Type*) [Field k] : paritySign k 1 1 = -1 := by
  simp [paritySign, ZMod.val_one_eq_one_mod]

theorem two_ne_zero_iff_char_ne_two (k : Type*) [Field k] :
    (2 : k) ≠ 0 ↔ ringChar k ≠ 2 := by
  constructor
  · intro htwo hchar
    have hdiv : ringChar k ∣ 2 := hchar.symm ▸ dvd_rfl
    exact htwo ((ringChar.spec k 2).mpr hdiv)
  · exact Ring.two_ne_zero

section OddTriple

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Applying graded Jacobi to three copies of an odd element gives a factor of three. -/
theorem three_smul_oddTriple_eq_zero (G : Grading k V) (b : V →ₗ[k] V →ₗ[k] V)
    (hdegree : BracketGraded G b) (hskew : GradedSkew G b) (hjacobi : GradedJacobi G b)
    {x : V} (hx : x ∈ G.piece 1) : (3 : k) • b x (b x x) = 0 := by
  have hxx : b x x ∈ G.piece 0 := by
    have h := hdegree hx hx
    rwa [show (1 : ZMod 2) + 1 = 0 by decide] at h
  have hswap := hskew hxx hx
  rw [paritySign_zero_left, neg_one_smul] at hswap
  have hj := hjacobi hx hx hx
  rw [paritySign_one_one, neg_one_smul, hswap] at hj
  let t := b x (b x x)
  change t = -t + -t at hj
  change (3 : k) • t = 0
  calc
    (3 : k) • t = (t + t) + t := by
      have hthree : (3 : k) = 1 + 1 + 1 := by
        rw [one_add_one_eq_two]
        exact Nat.cast_succ (R := k) 2
      simp only [hthree, add_smul, one_smul]
    _ = t + (t + t) := add_assoc t t t
    _ = (-t + -t) + (t + t) := congrArg (fun s => s + (t + t)) hj
    _ = 0 := by rw [← neg_add, neg_add_cancel]

theorem oddTriple_of_char_ne_three (G : Grading k V) (b : V →ₗ[k] V →ₗ[k] V)
    (hdegree : BracketGraded G b) (hskew : GradedSkew G b) (hjacobi : GradedJacobi G b)
    (hchar : ringChar k ≠ 3) : OddTripleIdentity G b := by
  intro x hx
  have hthree : (3 : k) ≠ 0 :=
    fun h => hchar (CharP.ringChar_of_prime_eq_zero Nat.prime_three h)
  exact (smul_eq_zero_iff_right hthree).mp
    (three_smul_oddTriple_eq_zero G b hdegree hskew hjacobi hx)

theorem LieSuperalgebra.oddTriple [NeZero (2 : k)] (L : LieSuperalgebra k V) :
    OddTripleIdentity L.grading L.bracket := by
  by_cases hchar : ringChar k = 3
  · exact L.oddTriple_char_three hchar
  · exact oddTriple_of_char_ne_three L.grading L.bracket L.bracket_mem L.skew L.jacobi hchar

end OddTriple

end LieNotes.SuperRestricted
