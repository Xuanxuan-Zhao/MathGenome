import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.SuperLie
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.Supercommutator
import Mathlib.Tactic.NoncommRing

namespace LieNotes.SuperRestricted.Supercommutator

open scoped BigOperators

variable {k A : Type*} [Field k] [NonUnitalRing A] [Module k A]

open Specs.LieNotes.SuperRestricted.Supercommutator (projection bracketValue)

private theorem projection_same (G : Grading k A) {i : ZMod 2} {x : A}
    (hx : x ∈ G.piece i) : projection G i x = x :=
  congrArg Subtype.val (G.isInternal.ofBijective_coeLinearMap_of_mem hx)

private theorem projection_other (G : Grading k A) {i j : ZMod 2} {x : A}
    (hx : x ∈ G.piece i) (hij : i ≠ j) : projection G j x = 0 :=
  congrArg Subtype.val (G.isInternal.ofBijective_coeLinearMap_of_mem_ne hij hx)

variable [SMulCommClass k A A] [IsScalarTower k A A]

/-- The bilinear extension of the homogeneous supercommutator. -/
noncomputable abbrev bracket (G : Grading k A) : A →ₗ[k] A →ₗ[k] A :=
  bracketValue G

theorem bracket_of_mem (G : Grading k A) {i j : ZMod 2} {x y : A}
    (hx : x ∈ G.piece i) (hy : y ∈ G.piece j) :
    bracket G x y = x * y - paritySign k i j • (y * x) := by
  simp only [bracket, bracketValue, LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.mul_apply']
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [projection_same G hx, projection_same G hy]
    · intro j' _ hj'
      simp [projection_other G hy hj'.symm]
  · intro i' _ hi'
    simp [projection_other G hx hi'.symm]

theorem bracket_graded (G : Grading k A) (hmul : MulGraded G) : BracketGraded G (bracket G) := by
  intro i j x y hx hy
  have hyx : y * x ∈ G.piece (i + j) := add_comm j i ▸ hmul hy hx
  rw [bracket_of_mem G hx hy]
  exact (G.piece (i + j)).sub_mem (hmul hx hy) ((G.piece (i + j)).smul_mem _ hyx)

private theorem parity_cases (i : ZMod 2) : i = 0 ∨ i = 1 := by
  have hi : i.val < 2 := i.val_lt
  have h : i.val = 0 ∨ i.val = 1 := by omega
  obtain h | h := h
  · exact Or.inl (ZMod.val_injective 2 (by simpa [ZMod.val_zero] using h))
  · exact Or.inr (ZMod.val_injective 2 (by simpa [ZMod.val_one_eq_one_mod] using h))

private theorem odd_add_odd : (1 : ZMod 2) + 1 = 0 := by decide

theorem bracket_skew (G : Grading k A) : GradedSkew G (bracket G) := by
  intro i j x y hx hy
  rw [bracket_of_mem G hx hy, bracket_of_mem G hy hx]
  obtain rfl | rfl := parity_cases i <;> obtain rfl | rfl := parity_cases j <;>
    simp only [paritySign_zero_left, paritySign_zero_right, paritySign_one_one, one_smul,
      neg_one_smul, neg_neg] <;> abel

theorem bracket_jacobi (G : Grading k A) (hmul : MulGraded G) : GradedJacobi G (bracket G) := by
  intro i j l x y z hx hy hz
  have hgraded := bracket_graded G hmul
  rw [bracket_of_mem G hx (hgraded hy hz), bracket_of_mem G (hgraded hx hy) hz,
    bracket_of_mem G hy (hgraded hx hz), bracket_of_mem G hx hy,
    bracket_of_mem G hx hz, bracket_of_mem G hy hz]
  obtain rfl | rfl := parity_cases i <;> obtain rfl | rfl := parity_cases j <;>
    obtain rfl | rfl := parity_cases l <;>
    simp only [zero_add, add_zero, odd_add_odd, paritySign_zero_left, paritySign_zero_right,
      paritySign_one_one, one_smul, neg_one_smul] <;> noncomm_ring

theorem bracket_odd_self (G : Grading k A) {x : A} (hx : x ∈ G.piece 1) :
    bracket G x x = (2 : k) • (x * x) := by
  rw [bracket_of_mem G hx hx, paritySign_one_one, neg_one_smul, sub_neg_eq_add, ← one_add_one_eq_two,
    add_smul, one_smul]

theorem oddTriple (G : Grading k A) (hmul : MulGraded G) : OddTripleIdentity G (bracket G) := by
  intro x hx
  have hxx : bracket G x x ∈ G.piece 0 := odd_add_odd ▸ bracket_graded G hmul hx hx
  rw [bracket_of_mem G hx hxx, paritySign_zero_right, one_smul, bracket_odd_self G hx,
    mul_smul_comm, smul_mul_assoc, mul_assoc, sub_self]

/-- The supercommutator gives a Lie superalgebra on the original graded vector space. -/
noncomputable def toLieSuperalgebra [NeZero (2 : k)] (G : Grading k A) (hmul : MulGraded G) :
    LieSuperalgebra k A where
  grading := G
  bracket := bracket G
  bracket_mem := bracket_graded G hmul
  skew := bracket_skew G
  jacobi := bracket_jacobi G hmul
  oddTriple_char_three := fun _ => oddTriple G hmul

theorem exists_lieSuperalgebra [NeZero (2 : k)] (G : Grading k A) (hmul : MulGraded G) :
    ∃ L : LieSuperalgebra k A, L.grading = G ∧ L.bracket = bracket G :=
  ⟨toLieSuperalgebra G hmul, rfl, rfl⟩

end LieNotes.SuperRestricted.Supercommutator
