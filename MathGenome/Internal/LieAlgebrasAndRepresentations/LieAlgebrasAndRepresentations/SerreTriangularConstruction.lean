import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CartanMatrix
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWOrdered
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-!
The Serre quotient and its exact triangular decomposition (LA-F02).
The proof uses the pre-Serre word action and the symmetry exchanging the
positive and negative generators to prove injectivity of the coordinate sum.
It identifies the kernel of the final quotient with the sum of the two
one-sided Serre ideals. The argument follows notes/005, lines 2542–2646.
See also Etingof, Lie groups and Lie algebras, Theorem 24.2(i) and Lemma 24.3
(arXiv:2201.09397, pp. 121–123).
The algebraic construction works for all matrices satisfying CartanConditions,
including infinite index types. The final specification specializes it to the
original finite reduced root systems, including the empty root system.
-/
noncomputable section
namespace LieAlgebrasAndRepresentations.Serre
universe u v
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

abbrev serreAlgebra := Algebra A
abbrev quotientMap := projection A
def generators := (e A, f A, h A)

@[simp] theorem projection_eq_zero (x : Free ι) :
    projection A x = 0 ↔ x ∈ CartanMatrix.Relations.toIdeal ℂ A :=
  LieSubmodule.Quotient.mk_eq_zero'

theorem projection_surjective : Function.Surjective (projection A) := Quot.mk_surjective

theorem projection_ker : (projection A).ker = CartanMatrix.Relations.toIdeal ℂ A := by
  ext x
  exact projection_eq_zero A x

private theorem relation_zero {x : Free ι} (hx : x ∈ CartanMatrix.Relations.toSet ℂ A) :
    projection A x = 0 :=
  (projection_eq_zero A x).mpr (LieSubmodule.subset_lieSpan hx)

@[simp] theorem map_iterBracket {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
    [LieRing M] [LieAlgebra ℂ M] (φ : L →ₗ⁅ℂ⁆ M) (x y : L) (n : ℕ) :
    φ (iterBracket x n y) = iterBracket (φ x) n (φ y) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterBracket, LieHom.map_lie, ih]

theorem iterBracket_eq_pow {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (x y : L) (n : ℕ) : iterBracket x n y = (LieAlgebra.ad ℂ L x ^ n) y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterBracket, ih, pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]

private theorem iterBracket_succ_right {L : Type*} [LieRing L]
    (x y : L) (n : ℕ) : iterBracket x (n+1) y = iterBracket x n ⁅x,y⁆ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ⁅x, iterBracket x (n+1) y⁆ = ⁅x, iterBracket x n ⁅x,y⁆⁆
    rw [ih]

private theorem exponent_eq (a : ℤ) (ha : a ≤ 0) : (1-a).toNat = (-a).toNat + 1 := by
  omega

theorem hh (i j : ι) : ⁅h A i, h A j⁆ = 0 := by
  have hr := relation_zero A (x := CartanMatrix.Relations.HH ℂ (i,j)) (by
    simp only [CartanMatrix.Relations.toSet, Set.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(i,j), rfl⟩)))))
  simpa only [CartanMatrix.Relations.HH, Function.uncurry_apply_pair, Function.comp_apply, LieHom.map_lie, h] using hr

theorem he (i j : ι) : ⁅h A i, e A j⁆ = A i j • e A j := by
  have hr := relation_zero A (x := CartanMatrix.Relations.HE ℂ A (i,j)) (by
    simp only [CartanMatrix.Relations.toSet, Set.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(i,j), rfl⟩))))
  apply sub_eq_zero.mp
  simpa only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply,
    map_sub, LieHom.map_lie, map_zsmul, h, e] using hr

theorem hf (i j : ι) : ⁅h A i, f A j⁆ = -(A i j • f A j) := by
  have hr := relation_zero A (x := CartanMatrix.Relations.HF ℂ A (i,j)) (by
    simp only [CartanMatrix.Relations.toSet, Set.mem_union]
    exact Or.inl (Or.inl (Or.inr ⟨(i,j), rfl⟩)))
  apply eq_neg_of_add_eq_zero_left
  simpa only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply,
    map_add, LieHom.map_lie, map_zsmul, h, f] using hr

theorem ef (i j : ι) : ⁅e A i, f A j⁆ = if i = j then h A i else 0 := by
  have hr := relation_zero A (x := CartanMatrix.Relations.EF ℂ (i,j)) (by
    simp only [CartanMatrix.Relations.toSet, Set.mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i,j), rfl⟩)))))
  by_cases hij : i = j
  · subst j
    simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply, ite_true,
      map_sub, LieHom.map_lie] at hr
    simpa only [ite_true, e, f, h] using sub_eq_zero.mp hr
  · simpa only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply, ite_eq_right hij,
      LieHom.map_lie, e, f] using hr

theorem native_serre_e (i j : ι) :
    iterBracket (e A i) (-A i j).toNat ⁅e A i, e A j⁆ = 0 := by
  have hr := relation_zero A (x := CartanMatrix.Relations.adE ℂ A (i,j)) (by
    simp only [CartanMatrix.Relations.toSet, Set.mem_union]
    exact Or.inl (Or.inr ⟨(i,j), rfl⟩))
  simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply,
    ← iterBracket_eq_pow, map_iterBracket, LieHom.map_lie] at hr
  exact hr

theorem native_serre_f (i j : ι) :
    iterBracket (f A i) (-A i j).toNat ⁅f A i, f A j⁆ = 0 := by
  have hr := relation_zero A (x := CartanMatrix.Relations.adF ℂ A (i,j)) (by
    simp only [CartanMatrix.Relations.toSet, Set.mem_union]
    exact Or.inr ⟨(i,j), rfl⟩)
  simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply,
    ← iterBracket_eq_pow, map_iterBracket, LieHom.map_lie] at hr
  exact hr

theorem relations_spec :
    Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction.relationsExpected.{u} := by
  intro ι _ A ha
  refine ⟨hh A, he A, hf A, ef A, ?_, ?_⟩
  · intro i j hij
    rw [exponent_eq (A i j) (ha i j hij), iterBracket_succ_right]
    exact native_serre_e A i j
  · intro i j hij
    rw [exponent_eq (A i j) (ha i j hij), iterBracket_succ_right]
    exact native_serre_f A i j


@[simp] theorem iterBracket_zero {L : Type*} [LieRing L] (x : L) (n : ℕ) :
    iterBracket x n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterBracket, ih, lie_zero]

/-- Descent along an actual Lie-ideal quotient. -/
def quotientLift {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
    [LieRing M] [LieAlgebra ℂ M] (I : LieIdeal ℂ L)
    (φ : L →ₗ⁅ℂ⁆ M) (hI : I ≤ φ.ker) : L ⧸ I →ₗ⁅ℂ⁆ M :=
  { I.toSubmodule.liftQ φ.toLinearMap hI with
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on with | _ x =>
      induction y using Submodule.Quotient.induction_on with | _ y =>
      exact φ.map_lie x y }

@[simp] theorem quotientLift_mk {L M : Type*} [LieRing L] [LieAlgebra ℂ L]
    [LieRing M] [LieAlgebra ℂ M] (I : LieIdeal ℂ L)
    (φ : L →ₗ⁅ℂ⁆ M) (hI : I ≤ φ.ker) (x : L) :
    quotientLift I φ hI (LieSubmodule.Quotient.mk x) = φ x := rfl

/-- Assigning the three sorts of symbols fixes a homomorphism from the free algebra. -/
def freeAssignment {L : Type*} [LieRing L] [LieAlgebra ℂ L] (E F H : ι → L) :
    Free ι →ₗ⁅ℂ⁆ L :=
  FreeLieAlgebra.lift ℂ (fun x => match x with
    | .E i => E i
    | .F i => F i
    | .H i => H i)

omit [DecidableEq ι] in
@[simp] theorem freeAssignment_e {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (E F H : ι → L) (i : ι) :
    freeAssignment E F H (FreeLieAlgebra.of ℂ (.E i)) = E i :=
  FreeLieAlgebra.lift_of_apply _ _
omit [DecidableEq ι] in
@[simp] theorem freeAssignment_f {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (E F H : ι → L) (i : ι) :
    freeAssignment E F H (FreeLieAlgebra.of ℂ (.F i)) = F i :=
  FreeLieAlgebra.lift_of_apply _ _
omit [DecidableEq ι] in
@[simp] theorem freeAssignment_h {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (E F H : ι → L) (i : ι) :
    freeAssignment E F H (FreeLieAlgebra.of ℂ (.H i)) = H i :=
  FreeLieAlgebra.lift_of_apply _ _

theorem relations_le_ker {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (ha : ∀ i j, i ≠ j → A i j ≤ 0) (E F H : ι → L)
    (hr : RelationsHold A E F H) :
    CartanMatrix.Relations.toIdeal ℂ A ≤ (freeAssignment E F H).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  intro x hx
  change freeAssignment E F H x = 0
  simp only [CartanMatrix.Relations.toSet, Set.mem_union] at hx
  rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx)
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    simpa only [CartanMatrix.Relations.HH, Function.uncurry_apply_pair, Function.comp_apply, LieHom.map_lie, freeAssignment_h] using hr.1 i j
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    by_cases hij : i = j
    · subst j
      simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply,
        ite_true, map_sub, LieHom.map_lie,
        freeAssignment_e, freeAssignment_f, freeAssignment_h]
      exact sub_eq_zero.mpr (by simpa using hr.2.2.2.1 i i)
    · simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply,
        ite_eq_right hij, LieHom.map_lie, freeAssignment_e, freeAssignment_f]
      simpa only [ite_eq_right hij] using hr.2.2.2.1 i j
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply, map_sub, LieHom.map_lie, map_zsmul, freeAssignment_h,
      freeAssignment_e, hr.2.1 i j, sub_self]
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply, map_add, LieHom.map_lie, map_zsmul, freeAssignment_h,
      freeAssignment_f, hr.2.2.1 i j, neg_add_cancel]
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply,
      ← iterBracket_eq_pow, map_iterBracket, LieHom.map_lie, Function.comp_apply,
      freeAssignment_e]
    by_cases hij : i = j
    · subst j; simp only [lie_self, iterBracket_zero]
    · have hs := hr.2.2.2.2.1 i j hij
      rw [exponent_eq (A i j) (ha i j hij), iterBracket_succ_right] at hs
      exact hs
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply,
      ← iterBracket_eq_pow, map_iterBracket, LieHom.map_lie, Function.comp_apply,
      freeAssignment_f]
    by_cases hij : i = j
    · subst j; simp only [lie_self, iterBracket_zero]
    · have hs := hr.2.2.2.2.2 i j hij
      rw [exponent_eq (A i j) (ha i j hij), iterBracket_succ_right] at hs
      exact hs

def lift {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (ha : ∀ i j, i ≠ j → A i j ≤ 0) (E F H : ι → L)
    (hr : RelationsHold A E F H) : Algebra A →ₗ⁅ℂ⁆ L :=
  quotientLift _ (freeAssignment E F H) (relations_le_ker A ha E F H hr)

@[simp] theorem lift_e {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (ha : ∀ i j, i ≠ j → A i j ≤ 0) (E F H : ι → L)
    (hr : RelationsHold A E F H) (i : ι) : lift A ha E F H hr (e A i) = E i := by
  exact freeAssignment_e E F H i
@[simp] theorem lift_f {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (ha : ∀ i j, i ≠ j → A i j ≤ 0) (E F H : ι → L)
    (hr : RelationsHold A E F H) (i : ι) : lift A ha E F H hr (f A i) = F i := by
  exact freeAssignment_f E F H i
@[simp] theorem lift_h {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (ha : ∀ i j, i ≠ j → A i j ≤ 0) (E F H : ι → L)
    (hr : RelationsHold A E F H) (i : ι) : lift A ha E F H hr (h A i) = H i := by
  exact freeAssignment_h E F H i

@[ext] theorem hom_ext {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    {φ ψ : Algebra A →ₗ⁅ℂ⁆ L} (heq : ∀ i, φ (e A i) = ψ (e A i))
    (hfeq : ∀ i, φ (f A i) = ψ (f A i)) (hheq : ∀ i, φ (h A i) = ψ (h A i)) : φ = ψ := by
  have hc : φ.comp (projection A) = ψ.comp (projection A) := by
    apply FreeLieAlgebra.hom_ext
    intro x
    cases x with
    | E i => exact heq i
    | F i => exact hfeq i
    | H i => exact hheq i
  ext x
  obtain ⟨y, rfl⟩ := projection_surjective A x
  exact LieHom.congr_fun hc y

theorem presentation_spec :
    Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction.presentationExpected.{u,v} := by
  intro ι _ A ha L _ _ E F H hr
  refine ⟨lift A ha E F H hr, ⟨lift_e A ha E F H hr, lift_f A ha E F H hr,
    lift_h A ha E F H hr⟩, ?_⟩
  intro φ hφ
  apply hom_ext A
  · intro i; exact (hφ.1 i).trans (lift_e A ha E F H hr i).symm
  · intro i; exact (hφ.2.1 i).trans (lift_f A ha E F H hr i).symm
  · intro i; exact (hφ.2.2 i).trans (lift_h A ha E F H hr i).symm


/-- Set-free generators generate their free Lie algebra. -/
theorem free_generated (X : Type*) :
    LieSubalgebra.lieSpan ℂ (FreeLieAlgebra ℂ X) (Set.range (FreeLieAlgebra.of ℂ)) = ⊤ := by
  let S := LieSubalgebra.lieSpan ℂ (FreeLieAlgebra ℂ X) (Set.range (FreeLieAlgebra.of ℂ))
  let g : FreeLieAlgebra ℂ X →ₗ⁅ℂ⁆ S := FreeLieAlgebra.lift ℂ
    (fun x => ⟨FreeLieAlgebra.of ℂ x, LieSubalgebra.subset_lieSpan (Set.mem_range_self x)⟩)
  have hg : S.incl.comp g = (LieHom.id : FreeLieAlgebra ℂ X →ₗ⁅ℂ⁆ FreeLieAlgebra ℂ X) := by
    apply FreeLieAlgebra.hom_ext
    intro x
    exact congrArg (fun y : S => (y : FreeLieAlgebra ℂ X)) (FreeLieAlgebra.lift_of_apply _ x)
  apply top_unique
  intro x _
  have hx := LieHom.congr_fun hg x
  change (g x : FreeLieAlgebra ℂ X) = x at hx
  exact hx ▸ (g x).property

theorem free_lift_range {X L : Type*} [LieRing L] [LieAlgebra ℂ L] (g : X → L) :
    (FreeLieAlgebra.lift ℂ g).range = LieSubalgebra.lieSpan ℂ L (Set.range g) := by
  rw [LieHom.range_eq_map, ← free_generated X, LieSubalgebra.map_lieSpan]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext x
  exact FreeLieAlgebra.lift_of_apply g x

theorem sideIdeal_le_positive_ker : sideIdeal A ≤ (positiveLift A).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro x ⟨i,j,rfl⟩
  change positiveLift A (sideRelation A i j) = 0
  simpa only [sideRelation, map_iterBracket, LieHom.map_lie,
    positiveLift, FreeLieAlgebra.lift_of_apply] using native_serre_e A i j

theorem sideIdeal_le_negative_ker : sideIdeal A ≤ (negativeLift A).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro x ⟨i,j,rfl⟩
  change negativeLift A (sideRelation A i j) = 0
  simpa only [sideRelation, map_iterBracket, LieHom.map_lie,
    negativeLift, FreeLieAlgebra.lift_of_apply] using native_serre_f A i j

/-- These maps exist without assuming that they are injective. -/
def positiveMap : Side A →ₗ⁅ℂ⁆ Algebra A :=
  quotientLift _ (positiveLift A) (sideIdeal_le_positive_ker A)
def negativeMap : Side A →ₗ⁅ℂ⁆ Algebra A :=
  quotientLift _ (negativeLift A) (sideIdeal_le_negative_ker A)

theorem positiveLift_range : (positiveLift A).range = positive A := free_lift_range (e A)
theorem negativeLift_range : (negativeLift A).range = negative A := free_lift_range (f A)

theorem oneSided_spec :
    Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction.oneSidedExpected.{u} := by
  intro ι _ A
  exact ⟨sideIdeal_le_positive_ker A, sideIdeal_le_negative_ker A,
    positiveLift_range A, negativeLift_range A⟩

theorem empty_spec :
    Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction.emptyExpected.{u} := by
  intro ι _ _ A
  have hz : (LieHom.id : Algebra A →ₗ⁅ℂ⁆ Algebra A) = 0 := by
    apply hom_ext A
    all_goals intro i; exact isEmptyElim i
  have hx (x : Algebra A) : x = 0 := LieHom.congr_fun hz x
  exact ⟨fun x y => (hx x).trans (hx y).symm⟩


section SideSurvival
attribute [local instance 100] LieRing.ofAssociativeRing

/-- An abelian test representation detects a one-sided generator. -/
def sideEvaluation (i : ι) : SideFree ι →ₗ⁅ℂ⁆ ℂ :=
  FreeLieAlgebra.lift ℂ (fun j => if j = i then 1 else 0)

theorem sideIdeal_le_evaluation_ker (i : ι) : sideIdeal A ≤ (sideEvaluation i).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro x ⟨j,k,rfl⟩
  change sideEvaluation i (sideRelation A j k) = 0
  rw [sideRelation, map_iterBracket, LieHom.map_lie]
  have hc : ⁅sideEvaluation i (FreeLieAlgebra.of ℂ j),
      sideEvaluation i (FreeLieAlgebra.of ℂ k)⁆ = 0 := by
    simp only [Ring.lie_def, mul_comm, sub_self]
  rw [hc, iterBracket_zero]

theorem sideGenerator_ne_zero (i : ι) : sideGenerator A i ≠ 0 := by
  let φ : Side A →ₗ⁅ℂ⁆ ℂ :=
    quotientLift _ (sideEvaluation i) (sideIdeal_le_evaluation_ker A i)
  have hφ : φ (sideGenerator A i) = 1 := by
    change sideEvaluation i (FreeLieAlgebra.of ℂ i) = 1
    simp [sideEvaluation]
  intro hz
  rw [hz, map_zero] at hφ
  exact zero_ne_one hφ

end SideSurvival

theorem sideSurvival_spec :
    Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction.sideSurvivalExpected.{u} := by
  intro ι _ A i
  exact sideGenerator_ne_zero A i


theorem cartanConditions_spec :
    Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction.cartanConditionsExpected.{v,u} := by
  intro E _ _ ι _ R hR z hz b hb A hA
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply Int.cast_injective (α := ℝ)
    simpa only [Int.cast_ofNat] using
      (hA i i).trans (cartan_diagonal R hR z hz b hb i)
  · intro i j hij
    apply (Int.cast_nonpos (R := ℝ)).mp
    rw [hA i j]
    exact (cartan_offDiagonal R hR z hz b hb).2 i j hij
  · intro i j
    have hzero (i j : ι) : A i j = 0 ↔ inner ℝ (b i) (b j) = 0 := by
      rw [← cartan_zero_iff hR.toRootAxioms hb i j, ← hA i j]
      exact Int.cast_eq_zero.symm
    rw [hzero i j, hzero j i, real_inner_comm (b i) (b j)]


/-! The spanning direction uses only the mixed and Cartan relations. -/

section SpanningHelpers
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- Jacobi extends a bracket condition from a generating set to its Lie span. -/
theorem bracket_lieSpan_mem (K : LieSubalgebra ℂ L) (s : Set L) (a : L)
    (hs : s ⊆ K) (ha : ∀ x ∈ s, ⁅a,x⁆ ∈ K)
    {x : L} (hx : x ∈ LieSubalgebra.lieSpan ℂ L s) : ⁅a,x⁆ ∈ K := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx => exact ha x hx
  | zero => simpa only [lie_zero] using K.zero_mem
  | add x y _ _ hx hy => simpa only [lie_add] using K.add_mem hx hy
  | smul r x _ hx => simpa only [lie_smul] using K.smul_mem r hx
  | lie x y hx hy ihx ihy =>
    have hle := LieSubalgebra.lieSpan_le.mpr hs
    rw [leibniz_lie]
    exact K.add_mem (K.lie_mem ihx (hle hy)) (K.lie_mem (hle hx) ihy)

omit [DecidableEq ι] in
/-- A linear span of commuting generators is abelian. -/
theorem bracket_span_eq_zero (H : ι → L) (hH : ∀ i j, ⁅H i,H j⁆ = 0)
    {x y : L} (hx : x ∈ Submodule.span ℂ (Set.range H))
    (hy : y ∈ Submodule.span ℂ (Set.range H)) : ⁅x,y⁆ = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨j,rfl⟩ := hy; exact hH i j
    | zero => exact lie_zero _
    | add y z _ _ hy hz => simp only [lie_add, hy, hz, add_zero]
    | smul r y _ hy => simp only [lie_smul, hy, smul_zero]
  | zero => exact zero_lie _
  | add x z _ _ hx hz => simp only [add_lie, hx, hz, add_zero]
  | smul r x _ hx => simp only [smul_lie, hx, smul_zero]

omit [DecidableEq ι] in
/-- Linear combinations of elements normalizing a subalgebra still normalize it. -/
theorem bracket_span_mem (K : LieSubalgebra ℂ L) (H : ι → L)
    (hH : ∀ i y, y ∈ K → ⁅H i,y⁆ ∈ K)
    {x y : L} (hx : x ∈ Submodule.span ℂ (Set.range H)) (hy : y ∈ K) :
    ⁅x,y⁆ ∈ K := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i,rfl⟩ := hx; exact hH i y hy
  | zero => simpa only [zero_lie] using K.zero_mem
  | add x z _ _ hx hz => simpa only [add_lie] using K.add_mem hx hz
  | smul r x _ hx => simpa only [smul_lie] using K.smul_mem r hx

/-- Add an abelian subspace normalizing K to the Lie subalgebra K. -/
def sumWithAbelian (K : LieSubalgebra ℂ L) (H : Submodule ℂ L)
    (hH : ∀ x ∈ H, ∀ y ∈ H, ⁅x,y⁆ = 0)
    (hK : ∀ x ∈ H, ∀ y ∈ K, ⁅x,y⁆ ∈ K) : LieSubalgebra ℂ L :=
  { K.toSubmodule ⊔ H with
    lie_mem' := by
      intro x y hx hy
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨c,hc,d,hd,rfl⟩ := Submodule.mem_sup.mp hy
      rw [add_lie, lie_add, lie_add, hH b hb d hd, add_zero]
      apply Submodule.add_mem
      · apply Submodule.add_mem
        · exact Submodule.mem_sup_left (K.lie_mem ha hc)
        · rw [← lie_skew]
          exact Submodule.mem_sup_left (K.neg_mem (hK d hd a ha))
      · exact Submodule.mem_sup_left (hK b hb c hc) }

/-- Elements whose adjoint action preserves a specified linear subspace. -/
def adjointStabilizer (S : Submodule ℂ L) : LieSubalgebra ℂ L where
  carrier := {x | ∀ y ∈ S, ⁅x,y⁆ ∈ S}
  zero_mem' := by intro y hy; simpa only [zero_lie] using S.zero_mem
  add_mem' := by
    intro x z hx hz y hy
    simpa only [add_lie] using S.add_mem (hx y hy) (hz y hy)
  smul_mem' := by
    intro r x hx y hy
    simpa only [smul_lie] using S.smul_mem r (hx y hy)
  lie_mem' := by
    intro x z hx hz y hy
    rw [lie_lie]
    exact S.sub_mem (hx _ (hz y hy)) (hz _ (hx y hy))

end SpanningHelpers

@[simp] theorem e_mem_positive (i : ι) : e A i ∈ positive A :=
  LieSubalgebra.subset_lieSpan (Set.mem_range_self i)
@[simp] theorem f_mem_negative (i : ι) : f A i ∈ negative A :=
  LieSubalgebra.subset_lieSpan (Set.mem_range_self i)
@[simp] theorem h_mem_cartan (i : ι) : h A i ∈ cartan A :=
  Submodule.subset_span (Set.mem_range_self i)

theorem h_bracket_positive (i : ι) {x : Algebra A} (hx : x ∈ positive A) :
    ⁅h A i,x⁆ ∈ positive A := by
  apply bracket_lieSpan_mem (positive A) (Set.range (e A)) (h A i) _ _ hx
  · rintro x ⟨j,rfl⟩; exact e_mem_positive A j
  · rintro x ⟨j,rfl⟩
    rw [he]
    exact (positive A).toSubmodule.toAddSubgroup.zsmul_mem (e_mem_positive A j) _

theorem h_bracket_negative (i : ι) {x : Algebra A} (hx : x ∈ negative A) :
    ⁅h A i,x⁆ ∈ negative A := by
  apply bracket_lieSpan_mem (negative A) (Set.range (f A)) (h A i) _ _ hx
  · rintro x ⟨j,rfl⟩; exact f_mem_negative A j
  · rintro x ⟨j,rfl⟩
    rw [hf]
    exact (negative A).neg_mem ((negative A).toSubmodule.toAddSubgroup.zsmul_mem (f_mem_negative A j) _)

theorem cartan_bracket_positive {x y : Algebra A} (hx : x ∈ cartan A)
    (hy : y ∈ positive A) : ⁅x,y⁆ ∈ positive A :=
  bracket_span_mem (positive A) (h A) (h_bracket_positive A) hx hy

theorem cartan_bracket_negative {x y : Algebra A} (hx : x ∈ cartan A)
    (hy : y ∈ negative A) : ⁅x,y⁆ ∈ negative A :=
  bracket_span_mem (negative A) (h A) (h_bracket_negative A) hx hy

theorem cartan_bracket_cartan {x y : Algebra A} (hx : x ∈ cartan A)
    (hy : y ∈ cartan A) : ⁅x,y⁆ = 0 := bracket_span_eq_zero (h A) (hh A) hx hy

/-- The negative Borel, constructed as the actual sum of the two subspaces. -/
def negativeBorel : LieSubalgebra ℂ (Algebra A) :=
  sumWithAbelian (negative A) (cartan A)
    (fun _ hx _ hy => cartan_bracket_cartan A hx hy)
    (fun _ hx _ hy => cartan_bracket_negative A hx hy)

/-- The positive Borel, constructed as the actual sum of the two subspaces. -/
def positiveBorel : LieSubalgebra ℂ (Algebra A) :=
  sumWithAbelian (positive A) (cartan A)
    (fun _ hx _ hy => cartan_bracket_cartan A hx hy)
    (fun _ hx _ hy => cartan_bracket_positive A hx hy)

theorem e_bracket_negative (i : ι) {x : Algebra A} (hx : x ∈ negative A) :
    ⁅e A i,x⁆ ∈ negativeBorel A := by
  apply bracket_lieSpan_mem (negativeBorel A) (Set.range (f A)) (e A i) _ _ hx
  · rintro x ⟨j,rfl⟩
    exact Submodule.mem_sup_left (f_mem_negative A j)
  · rintro x ⟨j,rfl⟩
    rw [ef]
    split_ifs
    · exact Submodule.mem_sup_right (h_mem_cartan A i)
    · exact (negativeBorel A).zero_mem

theorem f_bracket_positive (i : ι) {x : Algebra A} (hx : x ∈ positive A) :
    ⁅f A i,x⁆ ∈ positiveBorel A := by
  apply bracket_lieSpan_mem (positiveBorel A) (Set.range (e A)) (f A i) _ _ hx
  · rintro x ⟨j,rfl⟩
    exact Submodule.mem_sup_left (e_mem_positive A j)
  · rintro x ⟨j,rfl⟩
    rw [← lie_skew, ef]
    split_ifs
    · exact (positiveBorel A).neg_mem (Submodule.mem_sup_right (h_mem_cartan A j))
    · simpa only [neg_zero] using (positiveBorel A).zero_mem


omit [DecidableEq ι] in
/-- A bracket condition with linear target extends across a linear span. -/
theorem bracket_span_right_mem {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (S : Submodule ℂ L) (H : ι → L) (a : L)
    (ha : ∀ i, ⁅a,H i⁆ ∈ S) {x : L}
    (hx : x ∈ Submodule.span ℂ (Set.range H)) : ⁅a,x⁆ ∈ S := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i,rfl⟩ := hx; exact ha i
  | zero => simpa only [lie_zero] using S.zero_mem
  | add x y _ _ hx hy => simpa only [lie_add] using S.add_mem hx hy
  | smul r x _ hx => simpa only [lie_smul] using S.smul_mem r hx

/-- A bracket condition with linear target extends across a sum of subspaces. -/
theorem bracket_sup_right_mem {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (S T U : Submodule ℂ L) (a : L)
    (hT : ∀ x ∈ T, ⁅a,x⁆ ∈ S) (hU : ∀ x ∈ U, ⁅a,x⁆ ∈ S)
    {x : L} (hx : x ∈ T ⊔ U) : ⁅a,x⁆ ∈ S := by
  obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  rw [lie_add]
  exact S.add_mem (hT y hy) (hU z hz)

theorem e_bracket_cartan (i : ι) {x : Algebra A} (hx : x ∈ cartan A) :
    ⁅e A i,x⁆ ∈ positive A := by
  apply bracket_span_right_mem (positive A).toSubmodule (h A) (e A i) _ hx
  intro j
  rw [← lie_skew, he]
  exact (positive A).neg_mem
    ((positive A).toSubmodule.toAddSubgroup.zsmul_mem (e_mem_positive A i) _)

theorem f_bracket_cartan (i : ι) {x : Algebra A} (hx : x ∈ cartan A) :
    ⁅f A i,x⁆ ∈ negative A := by
  apply bracket_span_right_mem (negative A).toSubmodule (h A) (f A i) _ hx
  intro j
  rw [← lie_skew, hf, neg_neg]
  exact (negative A).toSubmodule.toAddSubgroup.zsmul_mem (f_mem_negative A i) _

/-- The three specified families generate the actual quotient. -/
theorem generators_generate (K : LieSubalgebra ℂ (Algebra A))
    (hE : ∀ i, e A i ∈ K) (hF : ∀ i, f A i ∈ K) (hH : ∀ i, h A i ∈ K) : K = ⊤ := by
  have hfree : (⊤ : LieSubalgebra ℂ (Free ι)) ≤ K.comap (projection A) := by
    rw [← free_generated (CartanMatrix.Generators ι)]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro x ⟨g,rfl⟩
    cases g with
    | E i => exact hE i
    | F i => exact hF i
    | H i => exact hH i
  apply top_unique
  intro x _
  obtain ⟨y,rfl⟩ := projection_surjective A x
  exact hfree (LieSubalgebra.mem_top y)

/-- The vector subspace of sums of negative, Cartan, and positive elements. -/
def triangularSpan : Submodule ℂ (Algebra A) :=
  (negative A).toSubmodule ⊔ (cartan A ⊔ (positive A).toSubmodule)

theorem negative_le_triangularSpan : (negative A).toSubmodule ≤ triangularSpan A := le_sup_left
theorem cartan_le_triangularSpan : cartan A ≤ triangularSpan A := le_sup_right.trans' le_sup_left
theorem positive_le_triangularSpan : (positive A).toSubmodule ≤ triangularSpan A :=
  le_sup_right.trans' le_sup_right

theorem negativeBorel_le_triangularSpan : (negativeBorel A).toSubmodule ≤ triangularSpan A :=
  sup_le (negative_le_triangularSpan A) (cartan_le_triangularSpan A)
theorem positiveBorel_le_triangularSpan : (positiveBorel A).toSubmodule ≤ triangularSpan A :=
  sup_le (positive_le_triangularSpan A) (cartan_le_triangularSpan A)

theorem e_mem_triangularStabilizer (i : ι) : e A i ∈ adjointStabilizer (triangularSpan A) := by
  intro x hx
  apply bracket_sup_right_mem (triangularSpan A) (negative A).toSubmodule
    (cartan A ⊔ (positive A).toSubmodule) (e A i) _ _ hx
  · intro y hy
    exact negativeBorel_le_triangularSpan A (e_bracket_negative A i hy)
  · intro y hy
    apply bracket_sup_right_mem (triangularSpan A) (cartan A) (positive A).toSubmodule
      (e A i) _ _ hy
    · intro z hz
      exact positive_le_triangularSpan A (e_bracket_cartan A i hz)
    · intro z hz
      exact positive_le_triangularSpan A ((positive A).lie_mem (e_mem_positive A i) hz)

theorem f_mem_triangularStabilizer (i : ι) : f A i ∈ adjointStabilizer (triangularSpan A) := by
  intro x hx
  apply bracket_sup_right_mem (triangularSpan A) (negative A).toSubmodule
    (cartan A ⊔ (positive A).toSubmodule) (f A i) _ _ hx
  · intro y hy
    exact negative_le_triangularSpan A ((negative A).lie_mem (f_mem_negative A i) hy)
  · intro y hy
    apply bracket_sup_right_mem (triangularSpan A) (cartan A) (positive A).toSubmodule
      (f A i) _ _ hy
    · intro z hz
      exact negative_le_triangularSpan A (f_bracket_cartan A i hz)
    · intro z hz
      exact positiveBorel_le_triangularSpan A (f_bracket_positive A i hz)

theorem h_mem_triangularStabilizer (i : ι) : h A i ∈ adjointStabilizer (triangularSpan A) := by
  intro x hx
  apply bracket_sup_right_mem (triangularSpan A) (negative A).toSubmodule
    (cartan A ⊔ (positive A).toSubmodule) (h A i) _ _ hx
  · intro y hy
    exact negative_le_triangularSpan A (h_bracket_negative A i hy)
  · intro y hy
    apply bracket_sup_right_mem (triangularSpan A) (cartan A) (positive A).toSubmodule
      (h A i) _ _ hy
    · intro z hz
      rw [cartan_bracket_cartan A (h_mem_cartan A i) hz]
      exact (triangularSpan A).zero_mem
    · intro z hz
      exact positive_le_triangularSpan A (h_bracket_positive A i hz)

/-- Every Lie word is a sum of a negative word, a Cartan element and a positive word.
This conclusion holds for every integer matrix, without any nonvanishing assumption. -/
theorem triangularSpan_eq_top : triangularSpan A = ⊤ := by
  have hstab : adjointStabilizer (triangularSpan A) = ⊤ :=
    generators_generate A _ (e_mem_triangularStabilizer A)
      (f_mem_triangularStabilizer A) (h_mem_triangularStabilizer A)
  let K : LieSubalgebra ℂ (Algebra A) :=
    { triangularSpan A with
      lie_mem' := by
        intro x y hx hy
        have hx' : x ∈ adjointStabilizer (triangularSpan A) := by rw [hstab]; trivial
        exact hx' y hy }
  have hK : K = ⊤ := generators_generate A K
    (fun i => positive_le_triangularSpan A (e_mem_positive A i))
    (fun i => negative_le_triangularSpan A (f_mem_negative A i))
    (fun i => cartan_le_triangularSpan A (h_mem_cartan A i))
  exact congrArg LieSubalgebra.toSubmodule hK

/-- Surjectivity is the spanning half of the triangular decomposition. -/
theorem triangularSum_surjective : Function.Surjective (triangularSum A) := by
  apply LinearMap.range_eq_top.mp
  change LinearMap.range ((negative A).toSubmodule.subtype.coprod
    ((cartan A).subtype.coprod (positive A).toSubmodule.subtype)) = ⊤
  rw [LinearMap.range_coprod, LinearMap.range_coprod,
    Submodule.range_subtype, Submodule.range_subtype, Submodule.range_subtype]
  exact triangularSpan_eq_top A


section IteratedCommutators
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- Weights add when a vector is repeatedly bracketed by a weight vector. -/
theorem bracket_iterBracket_weight (H E X : L) (a b : ℂ)
    (hE : ⁅H,E⁆ = a • E) (hX : ⁅H,X⁆ = b • X) (n : ℕ) :
    ⁅H,iterBracket E n X⁆ = (b + n * a) • iterBracket E n X := by
  induction n with
  | zero => simpa only [iterBracket, Nat.cast_zero, zero_mul, add_zero] using hX
  | succ n ih =>
    change ⁅H,⁅E,iterBracket E n X⁆⁆ = (b + (n+1 : ℕ) * a) • ⁅E,iterBracket E n X⁆
    rw [leibniz_lie, hE, ih, smul_lie, lie_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- The lowering calculation does not require a finite dimensional representation. -/
theorem lowering_iterBracket (H E F X : L) (a : ℂ)
    (hE : ⁅H,E⁆ = (2 : ℂ) • E) (hX : ⁅H,X⁆ = a • X)
    (hFE : ⁅F,E⁆ = -H) (hFX : ⁅F,X⁆ = 0) (n : ℕ) :
    ⁅F,iterBracket E (n+1) X⁆ =
      -((n+1 : ℕ) * (a+n) : ℂ) • iterBracket E n X := by
  induction n with
  | zero =>
    simp only [iterBracket, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add,
      add_zero, one_mul, neg_smul]
    rw [leibniz_lie, hFE, hFX, lie_zero, add_zero, neg_lie, hX]
  | succ n ih =>
    change ⁅F,⁅E,iterBracket E (n+1) X⁆⁆ =
      -((n+1+1 : ℕ) * (a+(n+1 : ℕ)) : ℂ) • ⁅E,iterBracket E n X⁆
    rw [leibniz_lie, hFE, neg_lie, bracket_iterBracket_weight H E X 2 a hE hX,
      ih, lie_smul]
    change -((a + (n+1 : ℕ) * 2) • iterBracket E (n+1) X) +
      (-((n+1 : ℕ) * (a+n) : ℂ)) • iterBracket E (n+1) X = _
    rw [← neg_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- A vector commuting with both inputs commutes with every iterated bracket. -/
theorem bracket_iterBracket_eq_zero (Y E X : L) (hE : ⁅Y,E⁆ = 0) (hX : ⁅Y,X⁆ = 0)
    (n : ℕ) : ⁅Y,iterBracket E n X⁆ = 0 := by
  induction n with
  | zero => exact hX
  | succ n ih => rw [iterBracket, leibniz_lie, hE, ih, zero_lie, lie_zero, add_zero]

/-- If Y commutes with E, its bracket passes through repeated bracketing by E. -/
theorem bracket_iterBracket_of_commute (Y E X : L) (hE : ⁅Y,E⁆ = 0) (n : ℕ) :
    ⁅Y,iterBracket E n X⁆ = iterBracket E n ⁅Y,X⁆ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterBracket, leibniz_lie, hE, zero_lie, zero_add, ih, iterBracket]

end IteratedCommutators


@[simp] theorem iterBracket_neg {L : Type*} [LieRing L] (x y : L) (n : ℕ) :
    iterBracket x n (-y) = -iterBracket x n y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterBracket, ih, lie_neg]

theorem iterBracket_add {L : Type*} [LieRing L] (x y : L) (m n : ℕ) :
    iterBracket x (m+n) y = iterBracket x m (iterBracket x n y) := by
  induction m with
  | zero => simp only [Nat.zero_add, iterBracket]
  | succ m ih =>
    rw [Nat.succ_add]
    exact congrArg (fun z => ⁅x,z⁆) ih

/-- Two repeated brackets kill a Cartan vector whose first bracket is a multiple of E. -/
theorem iterBracket_cartan_eq_zero {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (E H : L) (a : ℂ) (hEH : ⁅E,H⁆ = a • E) (n : ℕ) (hn : 2 ≤ n) :
    iterBracket E n H = 0 := by
  have hz : iterBracket E 2 H = 0 := by
    simp only [iterBracket, hEH, lie_smul, lie_self, smul_zero]
  rw [show n = (n-2)+2 by omega, iterBracket_add, hz, iterBracket_zero]

/-- The positive Serre vectors are annihilated by every negative generator,
using only the mixed relations and the three algebraic Cartan conditions.
In particular this applies before imposing any Serre relations. -/
theorem negative_bracket_serre {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (E F H : ι → L) (hA : CartanConditions A)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0)
    (i j : ι) (hij : i ≠ j) (k : ι) :
    ⁅F k,iterBracket (E i) (1-A i j).toNat (E j)⁆ = 0 := by
  have hFE (k l : ι) : ⁅F k,E l⁆ = -(if l = k then H l else 0) := by
    rw [← lie_skew, hEF]
  have hHE' (k l : ι) : ⁅H k,E l⁆ = (A k l : ℂ) • E l := by
    simpa only [Int.cast_smul_eq_zsmul] using hHE k l
  by_cases hki : k = i
  · subst k
    rw [exponent_eq _ (hA.2.1 i j hij)]
    have hE : ⁅H i,E i⁆ = (2 : ℂ) • E i := by
      simpa only [hA.1 i, Int.cast_ofNat] using hHE' i i
    have hFEi : ⁅F i,E i⁆ = -H i := by simpa only [ite_true] using hFE i i
    have hFEj : ⁅F i,E j⁆ = 0 := by
      simpa only [ite_eq_right (Ne.symm hij), neg_zero] using hFE i j
    rw [lowering_iterBracket (H i) (E i) (F i) (E j) (A i j : ℂ)
      hE (hHE' i j) hFEi hFEj]
    have hn : (((-A i j).toNat : ℕ) : ℤ) = -A i j :=
      Int.toNat_of_nonneg (neg_nonneg.mpr (hA.2.1 i j hij))
    have hn' : (((-A i j).toNat : ℕ) : ℂ) = -(A i j : ℂ) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ => (z : ℂ)) hn
    rw [hn', add_neg_cancel, mul_zero, neg_zero, zero_smul]
  · have hFEi : ⁅F k,E i⁆ = 0 := by
      simpa only [ite_eq_right (Ne.symm hki), neg_zero] using hFE k i
    rw [bracket_iterBracket_of_commute (F k) (E i) (E j) hFEi]
    by_cases hkj : k = j
    · subst k
      rw [hFE, ite_eq_left rfl, iterBracket_neg, neg_eq_zero]
      by_cases ha : A i j = 0
      · have haji := (hA.2.2 i j).mp ha
        simp only [ha, sub_zero, Int.toNat_one, iterBracket]
        rw [← lie_skew, hHE, haji, zero_smul, neg_zero]
      · apply iterBracket_cartan_eq_zero (E i) (H j) (-(A j i : ℂ))
        · rw [← lie_skew, hHE', neg_smul]
        · have hnonpos := hA.2.1 i j hij
          omega
    · have hz : ⁅F k,E j⁆ = 0 := by
        simpa only [ite_eq_right (Ne.symm hkj), neg_zero] using hFE k j
      rw [hz, iterBracket_zero]


section SerreIdeals
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

/-- Repeated left brackets, with the head of the list acting last. -/
def bracketWord (E : ι → L) : List ι → L → L
  | [], x => x
  | i::w, x => ⁅E i,bracketWord E w x⁆

/-- The original off-diagonal Serre vector, without imposing that it vanish. -/
def serreVector (E : ι → L) (i j : ι) : L :=
  iterBracket (E i) (1-A i j).toNat (E j)

/-- The one-sided ideal as a span of positive words acting on Serre vectors. -/
def serreWordSpan (E : ι → L) : Submodule ℂ L :=
  Submodule.span ℂ {x | ∃ (w : List ι) (i j : ι), i ≠ j ∧
    x = bracketWord E w (serreVector A E i j)}

theorem bracketWord_mem_serreWordSpan (E : ι → L) (w : List ι) (i j : ι) (hij : i ≠ j) :
    bracketWord E w (serreVector A E i j) ∈ serreWordSpan A E :=
  Submodule.subset_span ⟨w,i,j,hij,rfl⟩

theorem serreVector_mem_serreWordSpan (E : ι → L) (i j : ι) (hij : i ≠ j) :
    serreVector A E i j ∈ serreWordSpan A E :=
  bracketWord_mem_serreWordSpan A E [] i j hij

/-- Left brackets by a one-sided generator preserve its Serre-word span. -/
theorem generator_bracket_serreWordSpan (E : ι → L) (k : ι) {x : L}
    (hx : x ∈ serreWordSpan A E) : ⁅E k,x⁆ ∈ serreWordSpan A E := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,i,j,hij,rfl⟩ := hx
    exact bracketWord_mem_serreWordSpan A E (k::w) i j hij
  | zero => simpa only [lie_zero] using (serreWordSpan A E).zero_mem
  | add x y _ _ hx hy => simpa only [lie_add] using (serreWordSpan A E).add_mem hx hy
  | smul r x _ hx => simpa only [lie_smul] using (serreWordSpan A E).smul_mem r hx

/-- Cartan elements normalize the one-sided Serre-word span. -/
theorem cartan_bracket_serreWordSpan (E H : ι → L)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j) (k : ι) {x : L}
    (hx : x ∈ serreWordSpan A E) : ⁅H k,x⁆ ∈ serreWordSpan A E := by
  have hword (w : List ι) (i j : ι) (hij : i ≠ j) :
      ⁅H k,bracketWord E w (serreVector A E i j)⁆ ∈ serreWordSpan A E := by
    induction w with
    | nil =>
      change ⁅H k,iterBracket (E i) (1-A i j).toNat (E j)⁆ ∈ serreWordSpan A E
      have hc (l : ι) : ⁅H k,E l⁆ = (A k l : ℂ) • E l := by
        simpa only [Int.cast_smul_eq_zsmul] using hHE k l
      rw [bracket_iterBracket_weight (H k) (E i) (E j) _ _ (hc i) (hc j)]
      exact (serreWordSpan A E).smul_mem _ (serreVector_mem_serreWordSpan A E i j hij)
    | cons l w ih =>
      rw [bracketWord, leibniz_lie, hHE, zsmul_lie]
      apply (serreWordSpan A E).add_mem
      · exact (serreWordSpan A E).toAddSubgroup.zsmul_mem
          (bracketWord_mem_serreWordSpan A E (l::w) i j hij) _
      · exact generator_bracket_serreWordSpan A E l ih
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w,i,j,hij,rfl⟩ := hx; exact hword w i j hij
  | zero => simpa only [lie_zero] using (serreWordSpan A E).zero_mem
  | add x y _ _ hx hy => simpa only [lie_add] using (serreWordSpan A E).add_mem hx hy
  | smul r x _ hx => simpa only [lie_smul] using (serreWordSpan A E).smul_mem r hx

/-- Negative generators normalize the positive Serre-word span. -/
theorem negative_bracket_serreWordSpan (E F H : ι → L) (hA : CartanConditions A)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0)
    (k : ι) {x : L} (hx : x ∈ serreWordSpan A E) : ⁅F k,x⁆ ∈ serreWordSpan A E := by
  have hword (w : List ι) (i j : ι) (hij : i ≠ j) :
      ⁅F k,bracketWord E w (serreVector A E i j)⁆ ∈ serreWordSpan A E := by
    induction w with
    | nil =>
      rw [bracketWord, serreVector, negative_bracket_serre A E F H hA hHE hEF i j hij k]
      exact (serreWordSpan A E).zero_mem
    | cons l w ih =>
      rw [bracketWord, leibniz_lie]
      apply (serreWordSpan A E).add_mem
      · rw [← lie_skew (F k) (E l), hEF]
        split_ifs
        · rw [neg_lie]
          exact (serreWordSpan A E).neg_mem (cartan_bracket_serreWordSpan A E H hHE l
            (bracketWord_mem_serreWordSpan A E w i j hij))
        · simpa only [neg_zero, zero_lie] using (serreWordSpan A E).zero_mem
      · exact generator_bracket_serreWordSpan A E l ih
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨w,i,j,hij,rfl⟩ := hx; exact hword w i j hij
  | zero => simpa only [lie_zero] using (serreWordSpan A E).zero_mem
  | add x y _ _ hx hy => simpa only [lie_add] using (serreWordSpan A E).add_mem hx hy
  | smul r x _ hx => simpa only [lie_smul] using (serreWordSpan A E).smul_mem r hx

/-- Under generation by E,F,H, the one-sided Serre-word span is a full Lie ideal.
Generation here is an explicit upstream condition, not a faithfulness assumption. -/
def positiveSerreIdeal (E F H : ι → L) (hA : CartanConditions A)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0)
    (hgen : ∀ K : LieSubalgebra ℂ L,
      (∀ i, E i ∈ K) → (∀ i, F i ∈ K) → (∀ i, H i ∈ K) → K = ⊤) :
    LieIdeal ℂ L :=
  { serreWordSpan A E with
    lie_mem := by
      intro x y hy
      have hstab : adjointStabilizer (serreWordSpan A E) = ⊤ := hgen _
        (fun i _ hz => generator_bracket_serreWordSpan A E i hz)
        (fun i _ hz => negative_bracket_serreWordSpan A E F H hA hHE hEF i hz)
        (fun i _ hz => cartan_bracket_serreWordSpan A E H hHE i hz)
      have hx : x ∈ adjointStabilizer (serreWordSpan A E) := by rw [hstab]; trivial
      exact hx y hy }


/-- Every ambient Lie ideal containing the Serre vectors contains their word span. -/
theorem serreWordSpan_le (E : ι → L) (J : LieIdeal ℂ L)
    (hJ : ∀ i j, i ≠ j → serreVector A E i j ∈ J) :
    serreWordSpan A E ≤ J.toSubmodule := by
  apply Submodule.span_le.mpr
  rintro x ⟨w,i,j,hij,rfl⟩
  induction w with
  | nil => exact hJ i j hij
  | cons l w ih => exact J.lie_mem ih

/-- Exact identification with the full ideal generated by the one-sided Serre vectors. -/
theorem positiveSerreIdeal_eq (E F H : ι → L) (hA : CartanConditions A)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0)
    (hgen : ∀ K : LieSubalgebra ℂ L,
      (∀ i, E i ∈ K) → (∀ i, F i ∈ K) → (∀ i, H i ∈ K) → K = ⊤) :
    positiveSerreIdeal A E F H hA hHE hEF hgen =
      LieSubmodule.lieSpan ℂ L {x | ∃ i j, i ≠ j ∧ x = serreVector A E i j} := by
  apply le_antisymm
  · exact serreWordSpan_le A E _ (fun i j hij => LieSubmodule.subset_lieSpan ⟨i,j,hij,rfl⟩)
  · apply LieSubmodule.lieSpan_le.mpr
    rintro x ⟨i,j,hij,rfl⟩
    exact serreVector_mem_serreWordSpan A E i j hij

/-- Exchange positive and negative generators and negate the Cartan generators. -/
def negativeSerreIdeal (E F H : ι → L) (hA : CartanConditions A)
    (hHF : ∀ i j, ⁅H i,F j⁆ = -(A i j • F j))
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0)
    (hgen : ∀ K : LieSubalgebra ℂ L,
      (∀ i, E i ∈ K) → (∀ i, F i ∈ K) → (∀ i, H i ∈ K) → K = ⊤) :
    LieIdeal ℂ L := by
  apply positiveSerreIdeal A F E (fun i => -H i) hA
  · intro i j
    rw [neg_lie, hHF, neg_neg]
  · intro i j
    rw [← lie_skew, hEF]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
    · simp only [ite_eq_right hij, ite_eq_right (Ne.symm hij), neg_zero]
  · intro K hF hE hH
    apply hgen K hE hF
    intro i
    have hHi : -H i ∈ K := hH i
    have hHi' : -(-H i) ∈ K := K.neg_mem hHi
    rwa [neg_neg] at hHi' 

/-- The negative ideal has exactly its negative-word span as underlying submodule. -/
theorem negativeSerreIdeal_toSubmodule (E F H : ι → L) (hA : CartanConditions A)
    (hHF : ∀ i j, ⁅H i,F j⁆ = -(A i j • F j))
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0)
    (hgen : ∀ K : LieSubalgebra ℂ L,
      (∀ i, E i ∈ K) → (∀ i, F i ∈ K) → (∀ i, H i ∈ K) → K = ⊤) :
    (negativeSerreIdeal A E F H hA hHF hEF hgen).toSubmodule = serreWordSpan A F := rfl

/-- The full Serre ideal is exactly the sum of the two one-sided word spans.
Directness and absence of a Cartan component subsequently follow from the
faithful pre-Serre triangular decomposition, which is not assumed or proved here. -/
theorem fullSerreIdeal_eq (E F H : ι → L) (hA : CartanConditions A)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i,F j⁆ = -(A i j • F j))
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0)
    (hgen : ∀ K : LieSubalgebra ℂ L,
      (∀ i, E i ∈ K) → (∀ i, F i ∈ K) → (∀ i, H i ∈ K) → K = ⊤) :
    (LieSubmodule.lieSpan ℂ L
      ({x | ∃ i j, i ≠ j ∧ x = serreVector A F i j} ∪
       {x | ∃ i j, i ≠ j ∧ x = serreVector A E i j})).toSubmodule =
      serreWordSpan A F ⊔ serreWordSpan A E := by
  let Iminus := negativeSerreIdeal A E F H hA hHF hEF hgen
  let Iplus := positiveSerreIdeal A E F H hA hHE hEF hgen
  have hmin : Iminus = LieSubmodule.lieSpan ℂ L
      {x | ∃ i j, i ≠ j ∧ x = serreVector A F i j} := by
    apply le_antisymm
    · exact serreWordSpan_le A F _
        (fun i j hij => LieSubmodule.subset_lieSpan ⟨i,j,hij,rfl⟩)
    · apply LieSubmodule.lieSpan_le.mpr
      rintro x ⟨i,j,hij,rfl⟩
      exact serreVector_mem_serreWordSpan A F i j hij
  have hplus := positiveSerreIdeal_eq A E F H hA hHE hEF hgen
  rw [LieSubmodule.span_union, ← hmin, ← hplus, LieSubmodule.sup_toSubmodule]
  rfl

end SerreIdeals

end LieAlgebrasAndRepresentations.Serre



namespace LieAlgebrasAndRepresentations.Serre
universe u v w
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

section WordSpanMaps
variable {L : Type v} {M : Type w} [LieRing L] [LieAlgebra ℂ L]
  [LieRing M] [LieAlgebra ℂ M]

omit [DecidableEq ι] in
@[simp] theorem map_bracketWord (φ : L →ₗ⁅ℂ⁆ M) (E : ι → L) (w : List ι) (x : L) :
    φ (bracketWord E w x) = bracketWord (fun i => φ (E i)) w (φ x) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [bracketWord, LieHom.map_lie, ih]

omit [DecidableEq ι] in
@[simp] theorem map_serreVector (φ : L →ₗ⁅ℂ⁆ M) (E : ι → L) (i j : ι) :
    φ (serreVector A E i j) = serreVector A (fun i => φ (E i)) i j :=
  map_iterBracket φ _ _ _

omit [DecidableEq ι] in
theorem serreWordSpan_map (φ : L →ₗ⁅ℂ⁆ M) (E : ι → L) :
    (serreWordSpan A E).map φ.toLinearMap = serreWordSpan A (fun i => φ (E i)) := by
  unfold serreWordSpan
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨w,i,j,hij,rfl⟩, rfl⟩
    exact ⟨w,i,j,hij, by
      change φ (bracketWord E w (serreVector A E i j)) = _
      rw [map_bracketWord, map_serreVector]⟩
  · rintro ⟨w,i,j,hij,rfl⟩
    exact ⟨_, ⟨w,i,j,hij,rfl⟩, by
      change φ (bracketWord E w (serreVector A E i j)) = _
      rw [map_bracketWord, map_serreVector]⟩
end WordSpanMaps

theorem sideWordSpan_eq_sideIdeal (ha : ∀ i j, i ≠ j → A i j ≤ 0) :
    serreWordSpan A (FreeLieAlgebra.of ℂ : ι → SideFree ι) =
      (sideIdeal A).toSubmodule := by
  let S := serreWordSpan A (FreeLieAlgebra.of ℂ : ι → SideFree ι)
  have hstab : adjointStabilizer S = ⊤ := by
    apply top_unique
    rw [← free_generated ι]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i,rfl⟩
    exact fun _ hx => generator_bracket_serreWordSpan A (FreeLieAlgebra.of ℂ) i hx
  let J : LieIdeal ℂ (SideFree ι) :=
    { S with
      lie_mem := by
        intro x y hy
        have hx : x ∈ adjointStabilizer S := by rw [hstab]; trivial
        exact hx y hy }
  have hvec (i j : ι) (hij : i ≠ j) :
      serreVector A (FreeLieAlgebra.of ℂ : ι → SideFree ι) i j = sideRelation A i j := by
    unfold serreVector sideRelation
    rw [show (1-A i j).toNat = (-A i j).toNat + 1 by have := ha i j hij; omega]
    have hr (x y : SideFree ι) (n : ℕ) :
        iterBracket x (n+1) y = iterBracket x n ⁅x,y⁆ := by
      induction n with
      | zero => rfl
      | succ n ih => exact congrArg (fun z => ⁅x,z⁆) ih
    exact hr _ _ _
  apply le_antisymm
  · exact serreWordSpan_le A (FreeLieAlgebra.of ℂ) (sideIdeal A) (fun i j hij => by
      rw [hvec i j hij]
      exact LieSubmodule.subset_lieSpan ⟨i,j,rfl⟩)
  · change (sideIdeal A).toSubmodule ≤ J.toSubmodule
    change sideIdeal A ≤ J
    apply LieSubmodule.lieSpan_le.mpr
    rintro _ ⟨i,j,rfl⟩
    by_cases hij : i = j
    · subst j
      simp only [sideRelation, lie_self, iterBracket_zero]
      exact J.zero_mem
    · rw [← hvec i j hij]
      exact serreVector_mem_serreWordSpan A (FreeLieAlgebra.of ℂ) i j hij

/-- Any canonical map from the one-sided free algebra carries its one-sided ideal
exactly to the span of the ambient Serre words. -/
theorem sideIdeal_map_eq_serreWordSpan {L : Type v} [LieRing L] [LieAlgebra ℂ L]
    (ha : ∀ i j, i ≠ j → A i j ≤ 0) (E : ι → L) :
    (sideIdeal A).toSubmodule.map (FreeLieAlgebra.lift ℂ E).toLinearMap =
      serreWordSpan A E := by
  rw [← sideWordSpan_eq_sideIdeal A ha, serreWordSpan_map]
  congr 1
  funext i
  exact FreeLieAlgebra.lift_of_apply _ i

end LieAlgebrasAndRepresentations.Serre

namespace LieAlgebrasAndRepresentations.Serre
universe u₁ u₂ u₃ u₄
section CoordinateIdeals
variable {X : Type u₁} {C : Type u₂} {Y : Type u₃} {L : Type u₄}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup C] [Module ℂ C]
  [AddCommGroup Y] [Module ℂ Y] [AddCommGroup L] [Module ℂ L]

/-- Under a faithful three-coordinate sum, the sum of ideals in the outer
coordinates has precisely those coordinates and zero middle coordinate. -/
theorem threeCoordinateIdeal_mem_iff (P : X →ₗ[ℂ] L) (H : C →ₗ[ℂ] L)
    (Q : Y →ₗ[ℂ] L) (N : Submodule ℂ X) (M : Submodule ℂ Y)
    (hinj : Function.Injective (P.coprod (H.coprod Q))) (x : X) (c : C) (y : Y) :
    P x + (H c + Q y) ∈ N.map P ⊔ M.map Q ↔ x ∈ N ∧ c = 0 ∧ y ∈ M := by
  constructor
  · intro hz
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
    obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hb
    have heq : P.coprod (H.coprod Q) (n, (0, m)) =
        P.coprod (H.coprod Q) (x, (c, y)) := by
      simpa only [LinearMap.coprod_apply, map_zero, zero_add] using hab
    have hcoord := hinj heq
    have hn' : n = x := congrArg Prod.fst hcoord
    have hc' : (0 : C) = c := congrArg (fun z : X × (C × Y) => z.2.1) hcoord
    have hm' : m = y := congrArg (fun z : X × (C × Y) => z.2.2) hcoord
    exact ⟨hn' ▸ hn, hc'.symm, hm' ▸ hm⟩
  · rintro ⟨hx,rfl,hy⟩
    simp only [map_zero, zero_add]
    exact (N.map P ⊔ M.map Q).add_mem
      (Submodule.mem_sup_left (Submodule.mem_map.mpr ⟨x,hx,rfl⟩))
      (Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨y,hy,rfl⟩))

/-- A coordinate quotient map, formed by descending the outer two summands. -/
def threeCoordinateQuotientSum (P : X →ₗ[ℂ] L) (H : C →ₗ[ℂ] L)
    (Q : Y →ₗ[ℂ] L) (N : Submodule ℂ X) (M : Submodule ℂ Y) :
    (X ⧸ N) × (C × (Y ⧸ M)) →ₗ[ℂ] L ⧸ (N.map P ⊔ M.map Q) :=
  (N.liftQ ((N.map P ⊔ M.map Q).mkQ.comp P) (by
    intro x hx
    change (N.map P ⊔ M.map Q).mkQ (P x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.mem_sup_left (Submodule.mem_map.mpr ⟨x,hx,rfl⟩))).coprod
    (((N.map P ⊔ M.map Q).mkQ.comp H).coprod
      (M.liftQ ((N.map P ⊔ M.map Q).mkQ.comp Q) (by
        intro y hy
        change (N.map P ⊔ M.map Q).mkQ (Q y) = 0
        apply (Submodule.Quotient.mk_eq_zero _).mpr
        exact Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨y,hy,rfl⟩))))

@[simp] theorem threeCoordinateQuotientSum_mk (P : X →ₗ[ℂ] L) (H : C →ₗ[ℂ] L)
    (Q : Y →ₗ[ℂ] L) (N : Submodule ℂ X) (M : Submodule ℂ Y)
    (x : X) (c : C) (y : Y) :
    threeCoordinateQuotientSum P H Q N M (N.mkQ x, (c, M.mkQ y)) =
      (N.map P ⊔ M.map Q).mkQ (P x + (H c + Q y)) := by
  simp only [threeCoordinateQuotientSum, LinearMap.coprod_apply,
    Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply, map_add]

/-- A bijective three-coordinate sum remains bijective after separately
quotienting the two outer coordinate ideals. -/
theorem threeCoordinateQuotientSum_bijective (P : X →ₗ[ℂ] L) (H : C →ₗ[ℂ] L)
    (Q : Y →ₗ[ℂ] L) (N : Submodule ℂ X) (M : Submodule ℂ Y)
    (hbij : Function.Bijective (P.coprod (H.coprod Q))) :
    Function.Bijective (threeCoordinateQuotientSum P H Q N M) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    rintro ⟨x,c,y⟩ hz
    induction x using Submodule.Quotient.induction_on with | _ x =>
    induction y using Submodule.Quotient.induction_on with | _ y =>
    change threeCoordinateQuotientSum P H Q N M (N.mkQ x, (c, M.mkQ y)) = 0 at hz
    rw [threeCoordinateQuotientSum_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨hx,hc,hy⟩ := (threeCoordinateIdeal_mem_iff P H Q N M hbij.1 x c y).mp hz
    change (N.mkQ x, (c, M.mkQ y)) = 0
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hx, hc, (Submodule.Quotient.mk_eq_zero _).mpr hy]
    rfl
  · intro z
    induction z using Submodule.Quotient.induction_on with | _ z =>
    obtain ⟨⟨x,c,y⟩, heq⟩ := hbij.2 z
    refine ⟨(N.mkQ x, (c, M.mkQ y)), ?_⟩
    rw [threeCoordinateQuotientSum_mk]
    exact congrArg (N.map P ⊔ M.map Q).mkQ heq
end CoordinateIdeals
end LieAlgebrasAndRepresentations.Serre


namespace LieAlgebrasAndRepresentations.Serre
universe u v
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

/-! The pre-Serre quotient imposes only the four Cartan and mixed relations. -/
namespace PreSerre

def relationSet : Set (Free ι) :=
  Set.range (CartanMatrix.Relations.HH ℂ) ∪ Set.range (CartanMatrix.Relations.EF ℂ) ∪
    Set.range (CartanMatrix.Relations.HE ℂ A) ∪ Set.range (CartanMatrix.Relations.HF ℂ A)

def ideal : LieIdeal ℂ (Free ι) := LieSubmodule.lieSpan ℂ _ (relationSet A)
abbrev Algebra := Free ι ⧸ ideal A

def projection : Free ι →ₗ⁅ℂ⁆ Algebra A :=
  { (ideal A).toSubmodule.mkQ with map_lie' := by intros; rfl }

def e (i : ι) : Algebra A := projection A (FreeLieAlgebra.of ℂ (.E i))
def f (i : ι) : Algebra A := projection A (FreeLieAlgebra.of ℂ (.F i))
def h (i : ι) : Algebra A := projection A (FreeLieAlgebra.of ℂ (.H i))

@[simp] theorem projection_eq_zero (x : Free ι) :
    projection A x = 0 ↔ x ∈ ideal A := LieSubmodule.Quotient.mk_eq_zero'
theorem projection_surjective : Function.Surjective (projection A) := Quot.mk_surjective

private theorem relation_zero {x : Free ι} (hx : x ∈ relationSet A) :
    projection A x = 0 :=
  (projection_eq_zero A x).mpr (LieSubmodule.subset_lieSpan hx)

theorem hh (i j : ι) : ⁅h A i, h A j⁆ = 0 := by
  have hr := relation_zero A (x := CartanMatrix.Relations.HH ℂ (i,j)) (by
    simp only [relationSet, Set.mem_union]
    exact Or.inl (Or.inl (Or.inl ⟨(i,j), rfl⟩)))
  simpa only [CartanMatrix.Relations.HH, Function.uncurry_apply_pair, Function.comp_apply, LieHom.map_lie, h] using hr

theorem he (i j : ι) : ⁅h A i, e A j⁆ = A i j • e A j := by
  have hr := relation_zero A (x := CartanMatrix.Relations.HE ℂ A (i,j)) (by
    simp only [relationSet, Set.mem_union]
    exact Or.inl (Or.inr ⟨(i,j), rfl⟩))
  apply sub_eq_zero.mp
  simpa only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply,
    map_sub, LieHom.map_lie, map_zsmul, h, e] using hr

theorem hf (i j : ι) : ⁅h A i, f A j⁆ = -(A i j • f A j) := by
  have hr := relation_zero A (x := CartanMatrix.Relations.HF ℂ A (i,j)) (by
    simp only [relationSet, Set.mem_union]
    exact Or.inr ⟨(i,j), rfl⟩)
  apply eq_neg_of_add_eq_zero_left
  simpa only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply,
    map_add, LieHom.map_lie, map_zsmul, h, f] using hr

theorem ef (i j : ι) : ⁅e A i, f A j⁆ = if i = j then h A i else 0 := by
  have hr := relation_zero A (x := CartanMatrix.Relations.EF ℂ (i,j)) (by
    simp only [relationSet, Set.mem_union]
    exact Or.inl (Or.inl (Or.inr ⟨(i,j), rfl⟩)))
  by_cases hij : i = j
  · subst j
    simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply, ite_true,
      map_sub, LieHom.map_lie] at hr
    simpa only [ite_true, e, f, h] using sub_eq_zero.mp hr
  · simpa only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply, ite_eq_right hij,
      LieHom.map_lie, e, f] using hr

theorem ideal_le_ker {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (E F H : ι → L)
    (hHH : ∀ i j, ⁅H i,H j⁆ = 0)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i,F j⁆ = -(A i j • F j))
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0) :
    ideal A ≤ (freeAssignment E F H).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  intro x hx
  change freeAssignment E F H x = 0
  simp only [relationSet, Set.mem_union] at hx
  rcases hx with (((hx | hx) | hx) | hx)
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    simpa only [CartanMatrix.Relations.HH, Function.uncurry_apply_pair, Function.comp_apply, LieHom.map_lie, freeAssignment_h] using hHH i j
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    by_cases hij : i = j
    · subst j
      simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply,
        ite_true, map_sub, LieHom.map_lie,
        freeAssignment_e, freeAssignment_f, freeAssignment_h]
      exact sub_eq_zero.mpr (by simpa using hEF i i)
    · simp only [CartanMatrix.Relations.EF, Function.uncurry_apply_pair, Function.comp_apply,
        ite_eq_right hij, LieHom.map_lie, freeAssignment_e, freeAssignment_f]
      simpa only [ite_eq_right hij] using hEF i j
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    simp only [CartanMatrix.Relations.HE, Function.uncurry_apply_pair, Function.comp_apply, map_sub, LieHom.map_lie, map_zsmul, freeAssignment_h,
      freeAssignment_e, hHE i j, sub_self]
  · rcases hx with ⟨⟨i,j⟩, rfl⟩
    simp only [CartanMatrix.Relations.HF, Function.uncurry_apply_pair, Function.comp_apply, map_add, LieHom.map_lie, map_zsmul, freeAssignment_h,
      freeAssignment_f, hHF i j, neg_add_cancel]

def lift {L : Type*} [LieRing L] [LieAlgebra ℂ L] (E F H : ι → L)
    (hHH : ∀ i j, ⁅H i,H j⁆ = 0)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i,F j⁆ = -(A i j • F j))
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0) :
    Algebra A →ₗ⁅ℂ⁆ L :=
  quotientLift _ (freeAssignment E F H) (ideal_le_ker A E F H hHH hHE hHF hEF)

@[simp] theorem lift_e {L : Type*} [LieRing L] [LieAlgebra ℂ L] (E F H : ι → L)
    (hHH : ∀ i j, ⁅H i,H j⁆ = 0)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i,F j⁆ = -(A i j • F j))
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0) (i : ι) :
    lift A E F H hHH hHE hHF hEF (e A i) = E i := freeAssignment_e E F H i
@[simp] theorem lift_f {L : Type*} [LieRing L] [LieAlgebra ℂ L] (E F H : ι → L)
    (hHH : ∀ i j, ⁅H i,H j⁆ = 0)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i,F j⁆ = -(A i j • F j))
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0) (i : ι) :
    lift A E F H hHH hHE hHF hEF (f A i) = F i := freeAssignment_f E F H i
@[simp] theorem lift_h {L : Type*} [LieRing L] [LieAlgebra ℂ L] (E F H : ι → L)
    (hHH : ∀ i j, ⁅H i,H j⁆ = 0)
    (hHE : ∀ i j, ⁅H i,E j⁆ = A i j • E j)
    (hHF : ∀ i j, ⁅H i,F j⁆ = -(A i j • F j))
    (hEF : ∀ i j, ⁅E i,F j⁆ = if i = j then H i else 0) (i : ι) :
    lift A E F H hHH hHE hHF hEF (h A i) = H i := freeAssignment_h E F H i

@[ext] theorem hom_ext {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    {φ ψ : Algebra A →ₗ⁅ℂ⁆ L} (heq : ∀ i, φ (e A i) = ψ (e A i))
    (hfeq : ∀ i, φ (f A i) = ψ (f A i)) (hheq : ∀ i, φ (h A i) = ψ (h A i)) : φ = ψ := by
  have hc : φ.comp (projection A) = ψ.comp (projection A) := by
    apply FreeLieAlgebra.hom_ext
    intro x
    cases x with
    | E i => exact heq i
    | F i => exact hfeq i
    | H i => exact hheq i
  ext x
  obtain ⟨y, rfl⟩ := projection_surjective A x
  exact LieHom.congr_fun hc y

theorem generators_generate (K : LieSubalgebra ℂ (Algebra A))
    (hE : ∀ i, e A i ∈ K) (hF : ∀ i, f A i ∈ K) (hH : ∀ i, h A i ∈ K) : K = ⊤ := by
  have hfree : (⊤ : LieSubalgebra ℂ (Free ι)) ≤ K.comap (projection A) := by
    rw [← free_generated (CartanMatrix.Generators ι)]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro x ⟨g,rfl⟩
    cases g with
    | E i => exact hE i
    | F i => exact hF i
    | H i => exact hH i
  apply top_unique
  intro x _
  obtain ⟨y,rfl⟩ := projection_surjective A x
  exact hfree (LieSubalgebra.mem_top y)


def negativeLift : SideFree ι →ₗ⁅ℂ⁆ Algebra A := FreeLieAlgebra.lift ℂ (f A)
def positiveLift : SideFree ι →ₗ⁅ℂ⁆ Algebra A := FreeLieAlgebra.lift ℂ (e A)
def cartanMap : (ι →₀ ℂ) →ₗ[ℂ] Algebra A := Finsupp.linearCombination ℂ (h A)
def sum : SideFree ι × ((ι →₀ ℂ) × SideFree ι) →ₗ[ℂ] Algebra A :=
  (negativeLift A).toLinearMap.coprod ((cartanMap A).coprod (positiveLift A).toLinearMap)

/-- The canonical projection imposing the remaining two families of relations. -/
def toSerre : Algebra A →ₗ⁅ℂ⁆ Serre.Algebra A :=
  lift A (Serre.e A) (Serre.f A) (Serre.h A)
    (Serre.hh A) (Serre.he A) (Serre.hf A) (Serre.ef A)
@[simp] theorem toSerre_e (i : ι) : toSerre A (e A i) = Serre.e A i :=
  lift_e _ _ _ _ _ _ _ _ _
@[simp] theorem toSerre_f (i : ι) : toSerre A (f A i) = Serre.f A i :=
  lift_f _ _ _ _ _ _ _ _ _
@[simp] theorem toSerre_h (i : ι) : toSerre A (h A i) = Serre.h A i :=
  lift_h _ _ _ _ _ _ _ _ _
@[simp] theorem toSerre_projection (x : Free ι) :
    toSerre A (projection A x) = Serre.projection A x := by
  have hm : (toSerre A).comp (projection A) = Serre.projection A := by
    apply FreeLieAlgebra.hom_ext
    intro g
    cases g with
    | E i => exact toSerre_e A i
    | F i => exact toSerre_f A i
    | H i => exact toSerre_h A i
  exact LieHom.congr_fun hm x

theorem toSerre_surjective : Function.Surjective (toSerre A) := by
  intro x
  obtain ⟨y,rfl⟩ := Serre.projection_surjective A x
  exact ⟨projection A y, toSerre_projection A y⟩


def positive : LieSubalgebra ℂ (Algebra A) := LieSubalgebra.lieSpan ℂ _ (Set.range (e A))
def negative : LieSubalgebra ℂ (Algebra A) := LieSubalgebra.lieSpan ℂ _ (Set.range (f A))
def cartan : Submodule ℂ (Algebra A) := Submodule.span ℂ (Set.range (h A))
@[simp] theorem e_mem_positive (i : ι) : e A i ∈ positive A :=
  LieSubalgebra.subset_lieSpan (Set.mem_range_self i)
@[simp] theorem f_mem_negative (i : ι) : f A i ∈ negative A :=
  LieSubalgebra.subset_lieSpan (Set.mem_range_self i)
@[simp] theorem h_mem_cartan (i : ι) : h A i ∈ cartan A :=
  Submodule.subset_span (Set.mem_range_self i)

theorem h_bracket_positive (i : ι) {x : Algebra A} (hx : x ∈ positive A) :
    ⁅h A i,x⁆ ∈ positive A := by
  apply bracket_lieSpan_mem (positive A) (Set.range (e A)) (h A i) _ _ hx
  · rintro x ⟨j,rfl⟩; exact e_mem_positive A j
  · rintro x ⟨j,rfl⟩
    rw [he]
    exact (positive A).toSubmodule.toAddSubgroup.zsmul_mem (e_mem_positive A j) _

theorem h_bracket_negative (i : ι) {x : Algebra A} (hx : x ∈ negative A) :
    ⁅h A i,x⁆ ∈ negative A := by
  apply bracket_lieSpan_mem (negative A) (Set.range (f A)) (h A i) _ _ hx
  · rintro x ⟨j,rfl⟩; exact f_mem_negative A j
  · rintro x ⟨j,rfl⟩
    rw [hf]
    exact (negative A).neg_mem ((negative A).toSubmodule.toAddSubgroup.zsmul_mem (f_mem_negative A j) _)

theorem cartan_bracket_positive {x y : Algebra A} (hx : x ∈ cartan A)
    (hy : y ∈ positive A) : ⁅x,y⁆ ∈ positive A :=
  bracket_span_mem (positive A) (h A) (h_bracket_positive A) hx hy

theorem cartan_bracket_negative {x y : Algebra A} (hx : x ∈ cartan A)
    (hy : y ∈ negative A) : ⁅x,y⁆ ∈ negative A :=
  bracket_span_mem (negative A) (h A) (h_bracket_negative A) hx hy

theorem cartan_bracket_cartan {x y : Algebra A} (hx : x ∈ cartan A)
    (hy : y ∈ cartan A) : ⁅x,y⁆ = 0 := bracket_span_eq_zero (h A) (hh A) hx hy

/-- The negative Borel, constructed as the actual sum of the two subspaces. -/
def negativeBorel : LieSubalgebra ℂ (Algebra A) :=
  sumWithAbelian (negative A) (cartan A)
    (fun _ hx _ hy => cartan_bracket_cartan A hx hy)
    (fun _ hx _ hy => cartan_bracket_negative A hx hy)

/-- The positive Borel, constructed as the actual sum of the two subspaces. -/
def positiveBorel : LieSubalgebra ℂ (Algebra A) :=
  sumWithAbelian (positive A) (cartan A)
    (fun _ hx _ hy => cartan_bracket_cartan A hx hy)
    (fun _ hx _ hy => cartan_bracket_positive A hx hy)

theorem e_bracket_negative (i : ι) {x : Algebra A} (hx : x ∈ negative A) :
    ⁅e A i,x⁆ ∈ negativeBorel A := by
  apply bracket_lieSpan_mem (negativeBorel A) (Set.range (f A)) (e A i) _ _ hx
  · rintro x ⟨j,rfl⟩
    exact Submodule.mem_sup_left (f_mem_negative A j)
  · rintro x ⟨j,rfl⟩
    rw [ef]
    split_ifs
    · exact Submodule.mem_sup_right (h_mem_cartan A i)
    · exact (negativeBorel A).zero_mem

theorem f_bracket_positive (i : ι) {x : Algebra A} (hx : x ∈ positive A) :
    ⁅f A i,x⁆ ∈ positiveBorel A := by
  apply bracket_lieSpan_mem (positiveBorel A) (Set.range (e A)) (f A i) _ _ hx
  · rintro x ⟨j,rfl⟩
    exact Submodule.mem_sup_left (e_mem_positive A j)
  · rintro x ⟨j,rfl⟩
    rw [← lie_skew, ef]
    split_ifs
    · exact (positiveBorel A).neg_mem (Submodule.mem_sup_right (h_mem_cartan A j))
    · simpa only [neg_zero] using (positiveBorel A).zero_mem


omit [DecidableEq ι] in
/-- A bracket condition with linear target extends across a linear span. -/
theorem bracket_span_right_mem {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (S : Submodule ℂ L) (H : ι → L) (a : L)
    (ha : ∀ i, ⁅a,H i⁆ ∈ S) {x : L}
    (hx : x ∈ Submodule.span ℂ (Set.range H)) : ⁅a,x⁆ ∈ S := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i,rfl⟩ := hx; exact ha i
  | zero => simpa only [lie_zero] using S.zero_mem
  | add x y _ _ hx hy => simpa only [lie_add] using S.add_mem hx hy
  | smul r x _ hx => simpa only [lie_smul] using S.smul_mem r hx

/-- A bracket condition with linear target extends across a sum of subspaces. -/
theorem bracket_sup_right_mem {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (S T U : Submodule ℂ L) (a : L)
    (hT : ∀ x ∈ T, ⁅a,x⁆ ∈ S) (hU : ∀ x ∈ U, ⁅a,x⁆ ∈ S)
    {x : L} (hx : x ∈ T ⊔ U) : ⁅a,x⁆ ∈ S := by
  obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  rw [lie_add]
  exact S.add_mem (hT y hy) (hU z hz)

theorem e_bracket_cartan (i : ι) {x : Algebra A} (hx : x ∈ cartan A) :
    ⁅e A i,x⁆ ∈ positive A := by
  apply bracket_span_right_mem (positive A).toSubmodule (h A) (e A i) _ hx
  intro j
  rw [← lie_skew, he]
  exact (positive A).neg_mem
    ((positive A).toSubmodule.toAddSubgroup.zsmul_mem (e_mem_positive A i) _)

theorem f_bracket_cartan (i : ι) {x : Algebra A} (hx : x ∈ cartan A) :
    ⁅f A i,x⁆ ∈ negative A := by
  apply bracket_span_right_mem (negative A).toSubmodule (h A) (f A i) _ hx
  intro j
  rw [← lie_skew, hf, neg_neg]
  exact (negative A).toSubmodule.toAddSubgroup.zsmul_mem (f_mem_negative A i) _

/-- The vector subspace of sums of negative, Cartan, and positive elements. -/
def triangularSpan : Submodule ℂ (Algebra A) :=
  (negative A).toSubmodule ⊔ (cartan A ⊔ (positive A).toSubmodule)

theorem negative_le_triangularSpan : (negative A).toSubmodule ≤ triangularSpan A := le_sup_left
theorem cartan_le_triangularSpan : cartan A ≤ triangularSpan A := le_sup_right.trans' le_sup_left
theorem positive_le_triangularSpan : (positive A).toSubmodule ≤ triangularSpan A :=
  le_sup_right.trans' le_sup_right

theorem negativeBorel_le_triangularSpan : (negativeBorel A).toSubmodule ≤ triangularSpan A :=
  sup_le (negative_le_triangularSpan A) (cartan_le_triangularSpan A)
theorem positiveBorel_le_triangularSpan : (positiveBorel A).toSubmodule ≤ triangularSpan A :=
  sup_le (positive_le_triangularSpan A) (cartan_le_triangularSpan A)

theorem e_mem_triangularStabilizer (i : ι) : e A i ∈ adjointStabilizer (triangularSpan A) := by
  intro x hx
  apply bracket_sup_right_mem (triangularSpan A) (negative A).toSubmodule
    (cartan A ⊔ (positive A).toSubmodule) (e A i) _ _ hx
  · intro y hy
    exact negativeBorel_le_triangularSpan A (e_bracket_negative A i hy)
  · intro y hy
    apply bracket_sup_right_mem (triangularSpan A) (cartan A) (positive A).toSubmodule
      (e A i) _ _ hy
    · intro z hz
      exact positive_le_triangularSpan A (e_bracket_cartan A i hz)
    · intro z hz
      exact positive_le_triangularSpan A ((positive A).lie_mem (e_mem_positive A i) hz)

theorem f_mem_triangularStabilizer (i : ι) : f A i ∈ adjointStabilizer (triangularSpan A) := by
  intro x hx
  apply bracket_sup_right_mem (triangularSpan A) (negative A).toSubmodule
    (cartan A ⊔ (positive A).toSubmodule) (f A i) _ _ hx
  · intro y hy
    exact negative_le_triangularSpan A ((negative A).lie_mem (f_mem_negative A i) hy)
  · intro y hy
    apply bracket_sup_right_mem (triangularSpan A) (cartan A) (positive A).toSubmodule
      (f A i) _ _ hy
    · intro z hz
      exact negative_le_triangularSpan A (f_bracket_cartan A i hz)
    · intro z hz
      exact positiveBorel_le_triangularSpan A (f_bracket_positive A i hz)

theorem h_mem_triangularStabilizer (i : ι) : h A i ∈ adjointStabilizer (triangularSpan A) := by
  intro x hx
  apply bracket_sup_right_mem (triangularSpan A) (negative A).toSubmodule
    (cartan A ⊔ (positive A).toSubmodule) (h A i) _ _ hx
  · intro y hy
    exact negative_le_triangularSpan A (h_bracket_negative A i hy)
  · intro y hy
    apply bracket_sup_right_mem (triangularSpan A) (cartan A) (positive A).toSubmodule
      (h A i) _ _ hy
    · intro z hz
      rw [cartan_bracket_cartan A (h_mem_cartan A i) hz]
      exact (triangularSpan A).zero_mem
    · intro z hz
      exact positive_le_triangularSpan A (h_bracket_positive A i hz)

/-- Every Lie word is a sum of a negative word, a Cartan element and a positive word.
This conclusion holds for every integer matrix, without any nonvanishing assumption. -/
theorem triangularSpan_eq_top : triangularSpan A = ⊤ := by
  have hstab : adjointStabilizer (triangularSpan A) = ⊤ :=
    generators_generate A _ (e_mem_triangularStabilizer A)
      (f_mem_triangularStabilizer A) (h_mem_triangularStabilizer A)
  let K : LieSubalgebra ℂ (Algebra A) :=
    { triangularSpan A with
      lie_mem' := by
        intro x y hx hy
        have hx' : x ∈ adjointStabilizer (triangularSpan A) := by rw [hstab]; trivial
        exact hx' y hy }
  have hK : K = ⊤ := generators_generate A K
    (fun i => positive_le_triangularSpan A (e_mem_positive A i))
    (fun i => negative_le_triangularSpan A (f_mem_negative A i))
    (fun i => cartan_le_triangularSpan A (h_mem_cartan A i))
  exact congrArg LieSubalgebra.toSubmodule hK


theorem negativeLift_range : (negativeLift A).range = negative A := free_lift_range (f A)
theorem positiveLift_range : (positiveLift A).range = positive A := free_lift_range (e A)

theorem sum_surjective : Function.Surjective (sum A) := by
  apply LinearMap.range_eq_top.mp
  rw [sum, LinearMap.range_coprod, LinearMap.range_coprod, cartanMap,
    Finsupp.range_linearCombination]
  change (negativeLift A).range.toSubmodule ⊔
    (cartan A ⊔ (positiveLift A).range.toSubmodule) = ⊤
  rw [negativeLift_range, positiveLift_range]
  exact triangularSpan_eq_top A


/-- The sign symmetry exchanges the two free sides before imposing Serre relations. -/
def flip : Algebra A →ₗ⁅ℂ⁆ Algebra A :=
  lift A (f A) (e A) (fun i => -h A i)
    (by intro i j; rw [neg_lie, lie_neg, hh, neg_zero, neg_zero])
    (by intro i j; rw [neg_lie, hf, neg_neg])
    (by intro i j; rw [neg_lie, he])
    (by
      intro i j
      rw [← lie_skew, ef]
      by_cases hij : i = j
      · subst j; simp only [ite_true]
      · simp only [ite_eq_right hij, ite_eq_right (Ne.symm hij), neg_zero])

@[simp] theorem flip_e (i : ι) : flip A (e A i) = f A i := lift_e ..
@[simp] theorem flip_f (i : ι) : flip A (f A i) = e A i := lift_f ..
@[simp] theorem flip_h (i : ι) : flip A (h A i) = -h A i := lift_h ..

@[simp] theorem flip_positiveLift (x : SideFree ι) :
    flip A (positiveLift A x) = negativeLift A x := by
  have hm : (flip A).comp (positiveLift A) = negativeLift A := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change flip A (FreeLieAlgebra.lift ℂ (e A) (FreeLieAlgebra.of ℂ i)) =
      FreeLieAlgebra.lift ℂ (f A) (FreeLieAlgebra.of ℂ i)
    simp only [FreeLieAlgebra.lift_of_apply, flip_e]
  exact LieHom.congr_fun hm x

@[simp] theorem flip_negativeLift (x : SideFree ι) :
    flip A (negativeLift A x) = positiveLift A x := by
  have hm : (flip A).comp (negativeLift A) = positiveLift A := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change flip A (FreeLieAlgebra.lift ℂ (f A) (FreeLieAlgebra.of ℂ i)) =
      FreeLieAlgebra.lift ℂ (e A) (FreeLieAlgebra.of ℂ i)
    simp only [FreeLieAlgebra.lift_of_apply, flip_f]
  exact LieHom.congr_fun hm x

end PreSerre
end LieAlgebrasAndRepresentations.Serre



open LieAlgebrasAndRepresentations
namespace LieAlgebrasAndRepresentations.Serre
universe u
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

/-- The coordinate sum before identifying its three factors with their images. -/
def sideTriangularSum :
    Side A × ((ι →₀ ℂ) × Side A) →ₗ[ℂ] Algebra A :=
  (negativeMap A).toLinearMap.coprod
    ((Finsupp.linearCombination ℂ (h A)).coprod (positiveMap A).toLinearMap)

theorem negativeMap_mem (x : Side A) : negativeMap A x ∈ negative A := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  change negativeLift A x ∈ negative A
  rw [← negativeLift_range A]
  exact ⟨x, rfl⟩

theorem positiveMap_mem (x : Side A) : positiveMap A x ∈ positive A := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  change positiveLift A x ∈ positive A
  rw [← positiveLift_range A]
  exact ⟨x, rfl⟩

def negativeCoordinates : Side A →ₗ[ℂ] negative A :=
  (negativeMap A).toLinearMap.codRestrict (negative A).toSubmodule (negativeMap_mem A)

def positiveCoordinates : Side A →ₗ[ℂ] positive A :=
  (positiveMap A).toLinearMap.codRestrict (positive A).toSubmodule (positiveMap_mem A)

def cartanCoordinates : (ι →₀ ℂ) →ₗ[ℂ] cartan A :=
  (Finsupp.linearCombination ℂ (h A)).codRestrict (cartan A) (by
    intro x
    change Finsupp.linearCombination ℂ (h A) x ∈ Submodule.span ℂ (Set.range (h A))
    rw [← Finsupp.range_linearCombination]
    exact ⟨x, rfl⟩)

theorem negativeCoordinates_surjective : Function.Surjective (negativeCoordinates A) := by
  intro x
  obtain ⟨y, hy⟩ : ∃ y, negativeLift A y = (x : Algebra A) := by
    apply (LieHom.mem_range (negativeLift A) _).mp
    rw [negativeLift_range A]
    exact x.property
  refine ⟨LieSubmodule.Quotient.mk y, ?_⟩
  apply Subtype.ext
  exact hy

theorem positiveCoordinates_surjective : Function.Surjective (positiveCoordinates A) := by
  intro x
  obtain ⟨y, hy⟩ : ∃ y, positiveLift A y = (x : Algebra A) := by
    apply (LieHom.mem_range (positiveLift A) _).mp
    rw [positiveLift_range A]
    exact x.property
  refine ⟨LieSubmodule.Quotient.mk y, ?_⟩
  apply Subtype.ext
  exact hy

theorem cartanCoordinates_surjective : Function.Surjective (cartanCoordinates A) := by
  intro x
  obtain ⟨y, hy⟩ : ∃ y, Finsupp.linearCombination ℂ (h A) y = (x : Algebra A) := by
    apply (LinearMap.mem_range).mp
    rw [Finsupp.range_linearCombination]
    exact x.property
  exact ⟨y, Subtype.ext hy⟩

theorem triangular_of_sideTriangularSum_injective
    (hinj : Function.Injective (sideTriangularSum A)) : Triangular A := by
  have hn : Function.Injective (negativeMap A) := by
    intro x y hxy
    have hh : sideTriangularSum A (x, (0, 0)) = sideTriangularSum A (y, (0, 0)) := by
      simpa [sideTriangularSum] using hxy
    exact congrArg Prod.fst (hinj hh)
  have hp : Function.Injective (positiveMap A) := by
    intro x y hxy
    have hh : sideTriangularSum A (0, (0, x)) = sideTriangularSum A (0, (0, y)) := by
      simpa [sideTriangularSum] using hxy
    exact congrArg (fun z => z.2.2) (hinj hh)
  have hc : Function.Injective (cartanCoordinates A) := by
    intro x y hxy
    have hh : sideTriangularSum A (0, (x, 0)) = sideTriangularSum A (0, (y, 0)) := by
      simpa [sideTriangularSum, cartanCoordinates] using congrArg Subtype.val hxy
    exact congrArg (fun z => z.2.1) (hinj hh)
  let en : Side A ≃ₗ[ℂ] negative A := LinearEquiv.ofBijective (negativeCoordinates A)
    ⟨fun _ _ hxy => hn (congrArg Subtype.val hxy), negativeCoordinates_surjective A⟩
  let ep : Side A ≃ₗ[ℂ] positive A := LinearEquiv.ofBijective (positiveCoordinates A)
    ⟨fun _ _ hxy => hp (congrArg Subtype.val hxy), positiveCoordinates_surjective A⟩
  let ec : (ι →₀ ℂ) ≃ₗ[ℂ] cartan A := LinearEquiv.ofBijective (cartanCoordinates A)
    ⟨hc, cartanCoordinates_surjective A⟩
  let E := en.prodCongr (ec.prodCongr ep)
  have hsum (x : Side A × ((ι →₀ ℂ) × Side A)) :
      triangularSum A (E x) = sideTriangularSum A x := rfl
  have ht : Function.Injective (triangularSum A) := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := E.surjective x
    obtain ⟨y', rfl⟩ := E.surjective y
    exact congrArg E (hinj (by simpa only [hsum] using hxy))
  have hnker : (negativeLift A).ker = sideIdeal A := by
    apply le_antisymm
    · intro x hx
      apply (LieSubmodule.Quotient.mk_eq_zero (sideIdeal A)).mp
      apply hn
      change negativeLift A x = 0
      exact hx
    · exact sideIdeal_le_negative_ker A
  have hpker : (positiveLift A).ker = sideIdeal A := by
    apply le_antisymm
    · intro x hx
      apply (LieSubmodule.Quotient.mk_eq_zero (sideIdeal A)).mp
      apply hp
      change positiveLift A x = 0
      exact hx
    · exact sideIdeal_le_positive_ker A
  refine ⟨⟨ht, triangularSum_surjective A⟩, ?_, ⟨hnker, negativeLift_range A⟩,
    ⟨hpker, positiveLift_range A⟩, ?_⟩
  · refine ⟨Module.Basis.ofRepr ec.symm, ?_⟩
    intro i
    change Finsupp.linearCombination ℂ (h A) (Finsupp.single i 1) = h A i
    simp
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      apply sideGenerator_ne_zero A i
      apply hp
      simpa [positiveMap, sideGenerator, positiveLift, e] using hz
    · intro hz
      apply sideGenerator_ne_zero A i
      apply hn
      simpa [negativeMap, sideGenerator, negativeLift, f] using hz
    · intro hz
      have hs : Finsupp.single i (1 : ℂ) = 0 := by
        apply hc
        apply Subtype.ext
        simpa [cartanCoordinates] using hz
      have : (1 : ℂ) = 0 := by simpa using congrArg (fun v => v i) hs
      exact one_ne_zero this

end LieAlgebrasAndRepresentations.Serre



namespace LieAlgebrasAndRepresentations.Serre
universe u
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

/-- A Lie ideal's actual quotient projection, as a Lie algebra homomorphism. -/
def idealProjection {L : Type*} [LieRing L] [LieAlgebra ℂ L] (I : LieIdeal ℂ L) :
    L →ₗ⁅ℂ⁆ L ⧸ I :=
  { I.toSubmodule.mkQ with map_lie' := by intros; rfl }

@[simp] theorem idealProjection_eq_zero {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    (I : LieIdeal ℂ L) (x : L) : idealProjection I x = 0 ↔ x ∈ I :=
  LieSubmodule.Quotient.mk_eq_zero'

namespace PreSerre

def serreIdeal : LieIdeal ℂ (Algebra A) := LieSubmodule.lieSpan ℂ _
  ({x | ∃ i j, i ≠ j ∧ x = serreVector A (f A) i j} ∪
   {x | ∃ i j, i ≠ j ∧ x = serreVector A (e A) i j})

theorem serreIdeal_le_ker (ha : ∀ i j, i ≠ j → A i j ≤ 0) :
    serreIdeal A ≤ (toSerre A).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  rintro x (hx | hx)
  · obtain ⟨i,j,hij,rfl⟩ := hx
    change toSerre A (iterBracket (f A i) (1-A i j).toNat (f A j)) = 0
    rw [map_iterBracket, toSerre_f, toSerre_f]
    exact (Serre.relations_spec A ha).2.2.2.2.2 i j hij
  · obtain ⟨i,j,hij,rfl⟩ := hx
    change toSerre A (iterBracket (e A i) (1-A i j).toNat (e A j)) = 0
    rw [map_iterBracket, toSerre_e, toSerre_e]
    exact (Serre.relations_spec A ha).2.2.2.2.1 i j hij

/-- Imposing the remaining Serre ideal gives the displayed full presentation. -/
theorem quotient_relations : RelationsHold A
    (fun i => idealProjection (serreIdeal A) (e A i))
    (fun i => idealProjection (serreIdeal A) (f A i))
    (fun i => idealProjection (serreIdeal A) (h A i)) := by
  let q := idealProjection (serreIdeal A)
  change RelationsHold A (fun i => q (e A i)) (fun i => q (f A i)) (fun i => q (h A i))
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i j
    rw [← LieHom.map_lie, hh, map_zero]
  · intro i j
    rw [← LieHom.map_lie, he, map_zsmul]
  · intro i j
    rw [← LieHom.map_lie, hf, map_neg, map_zsmul]
  · intro i j
    rw [← LieHom.map_lie, ef]
    split_ifs <;> simp
  · intro i j hij
    rw [← map_iterBracket]
    apply (idealProjection_eq_zero _ _).mpr
    exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,hij,rfl⟩)
  · intro i j hij
    rw [← map_iterBracket]
    apply (idealProjection_eq_zero _ _).mpr
    exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,hij,rfl⟩)

/-- Exact kernel of the second-stage projection, proved by both universal properties. -/
theorem toSerre_ker (ha : ∀ i j, i ≠ j → A i j ≤ 0) :
    (toSerre A).ker = serreIdeal A := by
  apply le_antisymm
  · let q := idealProjection (serreIdeal A)
    let r : Serre.Algebra A →ₗ⁅ℂ⁆ Algebra A ⧸ serreIdeal A :=
      Serre.lift A ha (fun i => q (e A i)) (fun i => q (f A i)) (fun i => q (h A i))
        (quotient_relations A)
    have hr : r.comp (toSerre A) = q := by
      apply hom_ext A
      · intro i
        change r (toSerre A (e A i)) = q (e A i)
        rw [toSerre_e]
        exact Serre.lift_e _ _ _ _ _ _ _
      · intro i
        change r (toSerre A (f A i)) = q (f A i)
        rw [toSerre_f]
        exact Serre.lift_f _ _ _ _ _ _ _
      · intro i
        change r (toSerre A (h A i)) = q (h A i)
        rw [toSerre_h]
        exact Serre.lift_h _ _ _ _ _ _ _
    intro x hx
    apply (idealProjection_eq_zero _ _).mp
    change q x = 0
    rw [← LieHom.congr_fun hr x]
    change r (toSerre A x) = 0
    rw [show toSerre A x = 0 from hx, map_zero]
  · exact serreIdeal_le_ker A ha


/-- Stability identifies the full extra ideal with the images of the two
one-sided ideals, without requiring faithfulness of the pre-Serre coordinates. -/
theorem serreIdeal_toSubmodule (hA : CartanConditions A) :
    (serreIdeal A).toSubmodule =
      (sideIdeal A).toSubmodule.map (negativeLift A).toLinearMap ⊔
      (sideIdeal A).toSubmodule.map (positiveLift A).toLinearMap := by
  rw [serreIdeal, fullSerreIdeal_eq A (e A) (f A) (h A) hA (he A) (hf A) (ef A)
    (generators_generate A)]
  rw [negativeLift, positiveLift, sideIdeal_map_eq_serreWordSpan A hA.2.1,
    sideIdeal_map_eq_serreWordSpan A hA.2.1]

end PreSerre
end LieAlgebrasAndRepresentations.Serre



namespace LieAlgebrasAndRepresentations.Serre
universe u
variable {ι : Type u}
attribute [local instance 100] LieRing.ofAssociativeRing

def freeLieEmbedding : FreeLieAlgebra ℂ ι →ₗ⁅ℂ⁆ FreeAlgebra ℂ ι :=
  FreeLieAlgebra.lift ℂ (FreeAlgebra.ι ℂ)

theorem freeLieEmbedding_injective : Function.Injective (freeLieEmbedding (ι := ι)) := by
  let : LinearOrder (Module.Free.ChooseBasisIndex ℂ (FreeLieAlgebra ℂ ι)) :=
    IsWellOrder.linearOrder WellOrderingRel
  have hi := Shared.Lie.PBW.inclusionInjective_spec ℂ (FreeLieAlgebra ℂ ι)
    (Module.Free.ChooseBasisIndex ℂ (FreeLieAlgebra ℂ ι))
    (Module.Free.chooseBasis ℂ (FreeLieAlgebra ℂ ι))
  intro x y hxy
  apply hi
  apply (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra ℂ ι).injective
  simpa [FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra, freeLieEmbedding,
    Shared.Lie.inclusion, Shared.Lie.canonicalLieMap]
    using hxy

@[simp] theorem freeLieEmbedding_augmentation (x : FreeLieAlgebra ℂ ι) :
    FreeAlgebra.algebraMapInv (freeLieEmbedding x) = 0 := by
  have he : FreeAlgebra.algebraMapInv.toLieHom.comp
      (freeLieEmbedding (ι := ι)) = 0 := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp [freeLieEmbedding, FreeAlgebra.algebraMapInv]
  exact LieHom.congr_fun he x

end LieAlgebrasAndRepresentations.Serre



namespace LieAlgebrasAndRepresentations.Serre.WordModel
universe u
variable {ι : Type u} [DecidableEq ι]
abbrev P (ι : Type u) := MvPolynomial ι ℂ
abbrev W (ι : Type u) := List ι →₀ P ι

def weight (A : Matrix ι ι ℤ) (i : ι) : List ι → P ι
  | [] => 0
  | j :: w => (A i j : P ι) + weight A i w

def F (j : ι) : Module.End (P ι) (W ι) :=
  Finsupp.lmapDomain _ _ (List.cons j)

@[simp] theorem F_single (j : ι) (w : List ι) (p : P ι) :
    F j (Finsupp.single w p) = Finsupp.single (j :: w) p := by
  simp [F]

def H (A : Matrix ι ι ℤ) (i : ι) : Module.End (P ι) (W ι) :=
  Finsupp.linearCombination (P ι) (fun w => Finsupp.single w (MvPolynomial.X i - weight A i w))

@[simp] theorem H_single (A : Matrix ι ι ℤ) (i : ι) (w : List ι) (p : P ι) :
    H A i (Finsupp.single w p) = Finsupp.single w ((MvPolynomial.X i - weight A i w) * p) := by
  simp only [H, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]
  rw [mul_comm]

@[simp] theorem H_single_one (A : Matrix ι ι ℤ) (i : ι) (w : List ι) :
    H A i (Finsupp.single w 1) =
      (MvPolynomial.X i - weight A i w) • Finsupp.single w 1 := by
  simp only [H_single, Finsupp.smul_single, smul_eq_mul]

def eword (A : Matrix ι ι ℤ) (i : ι) : List ι → W ι
  | [] => 0
  | j :: w => F j (eword A i w) + if i = j then H A i (Finsupp.single w 1) else 0

def E (A : Matrix ι ι ℤ) (i : ι) : Module.End (P ι) (W ι) :=
  Finsupp.linearCombination (P ι) (eword A i)

@[simp] theorem E_single (A : Matrix ι ι ℤ) (i : ι) (w : List ι) (p : P ι) :
    E A i (Finsupp.single w p) = p • eword A i w := by simp [E]

@[simp] theorem E_nil (A : Matrix ι ι ℤ) (i : ι) (p : P ι) :
    E A i (Finsupp.single [] p) = 0 := by simp [eword]

theorem EF_apply (A : Matrix ι ι ℤ) (i j : ι) (v : W ι) :
    E A i (F j v) = F j (E A i v) + if i = j then H A i v else 0 := by
  have hh : (E A i).comp (F j) = (F j).comp (E A i) + if i = j then H A i else 0 := by
    apply Finsupp.lhom_ext
    intro w p
    by_cases h : i = j
    · subst j
      simp only [LinearMap.comp_apply, LinearMap.add_apply, if_pos, F_single, E_single,
        eword, H_single, smul_add, map_smul, Finsupp.smul_single, smul_eq_mul]
      rw [mul_one, mul_comm p]
    · simp [eword, h]
  by_cases h : i = j <;> simpa [h] using LinearMap.congr_fun hh v

theorem HF_apply (A : Matrix ι ι ℤ) (i j : ι) (v : W ι) :
    H A i (F j v) = F j (H A i v) - (A i j : P ι) • F j v := by
  have hh : (H A i).comp (F j) = (F j).comp (H A i) - (A i j : P ι) • F j := by
    apply Finsupp.lhom_ext
    intro w p
    simp only [LinearMap.comp_apply, F_single, H_single, LinearMap.sub_apply,
      LinearMap.smul_apply, Finsupp.smul_single, smul_eq_mul, ← Finsupp.single_sub]
    congr 1
    simp [weight]
    ring
  exact LinearMap.congr_fun hh v

theorem HH_apply (A : Matrix ι ι ℤ) (i j : ι) (v : W ι) :
    H A i (H A j v) = H A j (H A i v) := by
  have hh : (H A i).comp (H A j) = (H A j).comp (H A i) := by
    apply Finsupp.lhom_ext
    intro w p
    simp only [LinearMap.comp_apply, H_single]
    congr 1
    ring
  exact LinearMap.congr_fun hh v

/-- Raising removes one occurrence of j from the word, so changes every Cartan weight by A i j. -/
theorem H_eword (A : Matrix ι ι ℤ) (i j : ι) (w : List ι) :
    H A i (eword A j w) =
      (MvPolynomial.X i - weight A i w + (A i j : P ι)) • eword A j w := by
  induction w with
  | nil => simp [eword]
  | cons k w ih =>
    rw [eword, map_add, HF_apply, ih, map_smul]
    by_cases h : j = k
    · subst k
      simp only [ite_true, H_single_one, map_smul, weight, smul_add]
      module
    · simp only [if_neg h, map_zero, add_zero, weight]
      module

theorem HE_apply (A : Matrix ι ι ℤ) (i j : ι) (v : W ι) :
    H A i (E A j v) = E A j (H A i v) + (A i j : P ι) • E A j v := by
  have hh : (H A i).comp (E A j) = (E A j).comp (H A i) + (A i j : P ι) • E A j := by
    apply Finsupp.lhom_ext
    intro w p
    simp only [LinearMap.comp_apply, E_single, map_smul, H_eword,
      LinearMap.add_apply, H_single, LinearMap.smul_apply]
    module
  exact LinearMap.congr_fun hh v

abbrev FC (i : ι) : Module.End ℂ (W ι) := (F i).restrictScalars ℂ
abbrev HC (A : Matrix ι ι ℤ) (i : ι) : Module.End ℂ (W ι) := (H A i).restrictScalars ℂ
abbrev EC (A : Matrix ι ι ℤ) (i : ι) : Module.End ℂ (W ι) := (E A i).restrictScalars ℂ

theorem hh (A : Matrix ι ι ℤ) (i j : ι) : ⁅HC A i, HC A j⁆ = 0 := by
  apply LinearMap.ext
  intro v
  change H A i (H A j v) - H A j (H A i v) = 0
  rw [HH_apply, sub_self]

theorem ef (A : Matrix ι ι ℤ) (i j : ι) :
    ⁅EC A i, FC j⁆ = if i = j then HC A i else 0 := by
  apply LinearMap.ext
  intro v
  change E A i (F j v) - F j (E A i v) = _
  rw [EF_apply]
  by_cases h : i = j <;> simp [h]

theorem hf (A : Matrix ι ι ℤ) (i j : ι) :
    ⁅HC A i, FC j⁆ = -(A i j • FC j) := by
  apply LinearMap.ext
  intro v
  change H A i (F j v) - F j (H A i v) = -(A i j • F j v)
  rw [HF_apply]
  have hs : (A i j : P ι) • F j v = A i j • F j v := by
    simp only [Int.cast_smul_eq_zsmul]
  rw [hs]
  abel

theorem he (A : Matrix ι ι ℤ) (i j : ι) :
    ⁅HC A i, EC A j⁆ = A i j • EC A j := by
  apply LinearMap.ext
  intro v
  change H A i (E A j v) - E A j (H A i v) = A i j • E A j v
  rw [HE_apply]
  have hs : (A i j : P ι) • E A j v = A i j • E A j v := by
    simp only [Int.cast_smul_eq_zsmul]
  rw [hs]
  abel

end LieAlgebrasAndRepresentations.Serre.WordModel



namespace LieAlgebrasAndRepresentations.Serre.WordModel
attribute [local instance 100] LieRing.ofAssociativeRing
universe u
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

def vacuum : W ι := Finsupp.single [] 1

def representation : PreSerre.Algebra A →ₗ⁅ℂ⁆ Module.End ℂ (W ι) :=
  PreSerre.lift A (EC A) FC (HC A) (hh A) (he A) (hf A) (ef A)

@[simp] theorem representation_e (i : ι) :
    representation A (PreSerre.e A i) = EC A i := PreSerre.lift_e ..
@[simp] theorem representation_f (i : ι) :
    representation A (PreSerre.f A i) = FC i := PreSerre.lift_f ..
@[simp] theorem representation_h (i : ι) :
    representation A (PreSerre.h A i) = HC A i := PreSerre.lift_h ..

def evaluate : PreSerre.Algebra A →ₗ[ℂ] W ι :=
  (LinearMap.applyₗ (vacuum (ι := ι))).comp (representation A).toLinearMap

@[simp] theorem evaluate_e (i : ι) : evaluate A (PreSerre.e A i) = 0 := by
  simp [evaluate, vacuum, eword]
@[simp] theorem evaluate_f (i : ι) :
    evaluate A (PreSerre.f A i) = Finsupp.single [i] 1 := by
  simp [evaluate, vacuum]
@[simp] theorem evaluate_h (i : ι) :
    evaluate A (PreSerre.h A i) = Finsupp.single [] (MvPolynomial.X i) := by
  simp [evaluate, vacuum, H_single, weight]

theorem evaluate_positive (x : SideFree ι) :
    evaluate A (PreSerre.positiveLift A x) = 0 := by
  have hx : x ∈ LieSubalgebra.lieSpan ℂ (SideFree ι) (Set.range (FreeLieAlgebra.of ℂ)) := by
    rw [free_generated]; trivial
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx => obtain ⟨i,rfl⟩ := hx; simp [PreSerre.positiveLift]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]
  | lie x y _ _ hx hy =>
    change representation A (PreSerre.positiveLift A ⁅x,y⁆) vacuum = 0
    rw [LieHom.map_lie, LieHom.map_lie]
    change representation A (PreSerre.positiveLift A x)
      (representation A (PreSerre.positiveLift A y) vacuum) -
      representation A (PreSerre.positiveLift A y)
      (representation A (PreSerre.positiveLift A x) vacuum) = 0
    change representation A (PreSerre.positiveLift A x) vacuum = 0 at hx
    change representation A (PreSerre.positiveLift A y) vacuum = 0 at hy
    rw [hx, hy, map_zero, map_zero, sub_self]

def cartanPolynomial : (ι →₀ ℂ) →ₗ[ℂ] P ι :=
  Finsupp.linearCombination ℂ (MvPolynomial.X : ι → P ι)

theorem cartanPolynomial_injective : Function.Injective (cartanPolynomial (ι := ι)) :=
  (MvPolynomial.linearIndependent_X ι ℂ)

theorem evaluate_cartan (c : ι →₀ ℂ) :
    evaluate A (PreSerre.cartanMap A c) = Finsupp.single [] (cartanPolynomial c) := by
  have he : (evaluate A).comp (PreSerre.cartanMap A) =
      (Finsupp.lsingle []).comp (cartanPolynomial (ι := ι)) := by
    apply Finsupp.lhom_ext
    intro i p
    simp [PreSerre.cartanMap, cartanPolynomial]
  exact LinearMap.congr_fun he c

/-- Once the faithful negative word action is known, evaluation at the empty word
separates Cartan from the two free Lie subalgebras. -/
theorem sum_injective_of_word_action
    (hneg : Function.Injective ((evaluate A).comp (PreSerre.negativeLift A).toLinearMap))
    (hconstant : ∀ x : SideFree ι, evaluate A (PreSerre.negativeLift A x) [] = 0)
    (hpos : Function.Injective (PreSerre.positiveLift A)) :
    Function.Injective (PreSerre.sum A) := by
  apply (PreSerre.sum A).ker_eq_bot.mp
  apply eq_bot_iff.mpr
  rintro ⟨x,c,y⟩ hzero
  change PreSerre.negativeLift A x + (PreSerre.cartanMap A c + PreSerre.positiveLift A y) = 0 at hzero
  have heval := congrArg (evaluate A) hzero
  simp only [map_add, evaluate_cartan, evaluate_positive, add_zero, map_zero] at heval
  have hc : c = 0 := by
    have hempty := congrArg (fun v : W ι => v []) heval
    simp only [Finsupp.add_apply, hconstant, Finsupp.single_eq_same, zero_add, Finsupp.zero_apply] at hempty
    exact cartanPolynomial_injective (hempty.trans (map_zero cartanPolynomial).symm)
  subst c
  have hx : x = 0 := by
    apply hneg
    change evaluate A (PreSerre.negativeLift A x) = evaluate A (PreSerre.negativeLift A 0)
    simpa only [map_zero, Finsupp.single_zero, add_zero, LinearMap.comp_apply] using heval
  subst x
  have hy : y = 0 := by
    apply hpos
    simpa only [map_zero, zero_add] using hzero
  subst y
  rfl

end LieAlgebrasAndRepresentations.Serre.WordModel



namespace LieAlgebrasAndRepresentations.Serre.WordModel
universe u
variable {ι : Type u} [DecidableEq ι]
attribute [local instance 100] LieRing.ofAssociativeRing

def monoidWordEmbed : MonoidAlgebra ℂ (FreeMonoid ι) →ₗ[ℂ] W ι :=
  (Finsupp.mapRange.linearMap (Algebra.linearMap ℂ (P ι))).comp
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

def wordEmbed : FreeAlgebra ℂ ι →ₗ[ℂ] W ι :=
  (monoidWordEmbed (ι := ι)).comp
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap

theorem wordEmbed_injective : Function.Injective (wordEmbed (ι := ι)) := by
  apply (Finsupp.mapRange_injective _ (map_zero (Algebra.linearMap ℂ (P ι)))
    (MvPolynomial.C_injective ι ℂ)).comp
  exact (MonoidAlgebra.coeffLinearEquiv ℂ).injective.comp
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective

@[simp] theorem monoidWordEmbed_single (w : FreeMonoid ι) (c : ℂ) :
    monoidWordEmbed (MonoidAlgebra.single w c) = Finsupp.single w (MvPolynomial.C c) := by
  change Finsupp.mapRange (Algebra.linearMap ℂ (P ι)) (map_zero (Algebra.linearMap ℂ (P ι)))
    (MonoidAlgebra.single w c).coeff = _
  simp only [MonoidAlgebra.coeff_single, Finsupp.mapRange_single]
  rfl

theorem monoidWordEmbed_prefix (i : ι) (m : MonoidAlgebra ℂ (FreeMonoid ι)) :
    monoidWordEmbed ((MonoidAlgebra.of ℂ (FreeMonoid ι) (FreeMonoid.of i)) * m) =
      F i (monoidWordEmbed m) := by
  induction m using MonoidAlgebra.induction_on with
  | of w =>
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
        one_mul, monoidWordEmbed_single, MvPolynomial.C_1]
      exact (F_single i w 1).symm
  | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | smul c x hx =>
      simp only [mul_smul_comm, map_smul, hx]
      exact (((F i).restrictScalars ℂ).map_smul c _).symm

@[simp] theorem wordEmbed_ι_mul (i : ι) (a : FreeAlgebra ℂ ι) :
    wordEmbed (FreeAlgebra.ι ℂ i * a) = F i (wordEmbed a) := by
  change monoidWordEmbed (FreeAlgebra.equivMonoidAlgebraFreeMonoid
    (FreeAlgebra.ι ℂ i * a)) = _
  rw [map_mul]
  have hi : FreeAlgebra.equivMonoidAlgebraFreeMonoid (FreeAlgebra.ι ℂ i) =
      MonoidAlgebra.of ℂ (FreeMonoid ι) (FreeMonoid.of i) := by
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hi, monoidWordEmbed_prefix]
  rfl

/-- The augmentation killing all letters is the coefficient of the empty word. -/
def emptyCoeff : MonoidAlgebra ℂ (FreeMonoid ι) →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ (FreeMonoid ι) (FreeMonoid.lift (fun _ : ι => (0 : ℂ)))

theorem emptyCoeff_apply (m : MonoidAlgebra ℂ (FreeMonoid ι)) :
    emptyCoeff m = m.coeff 1 := by
  induction m using MonoidAlgebra.induction_on with
  | of w =>
      cases w with
      | one => simp [emptyCoeff, MonoidAlgebra.of_apply]
      | of_mul i w => simp [emptyCoeff, MonoidAlgebra.of_apply, FreeMonoid.lift_apply,
          FreeMonoid.toList_mul, FreeMonoid.toList_of, FreeMonoid.toList_one]
  | add x y hx hy => simp only [map_add, hx, hy, MonoidAlgebra.coeff_add, Finsupp.add_apply]
  | smul c x hx => simp only [map_smul, hx, MonoidAlgebra.coeff_smul, Finsupp.smul_apply]

theorem freeAlgebra_augmentation_eq (a : FreeAlgebra ℂ ι) :
    FreeAlgebra.algebraMapInv a =
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid a).coeff 1 := by
  have he : FreeAlgebra.algebraMapInv =
      (emptyCoeff (ι := ι)).comp FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom := by
    apply FreeAlgebra.hom_ext
    funext i
    simp [FreeAlgebra.algebraMapInv, emptyCoeff,
      FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  exact (AlgHom.congr_fun he a).trans (emptyCoeff_apply _)

@[simp] theorem wordEmbed_nil (a : FreeAlgebra ℂ ι) :
    wordEmbed a [] = MvPolynomial.C (FreeAlgebra.algebraMapInv a) := by
  change MvPolynomial.C ((FreeAlgebra.equivMonoidAlgebraFreeMonoid a).coeff 1) = _
  rw [freeAlgebra_augmentation_eq]

@[simp] theorem wordEmbed_freeLie_nil (x : FreeLieAlgebra ℂ ι) :
    wordEmbed (freeLieEmbedding x) [] = 0 := by
  simp

end LieAlgebrasAndRepresentations.Serre.WordModel



namespace LieAlgebrasAndRepresentations.Serre.WordModel
universe u
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)
attribute [local instance 100] LieRing.ofAssociativeRing

def associativeAction : FreeAlgebra ℂ ι →ₐ[ℂ] Module.End ℂ (W ι) :=
  FreeAlgebra.lift ℂ FC

theorem wordEmbed_mul_action (a b : FreeAlgebra ℂ ι) :
    wordEmbed (a * b) = associativeAction a (wordEmbed b) := by
  induction a using FreeAlgebra.induction generalizing b with
  | grade0 c =>
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul]
    simp [associativeAction]
  | grade1 i => simpa [associativeAction] using wordEmbed_ι_mul i b
  | mul a c ha hc =>
    rw [mul_assoc, ha, hc, map_mul]
    rfl
  | add a c ha hc => rw [add_mul, map_add, ha, hc, map_add]; rfl

@[simp] theorem wordEmbed_one : wordEmbed (1 : FreeAlgebra ℂ ι) = vacuum := by
  change monoidWordEmbed (FreeAlgebra.equivMonoidAlgebraFreeMonoid 1) = _
  rw [map_one]
  change monoidWordEmbed (MonoidAlgebra.single 1 1) = _
  rw [monoidWordEmbed_single, MvPolynomial.C_1]
  rfl

theorem associativeAction_vacuum (a : FreeAlgebra ℂ ι) :
    associativeAction a vacuum = wordEmbed a := by
  rw [← wordEmbed_one, ← wordEmbed_mul_action, mul_one]

theorem representation_negative (x : SideFree ι) :
    representation A (PreSerre.negativeLift A x) = associativeAction (freeLieEmbedding x) := by
  have hm : (representation A).comp (PreSerre.negativeLift A) =
      (associativeAction (ι := ι)).toLieHom.comp freeLieEmbedding := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp [PreSerre.negativeLift, freeLieEmbedding, associativeAction]
  exact LieHom.congr_fun hm x

theorem evaluate_negative (x : SideFree ι) :
    evaluate A (PreSerre.negativeLift A x) = wordEmbed (freeLieEmbedding x) := by
  change representation A (PreSerre.negativeLift A x) vacuum = _
  rw [representation_negative, associativeAction_vacuum]

theorem negative_evaluate_injective :
    Function.Injective ((evaluate A).comp (PreSerre.negativeLift A).toLinearMap) := by
  intro x y hxy
  apply freeLieEmbedding_injective
  apply wordEmbed_injective
  change evaluate A (PreSerre.negativeLift A x) = evaluate A (PreSerre.negativeLift A y) at hxy
  simpa only [evaluate_negative] using hxy

theorem negativeLift_injective : Function.Injective (PreSerre.negativeLift A) := by
  intro x y hxy
  apply negative_evaluate_injective A
  exact congrArg (evaluate A) hxy

theorem positiveLift_injective : Function.Injective (PreSerre.positiveLift A) := by
  intro x y hxy
  apply negativeLift_injective A
  simpa only [PreSerre.flip_positiveLift] using congrArg (PreSerre.flip A) hxy

theorem negative_empty (x : SideFree ι) : evaluate A (PreSerre.negativeLift A x) [] = 0 := by
  rw [evaluate_negative, wordEmbed_freeLie_nil]

theorem sum_injective : Function.Injective (PreSerre.sum A) :=
  sum_injective_of_word_action A (negative_evaluate_injective A) (negative_empty A)
    (positiveLift_injective A)

end LieAlgebrasAndRepresentations.Serre.WordModel


namespace LieAlgebrasAndRepresentations.Serre
universe u
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

namespace PreSerre
@[simp] theorem toSerre_negativeLift (x : SideFree ι) :
    toSerre A (negativeLift A x) = Serre.negativeLift A x := by
  have hm : (toSerre A).comp (negativeLift A) = Serre.negativeLift A := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp only [negativeLift, Serre.negativeLift, LieHom.comp_apply, FreeLieAlgebra.lift_of_apply,
      toSerre_f]
  exact LieHom.congr_fun hm x

@[simp] theorem toSerre_positiveLift (x : SideFree ι) :
    toSerre A (positiveLift A x) = Serre.positiveLift A x := by
  have hm : (toSerre A).comp (positiveLift A) = Serre.positiveLift A := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp only [positiveLift, Serre.positiveLift, LieHom.comp_apply, FreeLieAlgebra.lift_of_apply,
      toSerre_e]
  exact LieHom.congr_fun hm x

@[simp] theorem toSerre_cartanMap (c : ι →₀ ℂ) :
    toSerre A (cartanMap A c) = Finsupp.linearCombination ℂ (Serre.h A) c := by
  have hm : (toSerre A).toLinearMap.comp (cartanMap A) =
      Finsupp.linearCombination ℂ (Serre.h A) := by
    apply Finsupp.lhom_ext
    intro i r
    simp only [cartanMap, LinearMap.comp_apply, Finsupp.linearCombination_single,
      LieHom.coe_toLinearMap, map_smul, toSerre_h]
  exact LinearMap.congr_fun hm c

@[simp] theorem toSerre_sum (x : SideFree ι) (c : ι →₀ ℂ) (y : SideFree ι) :
    toSerre A (sum A (x, (c, y))) =
      sideTriangularSum A (LieSubmodule.Quotient.mk x, (c, LieSubmodule.Quotient.mk y)) := by
  simp only [sum, sideTriangularSum, LinearMap.coprod_apply, LieHom.coe_toLinearMap,
    map_add, toSerre_negativeLift, toSerre_positiveLift, toSerre_cartanMap]
  rfl
end PreSerre

/-- The stable-ideal identity transfers pre-Serre coordinate faithfulness
through the exact full presentation, leaving the two exact side quotients. -/
theorem sideTriangularSum_injective_of_preSerre
    (hinj : Function.Injective (PreSerre.sum A))
    (hker : (PreSerre.toSerre A).ker.toSubmodule =
      (sideIdeal A).toSubmodule.map (PreSerre.negativeLift A).toLinearMap ⊔
      (sideIdeal A).toSubmodule.map (PreSerre.positiveLift A).toLinearMap) :
    Function.Injective (sideTriangularSum A) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  rintro ⟨x,c,y⟩ hz
  induction x using Submodule.Quotient.induction_on with | _ x =>
  induction y using Submodule.Quotient.induction_on with | _ y =>
  have hzero : PreSerre.toSerre A (PreSerre.sum A (x, (c,y))) = 0 := by
    rw [PreSerre.toSerre_sum]
    exact hz
  have hmem : PreSerre.sum A (x, (c,y)) ∈
      (sideIdeal A).toSubmodule.map (PreSerre.negativeLift A).toLinearMap ⊔
      (sideIdeal A).toSubmodule.map (PreSerre.positiveLift A).toLinearMap := by
    rw [← hker]
    exact hzero
  obtain ⟨hx,hc,hy⟩ := (threeCoordinateIdeal_mem_iff
    (PreSerre.negativeLift A).toLinearMap (PreSerre.cartanMap A)
    (PreSerre.positiveLift A).toLinearMap
    (sideIdeal A).toSubmodule (sideIdeal A).toSubmodule hinj x c y).mp hmem
  change (LieSubmodule.Quotient.mk x, (c, LieSubmodule.Quotient.mk y)) = 0
  exact Prod.ext ((Submodule.Quotient.mk_eq_zero (sideIdeal A).toSubmodule).mpr hx)
    (Prod.ext hc ((Submodule.Quotient.mk_eq_zero (sideIdeal A).toSubmodule).mpr hy))

end LieAlgebrasAndRepresentations.Serre

namespace LieAlgebrasAndRepresentations.Serre
universe u v
variable {ι : Type u} [DecidableEq ι] (A : Matrix ι ι ℤ)

/-- Exact triangular construction under the algebraic Cartan conditions.
All faithfulness and stable-ideal hypotheses have been proved above. -/
theorem triangular_of_cartanConditions (hA : CartanConditions A) : Triangular A := by
  apply triangular_of_sideTriangularSum_injective A
  apply sideTriangularSum_injective_of_preSerre A (WordModel.sum_injective A)
  rw [PreSerre.toSerre_ker A hA.2.1, PreSerre.serreIdeal_toSubmodule A hA]

/-- The full construction for every Cartan matrix of the original finite
reduced root systems, with the original specified simple roots. -/
theorem triangular_spec :
    Specs.LieAlgebrasAndRepresentations.SerreTriangularConstruction.triangularExpected.{v,u} := by
  intro E _ _ ι _ _ R hR z hz b hb A hA
  exact triangular_of_cartanConditions A (cartanConditions_spec R hR z hz b hb A hA)

end LieAlgebrasAndRepresentations.Serre
