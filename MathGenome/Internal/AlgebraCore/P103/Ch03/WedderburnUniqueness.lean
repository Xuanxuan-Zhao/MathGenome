import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.WedderburnUniqueness
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Field
import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.Algebra.Module.Equiv.Basic

/-!
Uniqueness in the Wedderburn–Artin theorem, paper.tex 708–750.

Images of the coordinate central idempotents force each projection of an
isomorphism of finite products of simple rings to use exactly one factor.
The resulting factor assignment is bijective. For a full matrix ring, its
regular module is a sum of simple columns, so its length recovers the size.
Its simple module is unique up to isomorphism, and the endomorphisms of a
column are right multiplications, recovering the opposite division ring.
The empty-product boundary is included in the factor-permutation theorem.
-/

universe u v w z

namespace P103.Ch03.WedderburnUniqueness

open P103.Specs.Ch03.WedderburnUniqueness

/-- A simple ring has no nontrivial central idempotents. -/
theorem central_idempotent : central_idempotentType.{u} := by
  intro R _ _ z hz he
  let := (IsSimpleRing.isField_center R).toField
  have he' : IsIdempotentElem (⟨z, hz⟩ : Subring.center R) := Subtype.ext he
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he' with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

/-- A surjection from a finite product onto a simple ring uses one coordinate. -/
lemma surjective_pi_to_simple {I : Type u} [Fintype I]
    (A : I → Type v) [∀ i, Ring (A i)]
    (S : Type w) [Ring S] [IsSimpleRing S]
    (f : (Π i, A i) →+* S) (hf : Function.Surjective f) :
    ∃ i, ∃ g : A i →+* S, Function.Surjective g ∧ ∀ x, g (x i) = f x := by
  classical
  have hc (i : I) : f (Pi.single i 1) ∈ Subring.center S := by
    rw [Subring.mem_center_iff]
    intro a
    obtain ⟨x, rfl⟩ := hf a
    rw [← map_mul, ← map_mul]
    congr 1
    ext j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hi (i : I) : IsIdempotentElem (f (Pi.single i 1)) := by
    rw [IsIdempotentElem, ← map_mul]
    congr 1
    ext j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hex : ∃ i, f (Pi.single i 1) ≠ 0 := by
    by_contra h
    have hz : ∀ i, f (Pi.single i 1) = 0 := by simpa using h
    have hs := congrArg f (Finset.univ_sum_single (1 : Π i, A i))
    simp [hz] at hs
  obtain ⟨i, h⟩ := hex
  have hone : f (Pi.single i 1) = 1 := (central_idempotent S _ (hc i) (hi i)).resolve_left h
  let g : A i →+* S :=
    { toFun := fun a => f (Pi.single i a)
      map_zero' := by simp
      map_one' := hone
      map_add' := by intro a b; rw [Pi.single_add, map_add]
      map_mul' := by intro a b; rw [Pi.single_mul, map_mul] }
  have hg (x : Π i, A i) : g (x i) = f x := by
    change f (Pi.single i (x i)) = f x
    have hh : Pi.single i (x i) = (Pi.single i 1 : Π i, A i) * x := by
      ext j
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    rw [hh, map_mul, hone, one_mul]
  exact ⟨i, g, fun y => by obtain ⟨x, rfl⟩ := hf y; exact ⟨x i, hg x⟩, hg⟩

/-- Finite products of simple rings have unique factors up to permutation. -/
lemma simple_product_equiv_factors {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (A : I → Type w) (B : J → Type z)
    [∀ i, Ring (A i)] [∀ j, Ring (B j)]
    [∀ i, IsSimpleRing (A i)] [∀ j, IsSimpleRing (B j)]
    (e : (Π i, A i) ≃+* (Π j, B j)) :
    ∃ p : I ≃ J, ∀ i, Nonempty (A i ≃+* B (p i)) := by
  classical
  have hex (j : J) : ∃ i, ∃ g : A i →+* B j,
      Function.Surjective g ∧ ∀ x, g (x i) = e x j := by
    apply surjective_pi_to_simple A (B j) ((Pi.evalRingHom B j).comp e.toRingHom)
    intro b
    obtain ⟨x, hx⟩ := e.surjective (Pi.single j b)
    exact ⟨x, by simp [hx]⟩
  choose q g hg hq using hex
  have hzero (j : J) (x : Π i, A i) : e x j = 0 ↔ x (q j) = 0 := by
    rw [← hq j x]
    exact map_eq_zero_iff (g j) (g j).injective
  have hqin : Function.Injective q := by
    intro a b hab
    by_contra hne
    obtain ⟨x, hx⟩ := e.surjective (Pi.single a 1)
    have hxb : x (q b) = 0 := (hzero b x).mp (by simp [hx, Ne.symm hne])
    have hxa : x (q a) = 0 := Eq.mp (congrArg (fun t => x t = 0) hab).symm hxb
    have hza := (hzero a x).mpr hxa
    simp [hx] at hza
  have hqsur : Function.Surjective q := by
    intro i
    by_contra hnot
    have hn (j : J) : i ≠ q j := by intro h; exact hnot ⟨j, h.symm⟩
    have hz : e (Pi.single i 1) = 0 := by
      ext j
      exact (hzero j _).mpr (by simp [hn j])
    have hz' : (Pi.single i (1 : A i) : Π i, A i) = 0 := e.injective (by simpa only [map_zero] using hz)
    have h := congrFun hz' i
    simp at h
  let p : J ≃ I := Equiv.ofBijective q ⟨hqin, hqsur⟩
  refine ⟨p.symm, fun i => ?_⟩
  have hpi : q (p.symm i) = i := p.apply_symm_apply i
  have h := Nonempty.intro (RingEquiv.ofBijective (g (p.symm i))
    ⟨(g (p.symm i)).injective, hg (p.symm i)⟩)
  exact Eq.mp (congrArg (fun t => Nonempty (A t ≃+* B (p.symm i))) hpi) h

/-- Isomorphic finite products have matching matrix-ring factors. -/
theorem factor_permutation : factor_permutationType.{u,v} := by
  intro k l D E n m _ _ hn hm he
  let : ∀ i, NeZero (n i) := fun i => ⟨Nat.ne_zero_of_lt (hn i)⟩
  let : ∀ j, NeZero (m j) := fun j => ⟨Nat.ne_zero_of_lt (hm j)⟩
  exact simple_product_equiv_factors _ _ he.some

section ColumnEnd

open scoped Matrix.Module
open MulOpposite

variable {D : Type u} [Ring D] {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Every endomorphism of the column module is right multiplication by a scalar. -/
def columnEndHom : Dᵐᵒᵖ →+* Module.End (Matrix ι ι D) (ι → D) where
  toFun d := (RingEquiv.moduleEndSelf D d).mapMatrixModule ι
  map_one' := by ext v i; simp
  map_mul' d e := by ext v i; simp [Module.End.mul_apply, mul_assoc]
  map_zero' := by ext v i; simp
  map_add' d e := by ext v i; simp [mul_add]

@[simp] theorem columnEndHom_apply (d : Dᵐᵒᵖ) (v : ι → D) (i : ι) :
    columnEndHom (ι := ι) d v i = v i * unop d := rfl

/-- The endomorphism ring of a nonempty column is the opposite coefficient ring. -/
noncomputable def columnEndEquiv (i₀ : ι) :
    Dᵐᵒᵖ ≃+* Module.End (Matrix ι ι D) (ι → D) :=
  RingEquiv.ofBijective columnEndHom (by
    constructor
    · intro d e h
      apply unop_injective
      have := congrArg (fun f : Module.End (Matrix ι ι D) (ι → D) =>
        f (Pi.single i₀ 1) i₀) h
      simpa using this
    · intro f
      refine ⟨op (f (Pi.single i₀ 1) i₀), ?_⟩
      apply LinearMap.ext
      intro v
      ext i
      let A : Matrix ι ι D := fun a b => if b = i₀ then v a else 0
      have hA : A • Pi.single i₀ (1 : D) = v := by
        ext a
        change (∑ b, (if b = i₀ then v a else 0) * (Pi.single i₀ (1 : D) : ι → D) b) = v a
        simp
      have hf := congrFun (f.map_smul A (Pi.single i₀ 1)) i
      rw [hA] at hf
      change f v i = ∑ b, (if b = i₀ then v i else 0) * f (Pi.single i₀ 1) b at hf
      simpa using hf.symm)

end ColumnEnd

section MatrixSize

variable {D : Type u} [DivisionRing D] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The nonzero column module over a division ring is simple. -/
theorem simple_columns : IsSimpleModule (Matrix ι ι D) (ι → D) := by
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨inferInstance, ?_⟩
  intro x hx y
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (funext hn)
  refine ⟨fun i k => if k = j then y i * (x j)⁻¹ else 0, ?_⟩
  funext i
  change (∑ k : ι, (if k = j then y i * (x j)⁻¹ else 0) * x k) = y i
  simp [Finset.sum_ite_eq', mul_assoc, hj]

/-- The regular matrix module is the direct product of its column modules. -/
noncomputable def columnsEquiv :
    Matrix ι ι D ≃ₗ[Matrix ι ι D] (ι → (ι → D)) where
  toFun A j i := A i j
  invFun A i j := A j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' A B := by
    ext j i
    change (A * B) i j = Matrix.mulVec A (fun k => B k j) i
    rfl

/-- The regular composition length is the matrix size. -/
theorem length_matrix : Module.length (Matrix ι ι D) (Matrix ι ι D) = Fintype.card ι := by
  let := simple_columns (D := D) (ι := ι)
  rw [columnsEquiv.length_eq]
  simp

/-- Ring isomorphisms preserve the length of the left regular module. -/
theorem length_ringEquiv {R : Type u} {S : Type v} [Ring R] [Ring S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.symm (e : R →+* S) (e.symm : S →+* R)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e.toSemilinearEquiv)]

/-- Positive-size matrix rings over division rings determine their sizes. -/
theorem size_eq (E : Type v) [DivisionRing E] (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (e : Matrix (Fin n) (Fin n) D ≃+* Matrix (Fin m) (Fin m) E) : n = m := by
  let : NeZero n := ⟨hn.ne'⟩
  let : NeZero m := ⟨hm.ne'⟩
  have h := length_ringEquiv e
  rw [length_matrix, length_matrix] at h
  simpa using h

end MatrixSize

/-- A simple Artinian ring has a unique isomorphism class of simple modules. -/
theorem simple_modules_linearEquiv
    (R : Type u) [Ring R] [IsSimpleRing R] [IsArtinianRing R]
    (V : Type v) (W : Type w) [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W] [IsSimpleModule R V] [IsSimpleModule R W] :
    Nonempty (V ≃ₗ[R] W) := by
  obtain ⟨I, ⟨eV⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R V
  obtain ⟨J, ⟨eW⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R W
  let : IsSimpleModule R I := IsSimpleModule.congr eV.symm
  let : IsSimpleModule R J := IsSimpleModule.congr eW.symm
  obtain ⟨e⟩ := IsSimpleRing.isIsotypic R R I J
  exact ⟨eV.trans (e.symm.trans eW.symm)⟩

/-- Transport of the unique simple module along a ring isomorphism. -/
theorem simple_modules_semilinearEquiv
    (R : Type u) (S : Type v) [Ring R] [Ring S] [IsSimpleRing R] [IsArtinianRing R]
    (V : Type w) (W : Type*) [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module S W] [IsSimpleModule R V] [IsSimpleModule S W]
    (e : R ≃+* S) :
    have := RingHomInvPair.of_ringEquiv e
    have := RingHomInvPair.symm (e : R →+* S) (e.symm : S →+* R)
    Nonempty (V ≃ₛₗ[(e : R →+* S)] W) := by
  let : Module R W := Module.compHom W (e : R →+* S)
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.symm (e : R →+* S) (e.symm : S →+* R)
  let f : W ≃ₛₗ[(e.symm : S →+* R)] W :=
    { toEquiv := Equiv.refl W
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change r • x = e (e.symm r) • x
        rw [e.apply_symm_apply] }
  let : RingHomSurjective (e.symm : S →+* R) := ⟨e.symm.surjective⟩
  let : IsSimpleModule R W :=
    (f.toLinearMap.isSimpleModule_iff_of_bijective f.bijective).mp inferInstance
  obtain ⟨g⟩ := simple_modules_linearEquiv R V W
  exact ⟨g.trans f.symm⟩

/-- An isomorphism of full matrix rings recovers their division rings. -/
theorem divisionRing_equiv
    (D : Type u) (E : Type v) [DivisionRing D] [DivisionRing E]
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (e : Matrix (Fin n) (Fin n) D ≃+* Matrix (Fin m) (Fin m) E) :
    Nonempty (D ≃+* E) := by
  let : NeZero n := ⟨hn.ne'⟩
  let : NeZero m := ⟨hm.ne'⟩
  let := simple_columns (D := D) (ι := Fin n)
  let := simple_columns (D := E) (ι := Fin m)
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.symm (e : Matrix (Fin n) (Fin n) D →+* Matrix (Fin m) (Fin m) E)
    (e.symm : Matrix (Fin m) (Fin m) E →+* Matrix (Fin n) (Fin n) D)
  obtain ⟨f⟩ := simple_modules_semilinearEquiv
    (Matrix (Fin n) (Fin n) D) (Matrix (Fin m) (Fin m) E) (Fin n → D) (Fin m → E) e
  let d := columnEndEquiv (D := D) (0 : Fin n)
  let d' := columnEndEquiv (D := E) (0 : Fin m)
  exact ⟨RingEquiv.unop (d.trans (f.conjRingEquiv.trans d'.symm))⟩

/-- Both invariants are recovered from an isomorphism of matrix rings. -/
theorem matrix_parameters : matrix_parametersType.{u,v} := by
  intro D E _ _ n m hn hm ⟨e⟩
  exact ⟨size_eq E n m hn hm e, divisionRing_equiv D E n m hn hm e⟩

/-- The factor permutation also matches matrix sizes and division rings. -/
theorem uniqueness :
  ∀ (R : Type w) [Ring R] (k l : ℕ)
    (D : Fin k → Type u) (E : Fin l → Type v)
    (n : Fin k → ℕ) (m : Fin l → ℕ)
    [∀ i, DivisionRing (D i)] [∀ j, DivisionRing (E j)],
    (∀ i, 0 < n i) → (∀ j, 0 < m j) →
    Nonempty (R ≃+* Π i, Matrix (Fin (n i)) (Fin (n i)) (D i)) →
    Nonempty (R ≃+* Π j, Matrix (Fin (m j)) (Fin (m j)) (E j)) →
    ∃ p : Fin k ≃ Fin l, ∀ i,
      Nonempty (Matrix (Fin (n i)) (Fin (n i)) (D i) ≃+*
        Matrix (Fin (m (p i))) (Fin (m (p i))) (E (p i))) ∧
      n i = m (p i) ∧ Nonempty (D i ≃+* E (p i)) := by
  intro R _ k l D E n m _ _ hn hm ⟨e⟩ ⟨f⟩
  obtain ⟨p, hp⟩ := factor_permutation k l D E n m hn hm ⟨e.symm.trans f⟩
  refine ⟨p, fun i => ?_⟩
  exact ⟨hp i, matrix_parameters (D i) (E (p i)) (n i) (m (p i)) (hn i) (hm (p i)) (hp i)⟩

/-- A product of nonzero rings can be simple only when its index type
has one element. This proof applies to arbitrary rings in the factors. -/
theorem subsingleton_index_of_simple_product
    {ι : Type u} (A : ι → Type v) [∀ i, Ring (A i)] [∀ i, Nontrivial (A i)]
    [IsSimpleRing (Π i, A i)] : Subsingleton ι := by
  classical
  refine ⟨fun i j => ?_⟩
  by_contra hij
  have hinj := (Pi.evalRingHom A i).injective
  have h : (Pi.single j (1 : A j) : Π i, A i) = 0 :=
    hinj (by simp [hij])
  have hone := congrFun h j
  simp at hone

/-- Every representation of a simple ring has exactly one matrix factor. -/
theorem simple_factor_count : simple_factor_countType.{u,v} := by
  intro R _ _ k D n _ hn ⟨e⟩
  let : ∀ i, NeZero (n i) := fun i => ⟨Nat.ne_zero_of_lt (hn i)⟩
  let : IsSimpleRing (Π i, Matrix (Fin (n i)) (Fin (n i)) (D i)) :=
    IsSimpleRing.of_ringEquiv e inferInstance
  have hs := subsingleton_index_of_simple_product
    (fun i => Matrix (Fin (n i)) (Fin (n i)) (D i))
  have hle : k ≤ 1 := by
    simpa using (Fintype.card_le_one_iff_subsingleton.mpr hs)
  have hpos : 0 < k := by
    by_contra h
    have hk : k = 0 := Nat.eq_zero_of_not_pos h
    subst k
    exact zero_ne_one (α := R) (e.injective (Subsingleton.elim _ _))
  exact Nat.le_antisymm hle hpos

/-- The one-factor existence statement follows with the original left
Artinian hypothesis and a genuinely noncommutative division ring. -/
theorem simple_artinian : simple_artinianType.{u} := by
  intro R _ _ _
  obtain ⟨n, hn, D, hD, he⟩ := IsSimpleRing.exists_ringEquiv_matrix_divisionRing R
  exact ⟨n, D, hD, Nat.pos_of_ne_zero hn.out, he⟩

end P103.Ch03.WedderburnUniqueness
