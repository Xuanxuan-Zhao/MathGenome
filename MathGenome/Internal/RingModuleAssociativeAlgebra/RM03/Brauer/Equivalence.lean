import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.Equivalence
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MatrixDivision
import Mathlib.RingTheory.SimpleRing.Matrix

/-! Brauer equivalence and division representatives. -/

universe u v w x y

namespace RM03.Brauer

/-- Algebras are Brauer equivalent when positive-size matrix algebras over them are isomorphic. -/
def Equivalent (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A]
    (B : Type w) [Ring B] [Algebra k B] : Prop :=
  ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
    Nonempty (Matrix (Fin p) (Fin p) A ≃ₐ[k] Matrix (Fin q) (Fin q) B)

theorem equivalent_iff_isBrauerEquivalent (k : Type u) [Field k]
    (A B : _root_.CSA.{u, v} k) :
    Equivalent k A B ↔ IsBrauerEquivalent A B := by
  simp only [Equivalent, IsBrauerEquivalent, Nat.pos_iff_ne_zero]

theorem equivalence_on_csa (k : Type u) [Field k] :
    Equivalence (fun A B : _root_.CSA.{u, v} k => Equivalent k A B) := by
  let compare := equivalent_iff_isBrauerEquivalent k
  constructor
  · intro A
    exact (compare A A).mpr (IsBrauerEquivalent.refl A)
  · intro A B h
    exact (compare B A).mpr ((compare A B).mp h).symm
  · intro A B C hAB hBC
    exact (compare A C).mpr (((compare A B).mp hAB).trans ((compare B C).mp hBC))

private noncomputable def oneMatrixEquiv (k A : Type*) [Field k] [Ring A] [Algebra k A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[k] A := by
  refine (AlgEquiv.ofBijective (Matrix.scalarAlgHom (Fin 1) k (α := A)) ⟨?_, ?_⟩).symm
  · intro a b h
    simpa [Matrix.scalar_apply] using congrArg
      (fun M : Matrix (Fin 1) (Fin 1) A => M 0 0) h
  · intro M
    refine ⟨M 0 0, ?_⟩
    ext i j
    rw [Subsingleton.elim i (0 : Fin 1), Subsingleton.elim j (0 : Fin 1)]
    simp [Matrix.scalar_apply]

private def matrixOfPresentation {k A D : Type*} [Field k] [Ring A] [Ring D]
    [Algebra k A] [Algebra k D] {r : ℕ} (p : ℕ)
    (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) :
    Matrix (Fin p) (Fin p) A ≃ₐ[k] Matrix (Fin (p * r)) (Fin (p * r)) D :=
  (e.mapMatrix (m := Fin p)).trans <|
    (Matrix.compAlgEquiv (Fin p) (Fin r) D k).trans <|
      Matrix.reindexAlgEquiv k D finProdFinEquiv

/-- Matrix enlargement preserves the division factor. Conversely, if the division
factors agree, enlarging by the other presentation's size identifies the algebras. -/
theorem equivalent_iff_division_factors (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A] (B : Type w) [Ring B] [Algebra k B]
    (hA : CSA.IsCentralSimple k A) (_hB : CSA.IsCentralSimple k B)
    (D : Type x) [DivisionRing D] [Algebra k D]
    (E : Type y) [DivisionRing E] [Algebra k E]
    (_hD : CSA.IsCentralDivision k D) (_hE : CSA.IsCentralDivision k E)
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) (f : B ≃ₐ[k] Matrix (Fin s) (Fin s) E) :
    Equivalent k A B ↔ Nonempty (D ≃ₐ[k] E) := by
  constructor
  · rintro ⟨p, q, hp, hq, ⟨g⟩⟩
    let : IsSimpleRing A := hA.1
    let : Algebra.IsCentral k A := hA.2.1
    let : FiniteDimensional k A := hA.2.2
    let : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
    have hMatrix : CSA.IsCentralSimple k (Matrix (Fin p) (Fin p) A) :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    exact (CSA.MatrixDivision.presentation_unique k _ hMatrix D E (p * r) (q * s)
      (Nat.mul_pos hp hr) (Nat.mul_pos hq hs)
      (matrixOfPresentation p e) (g.trans (matrixOfPresentation q f))).2
  · rintro ⟨g⟩
    refine ⟨s, r, hs, hr, ⟨?_⟩⟩
    exact (matrixOfPresentation s e).trans <|
      g.mapMatrix.trans <|
        (Matrix.reindexAlgEquiv k E (finCongr (Nat.mul_comm s r))).trans <|
          (matrixOfPresentation r f).symm

/-- The class of a bundled central simple algebra in Mathlib's Brauer quotient. -/
def classOf {k : Type u} [Field k] (A : _root_.CSA.{u, v} k) : BrauerGroup.{u, v} k :=
  Quotient.mk (Brauer.CSA_Setoid k) A

theorem classOf_eq_iff (k : Type u) [Field k] (A B : _root_.CSA.{u, v} k) :
    classOf A = classOf B ↔ Equivalent k A B := by
  rw [equivalent_iff_isBrauerEquivalent]
  exact ⟨@Quotient.exact _ (Brauer.CSA_Setoid k) A B,
    @Quotient.sound _ (Brauer.CSA_Setoid k) A B⟩

/-- View a central division algebra as a central simple algebra. -/
def divisionCSA {k : Type u} [Field k] {D : Type v} [DivisionRing D] [Algebra k D]
    (h : CSA.IsCentralDivision k D) : _root_.CSA.{u, v} k :=
  CSA.toCSA (CSA.isCentralSimple_of_isCentralDivision k D h)

private theorem equivalent_of_matrix_presentation {k A D : Type*} [Field k] [Ring A]
    [Ring D] [Algebra k A] [Algebra k D] {r : ℕ} (hr : 0 < r)
    (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) : Equivalent k A D :=
  ⟨1, r, Nat.one_pos, hr, ⟨(oneMatrixEquiv k A).trans e⟩⟩

theorem exists_division_representative (k : Type u) [Field k] (c : BrauerGroup.{u, v} k) :
    ∃ (D : Type v) (_ : DivisionRing D) (_ : Algebra k D) (h : CSA.IsCentralDivision k D),
      classOf (divisionCSA h) = c := by
  induction c using Quotient.inductionOn with
  | _ A =>
    have hA : CSA.IsCentralSimple k A := ⟨A.isSimple, A.isCentral, A.fin_dim⟩
    obtain ⟨r, D, _, _, hD, hr, ⟨e⟩⟩ := CSA.MatrixDivision.exists_presentation k A hA
    refine ⟨D, ‹DivisionRing D›, ‹Algebra k D›, hD, ?_⟩
    change classOf (divisionCSA hD) = classOf A
    exact ((classOf_eq_iff k A (divisionCSA hD)).mpr (equivalent_of_matrix_presentation hr e)).symm

theorem classOf_division_eq_iff (k : Type u) [Field k] (D E : Type v)
    [DivisionRing D] [Algebra k D] [DivisionRing E] [Algebra k E]
    (hD : CSA.IsCentralDivision k D) (hE : CSA.IsCentralDivision k E) :
    classOf (divisionCSA hD) = classOf (divisionCSA hE) ↔ Nonempty (D ≃ₐ[k] E) :=
  (classOf_eq_iff k (divisionCSA hD) (divisionCSA hE)).trans <|
    equivalent_iff_division_factors k D E
      (CSA.isCentralSimple_of_isCentralDivision k D hD)
      (CSA.isCentralSimple_of_isCentralDivision k E hE) D E hD hE 1 1
      Nat.one_pos Nat.one_pos (oneMatrixEquiv k D).symm (oneMatrixEquiv k E).symm

/-- The Brauer class of the field consists of the split central simple algebras. -/
theorem equivalent_iff_split (k : Type u) [Field k] (A : Type v)
    [Ring A] [Algebra k A] (hA : CSA.IsCentralSimple k A) :
    Equivalent k A k ↔ CSA.IsSplit k A := by
  constructor
  · intro h
    obtain ⟨r, D, _, _, hD, hr, ⟨e⟩⟩ := CSA.MatrixDivision.exists_presentation k A hA
    have hk : CSA.IsCentralDivision k k := ⟨inferInstance, inferInstance⟩
    obtain ⟨g⟩ := (equivalent_iff_division_factors k A k hA
      (CSA.isCentralSimple_of_isCentralDivision k k hk) D k hD hk r 1
      hr Nat.one_pos e (oneMatrixEquiv k k).symm).mp h
    exact ⟨r, hr, ⟨e.trans g.mapMatrix⟩⟩
  · rintro ⟨r, hr, ⟨e⟩⟩
    exact equivalent_of_matrix_presentation hr e

/-- The base field as a central simple algebra in a carrier universe that supports it. -/
def scalarCSA (k : Type u) [Field k] : _root_.CSA.{u, max u v} k :=
  divisionCSA (D := ULift.{v} k)
    ⟨⟨fun x _ => Algebra.mem_bot.mpr ⟨x.down, rfl⟩⟩,
      FiniteDimensional.of_injective (ULift.algEquiv (R := k)).toLinearEquiv.toLinearMap
        (ULift.algEquiv (R := k)).injective⟩

theorem classOf_eq_scalar_iff_split (k : Type u) [Field k]
    (A : _root_.CSA.{u, max u v} k) :
    classOf A = classOf (scalarCSA.{u, v} k) ↔ CSA.IsSplit k A := by
  rw [classOf_eq_iff]
  have hA : CSA.IsCentralSimple k A := ⟨A.isSimple, A.isCentral, A.fin_dim⟩
  refine Iff.trans ?_ (equivalent_iff_split k A hA)
  change Equivalent k A (ULift.{v} k) ↔ Equivalent k A k
  constructor
  · rintro ⟨p, q, hp, hq, ⟨e⟩⟩
    exact ⟨p, q, hp, hq, ⟨e.trans (ULift.algEquiv (R := k)).mapMatrix⟩⟩
  · rintro ⟨p, q, hp, hq, ⟨e⟩⟩
    exact ⟨p, q, hp, hq, ⟨e.trans (ULift.algEquiv (R := k)).symm.mapMatrix⟩⟩

end RM03.Brauer
