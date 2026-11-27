import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveTwists
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.DirectSum.Module

noncomputable section

open CategoryTheory
open scoped BigOperators DirectSum

namespace DerivedFormalization.LaurentCechCohomology

open ProjectiveTwists (Index Polynomials ChartLocalization DegreePiece chartProduct chartDenominator
  variablePolynomial grading localizationRestriction)

universe u

variable (k : Type u) [Field k] (n : ℕ)

abbrev ExponentVector (n : ℕ) := Index n → ℤ
abbrev Exponents (n : ℕ) (m : ℤ) := {a : ExponentVector n // ∑ i, a i = m}

def negativeSupport (a : ExponentVector n) : Finset (Index n) :=
  Finset.univ.filter fun i ↦ a i < 0

variable {n}

/-- The alternating sign for deleting the vertex `i` from an increasing list of vertices. -/
def sign (J : Finset (Index n)) (i : Index n) : k :=
  (-1) ^ (J.filter fun j ↦ j < i).card

def admissible (augmented : Bool) (a : ExponentVector n) (p : ℤ) (J : Finset (Index n)) : Prop :=
  (J.card : ℤ) = p + 1 ∧ negativeSupport n a ⊆ J ∧ (augmented = true ∨ J.Nonempty)

/-- A single exponent column, extended by zero to all vertex sets. -/
def fixedSubmodule (augmented : Bool) (a : ExponentVector n) (p : ℤ) :
    Submodule k (Finset (Index n) → k) where
  carrier := {x | ∀ J, ¬ admissible augmented a p J → x J = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy J hJ
    change x J + y J = 0
    rw [hx J hJ, hy J hJ, add_zero]
  smul_mem' := by
    intro r x hx J hJ
    change r * x J = 0
    rw [hx J hJ, mul_zero]

abbrev Fixed (augmented : Bool) (a : ExponentVector n) (p : ℤ) :=
  ↥(fixedSubmodule k augmented a p)

def deleteSum (x : Finset (Index n) → k) (J : Finset (Index n)) : k :=
  ∑ i ∈ J, sign k J i * x (J.erase i)

def insertAt (j : Index n) (x : Finset (Index n) → k) (J : Finset (Index n)) : k :=
  if j ∈ J then 0 else sign k J j * x (insert j J)

def fixedD (augmented : Bool) (a : ExponentVector n) (p : ℤ) :
    Fixed k augmented a p →ₗ[k] Fixed k augmented a (p + 1) where
  toFun x := ⟨deleteSum k x.val, by
    intro J hJ
    apply Finset.sum_eq_zero
    intro i hi
    rw [x.property _ (fun h ↦ hJ
      ⟨by have := Finset.card_erase_add_one hi; have := h.1; omega,
        h.2.1.trans (Finset.erase_subset _ _),
        h.2.2.imp_right (fun hh ↦ hh.mono (Finset.erase_subset _ _))⟩), mul_zero]⟩
  map_add' x y := by
    apply Subtype.ext
    funext J
    change (∑ i ∈ J, sign k J i * (x.val (J.erase i) + y.val (J.erase i))) = _
    simp only [mul_add, Finset.sum_add_distrib]
    rfl
  map_smul' r x := by
    apply Subtype.ext
    funext J
    change (∑ i ∈ J, sign k J i * (r * x.val (J.erase i))) =
      r * (∑ i ∈ J, sign k J i * x.val (J.erase i))
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ mul_left_comm _ _ _

variable (n)

/-- The direct sum has finite support in the exponent coordinate. -/
abbrev Term (m p : ℤ) := ⨁ a : Exponents n m, Fixed k false a.val p

def differential (m p : ℤ) : Term k n m p →ₗ[k] Term k n m (p + 1) :=
  DirectSum.lmap fun a ↦ fixedD k false a.val p

abbrev LaurentPolynomials := AddMonoidAlgebra k (ExponentVector n)

abbrev LocalExponents (m : ℤ) (J : Finset (Index n)) :=
  {a : Exponents n m // negativeSupport n a.val ⊆ J}

abbrev TopExponents (m : ℤ) :=
  {a : Exponents n m // ∀ i, a.val i < 0}

abbrev PolynomialExponents (m : ℤ) :=
  {a : Index n →₀ ℕ // (∑ i, (a i : ℤ)) = m}

def polynomialDegree (m : ℤ) : Submodule k (Polynomials k n) where
  carrier := {p | ∀ a : Index n →₀ ℕ, p.coeff a ≠ 0 → (∑ i, (a i : ℤ)) = m}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    intro a ha
    by_contra h
    simp [show p.coeff a = 0 by contrapose! h; exact hp a h,
      show q.coeff a = 0 by contrapose! h; exact hq a h] at ha
  smul_mem' r p hp := by
    intro a ha
    apply hp a
    intro h
    simp [h] at ha

def naturalExponent : (Index n →₀ ℕ) →+ ExponentVector n where
  toFun a i := a i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def polynomialToLaurent : Polynomials k n →ₐ[k] LaurentPolynomials k n :=
  AddMonoidAlgebra.mapDomainAlgHom k k (naturalExponent n)

def characteristic (J : Finset (Index n)) : ExponentVector n :=
  fun i ↦ if i ∈ J then 1 else 0

theorem laurentSingle_isUnit (a : ExponentVector n) :
    IsUnit (AddMonoidAlgebra.single a (1 : k) : LaurentPolynomials k n) := by
  refine isUnit_iff_exists_inv.mpr ⟨AddMonoidAlgebra.single (-a) 1, ?_⟩
  simp [AddMonoidAlgebra.one_def]

theorem polynomialToLaurent_chartProduct (J : Finset (Index n)) :
    polynomialToLaurent k n (chartProduct k n J) =
      AddMonoidAlgebra.single (characteristic n J) 1 := by
  classical
  unfold chartProduct
  rw [map_prod]
  have hvar (i : Index n) :
      polynomialToLaurent k n (variablePolynomial k n i) =
        AddMonoidAlgebra.single (characteristic n {i}) 1 := by
    change AddMonoidAlgebra.mapDomain (naturalExponent n)
      (AddMonoidAlgebra.single (Finsupp.single i 1) 1) = _
    rw [AddMonoidAlgebra.mapDomain_single]
    congr 1
    ext j
    simp [characteristic, naturalExponent, Finsupp.single_apply, eq_comm]
  simp_rw [hvar]
  induction J using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, AddMonoidAlgebra.one_def]
    congr 1
  | insert i J hi ih =>
    rw [Finset.prod_insert hi, ih, AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1
    ext j
    by_cases hji : j = i
    · subst j; simp [characteristic, hi]
    · simp [characteristic, hji]

theorem chartProduct_maps_to_unit (J : Finset (Index n))
    (x : Submonoid.powers (chartProduct k n J)) :
    IsUnit (polynomialToLaurent k n x.val) := by
  obtain ⟨t, ht⟩ := x.property
  rw [← ht, map_pow, polynomialToLaurent_chartProduct]
  exact (laurentSingle_isUnit k n _).pow _

instance chartScalarTower (J : Finset (Index n)) :
    IsScalarTower k (Polynomials k n) (ChartLocalization k n J) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)

/-- The unique extension of the polynomial embedding to the chart localization. -/
def chartToLaurent (J : Finset (Index n)) :
    ChartLocalization k n J →ₐ[k] LaurentPolynomials k n :=
  IsLocalization.liftAlgHom (chartProduct_maps_to_unit k n J)

def exponentSet (m : ℤ) (J : Finset (Index n)) : Set (ExponentVector n) :=
  {a | (∑ i, a i) = m ∧ negativeSupport n a ⊆ J}

def laurentPiece (m : ℤ) (J : Finset (Index n)) : Submodule k (LaurentPolynomials k n) :=
  AddMonoidAlgebra.supported k k (exponentSet n m J)

def chartPiece (m : ℤ) (J : Finset (Index n)) : Submodule k (ChartLocalization k n J) :=
  (laurentPiece k n m J).comap (chartToLaurent k n J).toLinearMap

def orderedComplex (m : ℤ)
    (sq : ∀ p, (differential k n m (p + 1)).comp (differential k n m p) = 0) :
    CochainComplex (ModuleCat.{u} k) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of k (Term k n m p))
    (fun p ↦ ModuleCat.ofHom (differential k n m p))
    (fun p ↦ ModuleCat.hom_ext (sq p))

abbrev Faces (p : ℤ) :=
  {J : Finset (Index n) // (J.card : ℤ) = p + 1 ∧ J.Nonempty}

abbrev LocalizedTerm (m p : ℤ) :=
  ∀ J : Faces n p, chartPiece k n m J.val

/-- The alternating sum using the actual further localizations. -/
def localizedDeleteSum (m p : ℤ) (x : LocalizedTerm k n m p)
    (J : Faces n (p + 1)) : ChartLocalization k n J.val :=
  ∑ i ∈ J.val, if h : (↑(J.val.erase i).card : ℤ) = p + 1 ∧ (J.val.erase i).Nonempty
    then sign k J.val i •
      localizationRestriction k n (Finset.erase_subset i J.val) (x ⟨J.val.erase i, h⟩).val
    else 0

namespace Expected

def fixedSquareZero : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (augmented : Bool) (a : ExponentVector n) (p : ℤ),
    (fixedD k augmented a (p + 1)).comp (fixedD k augmented a p) = 0

def differentialSquareZero : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (m p : ℤ),
    (differential k n m (p + 1)).comp (differential k n m p) = 0

def insertionContraction : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (augmented : Bool) (a : ExponentVector n)
    (j : Index n), j ∉ negativeSupport n a → (augmented = true ∨ (negativeSupport n a).Nonempty) →
    ∀ (p : ℤ) (x : Fixed k augmented a p),
      (∀ J, ¬ admissible augmented a (p - 1) J → insertAt k j x.val J = 0) ∧
      ∀ J, deleteSum k (insertAt k j x.val) J +
        insertAt k j (deleteSum k x.val) J = x.val J

/-- The ordinary localization carries exactly the indicated homogeneous piece, and
restricting to a larger intersection preserves its Laurent coefficients. -/
def chartCoefficientComparison : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    (∀ J (_hJ : J.Nonempty) (m : ℤ) (s : ChartLocalization k n J),
      s ∈ chartPiece k n m J ↔ ∃ a : DegreePiece k n J m, a.val = s) ∧
    (∀ (J K : Finset (Index n)) (h : J ⊆ K) (s : ChartLocalization k n J),
      chartToLaurent k n K (localizationRestriction k n h s) = chartToLaurent k n J s) ∧
    ∀ (J : Finset (Index n)) (m : ℤ),
      ∃ e : (exponentSet n m J →₀ k) ≃ₗ[k] chartPiece k n m J,
        ∀ f, chartToLaurent k n J (e f).val =
          AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain Subtype.val f)

/-- The integer-indexed polynomial piece agrees with the usual natural grading and is
zero in negative degrees. -/
def polynomialGrading : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    (∀ d : ℕ, polynomialDegree k n (d : ℤ) = grading k n d) ∧
    ∀ m : ℤ, m < 0 → polynomialDegree k n m = ⊥

/-- Reordering the finite chart factors and finitely supported monomials gives the
direct sum of exponent columns, intertwining the actual alternating restrictions. -/
def localizedComplexComparison : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (m : ℤ),
    ∃ e : ∀ p : ℤ, Term k n m p ≃ₗ[k] LocalizedTerm k n m p,
      (∀ p x (J : Faces n p) (a : Exponents n m),
        (chartToLaurent k n J.val (e p x J).val).coeff a.val = (x a).val J.val) ∧
      ∀ p x (J : Faces n (p + 1)),
        (e (p + 1) (differential k n m p x) J).val = localizedDeleteSum k n m p (e p x) J

/-- The cohomology identifications use the classes of the polynomial restrictions and
of the all-negative Laurent monomials in the stated ordered complex. -/
def cohomologyComputation : Prop := by
  classical
  exact ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n → ∀ m : ℤ,
    ∃ sq : ∀ p, (differential k n m (p + 1)).comp (differential k n m p) = 0,
      let C := orderedComplex k n m sq
      (∃ e : polynomialDegree k n m ≃ₗ[k] C.homology 0,
        ∀ f, ∃ z : C.cycles 0,
          C.homologyπ 0 z = e f ∧
          ∀ (J : Finset (Index n)) (a : Exponents n m), J.card = 1 →
            ((show Term k n m 0 from C.iCycles 0 z) a).val J = (polynomialToLaurent k n f.val).coeff a.val) ∧
      (∃ e : (TopExponents n m →₀ k) ≃ₗ[k] C.homology (n : ℤ),
        ∀ f, ∃ z : C.cycles (n : ℤ),
          C.homologyπ (n : ℤ) z = e f ∧
          ∀ a : Exponents n m, ((show Term k n m (n : ℤ) from C.iCycles (n : ℤ) z) a).val Finset.univ =
            if h : ∀ i, a.val i < 0 then f ⟨a, h⟩ else 0) ∧
      ∀ p : ℤ, 0 < p → p ≠ n → C.ExactAt p

end Expected

end DerivedFormalization.LaurentCechCohomology
