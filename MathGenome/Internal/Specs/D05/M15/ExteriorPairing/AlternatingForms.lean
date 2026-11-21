import MathGenome.Internal.Specs.D05.M15.ExteriorPairing
import MathGenome.Internal.Specs.D05.M15.InteriorProduct
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Algebra.DirectSum.Module

/-! Independent interface for paper.tex:3098–3108. Scalar forms are actual
alternating multilinear maps. The product uses the division-free coset shuffle
construction; `shuffle_formula` separately specifies the ordered representatives.
All equivalences with *all* forms require finite dimension. -/
noncomputable section
open scoped Classical
namespace Specs.D05.M15.ExteriorPairing.AlternatingForms
universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

abbrev Form (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V]
    (p : ℕ) := AlternatingMap K V K (Fin p)

/-- Evaluation through the existing determinant pairing. -/
def toForm (p : ℕ) : (⋀[K]^p (Module.Dual K V)) →ₗ[K] Form K V p :=
  exteriorPower.alternatingMapLinearEquiv.symm.toLinearMap.comp
    (pairing_value K V p)

/-- The actual homogeneous multiplication in the exterior quotient. -/
def wedge {p q : ℕ} (a : ⋀[K]^p (Module.Dual K V))
    (b : ⋀[K]^q (Module.Dual K V)) : ⋀[K]^(p+q) (Module.Dual K V) :=
  ⟨(a : _root_.ExteriorAlgebra K (Module.Dual K V)) * b,
    SetLike.GradedMul.mul_mem a.property b.property⟩

/-- The unnormalized shuffle product. No factorial or characteristic restriction. -/
def shuffleProduct {p q : ℕ} (B : Form K V p) (C : Form K V q) : Form K V (p+q) :=
  ((LinearMap.mul' K K).compAlternatingMap (B.domCoprod C)).domDomCongr
    finSumFinEquiv

/-- Bilinear structure of the division-free shuffle product. -/
def shuffleBilinear (p q : ℕ) : Form K V p →ₗ[K] Form K V q →ₗ[K] Form K V (p+q) :=
  LinearMap.mk₂ K (fun B C => shuffleProduct B C)
    (by
      intro B B' C
      simp only [shuffleProduct,
        ← AlternatingMap.domCoprod'_apply, TensorProduct.add_tmul, map_add,
        LinearMap.compAlternatingMap_add, AlternatingMap.domDomCongr_add])
    (by
      intro c B C
      simp only [shuffleProduct,
        ← AlternatingMap.domCoprod'_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
        LinearMap.compAlternatingMap_smul, AlternatingMap.domDomCongr_smul])
    (by
      intro B C C'
      simp only [shuffleProduct,
        ← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_add, map_add,
        LinearMap.compAlternatingMap_add, AlternatingMap.domDomCongr_add])
    (by
      intro c B C
      simp only [shuffleProduct,
        ← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_smul, map_smul,
        LinearMap.compAlternatingMap_smul, AlternatingMap.domDomCongr_smul])

/-- A permutation is a shuffle exactly when each block is increasing. -/
def IsShuffle (p q : ℕ) (σ : Equiv.Perm (Fin (p+q))) : Prop :=
  StrictMono (fun i : Fin p => σ (Fin.castAdd q i)) ∧
    StrictMono (fun j : Fin q => σ (Fin.natAdd p j))

/-- Ordinary product of covector values, before antisymmetrizing. -/
def covectorTensorForm (p : ℕ) (f : Fin p → Module.Dual K V) :
    MultilinearMap K (fun _ : Fin p => V) K :=
  (MultilinearMap.mkPiAlgebra K (Fin p) K).compLinearMap f

/-- Averaged alternation uses the inverse factorial, separately from shuffles. -/
def averageForm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : MultilinearMap K (fun _ : ι => V) K) : AlternatingMap K V K ι :=
  ((Fintype.card ι).factorial : K)⁻¹ • T.alternatization

/-- The unalternated tensor product of two forms, with scalar multiplication
of the two outputs. Its indices are the disjoint union of the two blocks. -/
def tensorForm {p q : ℕ} (B : Form K V p) (C : Form K V q) :
    MultilinearMap K (fun _ : Fin p ⊕ Fin q => V) K :=
  (LinearMap.mul' K K).compMultilinearMap
    (MultilinearMap.domCoprod B.toMultilinearMap C.toMultilinearMap)

abbrev toForm_type := (K : Type u) → (V : Type v) → [Field K] →
  [AddCommGroup V] → [Module K V] → (p : ℕ) →
    (⋀[K]^p (Module.Dual K V)) →ₗ[K] Form K V p
abbrev toForm_value : toForm_type := fun _ _ _ _ _ => toForm

abbrev shuffleProduct_type := (K : Type u) → (V : Type v) → [Field K] →
  [AddCommGroup V] → [Module K V] → {p q : ℕ} →
    Form K V p → Form K V q → Form K V (p+q)
abbrev shuffleProduct_value : shuffleProduct_type := fun _ _ _ _ _ => shuffleProduct

def evaluation : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (p : ℕ) (a : ⋀[K]^p (Module.Dual K V)) (x : Fin p → V),
  toForm p a x = pairing_value K V p a (exteriorPower.ιMulti K p x)

def elementary : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (p : ℕ) (f : Fin p → Module.Dual K V) (x : Fin p → V),
  toForm p (exteriorPower.ιMulti K p f) x = Matrix.det (fun i j => f i (x j))

def identification : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (p : ℕ),
  ∃ e : (⋀[K]^p (Module.Dual K V)) ≃ₗ[K] Form K V p,
    e.toLinearMap = toForm p

def shuffle_formula : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (p q : ℕ) (B : Form K V p) (C : Form K V q)
  (x : Fin (p+q) → V),
  shuffleProduct B C x = ∑ σ : {σ : Equiv.Perm (Fin (p+q)) // IsShuffle p q σ},
    Equiv.Perm.sign σ.val •
      (B (fun i => x (σ.val (Fin.castAdd q i))) *
       C (fun j => x (σ.val (Fin.natAdd p j))))

def multiplication : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (p q : ℕ)
  (a : ⋀[K]^p (Module.Dual K V)) (b : ⋀[K]^q (Module.Dual K V)),
  toForm (p+q) (wedge a b) = shuffleProduct (toForm p a) (toForm q b)

/-- Associativity includes the reindexing needed for the different degree sums. -/
def associativity : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (p q r : ℕ)
  (B : Form K V p) (C : Form K V q) (D : Form K V r),
  (shuffleProduct (shuffleProduct B C) D).domDomCongr
    (finCongr (Nat.add_assoc p q r)) = shuffleProduct B (shuffleProduct C D)

def graded_commutativity : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (p q : ℕ)
  (B : Form K V p) (C : Form K V q),
  shuffleProduct B C = (-1 : K)^(p*q) •
    (shuffleProduct C B).domDomCongr (finCongr (Nat.add_comm q p))

def degree_zero : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (c : K) (x : Fin 0 → V),
  toForm 0 ((exteriorPower.zeroEquiv K (Module.Dual K V)).symm c) x = c

def tensor_normalization : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [CharZero K] (p : ℕ) (f : Fin p → Module.Dual K V),
  toForm p (exteriorPower.ιMulti K p f) =
    (p.factorial : K) • averageForm (covectorTensorForm p f)

def product_normalization : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [CharZero K] (p q : ℕ)
  (B : Form K V p) (C : Form K V q),
  shuffleProduct B C =
    (((p+q).factorial : K) / ((p.factorial : K) * (q.factorial : K))) •
      (averageForm (tensorForm B C)).domDomCongr finSumFinEquiv

/-- Contraction of exterior covectors by evaluation at a vector is ordinary
first-slot insertion under the determinant pairing, with no extra multiplier. -/
def insertion : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] (p : ℕ)
  (a : ⋀[K]^(p+1) (Module.Dual K V)) (v : V),
  ∃ b : ⋀[K]^p (Module.Dual K V),
    (b : _root_.ExteriorAlgebra K (Module.Dual K V)) =
      InteriorProduct.interior (Module.Dual.eval K V v) a ∧
    toForm p b = (toForm (p+1) a).curryLeft v

/-- A scalar form has zero contraction; there is no negative-degree component. -/
def insertion_degree_zero : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] (c : K) (v : V),
  InteriorProduct.interior (Module.Dual.eval K V v)
    (((exteriorPower.zeroEquiv K (Module.Dual K V)).symm c) :
      _root_.ExteriorAlgebra K (Module.Dual K V)) = 0

open scoped DirectSum

/-- Finite sums of homogeneous alternating forms. -/
abbrev Forms (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V] :=
  ⨁ p : ℕ, Form K V p

/-- The bilinear Cauchy product on finite sums, using the shuffle product in
each pair of degrees. It is defined independently of any exterior-algebra map. -/
def formsMul : Forms K V →ₗ[K] Forms K V →ₗ[K] Forms K V :=
  DirectSum.toModule K ℕ _ (fun p =>
    (DirectSum.toModule K ℕ _ (fun q =>
      ((shuffleBilinear (K := K) (V := V) p q).flip).compr₂
        (DirectSum.lof K ℕ (Form K V) (p+q)))).flip)

/-- A scalar-preserving, multiplicative linear equivalence on the entire algebra
of finite sums. The homogeneous equation makes its grading explicit. Together
with the separately specified product and unit, these are algebra-equivalence
laws, without hiding a ring structure in a transported definition. -/
def graded_algebra_equivalence : Prop := ∀ {K : Type u} {V : Type v} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  ∃ e : _root_.ExteriorAlgebra K (Module.Dual K V) ≃ₗ[K] Forms K V,
    (∀ (p : ℕ) (a : ⋀[K]^p (Module.Dual K V)),
      e a = DirectSum.lof K ℕ (Form K V) p (toForm p a)) ∧
    (∀ a b, e (a*b) = formsMul (e a) (e b)) ∧
    e 1 = DirectSum.lof K ℕ (Form K V) 0 (AlternatingMap.constOfIsEmpty K V (Fin 0) 1)

end Specs.D05.M15.ExteriorPairing.AlternatingForms
