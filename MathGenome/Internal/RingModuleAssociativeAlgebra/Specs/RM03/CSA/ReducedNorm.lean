import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.ReducedCharpoly
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! The reduced norm assertions of RM03-C04.10. -/

namespace Specs.RM03.CSA

open scoped TensorProduct

set_option linter.checkUnivs false

universe u v w z

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {L : Type w} [Field L] [Algebra k L] {ι : Type z} [Fintype ι]

def ReducedNormType :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A → A → k

/-- The signed constant term of the reduced characteristic polynomial. -/
noncomputable def reducedNorm (hA : isCentralSimple k A) (a : A) : k :=
  (-1) ^ degree k A * (reducedCharpoly hA a).eval 0

def GenericReducedNormType :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι], isCentralSimple k A → (ι → A) → MvPolynomial ι k

/-- The norm polynomial of a formal linear combination with independent coordinates. -/
noncomputable def genericReducedNorm (hA : isCentralSimple k A) (a : ι → A) :
    MvPolynomial ι k :=
  (-1) ^ degree k A * (genericReducedCharpoly hA a).eval 0

def ReducedNormMap : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L] (hA : isCentralSimple k A) (a : A)
    (e : baseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L),
    algebraMap k L (reducedNorm hA a) = (e (1 ⊗ₜ[k] a)).det

def ReducedNormEqDet : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    (hA : isCentralSimple k A) (a : A)
    (e : A ≃ₐ[k] Matrix (Fin (degree k A)) (Fin (degree k A)) k),
    reducedNorm hA a = (e a).det

def GenericReducedNormMap : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] {L : Type w} [Field L] [Algebra k L]
    (hA : isCentralSimple k A) (a : ι → A)
    (e : baseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L),
    MvPolynomial.map (algebraMap k L) (genericReducedNorm hA a) =
      (genericMatrix fun i => e (1 ⊗ₜ[k] a i)).det

def GenericReducedNormHomogeneous : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] (hA : isCentralSimple k A) (a : ι → A),
    (genericReducedNorm hA a).IsHomogeneous (degree k A)

def GenericReducedNormEval : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] (hA : isCentralSimple k A) (a : ι → A) (x : ι → k),
    MvPolynomial.eval x (genericReducedNorm hA a) = reducedNorm hA (∑ i, x i • a i)

def ReducedNormBasisEval : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A) (a : A),
    MvPolynomial.eval (fun i => b.repr a i) (genericReducedNorm hA b) = reducedNorm hA a

def ReducedNormBasisTotalDegree : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] (hA : isCentralSimple k A) (b : Module.Basis ι k A),
    (genericReducedNorm hA b).totalDegree = degree k A

def GenericReducedNormBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] {L : Type w} [Field L] [Algebra k L]
    (hA : isCentralSimple k A) (a : ι → A)
    (hL : isCentralSimple L (baseChange k L A)),
    genericReducedNorm hL (fun i => 1 ⊗ₜ[k] a i) =
      MvPolynomial.map (algebraMap k L) (genericReducedNorm hA a)

def ReducedNormBasisBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] {L : Type w} [Field L] [Algebra k L]
    (hA : isCentralSimple k A) (b : Module.Basis ι k A)
    (hL : isCentralSimple L (baseChange k L A)),
    genericReducedNorm hL (b.baseChange L) =
      MvPolynomial.map (algebraMap k L) (genericReducedNorm hA b)

def GenericReducedNormEval₂ : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] {L : Type w} [Field L] [Algebra k L]
    (hA : isCentralSimple k A) (a : ι → A) (x : ι → L)
    (hL : isCentralSimple L (baseChange k L A)),
    MvPolynomial.eval₂ (algebraMap k L) x (genericReducedNorm hA a) =
      reducedNorm hL (∑ i, x i • (1 ⊗ₜ[k] a i))

def ReducedNormBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L] (hA : isCentralSimple k A) (a : A)
    (hL : isCentralSimple L (baseChange k L A)),
    reducedNorm hL (1 ⊗ₜ[k] a) = algebraMap k L (reducedNorm hA a)

def ReducedNormOne : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    (hA : isCentralSimple k A), reducedNorm hA 1 = 1

def ReducedNormMul : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    (hA : isCentralSimple k A) (a b : A),
    reducedNorm hA (a * b) = reducedNorm hA a * reducedNorm hA b

def ReducedNormNeZeroIffIsUnit : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    (hA : isCentralSimple k A) (a : A), reducedNorm hA a ≠ 0 ↔ IsUnit a

end Specs.RM03.CSA
