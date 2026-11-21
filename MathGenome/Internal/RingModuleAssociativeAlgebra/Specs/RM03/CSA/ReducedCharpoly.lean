import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.Degree
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Reduced characteristic polynomials in RM03-C04.10. -/

namespace Specs.RM03.CSA

open scoped TensorProduct
open Algebra.TensorProduct

set_option linter.checkUnivs false

universe u v w z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {ι : Type z} [Fintype ι] {L : Type w} [Field L] [Algebra k L]

/-- The matrix of a finite family with independent variables as coefficients. -/
noncomputable def genericMatrix {R : Type*} [CommRing R] {n : ℕ}
    (M : ι → Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (MvPolynomial ι R) :=
  ∑ i, (MvPolynomial.X i : MvPolynomial ι R) • (M i).map MvPolynomial.C

/-- The coefficient extension of a polynomial in the characteristic variable and
in the independent variables for the family. -/
noncomputable abbrev mapGeneric (f : k →+* L) (p : Polynomial (MvPolynomial ι k)) :
    Polynomial (MvPolynomial ι L) := p.map (MvPolynomial.map f)

def GenericReducedCharpolyType :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι],
    isCentralSimple k A → (ι → A) → Polynomial (MvPolynomial ι k)

/-- The canonical coefficient preimage of the generic characteristic polynomial
in a matrix splitting over the algebraic closure. -/
noncomputable def genericReducedCharpoly (_hA : isCentralSimple k A) (a : ι → A) :
    Polynomial (MvPolynomial ι k) := by
  classical
  let P := fun p : Polynomial (MvPolynomial ι k) =>
    ∃ e : baseChange k (AlgebraicClosure k) A ≃ₐ[AlgebraicClosure k]
        Matrix (Fin (degree k A)) (Fin (degree k A)) (AlgebraicClosure k),
      mapGeneric (algebraMap k (AlgebraicClosure k)) p =
        (genericMatrix fun i => e (1 ⊗ₜ[k] a i)).charpoly
  exact if h : ∃ p, P p then h.choose else 0

def GenericReducedCharpolyMap : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] {L : Type w} [Field L] [Algebra k L]
    (hA : isCentralSimple k A) (a : ι → A)
    (e : baseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L),
    mapGeneric (algebraMap k L) (genericReducedCharpoly hA a) =
      (genericMatrix fun i => e (1 ⊗ₜ[k] a i)).charpoly

def GenericReducedCharpolyBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] {L : Type w} [Field L] [Algebra k L]
    (hA : isCentralSimple k A) (a : ι → A)
    (hL : isCentralSimple L (baseChange k L A)),
    genericReducedCharpoly hL (fun i => 1 ⊗ₜ[k] a i) =
      mapGeneric (algebraMap k L) (genericReducedCharpoly hA a)

def ReducedCharpolyType :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A],
    isCentralSimple k A → A → Polynomial k

/-- The reduced characteristic polynomial is the single-element specialization
of the generic reduced characteristic polynomial. -/
noncomputable def reducedCharpoly (hA : isCentralSimple k A) (a : A) : Polynomial k :=
  (genericReducedCharpoly hA (fun _ : Unit => a)).map (MvPolynomial.eval fun _ => 1)

def ReducedCharpolyMap : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L] (hA : isCentralSimple k A) (a : A)
    (e : baseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L),
    (reducedCharpoly hA a).map (algebraMap k L) = (e (1 ⊗ₜ[k] a)).charpoly

def ReducedCharpolyMapIff : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L] (hA : isCentralSimple k A) (a : A)
    (e : baseChange k L A ≃ₐ[L] Matrix (Fin (degree k A)) (Fin (degree k A)) L)
    (p : Polynomial k),
    p.map (algebraMap k L) = (e (1 ⊗ₜ[k] a)).charpoly ↔ p = reducedCharpoly hA a

def ReducedCharpolyBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {L : Type w} [Field L] [Algebra k L] (hA : isCentralSimple k A) (a : A)
    (hL : isCentralSimple L (baseChange k L A)),
    reducedCharpoly hL (1 ⊗ₜ[k] a) = (reducedCharpoly hA a).map (algebraMap k L)

def GenericReducedCharpolyEval : Prop :=
  ∀ {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    {ι : Type z} [Fintype ι] (hA : isCentralSimple k A) (a : ι → A) (x : ι → k),
    (genericReducedCharpoly hA a).map (MvPolynomial.eval x) =
      reducedCharpoly hA (∑ i, x i • a i)

end Specs.RM03.CSA
