import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.ZornModel
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

namespace LinearAlgebraicGroups.Albert.CliffordSpecification

open CliffordAlgebra Module

set_option linter.checkUnivs false
open scoped TensorProduct

universe u v w z

section Basis

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {I : Type w} [LinearOrder I]

/-- The product of basis vectors indexed by a finite subset, in increasing order. -/
noncomputable def orderedWord (q : QuadraticForm R V) (b : Basis I R V)
    (s : Finset I) : CliffordAlgebra q :=
  (List.ofFn fun i => ι q (b (Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofCard (s := s) rfl) i))).prod

def orderedWordType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm R V) (_b : Basis I R V),
    Finset I → CliffordAlgebra q

def orderedBasisType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm R V) (b : Basis I R V),
    ∃ B : Basis (Finset I) R (CliffordAlgebra q), ∀ s, B s = orderedWord q b s

def vectorSummandType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm R V) (_b : Basis I R V),
    ∃ p : CliffordAlgebra q →ₗ[R] V, p.comp (ι q) = LinearMap.id

def paritySpanType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] (q : QuadraticForm R V) (b : Basis I R V) (k : ZMod 2),
    evenOdd q k = Submodule.span R (orderedWord q b '' {s | (s.card : ZMod 2) = k})

end Basis

/-- Extend the triangular matrix of diagonal and cross coefficients to the new scalars. -/
noncomputable def coefficientForm {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V] {I : Type w} [LinearOrder I]
    (S : Type z) [CommRing S] [Algebra R S] (q : QuadraticForm R V) (b : Basis I R V) :
    QuadraticForm S (S ⊗[R] V) :=
  (LinearMap.BilinForm.baseChange S (q.toBilin b)).toQuadraticMap

def coefficientFormType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] (S : Type z) [CommRing S] [Algebra R S]
    (_q : QuadraticForm R V) (_b : Basis I R V), QuadraticForm S (S ⊗[R] V)

def coefficientFormUniqueType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] (S : Type z) [CommRing S] [Algebra R S]
    (q : QuadraticForm R V) (b : Basis I R V) (Q : QuadraticForm S (S ⊗[R] V)),
    Q = coefficientForm S q b ↔ ∀ x, Q (1 ⊗ₜ[R] x) = algebraMap R S (q x)


def coefficientFormAgreementType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    [Module.Projective R V] {I : Type w} [LinearOrder I]
    (S : Type z) [CommRing S] [Algebra R S] (q : QuadraticForm R V) (b : Basis I R V),
    coefficientForm S q b = Composition.Specification.normBaseChange S q

def baseChangeType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] (S : Type z) [CommRing S] [Algebra R S]
    (q : QuadraticForm R V) (b : Basis I R V),
    ∃ e : S ⊗[R] CliffordAlgebra q ≃ₐ[S] CliffordAlgebra (coefficientForm S q b),
      (∀ a x, e (a ⊗ₜ[R] ι q x) = ι _ (a ⊗ₜ[R] x)) ∧
      (∀ s, e (1 ⊗ₜ[R] orderedWord q b s) =
        orderedWord (coefficientForm S q b) (b.baseChange S) s) ∧
      (∀ k, ((evenOdd q k).baseChange S).map e.toLinearEquiv.toLinearMap =
        evenOdd (coefficientForm S q b) k) ∧
      (∀ x, e ((reverse (Q := q)).baseChange S x) = reverse (e x))


/-- The operator on the exterior algebra for a hyperbolic vector `(φ, x)`. -/
def hyperbolicOperator {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] :
    Module.Dual R V × V →ₗ[R] Module.End R (ExteriorAlgebra R V) :=
  (Algebra.lmul R (ExteriorAlgebra R V)).toLinearMap ∘ₗ ExteriorAlgebra.ι R ∘ₗ
    LinearMap.snd R (Module.Dual R V) V +
  contractLeft (Q := (0 : QuadraticForm R V)) ∘ₗ LinearMap.fst R (Module.Dual R V) V

/-- The exterior representation, its even blocks and the scalar vector centralizer.
The parity submodules of the exterior algebra are the sums of its even and odd powers. -/
def hyperbolicModelType :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {I : Type w} [LinearOrder I] [Fintype I] (_b : Basis I R V),
    ∃ e : CliffordAlgebra (QuadraticForm.dualProd R V) ≃ₐ[R]
        Module.End R (ExteriorAlgebra R V),
      (∀ x, e (ι _ x) = hyperbolicOperator x) ∧
      (∀ a, a ∈ evenOdd (QuadraticForm.dualProd R V) 0 ↔
        ∀ k x, x ∈ evenOdd (0 : QuadraticForm R V) k →
          e a x ∈ evenOdd (0 : QuadraticForm R V) k) ∧
      (∀ a, (∀ x, Commute a (ι (QuadraticForm.dualProd R V) x)) ↔
        ∃ r : R, a = algebraMap R _ r)

section Octonions

open _root_.LinearAlgebraicGroups.Composition
open Composition.Zorn Composition.ZornSpecification Composition.AdjointSpecification

variable {R : Type u} [CommRing R]

/-- Left multiplication by the two octonion coordinates of a Clifford vector. -/
def octonionOperator : Zorn R →ₗ[R] Module.End R (Zorn R × Zorn R) where
  toFun c := ((LinearMap.mul R (Zorn R) c).comp (LinearMap.snd R _ _)).prod
    ((LinearMap.mul R (Zorn R) (conjugate (norm R) c)).comp (LinearMap.fst R _ _))
  map_add' c d := by
    apply LinearMap.ext
    intro x
    ext <;> simp
  map_smul' a c := by
    apply LinearMap.ext
    intro x
    ext <;> simp

/-- The orthogonal sum of the full octonion polar pairing with itself. -/
def octonionPairing : LinearMap.BilinForm R (Zorn R × Zorn R) :=
  (norm R).polarBilin.compl₁₂ (LinearMap.fst R _ _) (LinearMap.fst R _ _) +
    (norm R).polarBilin.compl₁₂ (LinearMap.snd R _ _) (LinearMap.snd R _ _)

/-- The full split-octonion matrix model, with the two diagonal blocks and reversion. -/
def octonionModelType :=
  ∀ (R : Type u) [CommRing R],
    ∃ e : CliffordAlgebra (norm R) ≃ₐ[R] Module.End R (Zorn R × Zorn R),
      (∀ c, e (ι _ c) = octonionOperator c) ∧
      (∀ a, a ∈ evenOdd (norm R) 0 ↔
        (∀ x, (e a (x, 0)).2 = 0) ∧ (∀ y, (e a (0, y)).1 = 0)) ∧
      (∀ a, LinearMap.IsAdjointPair octonionPairing octonionPairing (e a) (e (reverse a)))

end Octonions

end LinearAlgebraicGroups.Albert.CliffordSpecification
