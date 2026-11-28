import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.Basic
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.InfinitesimalDeformations
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PowerSeries.Basic

/-! Scalar bases and statements for change of coordinates in LD02. -/

noncomputable section

open scoped TensorProduct
open LieModule.Cohomology

namespace Specs.LieNotes.Heisenberg.DeformationTransport

universe u

open _root_.LieAlgebrasAndRepresentations.InfinitesimalDeformations
  (Deformation bracketFormula shear)

variable {k A : Type u}

abbrev Carrier (A : Type u) := Fin 3 → A

/-- The scalar base k[t]/(t³). -/
abbrev Truncated (k : Type u) [Field k] := AdjoinRoot ((Polynomial.X : Polynomial k) ^ 3)

def truncatedParameter (k : Type u) [Field k] : Truncated k :=
  AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ 3)

/-- Apply t ↦ ε in the quotient, with ε² = 0. -/
def truncatedReduction (k : Type u) [Field k] : Truncated k →ₐ[k] DualNumber k :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId k (DualNumber k)) DualNumber.eps (by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, pow_succ, DualNumber.eps_pow_two, zero_mul])

/-- Retain the constant and linear terms of a formal series. -/
def formalReduction (k : Type u) [Field k] : PowerSeries k →+* DualNumber k where
  toFun p := ⟨PowerSeries.coeff 0 p, PowerSeries.coeff 1 p⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' p q := by
    apply TrivSqZeroExt.ext
    · exact map_add (PowerSeries.coeff 0) p q
    · exact map_add (PowerSeries.coeff 1) p q
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · change PowerSeries.coeff 0 (p * q) = PowerSeries.coeff 0 p * PowerSeries.coeff 0 q
      simp [PowerSeries.coeff_zero_eq_constantCoeff]
    · change PowerSeries.coeff 1 (p * q) =
        PowerSeries.coeff 0 p * PowerSeries.coeff 1 q + PowerSeries.coeff 1 p * PowerSeries.coeff 0 q
      rw [PowerSeries.coeff_mul]
      have h : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
      rw [h, Finset.sum_insert (by decide), Finset.sum_singleton]

variable [Field k] [CommRing A]

/-- The free scalar extension in the fixed Heisenberg basis. -/
def tensorCoordinates [Algebra k A] : (A ⊗[k] ModelValue k) ≃ₗ[A] Carrier A :=
  ((basisValue k).baseChange A).equivFun

def constantVector (ι : k →+* A) (p : ModelValue k) : Carrier A :=
  fun i => ι (p.coords i)

/-- Coordinate matrix of a k-linear endomorphism in the Heisenberg basis. -/
def coefficientMatrix (f : Module.End k (ModelValue k)) : Matrix (Fin 3) (Fin 3) k :=
  LinearMap.toMatrix' ((coordinatesValue k).conj f)

/-- Entrywise scalar extension of an endomorphism. -/
def extendedEnd (ι : k →+* A) (f : Module.End k (ModelValue k)) :
    Module.End A (Carrier A) :=
  ((coefficientMatrix f).map ι).toLin'

/-- Reduction of all three coordinates to k[ε], separated into the constant and
ε coefficients in the upstream first-order model. -/
def reduce (ρ : A →+* DualNumber k) (p : Carrier A) : ModelValue k × ModelValue k :=
  (⟨fun i => (ρ (p i)).fst⟩, ⟨fun i => (ρ (p i)).snd⟩)

/-- A Lie bracket on the free rank-three module over the scalar base. -/
@[ext] structure LieBracket (A : Type u) [CommRing A] where
  bracket : Carrier A →ₗ[A] Carrier A →ₗ[A] Carrier A
  alternating : ∀ p, bracket p p = 0
  jacobi : ∀ p q r, bracket p (bracket q r) + bracket q (bracket r p) +
    bracket r (bracket p q) = 0

def ReducesTo (ρ : A →+* DualNumber k) (B : LieBracket A)
    (c : twoCochain k (ModelValue k) (ModelValue k)) : Prop :=
  ∀ p q, reduce ρ (B.bracket p q) = bracketFormula c (reduce ρ p) (reduce ρ q)

/-- Pullback of the bilinear operation along a change of basis. -/
def pullbackMap (T : Carrier A ≃ₗ[A] Carrier A) (B : LieBracket A) :
    Carrier A →ₗ[A] Carrier A →ₗ[A] Carrier A :=
  (B.bracket.compl₁₂ T.toLinearMap T.toLinearMap).compr₂ T.symm.toLinearMap

def tensorCoordinatesType := ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A],
  (A ⊗[k] ModelValue k) ≃ₗ[A] Carrier A

def tensorCoordinatesValue : tensorCoordinatesType := fun _ _ _ _ _ => tensorCoordinates

def scalarExtensionType : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (f : Module.End k (ModelValue k)) (a : A) (p : ModelValue k),
    tensorCoordinates (a ⊗ₜ[k] p) = a • constantVector (algebraMap k A) p ∧
    extendedEnd (algebraMap k A) f (tensorCoordinates (a ⊗ₜ[k] p)) =
      tensorCoordinates (a ⊗ₜ[k] f p)

/-- The two scalar reductions realize reduction modulo t². -/
def modTwoReductionsType : Prop :=
  ∀ (k : Type u) [Field k],
    Function.Surjective (truncatedReduction k) ∧
    (∀ a, truncatedReduction k a = 0 ↔ truncatedParameter k ^ 2 ∣ a) ∧
    Function.Surjective (formalReduction k) ∧
    (∀ a, formalReduction k a = 0 ↔ (PowerSeries.X : PowerSeries k) ^ 2 ∣ a)

def firstOrderTransportType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (c c' : twoCochain k (ModelValue k) (ModelValue k)) (f : Module.End k (ModelValue k)),
    c' = c + d₁₂ k (ModelValue k) (ModelValue k) f →
    ∀ p q, shear f (bracketFormula c' p q) = bracketFormula c (shear f p) (shear f q)

def truncatedTransportType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (f : Module.End k (ModelValue k)),
    let t := truncatedParameter k
    let F := extendedEnd (algebraMap k (Truncated k)) f
    ∃ T : Carrier (Truncated k) ≃ₗ[Truncated k] Carrier (Truncated k),
      T.toLinearMap = 1 + t • F ∧
      T.symm.toLinearMap = 1 - t • F + t ^ 2 • F ^ 2 ∧
      ∀ p, reduce (truncatedReduction k).toRingHom (T p) =
        shear f (reduce (truncatedReduction k).toRingHom p)

def formalTransportType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (f : Module.End k (ModelValue k)),
    ∃ T : Carrier (PowerSeries k) ≃ₗ[PowerSeries k] Carrier (PowerSeries k),
      T.toLinearMap = 1 + (PowerSeries.X : PowerSeries k) • extendedEnd PowerSeries.C f ∧
      (∀ n p i, PowerSeries.coeff n (T.symm (constantVector PowerSeries.C p) i) =
        (((-f) ^ n) p).coords i) ∧
      ∀ p, reduce (formalReduction k) (T p) = shear f (reduce (formalReduction k) p)

def pullbackType := ∀ (A : Type u) [CommRing A],
  (Carrier A ≃ₗ[A] Carrier A) → LieBracket A → LieBracket A

def pullbackValue : pullbackType := fun _ _ T B =>
  { bracket := pullbackMap T B
    alternating := by
      intro p
      change T.symm (B.bracket (T p) (T p)) = 0
      rw [B.alternating, map_zero]
    jacobi := by
      intro p q r
      change T.symm (B.bracket (T p) (T (T.symm (B.bracket (T q) (T r))))) +
        T.symm (B.bracket (T q) (T (T.symm (B.bracket (T r) (T p))))) +
        T.symm (B.bracket (T r) (T (T.symm (B.bracket (T p) (T q))))) = 0
      rw [T.apply_symm_apply, T.apply_symm_apply, T.apply_symm_apply,
        ← map_add, ← map_add, B.jacobi, map_zero] }

def pullbackReductionType : Prop :=
  ∀ (k A : Type u) [Field k] [CharZero k] [CommRing A]
    (ρ : A →+* DualNumber k) (B : LieBracket A)
    (T : Carrier A ≃ₗ[A] Carrier A) (f : Module.End k (ModelValue k))
    (c c' : twoCochain k (ModelValue k) (ModelValue k)),
    (∀ p, reduce ρ (T p) = shear f (reduce ρ p)) →
    c' = c + d₁₂ k (ModelValue k) (ModelValue k) f →
    (ReducesTo ρ (pullbackValue A T B) c' ↔ ReducesTo ρ B c)

def extensionsEquivalentType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (c c' : twoCochain k (ModelValue k) (ModelValue k)) (f : Module.End k (ModelValue k)),
    c' = c + d₁₂ k (ModelValue k) (ModelValue k) f →
    ((∃ B, ReducesTo (truncatedReduction k).toRingHom B c) ↔
      ∃ B, ReducesTo (truncatedReduction k).toRingHom B c') ∧
    ((∃ B, ReducesTo (formalReduction k) B c) ↔
      ∃ B, ReducesTo (formalReduction k) B c')

/-- An extension reduces to the given actual first-order bracket. -/
def Extends (ρ : A →+* DualNumber k) (D : Deformation k (ModelValue k)) : Prop :=
  ∃ B : LieBracket A, ∀ p q, reduce ρ (B.bracket p q) = D.bracket (reduce ρ p) (reduce ρ q)

/-- If D and D' are related by the specified first-order change, their actual
brackets have the same extension properties. -/
def actualExtensionsEquivalentType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (D D' : Deformation k (ModelValue k))
    (f : Module.End k (ModelValue k)),
    (∀ p q, shear f (D'.bracket p q) = D.bracket (shear f p) (shear f q)) →
    (Extends (truncatedReduction k).toRingHom D ↔ Extends (truncatedReduction k).toRingHom D') ∧
    (Extends (formalReduction k) D ↔ Extends (formalReduction k) D')

end Specs.LieNotes.Heisenberg.DeformationTransport
