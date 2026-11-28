import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Heisenberg.AdjointCohomology
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.DeformationObstructions
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PowerSeries.Basic

/-! The normalized representative in LD02, with the left-nested Jacobiator. -/

noncomputable section

namespace Specs.LieNotes.Heisenberg.NormalizedObstruction

open _root_.AdvancedHomologicalAlgebra.CE
open _root_.LieAlgebrasAndRepresentations.AbelianExtensions
open _root_.LieAlgebrasAndRepresentations.DeformationObstructions
open LieModule.Cohomology
open scoped TensorProduct Polynomial PowerSeries

universe u v

variable {k : Type u} [Field k]

abbrev Cochain (k : Type u) [Field k] := twoCochain k (ModelValue k) (ModelValue k)

def normalized (a b c d e : k) : Cochain k :=
  exteriorCochain (phiExteriorValue k a b c d e)

/-- The coefficient sequence of the normalized bracket through degree one. -/
def coefficients (a b c d e : k) : ℕ → Cochain k
  | 0 => originalBracket
  | 1 => normalized a b c d e
  | _ + 2 => 0

/-- Scalar extension of a cochain to the actual tensor product. -/
def extendCochain (A : Type v) [CommRing A] [Algebra k A] (f : Cochain k) :
    (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k) :=
  ((Module.End.baseChangeHom k A (ModelValue k)).toLinearMap.comp f.1).liftBaseChange A

/-- The operation μ + tφ + t²ψ on the scalar extension. -/
def bracket {A : Type v} [CommRing A] [Algebra k A] (t : A)
    (a b c d e : k) (ψ : Cochain k) :
    (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k) →ₗ[A] (A ⊗[k] ModelValue k) :=
  extendCochain A originalBracket + t • extendCochain A (normalized a b c d e) +
    t ^ 2 • extendCochain A ψ

section LieBracket

variable {A V : Type*} [CommRing A] [AddCommGroup V] [Module A V]

def cyclicJacobiator (B : V →ₗ[A] V →ₗ[A] V) (p q r : V) : V :=
  B (B p q) r + B (B q r) p + B (B r p) q

/-- Alternation and Jacobi for an already bilinear operation. -/
def IsLieBracket (B : V →ₗ[A] V →ₗ[A] V) : Prop :=
  (∀ p, B p p = 0) ∧ ∀ p q r, cyclicJacobiator B p q r = 0

end LieBracket

abbrev truncationIdeal (k : Type u) [Field k] : Ideal k[X] :=
  Ideal.span {(Polynomial.X : k[X]) ^ 3}

abbrev TruncatedBase (k : Type u) [Field k] := k[X] ⧸ truncationIdeal k

def truncatedParameter (k : Type u) [Field k] : TruncatedBase k :=
  Ideal.Quotient.mk (truncationIdeal k) Polynomial.X

def Equations (a b c d e : k) : Prop :=
  c * d - e * a = 0 ∧ e * b + c * a = 0

def ExtendCochainType : Prop :=
  ∀ (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    (f : Cochain k) (s t : A) (p q : ModelValue k),
    extendCochain A f (s ⊗ₜ[k] p) (t ⊗ₜ[k] q) = (s * t) ⊗ₜ[k] f p q

def FirstOrderType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (a b c d e : k),
    ∃ D : TruncatedDeformation (k := k) (g := ModelValue k) 2,
      D.coeff = coefficients a b c d e

def ObstructionType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (a b c d e : k),
    obstruction (coefficients a b c d e) 2 (xValue k) (yValue k) (zValue k) =
      (c * d - e * a) • xValue k - (e * b + c * a) • yValue k

def OrderTwoType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (a b c d e : k) (ψ : Cochain k),
    let D := coefficients a b c d e
    let x := xValue k
    let y := yValue k
    let z := zValue k
    jacobiCoefficient (Function.update D 2 ψ) 2 x y z =
      obstruction D 2 x y z - AdjointCohomology.d k (ModelValue k) 2 (cochainExterior ψ)
        (wedge k (ModelValue k) 3 ![x, y, z]) ∧
    AdjointCohomology.d k (ModelValue k) 2 (cochainExterior ψ)
        (wedge k (ModelValue k) 3 ![x, y, z]) ∈ centerLineValue k

def QuotientComparisonType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (a b c d e : k)
    (D : TruncatedDeformation (k := k) (g := ModelValue k) 2)
    (_hD : D.coeff = coefficients a b c d e) (ψ : Cochain k),
    IsLieBracket (bracket (truncatedParameter k) a b c d e ψ) ↔ Extends D ψ

def ExtensionType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (a b c d e : k),
    (∃ ψ : Cochain k, IsLieBracket (bracket (truncatedParameter k) a b c d e ψ)) ↔
      Equations a b c d e

def LinearBracketType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (A : Type v) [CommRing A] [Algebra k A]
    (t : A) (a b c d e : k), Equations a b c d e →
      IsLieBracket (bracket t a b c d e 0)

def PolynomialFormalType : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (a b c d e : k), Equations a b c d e →
    IsLieBracket (bracket (Polynomial.X : k[X]) a b c d e 0) ∧
    IsLieBracket (bracket (PowerSeries.X : k⟦X⟧) a b c d e 0)

end Specs.LieNotes.Heisenberg.NormalizedObstruction
