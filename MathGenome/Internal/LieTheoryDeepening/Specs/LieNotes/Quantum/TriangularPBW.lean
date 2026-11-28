import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Presentation
import Mathlib.Algebra.Algebra.Bilinear

/-! The ordered multiplication, PBW monomials, and rank-one subalgebras in type A₂. -/

noncomputable section

open scoped TensorProduct

namespace Specs.LieNotes.Quantum.TriangularPBW

open Presentation

universe u v w

section Multiplication

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

abbrev SerreTensor (C : Cartan A T) :=
  (SerrePresentation.SerreAlgebra A C.q ⊗[A] T) ⊗[A] SerrePresentation.SerreAlgebra A C.q

def negative (C : Cartan A T) : SerrePresentation.SerreAlgebra A C.q →ₐ[A] U C :=
  SerrePresentation.lift C.q (F C)
    ((serre_relations C).neg 0 1 (by decide)) ((serre_relations C).neg 1 0 (by decide))

def positive (C : Cartan A T) : SerrePresentation.SerreAlgebra A C.q →ₐ[A] U C :=
  SerrePresentation.lift C.q (E C)
    ((serre_relations C).pos 0 1 (by decide)) ((serre_relations C).pos 1 0 (by decide))

/-- The multiplication map sends `(f ⊗ t) ⊗ e` to the product of the three images
in negative, Cartan, positive order. -/
def multiplication (C : Cartan A T) : SerreTensor C →ₗ[A] U C :=
  let mul := LinearMap.mul' A (U C)
  let lower := mul.comp (TensorProduct.map (negative C).toLinearMap (cartan C).toLinearMap)
  mul.comp (TensorProduct.map lower (positive C).toLinearMap)

def multiplicationEquiv (C : Cartan A T) (h : Function.Bijective (multiplication C)) :
    SerreTensor C ≃ₗ[A] U C :=
  LinearEquiv.ofBijective (multiplication C) h

def zMinus (C : Cartan A T) : U C :=
  F C 0 * F C 1 - (↑(C.q⁻¹) : A) • (F C 1 * F C 0)

def zPlus (C : Cartan A T) : U C :=
  E C 0 * E C 1 - (↑(C.q⁻¹) : A) • (E C 1 * E C 0)

abbrev Exponents := ℕ × ℕ × ℕ

abbrev PBWIndex (ι : Type w) := (Exponents × ι) × Exponents

/-- One ordered PBW monomial at a specified Cartan monomial `t`. -/
def orderedMonomial (C : Cartan A T) (f : Exponents) (t : T) (e : Exponents) : U C :=
  (F C 0 ^ f.1 * zMinus C ^ f.2.1 * F C 1 ^ f.2.2) * cartan C t *
    (E C 0 ^ e.1 * zPlus C ^ e.2.1 * E C 1 ^ e.2.2)

def HasTriangularPBW {ι : Type w} (C : Cartan A T) (monomial : ι → T) : Prop :=
  Function.Bijective (multiplication C) ∧
    ∃ b : Module.Basis (PBWIndex ι) A (U C),
      ∀ i, b i = orderedMonomial C i.1.1 (monomial i.1.2) i.2

end Multiplication

def genericProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    HasTriangularPBW (generic q hq)
      (fun m : Lattice => AddMonoidAlgebra.single m (1 : k))

def indeterminateProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k],
    HasTriangularPBW (indeterminate k)
      (fun m : Lattice => AddMonoidAlgebra.single m (1 : RatFunc k))

def truncatedProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (N : ℕ), 1 ≤ N →
    HasTriangularPBW (truncated k N)
      (fun m : Root → ℕ => ∏ l : Root, (MvPolynomial.X l : TruncatedCartan k N) ^ m l)

namespace RankOne

/-- The generators of the rank-one presentation, including the inverse of K. -/
inductive Letter
  | E | F | K | Kinv

variable {k : Type u} [Field k]

abbrev Raw (k : Type u) [Field k] := FreeAlgebra k Letter

/-- Inverse, weight, and mixed commutator relations for `U_q(sl₂)`. -/
def ideal (q : kˣ) : TwoSidedIdeal (Raw k) :=
  let e := FreeAlgebra.ι k Letter.E
  let f := FreeAlgebra.ι k Letter.F
  let K := FreeAlgebra.ι k Letter.K
  let Kinv := FreeAlgebra.ι k Letter.Kinv
  TwoSidedIdeal.span
    {K * Kinv - 1, Kinv * K - 1,
     K * e * Kinv - ((q : k)^2) • e,
     K * f * Kinv - ((↑(q⁻¹) : k)^2) • f,
     e * f - f * e - ((↑q - ↑(q⁻¹) : k)⁻¹) • (K - Kinv)}

abbrev QuantumAlgebra (k : Type u) [Field k] (q : kˣ) :=
  Raw k ⧸ (ideal q).asIdeal

def generator (q : kˣ) (g : Letter) : QuantumAlgebra k q :=
  Ideal.Quotient.mkₐ k (ideal q).asIdeal (FreeAlgebra.ι k g)

/-- Images of the rank-one generators at the specified simple root. -/
def image {T : Type v} [CommRing T] [Algebra k T]
    (C : Cartan k T) (i : Root) : Letter → U C
  | .E => E C i
  | .F => F C i
  | .K => cartan C (C.K i : T)
  | .Kinv => cartan C (↑(C.K i)⁻¹ : T)

def subalgebra {T : Type v} [CommRing T] [Algebra k T]
    (C : Cartan k T) (i : Root) : Subalgebra k (U C) :=
  Algebra.adjoin k (Set.range (image C i))

/-- The rank-one presentation identifies with the subalgebra on the four indicated
generators and the equivalence has their prescribed images. -/
def Identifies {T : Type v} [CommRing T] [Algebra k T]
    (C : Cartan k T) (i : Root) : Prop :=
  ∃ e : QuantumAlgebra k C.q ≃ₐ[k] subalgebra C i,
    ∀ g, (e (generator C.q g) : U C) = image C i g

end RankOne

def genericRankOneProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1) (i : Root),
    RankOne.Identifies (generic q hq) i

def indeterminateRankOneProp : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (i : Root),
    RankOne.Identifies (indeterminate k) i

end Specs.LieNotes.Quantum.TriangularPBW
