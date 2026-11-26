import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.ExactOperations
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.WoundExample

noncomputable section

/-- Indices of the two coordinates of the additive plane. -/
abbrev PlaneIndex := ULift.{u} Bool

abbrev xIndex : PlaneIndex.{u} := ⟨false⟩
abbrev yIndex : PlaneIndex.{u} := ⟨true⟩

variable (k : Type u) [Field k]

abbrev Plane := MvPolynomial PlaneIndex.{u} k

def equation (p : ℕ) (c : k) : Plane k :=
  MvPolynomial.X yIndex ^ p - MvPolynomial.X xIndex +
    MvPolynomial.C c * MvPolynomial.X xIndex ^ p

def equationIdeal (p : ℕ) (c : k) : Ideal (Plane k) :=
  Ideal.span {equation k p c}

abbrev Coordinates (p : ℕ) (c : k) := Plane k ⧸ equationIdeal k p c

instance (p : ℕ) (c : k) : Algebra.FiniteType k (Coordinates k p c) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k (equationIdeal k p c))
    Ideal.Quotient.mk_surjective

abbrev x (p : ℕ) (c : k) : Coordinates k p c :=
  Ideal.Quotient.mk _ (MvPolynomial.X xIndex)

abbrev y (p : ℕ) (c : k) : Coordinates k p c :=
  Ideal.Quotient.mk _ (MvPolynomial.X yIndex)

def extendedX (p : ℕ) (c : k) (K : Type u) [Field K] [Algebra k K] :
    K ⊗[k] Coordinates k p c :=
  (1 : K) ⊗ₜ[k] x k p c

def extendedY (p : ℕ) (c : k) (K : Type u) [Field K] [Algebra k K] :
    K ⊗[k] Coordinates k p c :=
  (1 : K) ⊗ₜ[k] y k p c

/-- The affine line as a scheme over the given field. -/
abbrev affineLine := (testSpec k).obj (op (CommAlgCat.of k (Polynomial k)))

/-- A primitive coordinate of the additive group law. -/
def Primitive {A : Type u} [CommRing A] [Algebra k A]
    (h : StandardGroups.HopfOperations k A) (z : A) : Prop :=
  h.delta z = z ⊗ₜ[k] 1 + 1 ⊗ₜ[k] z ∧ h.epsilon z = 0 ∧ h.inverse z = -z

/-- The coordinate Hopf isomorphism of the splitting, including the change of coordinates
and its inverse. Its spectrum identifies the base-changed group with the additive group. -/
def Splits {p : ℕ} {c : k} (plane : StandardGroups.HopfOperations k (Plane k))
    (hI : letI := plane.hopf; (equationIdeal k p c).IsHopfIdeal k)
    (K : Type u) [Field K] [Algebra k K] (d : K) : Prop :=
  letI := plane.hopf
  letI := hI
  ∃ h : StandardGroups.HopfOperations K (Polynomial K),
    Primitive K h Polynomial.X ∧
    letI := h.hopf
    ∃ e : extendedHopf K (CommHopfAlgCat.of k (Coordinates k p c)) ≅
        CommHopfAlgCat.of K (Polynomial K),
      e.hom.hom (extendedX k p c K) = Polynomial.X ^ p ∧
      e.hom.hom (extendedY k p c K) = Polynomial.X - Polynomial.C d * Polynomial.X ^ p ∧
      e.inv.hom Polynomial.X = (extendedY k p c K) +
        (d ⊗ₜ[k] (1 : Coordinates k p c)) * extendedX k p c K ∧
      Nonempty ((groupBaseChange k K).obj
        (StandardGroups.spectrum k (Coordinates k p c)).val ≅
        (StandardGroups.spectrum K (Polynomial K)).val)

/-- The closed additive subgroup cut out by the equation, together with its geometric
properties, splitting, and woundness. -/
def WoundSubgroup : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (c : k),
    (∀ d : k, d ^ p ≠ c) →
    ∃ h : StandardGroups.HopfOperations k (Plane k),
      (∀ i : PlaneIndex.{u}, Primitive k h (MvPolynomial.X i)) ∧
      letI := h.hopf
      ∃ hI : (equationIdeal k p c).IsHopfIdeal k,
        letI := hI
        let A := CommHopfAlgCat.of k (Plane k)
        let W := StandardGroups.spectrum k (Coordinates k p c)
        IsClosedImmersion (specGroupMap (hopfQuotientMap A (equationIdeal k p c))).hom.hom.left ∧
        Smooth W.val.X.hom ∧ GeometricallyConnected W.val.X.hom ∧
        Unipotent.IsUnipotent W ∧
        (∀ (K : Type u) [Field K] [Algebra k K] (d : K),
          d ^ p = algebraMap k K c → Splits k h hI K d (p := p) (c := c)) ∧
        (∃ d : AlgebraicClosure k, d ^ p = algebraMap k (AlgebraicClosure k) c ∧
          ∃ d' : IntermediateField.adjoin k ({d} : Set (AlgebraicClosure k)),
            (d' : AlgebraicClosure k) = d ∧
            Splits k h hI _ d' (p := p) (c := c)) ∧
        (∀ f : affineLine k ⟶ W.val.X,
          ∃ q : (testSpec k).obj (op (CommAlgCat.of k k)) ⟶ W.val.X,
            f = (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k))).op ≫ q) ∧
        (∀ H : ClosedSubgroup W.val, ¬ Nonempty (affineLine k ≅ H.group.X))

end

end LinearAlgebraicGroups.Specs.WoundExample
