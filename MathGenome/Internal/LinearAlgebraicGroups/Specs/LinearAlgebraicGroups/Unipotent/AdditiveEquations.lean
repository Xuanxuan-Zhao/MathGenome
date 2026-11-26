import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Bialgebra.Primitive

noncomputable section

open CategoryTheory

namespace LinearAlgebraicGroups.Specs.AdditiveEquations

universe u

/-- Finite linear combinations of the Frobenius powers of the coordinate variables. -/
def IsAdditivePolynomial {k ι : Type u} [Field k] (p : ℕ) (f : MvPolynomial ι k) : Prop :=
  ∃ c : (ι × ℕ) →₀ k, f = c.sum fun ij a => a • MvPolynomial.X ij.1 ^ (p ^ ij.2)

/-- Primitivity for the specified Hopf operations on the usual polynomial algebra. -/
abbrev IsPrimitivePolynomial {k ι : Type u} [Field k]
    (h : StandardGroups.HopfOperations k (MvPolynomial ι k)) (f : MvPolynomial ι k) : Prop :=
  @Bialgebra.IsPrimitiveElem k (MvPolynomial ι k) _ _ h.hopf.toHopfAlgebraStruct.toBialgebra f

/-- The coordinate variables of the additive vector group are primitive. -/
def HasPrimitiveCoordinates {k ι : Type u} [Field k]
    (h : StandardGroups.HopfOperations k (MvPolynomial ι k)) : Prop :=
  ∀ i : ι, IsPrimitivePolynomial h (MvPolynomial.X i)

def PrimitivePolynomials : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] (p : ℕ) [CharP k p] [Fact p.Prime]
    (h : StandardGroups.HopfOperations k (MvPolynomial ι k)),
    HasPrimitiveCoordinates h →
      ∀ f : MvPolynomial ι k, IsPrimitivePolynomial h f ↔ IsAdditivePolynomial p f

def HopfIdealAdditiveGenerators : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] (p : ℕ) [CharP k p] [Fact p.Prime]
    (h : StandardGroups.HopfOperations k (MvPolynomial ι k)),
    letI := h.hopf
    HasPrimitiveCoordinates h →
      ∀ (I : Ideal (MvPolynomial ι k)) [I.IsHopfIdeal k],
        ∃ S : Finset (MvPolynomial ι k), I = Ideal.span (S : Set (MvPolynomial ι k)) ∧
          ∀ f ∈ S, IsPrimitivePolynomial h f ∧ IsAdditivePolynomial p f

def ClosedVectorSubgroupEquations : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] (p : ℕ) [CharP k p] [Fact p.Prime]
    (h : StandardGroups.HopfOperations k (MvPolynomial ι k)),
    letI := h.hopf
    HasPrimitiveCoordinates h →
      ∀ (H : GroupScheme k) (i : H ⟶ specGroup (CommHopfAlgCat.of k (MvPolynomial ι k))),
        AlgebraicGeometry.IsClosedImmersion i.hom.hom.left →
          ∃ S : Finset (MvPolynomial ι k), (∀ f ∈ S, IsAdditivePolynomial p f) ∧
            ∃ (_ : (Ideal.span (S : Set (MvPolynomial ι k))).IsHopfIdeal k),
              ∃ e : H ≅ specGroup
                  (hopfQuotient (CommHopfAlgCat.of k (MvPolynomial ι k))
                    (Ideal.span (S : Set (MvPolynomial ι k)))),
                e.hom ≫ specGroupMap
                  (hopfQuotientMap (CommHopfAlgCat.of k (MvPolynomial ι k))
                    (Ideal.span (S : Set (MvPolynomial ι k)))) = i

def FiniteAdditiveSubgroupEquation : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [Fact p.Prime]
    (h : StandardGroups.HopfOperations k (MvPolynomial PUnit.{u + 1} k)),
    letI := h.hopf
    HasPrimitiveCoordinates h →
      ∀ (I : Ideal (MvPolynomial PUnit.{u + 1} k)) [I.IsHopfIdeal k]
        [Module.Finite k (MvPolynomial PUnit.{u + 1} k ⧸ I)],
        ∃ f : MvPolynomial PUnit.{u + 1} k,
          I = Ideal.span {f} ∧ IsAdditivePolynomial p f ∧ f ≠ 0 ∧
            ((MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}) f).Monic


/-- The one-equation description as an isomorphism over the additive line. -/
def FiniteAdditiveLineSubgroupEquation : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [Fact p.Prime]
    (h : StandardGroups.HopfOperations k (MvPolynomial PUnit.{u + 1} k)),
    letI := h.hopf
    let A := CommHopfAlgCat.of k (MvPolynomial PUnit.{u + 1} k)
    HasPrimitiveCoordinates h →
      ∀ (H : GroupScheme k) (i : H ⟶ specGroup A),
        AlgebraicGeometry.IsClosedImmersion i.hom.hom.left →
        AlgebraicGeometry.IsFinite H.X.hom →
          ∃ f : MvPolynomial PUnit.{u + 1} k,
            IsAdditivePolynomial p f ∧ f ≠ 0 ∧
            ((MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}) f).Monic ∧
            ∃ (_ : (Ideal.span {f}).IsHopfIdeal k),
              ∃ e : H ≅ specGroup (hopfQuotient A (Ideal.span {f})),
                e.hom ≫ specGroupMap (hopfQuotientMap A (Ideal.span {f})) = i

end LinearAlgebraicGroups.Specs.AdditiveEquations
