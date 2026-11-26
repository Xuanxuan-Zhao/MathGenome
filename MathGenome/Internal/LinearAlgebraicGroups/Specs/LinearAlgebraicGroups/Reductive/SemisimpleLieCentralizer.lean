import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations
import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! The invariant-derivation model for the Lie algebra of an affine group. -/

open scoped TensorProduct Ring
open AlgebraicGeometry Bialgebra CategoryTheory WithConv

universe u

namespace LinearAlgebraicGroups.Specs.SemisimpleLieCentralizer

noncomputable section

variable {k : Type u} [Field k]

/-- Invariance under left translations. Right translation by a dual-number
identity lift induces a derivation with this invariance. -/
def IsInvariant (A : HopfAlgebraCategory k) (D : Module.End k A) : Prop :=
  (Coalgebra.comul (R := k)).comp D = (D.lTensor A).comp Coalgebra.comul

/-- The coordinate model for the Lie algebra, before passing to the point kernel. -/
abbrev InvariantDerivation (A : HopfAlgebraCategory k) :=
  {D : Derivation k A A // IsInvariant A D.toLinearMap}

/-- Evaluation at the identity identifies invariant derivations with the
tangent space at the counit of the coordinate Hopf algebra. -/
def InvariantDerivationCounit : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k),
    letI := (counitAlgHom k A).toRingHom.toAlgebra
    ∃ e : InvariantDerivation A ≃ Derivation k A k,
      ∀ D a, e D a = Coalgebra.counit (R := k) (D.val a)

/-- The corresponding dual-number lifts, with counit as their reduction. -/
def InvariantDerivationLifts : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k),
    ∃ e : InvariantDerivation A ≃
        Specs.AdvCommAlg.Differentials.Tangent.PointLifts k A k (counitAlgHom k A),
      ∀ D a, (e D).val a = (Coalgebra.counit (R := k) a, Coalgebra.counit (R := k) (D.val a))

/-- The restricted operation on the actual dual-number tangent kernel,
transported from invariant derivations. -/
def RestrictedLieOperation : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G)
    (p : ℕ) [Fact p.Prime] [CharP k p],
    ∃ (q : InvariantDerivation A ≃ Lie k G) (power : Lie k G → Lie k G),
      (∀ D a, let g := (hopfKernelLifts A) (mapDualKernel e.inv (q D))
        (g.val a).snd = Coalgebra.counit (R := k) (D.val a)) ∧
      ∀ x, (q.symm (power x)).val.toLinearMap = (q.symm x).val.toLinearMap ^ p

/-- Differential of a representation in a basis, evaluated at the counit. -/
def matrixAction (A : HopfAlgebraCategory k) {ι : Type u}
    (M : Matrix ι ι A) (D : InvariantDerivation A) : Matrix ι ι k :=
  fun i j => Coalgebra.counit (R := k) (D.val (M i j))

/-- The coordinate formula computes the differential on the actual
dual-number point of the scheme representation. -/
def MatrixDifferentialComparison : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineGroupCategory k) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ι : Type u) [Fintype ι] [DecidableEq ι] (L : GroupScheme k)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L) (D : InvariantDerivation A)
    (g : Specs.AdvCommAlg.Differentials.Tangent.PointLifts k A k (counitAlgHom k A)),
    (∀ a, (g.val a).snd = Coalgebra.counit (R := k) (D.val a)) →
    InfinitesimalCommutator.matrixDifferential f l
        (mapDualKernel e.hom ((hopfKernelLifts A).symm g)) =
      matrixAction A (RationalRepresentations.universalMatrix A G L e l f) D

/-- A homomorphism of groups is contravariant in its coordinate Hopf map. -/
def IsDifferential {A B : HopfAlgebraCategory k} (f : B ⟶ A)
    (D : InvariantDerivation A) (E : InvariantDerivation B) : Prop :=
  D.val.toLinearMap.comp f.hom.toLinearMap = f.hom.toLinearMap.comp E.val.toLinearMap

/-- The differential of a group homomorphism is the derivative of its
counit lift, equivalently the invariant derivation intertwined by pullback. -/
def InvariantDifferentialComparison : Prop :=
  ∀ (k : Type u) [Field k] (A B : HopfAlgebraCategory k) (f : B ⟶ A)
    (D : InvariantDerivation A),
    ∃ E : InvariantDerivation B, IsDifferential f D E ∧
      ∀ b, Coalgebra.counit (R := k) (E.val b) =
        Coalgebra.counit (R := k) (D.val (f.hom b))

def RestrictedDerivationPower : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k)
    (p : ℕ) [Fact p.Prime] [CharP k p] (D : InvariantDerivation A),
    ∃ E : InvariantDerivation A, E.val.toLinearMap = D.val.toLinearMap ^ p

def RestrictedMatrixAction : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k)
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (ι : Type u) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A)
    (_ : RationalRepresentations.IsCoactionMatrix A M)
    (D E : InvariantDerivation A),
    E.val.toLinearMap = D.val.toLinearMap ^ p →
    matrixAction A M E = matrixAction A M D ^ p

def RestrictedDifferentialNaturality : Prop :=
  ∀ (k : Type u) [Field k] (A B : HopfAlgebraCategory k)
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : B ⟶ A) (D Dp : InvariantDerivation A) (E Ep : InvariantDerivation B),
    IsDifferential f D E →
    Dp.val.toLinearMap = D.val.toLinearMap ^ p →
    Ep.val.toLinearMap = E.val.toLinearMap ^ p →
    IsDifferential f Dp Ep

/-- The two actual scheme differentials of the power commute, with the
operations on the point kernels determined by the invariant derivations. -/
def RestrictedSchemeNaturality : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A B : HopfAlgebraCategory k) (f : B ⟶ A)
    (eA : convolutionPoints A ≅ (groupPointsFunctor k).obj (specGroup A))
    (eB : convolutionPoints B ≅ (groupPointsFunctor k).obj (specGroup B)),
    (∀ (R : TestAlgebra k) (g : (convolutionPoints A).obj R),
      ((groupPointsFunctor k).map (specGroupMap f)).app R (eA.hom.app R g) =
        eB.hom.app R (toConv (g.ofConv.comp f.hom.toAlgHom))) →
    ∃ (qA : InvariantDerivation A ≃ Lie k (specGroup A))
      (qB : InvariantDerivation B ≃ Lie k (specGroup B))
      (powerA : Lie k (specGroup A) → Lie k (specGroup A))
      (powerB : Lie k (specGroup B) → Lie k (specGroup B)),
      (∀ D a, let g := (hopfKernelLifts A) (mapDualKernel eA.inv (qA D))
        (g.val a).snd = Coalgebra.counit (R := k) (D.val a)) ∧
      (∀ D b, let g := (hopfKernelLifts B) (mapDualKernel eB.inv (qB D))
        (g.val b).snd = Coalgebra.counit (R := k) (D.val b)) ∧
      (∀ x, (qA.symm (powerA x)).val.toLinearMap = (qA.symm x).val.toLinearMap ^ p) ∧
      (∀ y, (qB.symm (powerB y)).val.toLinearMap = (qB.symm y).val.toLinearMap ^ p) ∧
      ∀ x, mapPointKernel (specGroupMap f) (powerA x) = powerB (mapPointKernel (specGroupMap f) x)

/-- The restricted operation is transported along the counit lift to the
actual Lie algebra. Its differential in every rational representation is
the p-th matrix power. -/
def RestrictedSchemeDifferential : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineGroupCategory k) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (D E : InvariantDerivation A)
    (g h : Specs.AdvCommAlg.Differentials.Tangent.PointLifts k A k (counitAlgHom k A)),
    E.val.toLinearMap = D.val.toLinearMap ^ p →
    (∀ a, (g.val a).snd = Coalgebra.counit (R := k) (D.val a)) →
    (∀ a, (h.val a).snd = Coalgebra.counit (R := k) (E.val a)) →
    ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (L : GroupScheme k)
      (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι)
      (f : G.val ⟶ L),
      InfinitesimalCommutator.matrixDifferential f l
          (mapDualKernel e.hom ((hopfKernelLifts A).symm h)) =
        InfinitesimalCommutator.matrixDifferential f l
          (mapDualKernel e.hom ((hopfKernelLifts A).symm g)) ^ p

def RestrictedAdjointPower : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (s : IdentityLieStructure G.val)
    (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (D E : InvariantDerivation A)
    (g h : Specs.AdvCommAlg.Differentials.Tangent.PointLifts k A k (counitAlgHom k A)),
    E.val.toLinearMap = D.val.toLinearMap ^ p →
    (∀ a, (g.val a).snd = Coalgebra.counit (R := k) (D.val a)) →
    (∀ a, (h.val a).snd = Coalgebra.counit (R := k) (E.val a)) →
    letI := s.lieRing
    letI := s.lieAlgebra
    LieAlgebra.ad k (Lie k G.val) (mapDualKernel e.hom ((hopfKernelLifts A).symm h)) =
      LieAlgebra.ad k (Lie k G.val) (mapDualKernel e.hom ((hopfKernelLifts A).symm g)) ^ p

/-- Additive Jordan decomposition on a finite-dimensional space. -/
structure IsAdditiveJordanDecomposition {V : Type*} [AddCommGroup V] [Module k V]
    (X S N : Module.End k V) : Prop where
  sum : X = S + N
  commute : Commute S N
  semisimple : S.IsSemisimple
  nilpotent : IsNilpotent N

/-- A single pair of invariant derivations gives the two Jordan components in
every finite-dimensional rational representation in characteristic zero. -/
def CharacteristicZeroJordan : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (A : HopfAlgebraCategory k)
    (D : InvariantDerivation A),
    ∃ S N : InvariantDerivation A,
      D.val = S.val + N.val ∧
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A),
        RationalRepresentations.IsCoactionMatrix A M →
        IsAdditiveJordanDecomposition (Matrix.toLinAlgEquiv' (matrixAction A M D))
          (Matrix.toLinAlgEquiv' (matrixAction A M S))
          (Matrix.toLinAlgEquiv' (matrixAction A M N))

/-- The Jordan components of a Lie matrix over a perfect field are the
differentials of Lie vectors. -/
def PerfectFieldLieJordan : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : AffineGroupCategory k)
    (A : HopfAlgebraCategory k) (_e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ι : Type u) [Fintype ι] [DecidableEq ι] (L : GroupScheme k)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L) (x : Lie k G.val),
    ∃ s n : Lie k G.val,
      IsAdditiveJordanDecomposition
        (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l x))
        (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l s))
        (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l n))

/-- The same two tangent vectors work for every rational representation in
characteristic zero. -/
def CharacteristicZeroLieJordan : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (G : AffineGroupCategory k)
    (A : HopfAlgebraCategory k) (_e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (x : Lie k G.val),
    ∃ s n : Lie k G.val,
      ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (L : GroupScheme k)
        (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι)
        (f : G.val ⟶ L),
        IsAdditiveJordanDecomposition
          (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l x))
          (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l s))
          (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l n))

/-- Jordan decomposition takes place in the Lie algebra of the actual
base-changed group over the algebraic closure. -/
def GeometricLieJordan : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k),
    let K := AlgebraicClosure k
    let H := (groupBaseChange k K).obj G.val
    ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (L : GroupScheme K)
      (l : (groupPointsFunctor K).obj L ≅ StandardGroups.generalLinearPoints K ι)
      (f : H ⟶ L) (x : Lie K H),
      ∃ s n : Lie K H, IsAdditiveJordanDecomposition
        (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l x))
        (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l s))
        (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l n))

/-- Killing the image of a diagonalizable derivation gives a smooth closed
subscheme of a smooth affine scheme. For conjugation this is the fixed locus. -/
def SmoothDiagonalizableDerivationQuotient : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]
    (D : Derivation k A A), (⨆ w : k, Module.End.eigenspace D.toLinearMap w) = ⊤ →
    Algebra.Smooth k (A ⧸ Ideal.span (Set.range D))

def LargePrimePowerSemisimple : Prop :=
  ∀ (k V : Type u) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [PerfectField k] (p r : ℕ) [Fact p.Prime] [CharP k p]
    (X : Module.End k V), Module.finrank k V ≤ p ^ r → (X ^ (p ^ r)).IsSemisimple

/-- A rational vector in a scalar-extended Lie subspace descends to the
original subspace. -/
def MembershipDescends : Prop :=
  ∀ (k K V : Type u) [Field k] [Field K] [Algebra k K]
    [AddCommGroup V] [Module k V] (W : Submodule k V) (x : V),
    (1 : K) ⊗ₜ[k] x ∈ W.baseChange K ↔ x ∈ W

/-- Over an algebraically closed field of characteristic p, a linear
subspace of the matrix Lie algebra closed under p-th powers contains the
additive Jordan components of each of its elements. -/
def PrimePowerJordanMembership : Prop :=
  ∀ (k V : Type u) [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (p : ℕ) [Fact p.Prime] [CharP k p]
    (W : Submodule k (Module.End k V))
    (_ : ∀ X ∈ W, X ^ p ∈ W) (X : Module.End k V), X ∈ W →
    ∃ S ∈ W, ∃ N ∈ W, IsAdditiveJordanDecomposition X S N

/-- The same quantitative semisimplicity statement over the algebraic closure
of an arbitrary field of characteristic p. -/
def LargePrimePowerGeometricallySemisimple : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι]
    (p r : ℕ) [Fact p.Prime] [CharP k p] (X : Matrix ι ι k),
    Fintype.card ι ≤ p ^ r →
    Module.End.IsSemisimple (Matrix.toLinAlgEquiv'
      ((X ^ (p ^ r)).map (algebraMap k (AlgebraicClosure k))))

def RestrictedIteratedMatrixAction : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k)
    (p r : ℕ) [Fact p.Prime] [CharP k p]
    (ι : Type u) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A)
    (_ : RationalRepresentations.IsCoactionMatrix A M) (D : InvariantDerivation A),
    ∃ E : InvariantDerivation A,
      E.val.toLinearMap = D.val.toLinearMap ^ (p ^ r) ∧
      matrixAction A M E = matrixAction A M D ^ (p ^ r)

section Adjoint

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A faithful linear Lie algebra map detects the conditions needed here for
semisimplicity and nilpotence of the adjoint operator. -/
def AdjointFromFaithfulDifferential : Prop :=
  ∀ (k L V : Type u) [Field k] [PerfectField k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : L →ₗ⁅k⁆ Module.End k V), Function.Injective f →
    ∀ x : L,
      ((f x).IsSemisimple → (LieAlgebra.ad k L x).IsSemisimple) ∧
      (IsNilpotent (f x) → IsNilpotent (LieAlgebra.ad k L x))

end Adjoint

section CharacteristicPolynomial

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The matrix of a linear family over the coordinate ring of its parameter
space. Its specialization is obtained by scalar extension of that family. -/
def genericMatrix (F : (ι → k) →ₗ[k] Matrix ι ι k) :
    Matrix ι ι (MvPolynomial ι k) :=
  fun i j => ∑ l, MvPolynomial.C (F (Pi.single l 1) i j) * MvPolynomial.X l

/-- The open where the characteristic polynomial differs from the indicated
power of the variable. For the adjoint family this is the nonnilpotent locus. -/
def charpolyOpen (M : Matrix ι ι (MvPolynomial ι k)) :
    Set (PrimeSpectrum (MvPolynomial ι k)) :=
  (PrimeSpectrum.zeroLocus (Set.range fun n =>
    (M.charpoly - Polynomial.X ^ Fintype.card ι).coeff n))ᶜ

def evaluationPoint (K : Type u) [Field K] [Algebra k K] (v : ι → K) :
    PrimeSpectrum (MvPolynomial ι k) :=
  ⟨RingHom.ker (MvPolynomial.aeval v).toRingHom,
    RingHom.ker_isPrime (MvPolynomial.aeval v).toRingHom⟩

end CharacteristicPolynomial

def CharacteristicPolynomialOpen : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial ι k)),
    IsOpen (charpolyOpen M) ∧
    (∀ (K : Type u) [Field K] [Algebra k K] (v : ι → K),
      evaluationPoint K v ∈ charpolyOpen M ↔
        (M.map (MvPolynomial.aeval v : MvPolynomial ι k →ₐ[k] K)).charpoly ≠
          Polynomial.X ^ Fintype.card ι) ∧
    (∀ (K : Type u) [Field K] [Algebra k K] (v : ι → K),
      (M.map (MvPolynomial.aeval v : MvPolynomial ι k →ₐ[k] K)).charpoly ≠
        Polynomial.X ^ Fintype.card ι → (charpolyOpen M).Nonempty)

def GenericMatrixSpecialization : Prop :=
  ∀ (k ι K : Type u) [Field k] [Field K] [Algebra k K] [Fintype ι] [DecidableEq ι]
    (F : (ι → k) →ₗ[k] Matrix ι ι k) (v : ι → K),
    (genericMatrix F).map (MvPolynomial.aeval v : MvPolynomial ι k →ₐ[k] K) =
      ∑ l, v l • (F (Pi.single l 1)).map (algebraMap k K)

def CharacteristicPolynomialOpenRationalPoint : Prop :=
  ∀ (k ι : Type u) [Field k] [Infinite k] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial ι k)) (K : Type u) [Field K] [Algebra k K] (v : ι → K),
    evaluationPoint K v ∈ charpolyOpen M →
      ∃ w : ι → k, evaluationPoint k w ∈ charpolyOpen M

/-- The scheme centralizer functor on all algebras. -/
def CentralizesMatrix (A : HopfAlgebraCategory k) {ι : Type u} [Fintype ι]
    (M : Matrix ι ι A) (Y : Matrix ι ι k)
    {R : Type u} [CommRing R] [Algebra k R] (g : A →ₐ[k] R) : Prop :=
  Commute (M.map g) (Y.map (algebraMap k R))

/-- The equations of the scheme centralizer in a faithful matrix representation. -/
def centralizerIdeal (A : HopfAlgebraCategory k) {ι : Type u} [Fintype ι]
    (M : Matrix ι ι A) (Y : Matrix ι ι k) : Ideal A :=
  let T := Y.map (algebraMap k A)
  Ideal.span (Set.range fun ij : ι × ι => (M * T - T * M) ij.1 ij.2)

def MatrixCentralizerPoints : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k) (ι : Type u)
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (Y : Matrix ι ι k)
    (R : Type u) [CommRing R] [Algebra k R],
    ∃ e : ((A ⧸ centralizerIdeal A M Y) →ₐ[k] R) ≃ {g : A →ₐ[k] R // CentralizesMatrix A M Y g},
      ∀ g, (e g).val = g.comp (Ideal.Quotient.mkₐ k (centralizerIdeal A M Y))

/-- The tangent to the matrix centralizer consists of the original tangent
lifts whose differentials commute with the infinitesimal element. -/
def MatrixCentralizerTangent : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k) (ι : Type u)
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (Y : Matrix ι ι k)
    (_ : RationalRepresentations.IsCoactionMatrix A M) (D : InvariantDerivation A)
    (g : Specs.AdvCommAlg.Differentials.Tangent.PointLifts k A k (counitAlgHom k A)),
    (∀ a, (g.val a).snd = Coalgebra.counit (R := k) (D.val a)) →
    (CentralizesMatrix A M Y g.val ↔ Commute (matrixAction A M D) Y)

/-- The equations for the centralizer of a matrix cut out a closed subgroup
of the group acting through the given coaction matrix. -/
def MatrixCentralizerHopf : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k) (ι : Type u)
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) (Y : Matrix ι ι k),
    RationalRepresentations.IsCoactionMatrix A M → (centralizerIdeal A M Y).IsHopfIdeal k

/-- The matrix entries and the inverse determinant generate the coordinates
of a closed subgroup of the general linear group. -/
def MatrixGeneratesCoordinates (A : HopfAlgebraCategory k) {ι : Type u}
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A) : Prop :=
  Algebra.adjoin k (Set.range (fun ij : ι × ι => M ij.1 ij.2) ∪ {M.det⁻¹ʳ}) = ⊤

/-- Smoothness of the Lie centralizer in the split eigenvalue case. -/
def SplitMatrixCentralizerSmooth : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (A : HopfAlgebraCategory k)
    [Algebra.Smooth k A] (ι : Type u) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A),
    RationalRepresentations.IsCoactionMatrix A M → MatrixGeneratesCoordinates A M →
    ∀ (D : InvariantDerivation A),
      Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (matrixAction A M D)) →
      Algebra.Smooth k (A ⧸ centralizerIdeal A M (matrixAction A M D))

/-- Matrix semisimplicity is tested over an algebraic closure of the ground field. -/
def GeometricallySemisimple {ι : Type u} [Fintype ι] [DecidableEq ι]
    (Y : Matrix ι ι k) : Prop :=
  Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (Y.map (algebraMap k (AlgebraicClosure k))))

def MatrixCentralizerSmooth : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k)
    [Algebra.Smooth k A] (ι : Type u) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι A),
    RationalRepresentations.IsCoactionMatrix A M → MatrixGeneratesCoordinates A M →
    ∀ (D : InvariantDerivation A), GeometricallySemisimple (matrixAction A M D) →
      Algebra.Smooth k (A ⧸ centralizerIdeal A M (matrixAction A M D))

def FaithfulMatrixGenerates : Prop :=
  ∀ (k : Type u) [Field k] (G L : AffineGroupCategory k) (A : HopfAlgebraCategory k)
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L.val), IsClosedImmersion f.hom.hom.left →
    MatrixGeneratesCoordinates A (RationalRepresentations.universalMatrix A G L.val e l f)

/-- In the counit-lift model the inclusion of the centralizer's Lie algebra
is the kernel of the intrinsic adjoint operator. -/
def CentralizerLieComparison : Prop :=
  ∀ (k : Type u) [Field k] (G L : AffineGroupCategory k) (s : IdentityLieStructure G.val)
    (A : HopfAlgebraCategory k) (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L.val), IsClosedImmersion f.hom.hom.left →
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ y x : Lie k G.val,
      let M := RationalRepresentations.universalMatrix A G L.val e l f
      let Y := InfinitesimalCommutator.matrixDifferential f l y
      let g := (hopfKernelLifts A) (mapDualKernel e.inv x)
      (centralizerIdeal A M Y ≤ RingHom.ker g.val.toRingHom) ↔ LieAlgebra.ad k (Lie k G.val) y x = 0

/-- For a connected group, a semisimple Lie vector with zero adjoint operator
has the whole group as its scheme centralizer. -/
def CentralizerOfCentralSemisimple : Prop :=
  ∀ (k : Type u) [Field k] (G L : AffineGroupCategory k) (s : IdentityLieStructure G.val)
    (A : HopfAlgebraCategory k) [Algebra.Smooth k A] [PreconnectedSpace (PrimeSpectrum A)]
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L.val), IsClosedImmersion f.hom.hom.left →
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ y : Lie k G.val,
      let M := RationalRepresentations.universalMatrix A G L.val e l f
      let Y := InfinitesimalCommutator.matrixDifferential f l y
      GeometricallySemisimple Y → LieAlgebra.ad k (Lie k G.val) y = 0 → centralizerIdeal A M Y = ⊥

/-- The smooth closed subgroup that represents the centralizer on all test
algebras, including its image on the Lie algebra and the connected case. -/
def SchemeCentralizerOfSemisimple : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (L : AffineGroupCategory k)
    (s : IdentityLieStructure G.val), Smooth G.val.X.hom →
    ∀ (ι : Type u) [Fintype ι] [DecidableEq ι]
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L.val), IsClosedImmersion f.hom.hom.left →
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ y : Lie k G.val,
      let Y := InfinitesimalCommutator.matrixDifferential f l y
      GeometricallySemisimple Y →
      ∃ H : ClosedSubgroup G.val, Smooth H.group.X.hom ∧
        (∀ (R : TestAlgebra k) (g : ((groupPointsFunctor k).obj G.val).obj R),
          (∃ h : ((groupPointsFunctor k).obj H.group).obj R,
            ((groupPointsFunctor k).map H.inclusion).app R h = g) ↔
          Commute (l.hom.app R (((groupPointsFunctor k).map f).app R g)).val
            (Y.map (algebraMap k R))) ∧
        (∀ x : Lie k G.val, (∃ z : Lie k H.group, mapPointKernel H.inclusion z = x) ↔
          LieAlgebra.ad k (Lie k G.val) y x = 0) ∧
        (PreconnectedSpace G.val.X.left → LieAlgebra.ad k (Lie k G.val) y = 0 → IsIso H.inclusion)

attribute [local instance 100] LieRing.ofAssociativeRing

def adjointMatrixFamily {V ι : Type u} [LieRing V] [LieAlgebra k V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) : (ι → k) →ₗ[k] Matrix ι ι k :=
  (LinearMap.toMatrixAlgEquiv b).toLinearMap.comp
    ((LieAlgebra.ad k V).toLinearMap.comp b.equivFun.symm.toLinearMap)

/-- A geometric vector is noncentral here when its adjoint Lie operator is nonzero. -/
def HasGeometricNoncentralSemisimple (G : AffineAlgebraicGroup k) : Prop :=
  let K := AlgebraicClosure k
  let H := (groupBaseChange k K).obj G.val
  ∃ (s : IdentityLieStructure H) (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι)
    (L : AffineGroupCategory K)
    (l : (groupPointsFunctor K).obj L.val ≅ StandardGroups.generalLinearPoints K ι)
    (f : H ⟶ L.val), IsClosedImmersion f.hom.hom.left ∧
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ y : Lie K H,
      Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (InfinitesimalCommutator.matrixDifferential f l y)) ∧
      LieAlgebra.ad K (Lie K H) y ≠ 0

def AdjointNonnilpotentOpen : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (s : IdentityLieStructure G.val),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k (Lie k G.val)),
      let U := charpolyOpen (genericMatrix (adjointMatrixFamily b))
      IsOpen U ∧
      (∀ x : Lie k G.val, evaluationPoint k (b.equivFun x) ∈ U ↔
        ¬ IsNilpotent (LieAlgebra.ad k (Lie k G.val) x)) ∧
      (HasGeometricNoncentralSemisimple G → U.Nonempty ∧
        (Infinite k → ∃ x : Lie k G.val, evaluationPoint k (b.equivFun x) ∈ U))

/-- At each rational point of the adjoint open, a rational semisimple vector
with proper smooth centralizer is given by the stated characteristic-dependent construction. -/
def RationalSemisimpleWitness : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (L : AffineGroupCategory k)
    (s : IdentityLieStructure G.val) (A : HopfAlgebraCategory k) [Algebra.Smooth k A]
    (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k ι)
    (f : G.val ⟶ L.val), IsClosedImmersion f.hom.hom.left →
    letI := s.lieRing
    letI := s.lieAlgebra
    let d := InfinitesimalCommutator.matrixDifferential f l
    let M := RationalRepresentations.universalMatrix A ⟨G.val, G.property.1⟩ L.val e l f
    ∀ x : Lie k G.val, ¬ IsNilpotent (LieAlgebra.ad k (Lie k G.val) x) →
      ∃ y : Lie k G.val, GeometricallySemisimple (d y) ∧ ⁅x, y⁆ = 0 ∧
        LieAlgebra.ad k (Lie k G.val) y ≠ 0 ∧
        Algebra.Smooth k (A ⧸ centralizerIdeal A M (d y)) ∧ centralizerIdeal A M (d y) ≠ ⊥ ∧
        ((CharZero k ∧ ∃ n : Lie k G.val, IsAdditiveJordanDecomposition
          (Matrix.toLinAlgEquiv' (d x)) (Matrix.toLinAlgEquiv' (d y)) (Matrix.toLinAlgEquiv' (d n))) ∨
        ∃ p r : ℕ, p.Prime ∧ CharP k p ∧ Fintype.card ι ≤ p ^ r ∧
          d y = d x ^ (p ^ r) ∧ LieAlgebra.ad k (Lie k G.val) y =
            (LieAlgebra.ad k (Lie k G.val) x) ^ (p ^ r))

end

end LinearAlgebraicGroups.Specs.SemisimpleLieCentralizer
