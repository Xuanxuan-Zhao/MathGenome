import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.OpenCell
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelPositivity
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FiniteDistributions
import Mathlib.RingTheory.MvPolynomial.Ideal

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.SteinbergDistributions

open AbstractPairing (Root)
open BorelsAndChambers (subgroupRoots)
open OrderedRootProducts (RootSubgroupFamily Enumerates)
open GeometricRadicals (IsReductive IsSplitTorus)
open GeometricBorelConjugacy (IsKBorel)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open LinearAlgebraicGroups.FiniteDistributions (FrobeniusFormula twistCoordinates Dist)

noncomputable section

variable {k : Type u} [Field k]

/-- A coordinate presentation of the relative Frobenius and its scheme kernel. -/
structure KernelPresentation (p r : ℕ) [Fact p.Prime] [CharP k p] (H : GroupScheme k) where
  coordinates : HopfAlgebraCategory k
  ambient : specGroup coordinates ≅ H
  frobenius : twistCoordinates k p r coordinates ⟶ coordinates
  formula : FrobeniusFormula k p r coordinates frobenius
  idealIsHopf : (kernelIdeal frobenius).IsHopfIdeal k

variable {p r : ℕ} [Fact p.Prime] [CharP k p] {H : GroupScheme k}

abbrev KernelPresentation.hopf (P : KernelPresentation p r H) : HopfAlgebraCategory k :=
  letI := P.idealIsHopf
  hopfQuotient P.coordinates (kernelIdeal P.frobenius)

abbrev KernelPresentation.scheme (P : KernelPresentation p r H) : SchemeOver k :=
  (specGroup P.hopf).X

def KernelPresentation.inclusion (P : KernelPresentation p r H) : P.scheme ⟶ H.X :=
  letI := P.idealIsHopf
  (specGroupMap (hopfQuotientMap P.coordinates (kernelIdeal P.frobenius)) ≫ P.ambient.hom).hom.hom

/-- Multiplication of the three Frobenius kernels gives the ambient kernel as
a scheme, with the isomorphism commuting with the inclusions into G.
The geometric assertion holds for the larger class of connected reductive groups. -/
def KernelFactorization : Prop :=
  ∀ {k : Type u} [Field k] (p r : ℕ) [Fact p.Prime] [CharP k p], 1 ≤ r →
    ∀ (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B Bneg : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsKBorel Bneg → IsSubgroupOf T B → IsSubgroupOf T Bneg →
      OpenCell.AreOpposite T B Bneg →
    ∃ (Uneg : ClosedSubgroup Bneg.group) (Upos : ClosedSubgroup B.group),
      GeometricRadicals.IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup Bneg) Uneg ∧
      GeometricRadicals.IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup B) Upos ∧
      Nonempty (KernelPresentation p r G.val) ∧ Nonempty (KernelPresentation p r T.group) ∧
      Nonempty (KernelPresentation p r Uneg.group) ∧ Nonempty (KernelPresentation p r Upos.group) ∧
      ∀ (PG : KernelPresentation p r G.val) (PT : KernelPresentation p r T.group)
        (PN : KernelPresentation p r Uneg.group) (PP : KernelPresentation p r Upos.group),
        ∃ e : PN.scheme ⊗ (PT.scheme ⊗ PP.scheme) ≅ PG.scheme,
          e.hom ≫ PG.inclusion =
            (PN.inclusion ⊗ₘ (PT.inclusion ⊗ₘ PP.inclusion)) ≫ OpenCell.cellMap T Uneg Upos

/-- A choice of additive coordinates for the actual root subgroups in an order. -/
structure RootCoordinates {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (U : RootSubgroupFamily T) (l : List (Root T)) where
  line : Fin l.length → RootGroups.AdditiveLine k
  groupIso : ∀ i : Fin l.length, (line i).group ≅ (U (l.get i)).val.group

/-- The root product evaluated on affine coordinates. -/
def orderedPoint {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    {U : RootSubgroupFamily T} {l : List (Root T)} (x : RootCoordinates U l)
    (R : TestAlgebra k) (a : Fin l.length → R) : Points G.val.X R :=
  (List.ofFn fun i : Fin l.length =>
    (RootGroups.rootPoint ((x.groupIso i).hom ≫ (U (l.get i)).val.inclusion) R (a i) :
      Points G.val.X R)).prod

abbrev powersIdeal (k : Type u) [Field k] (I : Type) (q : ℕ) :
    Ideal (MvPolynomial I k) :=
  Ideal.span (Set.range fun i : I => (MvPolynomial.X i : MvPolynomial I k) ^ q)

def topExponent (n q : ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => q - 1)

def IsTopCoefficient {n q : ℕ} {C : Type u} [AddCommGroup C] [Module k C]
    (e : (MvPolynomial (Fin n) k ⧸ powersIdeal k (Fin n) q) ≃ₗ[k] C)
    (ω : Module.Dual k C) : Prop :=
  ∀ f : MvPolynomial (Fin n) k,
    ω (e (Ideal.Quotient.mk _ f)) = f.coeff (topExponent n q)

/-- Left and right translation invariance, as identities on the universal
coordinate coaction. These identities apply after any scalar extension. -/
def IsTranslationInvariant {A : HopfAlgebraCategory k} (ω : Module.Dual k A) : Prop :=
  ∀ a : A,
    (TensorProduct.rid k A) (ω.lTensor A (Coalgebra.comul a)) = algebraMap k A (ω a) ∧
    (TensorProduct.lid k A) (ω.rTensor A (Coalgebra.comul a)) = algebraMap k A (ω a)

def DistributionAugmentation (A : HopfAlgebraCategory k) : Ideal (Dist k A) where
  carrier := {f | f.ofConv 1 = 0}
  zero_mem' := rfl
  add_mem' := by
    intro a b ha hb
    change a.ofConv 1 + b.ofConv 1 = 0
    rw [show a.ofConv 1 = 0 from ha, show b.ofConv 1 = 0 from hb, add_zero]
  smul_mem' := by
    intro a b hb
    change (a * b).ofConv 1 = 0
    rw [LinearMap.convMul_apply]
    change LinearMap.mul' k k (TensorProduct.map a.ofConv b.ofConv
      (Bialgebra.comulAlgHom k A 1)) = 0
    rw [map_one]
    change a.ofConv 1 * b.ofConv 1 = 0
    rw [show b.ofConv 1 = 0 from hb, mul_zero]

def HasDistributionSocle (A : HopfAlgebraCategory k) (ω : Module.Dual k A) : Prop :=
  (∃ m : ℕ, DistributionAugmentation A ^ m = ⊥) ∧
    ∀ I : Ideal (Dist k A), I ≠ ⊥ → WithConv.toConv ω ∈ I

/-- Ordered root coordinates on the negative Frobenius kernel, with the
nondegenerate pairing induced by the top coefficient. -/
def OrderedNegativeCoordinates : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p], 1 ≤ r →
    ∀ (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B Bneg : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsKBorel Bneg → IsSubgroupOf T B → IsSubgroupOf T Bneg →
      OpenCell.AreOpposite T B Bneg →
    ∃ (Uneg : ClosedSubgroup Bneg.group),
      GeometricRadicals.IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup Bneg) Uneg ∧
      Nonempty (KernelPresentation p r Uneg.group) ∧
      Nonempty (RootSubgroupFamily T) ∧
      (∃ l : List (Root T), Enumerates l (subgroupRoots T Bneg)) ∧
      ∀ (P : KernelPresentation p r Uneg.group) (U : RootSubgroupFamily T)
        (l : List (Root T)), Enumerates l (subgroupRoots T Bneg) →
        ∃ lpos : List (Root T), Enumerates lpos (subgroupRoots T B) ∧ l.length = lpos.length ∧
        ∃ _x : RootCoordinates U l,
        ∀ x : RootCoordinates U l,
        ∃ e : (MvPolynomial (Fin l.length) k ⧸ powersIdeal k (Fin l.length) (p ^ r)) ≃ₐ[k] P.hopf,
          (∀ (R : TestAlgebra k) (a : P.hopf →ₐ[k] R),
            (testSpec k).map (CommAlgCat.ofHom a).op ≫ P.inclusion ≫
                (Uneg.inclusion ≫ Bneg.inclusion).hom.hom =
              orderedPoint x R
                (fun i => a (e (Ideal.Quotient.mk _ (MvPolynomial.X i))))) ∧
          ∃ ω : Module.Dual k P.hopf,
            IsTopCoefficient e.toLinearEquiv ω ∧
            ∀ f : P.hopf, (∀ g : P.hopf, ω (f * g) = 0) → f = 0

/-- Ordered root coordinates, their top coefficient, and the distribution
algebra socle for the negative radical. -/
def OrderedNegativeDistributions : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (p r : ℕ) [Fact p.Prime] [CharP k p], 1 ≤ r →
    ∀ (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B Bneg : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsKBorel Bneg → IsSubgroupOf T B → IsSubgroupOf T Bneg →
      OpenCell.AreOpposite T B Bneg →
    ∃ (Uneg : ClosedSubgroup Bneg.group),
      GeometricRadicals.IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup Bneg) Uneg ∧
      Nonempty (KernelPresentation p r Uneg.group) ∧
      Nonempty (RootSubgroupFamily T) ∧
      (∃ l : List (Root T), Enumerates l (subgroupRoots T Bneg)) ∧
      ∀ (P : KernelPresentation p r Uneg.group) (U : RootSubgroupFamily T)
        (l : List (Root T)), Enumerates l (subgroupRoots T Bneg) →
        ∃ lpos : List (Root T), Enumerates lpos (subgroupRoots T B) ∧ l.length = lpos.length ∧
        ∃ _x : RootCoordinates U l,
        ∀ x : RootCoordinates U l,
        ∃ e : (MvPolynomial (Fin l.length) k ⧸ powersIdeal k (Fin l.length) (p ^ r)) ≃ₐ[k] P.hopf,
          (∀ (R : TestAlgebra k) (a : P.hopf →ₐ[k] R),
            (testSpec k).map (CommAlgCat.ofHom a).op ≫ P.inclusion ≫
                (Uneg.inclusion ≫ Bneg.inclusion).hom.hom =
              orderedPoint x R
                (fun i => a (e (Ideal.Quotient.mk _ (MvPolynomial.X i))))) ∧
          ∃ ω : Module.Dual k P.hopf,
            IsTopCoefficient e.toLinearEquiv ω ∧ IsTranslationInvariant (A := P.hopf) ω ∧
            (∀ f : P.hopf, (∀ g : P.hopf, ω (f * g) = 0) → f = 0) ∧
            HasDistributionSocle P.hopf ω

end

end LinearAlgebraicGroups.Specs.SteinbergDistributions
