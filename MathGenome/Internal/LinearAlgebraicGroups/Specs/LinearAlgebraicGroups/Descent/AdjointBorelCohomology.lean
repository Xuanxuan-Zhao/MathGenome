import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.WeilHilbert90
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointCocharacters
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelNormalizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.CentralSeries
import Mathlib.AlgebraicGeometry.Morphisms.Proper

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.AdjointBorelCohomology

open Descent.NonabelianCohomology (groupH1 groupBasepoint)
open Unipotent (IsSplitUnipotent)

/-- Finite Galois additive Hilbert 90 in the trace averaging convention. -/
def FiniteAdditiveVanishing : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K] [IsGalois k K]
    (v : Gal(K/k) → K), (∀ σ τ, v (σ * τ) = v σ + σ (v τ)) →
    ∃ t : K, ∀ σ, v σ = t - σ t

/-- Continuous first cohomology of a form of the additive point functor
identified over the ground field with the additive group. -/
def AdditiveVanishing : Prop :=
  ∀ (k S : Type u) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : GroupScheme k), ((groupPointsFunctor k).obj G ≅ StandardGroups.additivePoints k) →
    ∀ x : groupH1 k G.X S, x = groupBasepoint k G.X S

/-- Continuous first cohomology of a split unipotent group is trivial. -/
def SplitUnipotentVanishing : Prop :=
  ∀ (k S : Type u) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k), IsSplitUnipotent G →
    ∀ x : groupH1 k G.val.X S, x = groupBasepoint k G.val.X S

open AdjointCocharacters (IsAdjointQuotient)
open GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsTorus IsUnipotentRadical)
open RankOneFlag (IsGeometricallyMaximal)
open QuotientEmbedding (Presentation)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (IsFppfGroupQuotient closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k]

/-- The image of a Borel in the central quotient is the full inverse-image
correspondent of the original Borel. The flags represent the same fppf
right-coset sheaf under the map induced by the quotient. -/
structure ImageBorel {G Q : AffineAlgebraicGroup k} (B : ClosedSubgroup G.val)
    (q : G.val ⟶ Q.val) where
  subgroup : ClosedSubgroup Q.val
  projection : B.group ⟶ subgroup.group
  factor : IsImageFactorization (B.inclusion ≫ q) projection subgroup.inclusion
  canonical : IsCanonicalImage (B.inclusion ≫ q) projection subgroup.inclusion
  inverseImage : IsPullback B.inclusion.hom.hom projection.hom.hom
    q.hom.hom subgroup.inclusion.hom.hom
  geometricallyReduced : ∀ (K : Type u) [Field K] [Algebra k K],
    AlgebraicGeometry.IsReduced ((groupBaseChange k K).obj subgroup.group).X.left
  smooth : Smooth subgroup.group.X.hom
  borel : IsKBorel subgroup
  normalizer : RepresentsSubgroup subgroup (fun _ g => Normalizes subgroup.inclusion g)
  flag : Nonempty (Presentation subgroup)
  proper : ∀ P : Presentation subgroup, IsProper P.scheme.hom
  flags : ∀ (P : Presentation B) (P' : Presentation subgroup),
    ∃ e : P.scheme ≅ P'.scheme, P.projection ≫ e.hom = q.hom.hom ≫ P'.projection

/-- This part of the argument applies to any rational Borel containing the
scheme centre. The indicated central quotient need only be fppf. -/
def AdjointBorelImage : Prop :=
  ∀ {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k}
    (B Z : ClosedSubgroup G.val) (q : G.val ⟶ Q.val),
    IsReductive G → IsReductive Q → IsKBorel B → IsSubgroupOf Z B →
    IsAdjointQuotient Z q → Nonempty (ImageBorel B q)

/-- Formation of the adjoint Borel for a reductive group equipped with a
rational Borel and a geometrically maximal torus in it. -/
def AdjointBorelForPair : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (B T : ClosedSubgroup G.val),
    IsReductive G → IsKBorel B → IsTorus T.group → IsGeometricallyMaximal T →
    IsSubgroupOf T B →
    ∃ (Z : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsAdjointQuotient Z q ∧ IsReductive Q ∧ IsSubgroupOf Z T ∧ Nonempty (ImageBorel B q)

/-- The image of the torus in the adjoint Borel, including the representation
of the quotient by the full scheme centre. -/
def AdjointTorusImage : Prop :=
  ∀ {k : Type u} [Field k] {G Q : AffineAlgebraicGroup k}
    {B T Z : ClosedSubgroup G.val} {q : G.val ⟶ Q.val} (D : ImageBorel B q),
    IsReductive G → IsAdjointQuotient Z q → IsTorus T.group →
    IsGeometricallyMaximal T →
    ∀ (j : T.group ⟶ B.group), j ≫ B.inclusion = T.inclusion →
    ∀ (z : Z.group ⟶ T.group), z ≫ T.inclusion = Z.inclusion →
    ∃ (A : ClosedSubgroup D.subgroup.group) (p : T.group ⟶ A.group)
      (hz : IsClosedImmersion z.hom.hom.left),
      IsTorus A.group ∧ IsGeometricallyMaximal (subgroupOfSubgroup D.subgroup A) ∧
      IsImageFactorization (j ≫ D.projection) p A.inclusion ∧
      IsCanonicalImage (j ≫ D.projection) p A.inclusion ∧
      IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup T)
        (Q := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup D.subgroup) A) ⟨_, z, hz⟩ p

/-- In a rational Borel containing a geometrically maximal torus, the torus
is a section of the quotient by the unipotent radical. -/
def BorelTorusQuotient : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (B : ClosedSubgroup G.val),
    IsReductive G → IsKBorel B → ∀ T : ClosedSubgroup B.group,
    IsGeometricallyMaximal (subgroupOfSubgroup B T) →
    ∃ (U : ClosedSubgroup B.group) (q : B.group ⟶ T.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U ∧
      IsSplitUnipotent (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup B) U) ∧
      IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup B)
        (Q := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup B) T) U q ∧
      T.inclusion ≫ q = 𝟙 T.group

open Pinning (PinnedGroup SimpleRoot transportCharacter)
open RootGroups (AdditiveLine)

/-- The pinned lifts act on the finite set of simple roots by their actual
transport of torus characters. -/
def PinnedSimpleRootPermutation : Prop :=
  ∀ {k : Type u} [Field k] {L : AdditiveLine k} (P : PinnedGroup L),
    Finite (SimpleRoot P.pair) ∧
      ∃ r : Aut P →* Equiv.Perm (SimpleRoot P.pair),
        ∀ (f : Aut P) (α : SimpleRoot P.pair),
          (r f α).val.val = transportCharacter f.asIso.hom.torus α.val.val

/-- The last cohomological step for a rational Borel and its radical quotient
with a specified Weil restriction decomposition. -/
def BorelVanishingWithInducedQuotient : Prop :=
  ∀ (k S : Type u) [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k) (B : ClosedSubgroup G.val),
    IsReductive G → IsKBorel B →
    ∀ (U : ClosedSubgroup B.group), IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U →
    ∀ (T : AffineAlgebraicGroup k) (q : B.group ⟶ T.val),
    IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup B) U q →
    ∀ (ι : Type u) [Finite ι] (E : ι → Type u) [∀ i, Field (E i)]
      [∀ i, Algebra k (E i)] [∀ i, Module.Finite k (E i)]
      [∀ i, Algebra.IsSeparable k (E i)] (W : ι → AffineAlgebraicGroup k),
      (∀ i, (groupPointsFunctor k).obj (W i).val ≅
        _root_.LinearAlgebraicGroups.WeilRestriction.extendedUnits k (E i)) →
      ∀ P : Fan (fun i => (W i).val), IsLimit P → Nonempty (P.pt ≅ T.val) →
        ∀ x : groupH1 k B.group.X S, x = groupBasepoint k B.group.X S

section Descent

open AutomorphismSequence (forgetPinning)
open AdjointCocharacters (coordinateHopf coordinateHopfIso coordinateHopfMap)
open CharacterDescent (Character GeometricCharacters)
open DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open SmoothnessAndIsogenies (pullbackCharacter)
open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)

variable (K : Type u) [Field K] [Algebra k K]
variable {L : AdditiveLine k} {P : PinnedGroup L}

/-- The three scalar-extension comparisons of a descended pinned pair.
The equation on the ambient Hopf algebra expresses twisting by the
inverse pullback of the pinned lift of the outer cocycle. -/
structure PinnedTwist (D : Pinning.AttachedDatum P.pair)
    (l : Aut D.toBased ≃* Aut P) {G : AffineAlgebraicGroup k}
    (B T : ClosedSubgroup G.val) where
  outer : Gal(K/k) →* Aut D.toBased
  groupIso : extendedHopf K (coordinateHopf P.pair.G) ≅ extendedHopf K (coordinateHopf G)
  borelIso : extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup P.pair.B)) ≅
    extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup B))
  torusIso : extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup P.pair.T)) ≅
    extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup T))
  borelComm : groupIso.hom ≫ extendedHopfMap K
      (coordinateHopfMap (G := closedSubgroupAlgebraicGroup B) (H := G) B.inclusion) =
    extendedHopfMap K (coordinateHopfMap (G := closedSubgroupAlgebraicGroup P.pair.B)
      (H := P.pair.G) P.pair.B.inclusion) ≫ borelIso.hom
  torusComm : groupIso.hom ≫ extendedHopfMap K
      (coordinateHopfMap (G := closedSubgroupAlgebraicGroup T) (H := G) T.inclusion) =
    extendedHopfMap K (coordinateHopfMap (G := closedSubgroupAlgebraicGroup P.pair.T)
      (H := P.pair.G) P.pair.T.inclusion) ≫ torusIso.hom
  twistedAction : ∀ (σ : Gal(K/k)) (x : extendedHopf K (coordinateHopf P.pair.G)),
    let f := (Functor.mapAut P (forgetPinning (A := L)) (l (outer σ))).asIso.inv
    (SemilinearAction.scalarExtension (K := K) (coordinateHopf G)).act σ
        (groupIso.hom.hom x) =
      groupIso.hom.hom ((extendedHopfMap K
        (coordinateHopfMap (G := P.pair.G) (H := P.pair.G) f)).hom
        ((SemilinearAction.scalarExtension (K := K) (coordinateHopf P.pair.G)).act σ x))

/-- Pull back the standard group-like coordinate along a ground-field
character, and extend it to the splitting field. -/
noncomputable def extendedCharacterValue (G : AffineAlgebraicGroup k) (χ : Character G.val) :
    extendedHopf K (coordinateHopf G) :=
  let f := ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage
    ((coordinateHopfIso G).hom ≫ χ)).unop
  (extendedHopfMap K f).hom (1 ⊗ₜ[k] MonoidAlgebra.of k IntegerCharacters integerGenerator)

/-- A permutation basis with its specified action on the actual group-like
elements of the scalar-extended coordinate Hopf algebra. -/
structure PermutedCharacterBasis (I : Type u) (H : AffineAlgebraicGroup k)
    (r : Gal(K/k) →* Equiv.Perm I) where
  basis : Module.Basis I ℤ (Additive (GeometricCharacters K (coordinateHopf H)))
  permutation : ∀ (σ : Gal(K/k)) (i : I),
    (SemilinearAction.scalarExtension (K := K) (coordinateHopf H)).act σ
        (basis i).toMul.val = (basis (r σ i)).toMul.val

/-- The Weil restriction factors are indexed by the orbits of the stated
permutation. Each field is the fixed field of the orbit representative's
stabilizer in the specified finite Galois extension. -/
def IsOrbitWeilProduct [Module.Finite k K] [IsGalois k K]
    {I : Type u} (r : Gal(K/k) →* Equiv.Perm I) (H : AffineAlgebraicGroup k) : Prop :=
  letI : MulAction Gal(K/k) I := MulAction.compHom I r
  let O := MulAction.orbitRel.Quotient Gal(K/k) I
  let E (o : O) := IntermediateField.fixedField (MulAction.stabilizer Gal(K/k) o.out)
  ∃ (W : O → AffineAlgebraicGroup k),
    (∀ o, Nonempty ((groupPointsFunctor k).obj (W o).val ≅
      _root_.LinearAlgebraicGroups.WeilRestriction.extendedUnits k (E o))) ∧
    ∃ (F : Fan (fun o => (W o).val)), Nonempty (IsLimit F) ∧ Nonempty (F.pt ≅ H.val)

/-- The complete adjoint-Borel assertion for the descended pair of a pinned
outer twist, including cohomology over every choice of separable closure. -/
def Statement [Module.Finite k K] [IsGalois k K] : Prop :=
  ∀ (D : Pinning.AttachedDatum P.pair) (l : Aut D.toBased ≃* Aut P)
    (Q₀ : AutomorphismSequence.AdjointQuotient P.pair.G)
    (_ : AutomorphismSequence.SplitSequence P D l Q₀)
    (G : AffineAlgebraicGroup k) (B T : ClosedSubgroup G.val)
    (F : PinnedTwist K D l B T),
    IsReductive G → IsKBorel B → IsTorus T.group → IsGeometricallyMaximal T →
    ∀ (j : T.group ⟶ B.group), j ≫ B.inclusion = T.inclusion →
    ∃ (Z : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val)
      (_ : IsAdjointQuotient Z q) (_ : IsReductive Q) (Dq : ImageBorel B q)
      (z : Z.group ⟶ T.group) (_ : z ≫ T.inclusion = Z.inclusion)
      (hz : IsClosedImmersion z.hom.hom.left) (Td : ClosedSubgroup Dq.subgroup.group)
      (p : T.group ⟶ Td.group) (U : ClosedSubgroup Dq.subgroup.group)
      (π : Dq.subgroup.group ⟶ Td.group),
      let A := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup Dq.subgroup) Td
      IsImageFactorization (j ≫ Dq.projection) p Td.inclusion ∧
      IsTorus Td.group ∧ IsGeometricallyMaximal (subgroupOfSubgroup Dq.subgroup Td) ∧
      IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup T) (Q := A) ⟨_, z, hz⟩ p ∧
      IsUnipotentRadical (closedSubgroupAlgebraicGroup Dq.subgroup) U ∧
      IsSplitUnipotent (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup Dq.subgroup) U) ∧
      IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup Dq.subgroup) (Q := A) U π ∧
      Td.inclusion ≫ π = 𝟙 _ ∧
      (∃ (r : Aut P →* Equiv.Perm (SimpleRoot P.pair))
        (b : PermutedCharacterBasis K (SimpleRoot P.pair) A
          (r.comp (l.toMonoidHom.comp F.outer))),
        (∀ f α, (r f α).val.val = transportCharacter f.asIso.hom.torus α.val.val) ∧
        (∀ α, (pullbackCharacter K (coordinateHopfMap
          (G := closedSubgroupAlgebraicGroup T) (H := A) p) (b.basis α).toMul).val =
          F.torusIso.hom.hom (extendedCharacterValue K
            (closedSubgroupAlgebraicGroup P.pair.T) α.val.val)) ∧
        IsOrbitWeilProduct K (r.comp (l.toMonoidHom.comp F.outer)) A) ∧
      ∀ (S : Type u) [Field S] [Algebra k S] [IsSepClosure k S]
        (x : groupH1 k Dq.subgroup.group.X S), x = groupBasepoint k Dq.subgroup.group.X S

end Descent

/-- The adjoint Borel assertion over any ground field and finite Galois
layer of a pinned outer twist. -/
def TwistedAdjointBorel : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Module.Finite k K] [IsGalois k K] {L : AdditiveLine k} {P : PinnedGroup L},
    Statement (P := P) K

end LinearAlgebraicGroups.Specs.AdjointBorelCohomology
