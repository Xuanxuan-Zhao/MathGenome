import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagFixedPoints
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.WeylDenominator
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.FlagEulerCharacteristic

open AbstractPairing (Datum Root)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open FlagCohomology (FlagKernelPair CohomologyIndex CohomologyBasis IsFlagCohomologyAction
  flagCohomology equivariantEulerCharacteristic)
open EquivariantAffineModules (CharacterRing)
open FlagFixedPoints (HasCotangentWeights)
open FlagLocalizationGeometry (cotangentWeight torusAction)
open FlagLineBundle (AssociatedBundle OppositeBorelPair BorelProjection affineLine linePoint)
open QuotientEmbedding (Presentation)
open WeylDenominator (GroupRing alternant rho)

noncomputable section

variable {k : Type u} [Field k]

/-- The integral character ring maps into the half-weight group ring by doubling
exponents in the coordinates of `WeylDenominator.HalfWeight`. -/
def includeCharacters (T : GroupScheme k) :
    CharacterRing T →+* GroupRing (Additive (Character T)) :=
  (AddMonoidAlgebra.mapDomainRingHom ℤ
    ({ toFun := fun x => 2 • x
       map_zero' := nsmul_zero 2
       map_add' := fun x y => nsmul_add x y 2 } :
      Additive (Character T) →+ Additive (Character T))).comp
    (MonoidAlgebra.toAdditive ℤ (Character T)).toRingHom

/-- The integer group ring of the half-weight lattice is a domain since a
free abelian group has the unique sums property. -/
theorem halfWeightDomain (T : GroupScheme k)
    [Module.Free ℤ (Additive (Character T))] :
    IsDomain (GroupRing (Additive (Character T))) := by
  let e := (Module.Free.chooseBasis ℤ (Additive (Character T))).repr
  let : UniqueSums (Additive (Character T)) :=
    UniqueSums.of_injective_addHom e.toAddEquiv.toAddMonoidHom.toAddHom e.injective inferInstance
  infer_instance

/-- In the frame of the associated line given by a rational representative, the
torus acts on the fiber by the normalizer translate of the inducing character. -/
def HasAssociatedFiberWeight {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme} {p : BorelProjection P}
    {χ : Character P.torus.group} (L : AssociatedBundle Q a p χ)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (ψ : Character P.torus.group) : Prop :=
  IsPullback (prod.fst : (𝟙_ (SchemeOver k) : SchemeOver k) ⨯ affineLine k ⟶ _)
    (prod.map n (𝟙 (affineLine k)) ≫ L.trivialization) (n ≫ Q.projection) L.projection ∧
  ∀ (R : TestAlgebra k) (t : Points P.torus.group.X R) (z : R),
    let g := toUnit _ ≫ n
    lift (t ≫ P.torus.inclusion.hom.hom)
        (prod.lift g (linePoint R z) ≫ L.trivialization) ≫ L.action.smul =
      prod.lift g (linePoint R (CharacterPairing.characterValue ψ R t * z)) ≫ L.trivialization

/-- The equivariant Euler identity for every character line bundle on the
negative-Borel flag. The cohomology admits finite bases presenting its rational
actions and a cutoff beyond which it vanishes. The identity holds for any such
choices. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} (P : OppositeBorelPair G)
    (Q : Presentation P.negative) (a : ModObj G.val.X Q.scheme),
    μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ a.smul →
    ∃ hT : IsCommMonObj P.torus.group.X, letI := hT
      ∃ (D : Datum P.torus) (J : DatumAndWeyl.Identification D)
        (_ : Finite D.rootDatum.weylGroup) (_ : Finite (Root P.torus))
        (b : D.rootDatum.Base),
        letI := D.freeCharacters
        letI := halfWeightDomain P.torus.group
        DominantOrder.IsBaseFor D.rootDatum (subgroupRoots P.torus P.positive) b ∧
        (∀ w, ∃ n, BruhatOrbitParametrization.IsRepresentative J w n) ∧
        (IsEmpty (Root P.torus) → Nonempty (Q.scheme ≅ 𝟙_ (SchemeOver k))) ∧
        (∀ w n, BruhatOrbitParametrization.IsRepresentative J w n →
          let g := n ≫ J.normalizer.inclusion.hom.hom
          HasCotangentWeights (a := torusAction P.torus a) (g ≫ Q.projection)
            (cotangentWeight J w) ∧
          ∀ (p : BorelProjection P) (χ : Character P.torus.group) (L : AssociatedBundle Q a p χ),
            HasAssociatedFiberWeight L g ((J.labelEquiv w).val χ)) ∧
        Nonempty (BorelProjection P) ∧ FlagKernelPair Q ∧
        ∀ (p : BorelProjection P) (χ : Character P.torus.group) (h : FlagKernelPair Q),
          (∃ (r : ∀ i, RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h i))
            (basis : ∀ i, CohomologyBasis (p := p) (χ := χ) h i) (N : ℕ),
            (∀ i, IsFlagCohomologyAction h a i (basis i) (r i)) ∧
            ∀ i ≥ N, IsZero (flagCohomology Q p χ h i)) ∧
          ∀ (r : ∀ i, RootWeightAction.Representation G.val (CohomologyIndex (p := p) (χ := χ) h i))
            (basis : ∀ i, CohomologyBasis (p := p) (χ := χ) h i),
            (∀ i, IsFlagCohomologyAction h a i (basis i) (r i)) →
            ∀ N, (∀ i ≥ N, IsZero (flagCohomology Q p χ h i)) →
              let S := subgroupRoots P.torus P.positive
              let K := FractionRing (GroupRing (Additive (Character P.torus.group)))
              let toFraction := algebraMap (GroupRing (Additive (Character P.torus.group))) K
              toFraction (alternant D.rootDatum b (rho D.rootDatum S)) ≠ 0 ∧
              toFraction (includeCharacters P.torus.group (equivariantEulerCharacteristic h r N)) =
                toFraction (alternant D.rootDatum b (2 • Additive.ofMul χ + rho D.rootDatum S)) /
                  toFraction (alternant D.rootDatum b (rho D.rootDatum S))

end

end LinearAlgebraicGroups.Specs.FlagEulerCharacteristic
