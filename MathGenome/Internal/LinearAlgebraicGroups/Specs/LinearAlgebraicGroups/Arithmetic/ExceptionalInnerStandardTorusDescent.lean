import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoveRepresentatives
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalTwistedTraceComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.MaximalSplitTori

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalInnerStandardTorusDescent

open ExceptionalAffineRootSystems (ApartmentRoots)
open ExceptionalAffineBruhat (ExceptionalNumbering IsUnramifiedLocalExtension SplitLevel)
open ExceptionalAffineBuilding (SplitBuildingLevel lengthZeroNormalizer)
open ExceptionalStableAlcoveRepresentatives (IsArithmeticFrobenius)
open ExceptionalTwistedTraceComparison (PointCocycle Twist)
open ExceptionalIwahoriImageComparison (MarkedCentralCover markedGroundPoint)
open ExceptionalMarkedRootDescent (MarkedFibre)
open IntegralSemisimpleModel (Model fibre integerAlgebra forgetFibrePoint)
open Pinning (BasedRootDatum)
open AutomorphismSequence (AdjointQuotient)
open RelativeFormComparison (IsInduced)
open CharacterDescent (Character Cocharacter)
open Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open GeometricRadicals (IsMaximalTorus IsSplitTorus)
open SchemeDerivedGroup (IsSubgroupOf)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition unitPoint)

attribute [local instance] integerAlgebra

noncomputable section

/-- The character indexed by a root of the integral datum. -/
def markedCharacter {K : Type u} [Field K] {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M K) (i : D.I) : Character C.realization.pinned.pair.T.group :=
  Additive.toMul (C.realization.datumIso.val.weightEquiv (D.datum.root i))

/-- Push cocharacters through the inclusion and read them in the marked lattice. -/
def markedCocharacterMap {K : Type u} [Field K] {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M K) {H : GroupScheme K} [IsCommMonObj H.X]
    (s : H ⟶ C.realization.pinned.pair.T.group) :
    Additive (Cocharacter H) →ₗ[ℤ] D.Y :=
  letI := C.realization.attached.comm
  C.realization.datumIso.val.coweightEquiv.toLinearMap.comp
    (show Cocharacter H →* Cocharacter C.realization.pinned.pair.T.group from
      { toFun := fun y => y ≫ s
        map_one' := Grp.hom_ext _ _ (MonObj.one_comp s.hom.hom)
        map_mul' := fun x y => Grp.hom_ext _ _ (MonObj.mul_comp x.hom.hom y.hom.hom s.hom.hom)
      }).toAdditive.toIntLinearMap

/-- Both compositions are the projection from the marked split fibre to the integral model. -/
def IsMarkedTrivialization {F K : Type u} [Field F] [Field K] [Algebra F K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K)
    {G H : AffineAlgebraicGroup F} (iG : G.val ≅ (fibre F).obj M.group)
    (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
    (f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj H.val) : Prop :=
  (f.hom ≫ j.inv).hom.hom.left ≫
      pullback.fst G.val.X.hom (fieldSpecMap F K) ≫
      iG.hom.hom.hom.left ≫ pullback.fst M.group.X.hom _ =
    C.groupIso.inv.hom.hom.left ≫ pullback.fst M.group.X.hom _

/-- A comparison of Gₘ with its scalar extension which preserves units on all test algebras. -/
def IsUnitComparison (F K : Type u) [Field F] [Field K] [Algebra F K]
    (e : specGroup (groupAlgebra K IntegerCharacters) ≅
      (groupBaseChange F K).obj (specGroup (groupAlgebra F IntegerCharacters))) : Prop :=
  ∀ (R : TestAlgebra K) (s : Rˣ),
    baseChangePoint F K (specGroup (groupAlgebra F IntegerCharacters)).X R
      (unitPoint R s ≫ e.hom.hom.hom) = unitPoint ((restrictTestAlgebra F K).obj R) s

/-- The descended torus and its largest split subtorus, with the comparison in
the actual adjoint apartment and the parabolic determined by a generic cocharacter. -/
def StandardTorusAndParabolic {F K : Type u} [Field F] [Field K] [Algebra F K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (C : MarkedFibre M K)
    {H : AffineAlgebraicGroup F}
    (f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj H.val)
    (N : Subgroup (ExceptionalAffineBruhat.FieldPoints M K))
    (L : (ℚ ⊗[ℤ] E.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)) : Prop :=
  let P := C.realization.pinned.pair
  let A := ApartmentRoots.split D.datum ℚ
  let fixed := LinearMap.ker (L.toLinearMap - LinearMap.id)
  ∃ (U : ClosedSubgroup H.val) (S : ClosedSubgroup U.group)
    (uK : (groupBaseChange F K).obj U.group ≅ P.T.group),
    IsMaximalTorus U ∧
    uK.hom ≫ P.T.inclusion ≫ f.hom = (groupBaseChange F K).map U.inclusion ∧
    (∀ R : ClosedSubgroup U.group, IsSplitTorus R.group → IsSubgroupOf R S) ∧
    Nonempty (S.group ≅
      (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin (Module.finrank ℚ fixed)))).val) ∧
    ∃ (e : specGroup (groupAlgebra K IntegerCharacters) ≅
        (groupBaseChange F K).obj (specGroup (groupAlgebra F IntegerCharacters)))
      (hS : IsCommMonObj ((groupBaseChange F K).obj S.group).X),
      IsUnitComparison F K e ∧
      Function.Bijective (fun cochar : Cocharacter S.group =>
        e.hom ≫ (groupBaseChange F K).map cochar) ∧
      letI := hS
      let sK := (groupBaseChange F K).map S.inclusion ≫ uK.hom
      let V := (markedCocharacterMap C sK).baseChange ℚ
      Function.Injective V ∧
      LinearMap.range ((c.pushCocharacter.baseChange ℚ).comp V) = fixed ∧
      ∀ g : 𝟙_ (SchemeOver K) ⟶ P.G.val.X, markedGroundPoint C g ∈ N →
        ∃ a : P.T.group ≅ P.T.group,
          (a.hom ≫ P.T.inclusion).hom.hom =
            (toUnit P.T.group.X ≫ g) * P.T.inclusion.hom.hom *
              (toUnit P.T.group.X ≫ g)⁻¹ ∧
          let sKg := sK ≫ a.hom
          let W := LinearMap.range ((markedCocharacterMap C sKg).baseChange ℚ)
          (∀ i, (sKg ≫ markedCharacter C i).hom.hom = 1 ↔ ∀ y ∈ W, A.root i y = 0) ∧
          ∀ cochar : Cocharacter S.group,
            let y := markedCocharacterMap C sKg
              (Additive.ofMul (e.hom ≫ (groupBaseChange F K).map cochar))
            let x := (1 : ℚ) ⊗ₜ[ℤ] y
            (∀ i, D.base.IsPos i → 0 ≤ A.root i x) →
            (∀ i, A.root i x = 0 → ∀ z ∈ W, A.root i z = 0) →
            ∃ J : LimitDecomposition (cochar ≫ S.inclusion ≫ U.inclusion),
              BorelProper.IsParabolic H J.parabolic ∧
              IsSubgroupOf (subgroupOfSubgroup U S) J.parabolic ∧
              (IsMaximalSplitTorus (subgroupOfSubgroup U S) → IsMinimalParabolic H J.parabolic) ∧
              ∃ bK : P.B.group ⟶ (groupBaseChange F K).obj J.parabolic.group,
                let gb := toUnit P.B.group.X ≫ g
                (bK ≫ (groupBaseChange F K).map J.parabolic.inclusion ≫ f.inv).hom.hom =
                  gb⁻¹ * P.B.inclusion.hom.hom * gb

/-- The standard torus preserved by the length-zero Frobenius representative
descends for the inner twist over the finite unramified level. -/
def DescendedStandardTorus : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
      (c : MarkedCentralCover M M') (n : ℕ)
      (b : Fin n ≃ D.base.support) (b' : Fin n ≃ E.base.support),
      (n = 6 ∨ n = 7) → ExceptionalNumbering D n b → ExceptionalNumbering E n b' →
      D.datum.corootSpan ℤ = ⊤ → E.datum.rootSpan ℤ = ⊤ →
      ∀ {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
        {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
        (Y : SplitLevel K c p p' e) (_B : SplitBuildingLevel Y),
        (∀ i, E.base.IsPos i →
          0 < (ApartmentRoots.split E.datum ℚ).root i p' ∧
          (ApartmentRoots.split E.datum ℚ).root i p' < 1) →
        ∀ (G : AffineAlgebraicGroup F) (Q : AdjointQuotient G)
          (iG : G.val ≅ (fibre F).obj M.group) (iQ : Q.quotient.val ≅ (fibre F).obj M'.group),
          Q.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map c.map →
          ∀ (a : PointCocycle (S := K) Q.quotient.val) (T : Twist a) (σ : Gal(K/F)),
            IsArithmeticFrobenius σ →
            let t := forgetFibrePoint M'.group (CommAlgCat.of F K) (a.val σ ≫ iQ.hom.hom.hom)
            ∀ ht : t ∈ lengthZeroNormalizer Y.ad,
              let L := (Y.ad.affine ⟨t, (Subgroup.mem_map.mp ht).choose_spec.2 ▸
                (Subgroup.mem_map.mp ht).choose.property⟩).linear
              ∃ (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj T.group.val)
                (f : Y.sc_fibre.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj T.group.val),
                IsInduced F K j T.trivialization ∧ IsMarkedTrivialization Y.sc_fibre iG j f ∧
                StandardTorusAndParabolic c Y.sc_fibre f Y.sc.N L

end

end LinearAlgebraicGroups.Specs.ExceptionalInnerStandardTorusDescent
