import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalUnramifiedCocycleSupport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoveRepresentatives

namespace LinearAlgebraicGroups.Specs.ExceptionalStableAlcoves

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj WithZero Pointwise
open ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open ExceptionalAffineBruhat
open ExceptionalAffineBuilding
open ExceptionalIwahoriImageComparison (MarkedCentralCover)
open ExceptionalIwahoriCongruence (integralRing)
open ExceptionalLocalRootCoordinates (normalizedValuation ramificationIndex)
open ExceptionalMarkedRootDescent (MarkedFibre markedWeylWord)
open ExceptionalSplitParahoricDescent
  (FaceReduction DescendedFaceResidue IncidentChambers IsLiftOfFlag MarkedCoefficientAction
    uniformizerPolynomial)
open ExceptionalStableAlcoveRepresentatives (IsArithmeticFrobenius)
open ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open IntegralSemisimpleModel (Model fibre integerAlgebra forgetFibrePoint cocharacter torusPoint
  splitTorus)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open Pinning (BasedRootDatum BasedIso AttachedDatum PinnedGroup)
open AdjointRepresentation (GroupPoints)
open ExceptionalFormsOverUnramifiedFields (HasTypeE)
open ExceptionalTwistedTraceComparison (PointCocycle Twist)
open GeometricRadicals (IsSemisimple IsSplitReductive)
open GeometricBorelConjugacy (IsQuasiSplit)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open SteinbergPinnedDescent (comparisonOnPoints)
open Arithmetic.MaximalUnramifiedBrauer (IsUnramified)
open QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction basedAutTopology fieldGalTopology)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology
  (Cocycle pointAction pointMap restriction)

attribute [local instance] integerAlgebra basedAutTopology fieldGalTopology

universe u v

local notation "CohPoints" => _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points

noncomputable section

/-- Changing coordinates by a point acts on the values of a crossed homomorphism. -/
def changeCoordinates {Γ H : Type*} [Group Γ] [Group H]
    (ρ : Γ →* MulAut H) (a : Γ → H) (g : H) (σ : Γ) : H :=
  g⁻¹ * a σ * ρ σ g

section FixedFace

variable {K G W V : Type u} {J : Type v} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} [Group G] [Group W]
  {j : G →* FieldPoints M K} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := W) A p}
  {B : Building C} {Q : C.TypeQuotient}
  {Γ : Type u} [Group Γ]

/-- A fixed barycenter placed in the standard apartment by a chamber representative
of the same marked complex. -/
structure FixedStandardFace (ad : AdjointAction B Q)
    (ρ : Γ →* MulAut G) (h : Γ → V ≃ᵃ[ℚ] V) (a : Γ → G) where
  coefficient : CoefficientAction B ρ h
  equivariant (σ : Γ) (g : G) (x : B.realization.Point) :
    coefficient.action σ (ad.action g x) = ad.action (ρ σ g) (coefficient.action σ x)
  mover : C.G₀
  weights : Weights (A.SimpleWall p)
  x : V
  barycenter : IsBarycenter (cotype weights) weights
  rational_eq : rationalPoint B.realization.coordinates x =
    simplexPoint B.realization.coordinates B.realization.vertex weights
  chart_eq : B.realization.chart 1 (rationalPoint B.realization.coordinates x) =
    B.realization.place 1 weights
  cocycle (σ τ : Γ) :
    changeCoordinates ρ a (mover : G) (σ * τ) =
      changeCoordinates ρ a (mover : G) σ * ρ σ (changeCoordinates ρ a (mover : G) τ)
  fixed (σ : Γ) :
    ad.action (changeCoordinates ρ a (mover : G) σ)
      (coefficient.action σ (B.realization.place 1 weights)) = B.realization.place 1 weights

end FixedFace

/-- Clearing a denominator in the rational cocharacter apartment. -/
def IntegralScalingDenominator : Prop :=
  ∀ {Y : Type u} [AddCommGroup Y] (x : ℚ ⊗[ℤ] Y),
    ∃ (d : ℕ) (y : Y), 0 < d ∧ (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y

section StableAlcove

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e}

/-- Scaling at the fixed barycenter and descent of its residue flags give an
incident alcove fixed by the translated cocycle. -/
structure StableIncidentAlcove (B : SplitBuildingLevel Y)
    (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
    (h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y))
    (a : Gal(K/F) → FieldPoints M' K) where
  face : FixedStandardFace B.adjoint ρ h a
  denominator : ℕ
  cocharacter : E.Y
  denominator_pos : 0 < denominator
  scaling_eq : (denominator : ℚ) • face.x = (1 : ℚ) ⊗ₜ[ℤ] cocharacter
  uniformizer : Fˣ
  uniformizer_value : normalizedValuation F (uniformizer : F) = WithZero.exp (-1 : ℤ)
  extension : Type u
  [extensionField : Field extension]
  [extensionAlgebra : Algebra K extension]
  [extensionFinite : FiniteDimensional K extension]
  [baseAlgebra : Algebra F extension]
  [scalarTower : IsScalarTower F K extension]
  [extensionValuation : ValuativeRel extension]
  [extensionTopology : TopologicalSpace extension]
  [extensionLocal : IsNonarchimedeanLocalField extension]
  [extendsLevel : ValuativeExtension K extension]
  [extendsBase : ValuativeExtension F extension]
  root : extensionˣ
  rootAlgebra : AdjoinRoot (uniformizerPolynomial (K := K) denominator uniformizer) ≃ₐ[K] extension
  root_eq : rootAlgebra (AdjoinRoot.root (uniformizerPolynomial (K := K) denominator uniformizer)) = root
  ramification : ramificationIndex K extension = (denominator : ℤ)
  reduction : FaceReduction B face.weights face.x denominator cocharacter
    (Units.map (algebraMap F K).toMonoidHom uniformizer) extension root
  descended : DescendedFaceResidue reduction face.coefficient
    (changeCoordinates ρ a (face.mover : FieldPoints M' K))
  flag : Points descended.flags.scheme (CommAlgCat.of (residue F) (residue F))
  incident : IncidentChambers B (B.ad.realization.place 1 face.weights)
  chamber : Y.ad.G₀
  flag_eq : IsLiftOfFlag descended flag incident
  chamber_eq : incident.val = QuotientGroup.mk (chamber : FieldPoints M' K)
  fixed (σ : Gal(K/F)) :
    B.adjoint.action (changeCoordinates ρ a (face.mover : FieldPoints M' K) σ) ''
      (face.coefficient.action σ '' B.ad.realization.closedFace chamber ∅) =
        B.ad.realization.closedFace chamber ∅

/-- The representative that first moves the fixed face, then its chosen alcove. -/
def StableIncidentAlcove.mover
    {B : SplitBuildingLevel Y} {ρ : Gal(K/F) →* MulAut (FieldPoints M' K)}
    {h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    {a : Gal(K/F) → FieldPoints M' K} (S : StableIncidentAlcove B ρ h a) : Y.ad.G₀ :=
  S.face.mover * S.chamber

end StableAlcove

/-- The actual pinned action of a finite unramified level has a stable incident
alcove, with reduction of the same parahoric and a flag over the base residue field. -/
def StableIncidentAlcoves : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
      {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
      {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
      {Y : SplitLevel K c p p' e} (B : SplitBuildingLevel Y)
      (C : MarkedFibre M' F) (l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned)
      (ω : Gal(K/F) →* Aut C.realization.attached.toBased)
      (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
      (h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)),
      MarkedCoefficientAction C l ω ρ h → (∀ σ, AutomorphismComparison Y.ad (ρ σ) (h σ)) →
      ∀ (a : Gal(K/F) → FieldPoints M' K),
        (∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) → Nonempty (StableIncidentAlcove B ρ h a)

/-- The simply connected and adjoint integral models, with the based datum of
the specified split pinning and compatible simple labels for the central map. -/
structure MarkedExceptionalCover (D : BasedRootDatum.{u}) (n : ℕ) where
  scDatum : BasedRootDatum.{u}
  adDatum : BasedRootDatum.{u}
  scModel : Model scDatum
  adModel : Model adDatum
  cover : MarkedCentralCover scModel adModel
  datum : BasedIso D scDatum
  scNumbering : Fin n ≃ scDatum.base.support
  adNumbering : Fin n ≃ adDatum.base.support
  scNumbering_eq : ExceptionalNumbering scDatum n scNumbering
  adNumbering_eq : ExceptionalNumbering adDatum n adNumbering
  numbering_comm (i : Fin n) : cover.rootEquiv (scNumbering i).val = (adNumbering i).val
  corootSpan : scDatum.datum.corootSpan ℤ = ⊤
  rootSpan : adDatum.datum.rootSpan ℤ = ⊤

section MarkedLevel

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
  {G : AffineAlgebraicGroup F} {D : BasedRootDatum.{u}} {n : ℕ}

/-- The split comparison of the actual central quotient, with its adjoint point
map, affine building, pinned coefficient action and type quotient. -/
structure MarkedUnramifiedLevel (M : MarkedExceptionalCover D n) (Q : AdjointQuotient G) where
  p : ℚ ⊗[ℤ] M.scDatum.Y
  p' : ℚ ⊗[ℤ] M.adDatum.Y
  apartments : (ℚ ⊗[ℤ] M.scDatum.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] M.adDatum.Y)
  apartments_eq : apartments.toLinearMap = M.cover.pushCocharacter.baseChange ℚ
  p_eq : p' = apartments p
  base : SplitLevel F M.cover p p' apartments
  baseBuilding : SplitBuildingLevel base
  level : SplitLevel K M.cover p p' apartments
  building : SplitBuildingLevel level
  scalar : ScalarComparison (algebraMap F K) (scalarPoints M.adModel (algebraMap F K))
    base.ad level.ad
  scalar_types : TypeQuotientTransport base.typeQuotient level.typeQuotient
    (scalarPoints M.adModel (algebraMap F K)) (MonoidHom.id _)
  referenceIso : (groupBaseChange F K).obj G.val ≅ (fibre K).obj M.scModel.group
  adjointIso : (groupBaseChange F K).obj Q.quotient.val ≅ (fibre K).obj M.adModel.group
  central_comm : (groupBaseChange F K).map Q.projection ≫ adjointIso.hom =
    referenceIso.hom ≫ (fibre K).map M.cover.map
  adjointPoint : CohPoints F K Q.quotient.val.X ≃* FieldPoints M.adModel K
  adjointPoint_eq (x : GroupPoints ((groupBaseChange F K).obj Q.quotient.val) (CommAlgCat.of K K)) :
    adjointPoint (baseChangePoint F K Q.quotient.val.X (CommAlgCat.of K K) x) =
      forgetFibrePoint M.adModel.group (CommAlgCat.of K K) (x ≫ adjointIso.hom.hom.hom)
  marking : MarkedFibre M.adModel F
  pinned : Aut marking.realization.attached.toBased ≃* Aut marking.realization.pinned
  diagram : Gal(K/F) →* Aut marking.realization.attached.toBased
  coefficient : Gal(K/F) →* MulAut (FieldPoints M.adModel K)
  affineAction : Gal(K/F) → (ℚ ⊗[ℤ] M.adDatum.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] M.adDatum.Y)
  typeAction : Gal(K/F) →* MulAut
    (alcoveStabilizer (ApartmentRoots.split M.adDatum.datum ℚ)
      ((ApartmentRoots.split M.adDatum.datum ℚ).alcove p'))
  markedCoefficient : MarkedCoefficientAction marking pinned diagram coefficient affineAction
  coefficient_eq (σ : Gal(K/F)) (x : CohPoints F K Q.quotient.val.X) :
    adjointPoint (pointAction F K Q.quotient.val.X σ x) = coefficient σ (adjointPoint x)
  affine_comparison (σ : Gal(K/F)) : AutomorphismComparison level.ad (coefficient σ) (affineAction σ)
  type_comparison (σ : Gal(K/F)) : TypeQuotientTransport level.typeQuotient level.typeQuotient
    (coefficient σ).toMonoidHom (typeAction σ).toMonoidHom
  type_action_eq (σ : Gal(K/F)) :
    (diagram σ = 1 → typeAction σ = 1) ∧ (diagram σ ≠ 1 → ∀ z, typeAction σ z = z⁻¹)
  type_order : Nat.card (alcoveStabilizer (ApartmentRoots.split M.adDatum.datum ℚ)
    ((ApartmentRoots.split M.adDatum.datum ℚ).alcove p')) = (if n = 6 then 3 else if n = 7 then 2 else 1)

/-- The alcove normal form in the marked adjoint points. The two changes of
chamber and the final Iwahori correction refer to this level's actual building. -/
structure AlcoveNormalForm
    {M : MarkedExceptionalCover D n} {Q : AdjointQuotient G}
    (L : MarkedUnramifiedLevel (K := K) M Q)
    (a : Gal(K/F) → FieldPoints M.adModel K) where
  stable : StableIncidentAlcove L.building L.coefficient L.affineAction a
  stabilized (σ : Gal(K/F)) :
    let b := changeCoordinates L.coefficient a (stable.mover : FieldPoints M.adModel K) σ
    L.building.adjoint.action b ''
        (stable.face.coefficient.action σ '' L.building.ad.realization.closedFace 1 ∅) =
          L.building.ad.realization.closedFace 1 ∅ ∧
    b ∈ L.level.ad.I ⊔ lengthZeroNormalizer L.level.ad ∧
    (typeChange L.level.typeQuotient b = 1 ↔ b ∈ L.level.ad.I)
  frobenius : Gal(K/F)
  arithmetic : IsArithmeticFrobenius frobenius
  correction : FieldPoints M.adModel K
  representative : Gal(K/F) → FieldPoints M.adModel K
  representative_cocycle (σ τ : Gal(K/F)) :
    representative (σ * τ) = representative σ * L.coefficient σ (representative τ)
  representative_mem (σ : Gal(K/F)) : representative σ ∈ lengthZeroNormalizer L.level.ad
  correction_eq (σ : Gal(K/F)) :
    representative σ = changeCoordinates L.coefficient a
      ((stable.mover : FieldPoints M.adModel K) * correction) σ
  outer_correction : L.diagram ≠ 1 →
    ∃ (δ : lengthZeroNormalizer L.level.ad) (k : L.level.ad.I),
      correction = (δ : FieldPoints M.adModel K) * k ∧
      (∀ σ, changeCoordinates L.coefficient a
        ((stable.mover : FieldPoints M.adModel K) * δ) σ ∈ L.level.ad.I) ∧
      ∀ σ, representative σ = 1
  inner_correction : L.diagram = 1 →
    correction ∈ L.level.ad.I ∧
    ∃ (π : Fˣ) (y : M.adDatum.Y) (word : List M.adDatum.I) (t : lengthZeroNormalizer L.base.ad),
      normalizedValuation F (π : F) = WithZero.exp (-1 : ℤ) ∧
      (∀ i ∈ word, i ∈ M.adDatum.base.support) ∧
      (t : FieldPoints M.adModel F) =
        (torusPoint M.adDatum (integralRing F) (cocharacter M.adDatum y (integralRing F) π) ≫
          M.adModel.torus.hom.hom) * markedWeylWord M.adModel.toIntegralMarking (integralRing F) word ∧
      IsOfFinOrder (t : FieldPoints M.adModel F) ∧
      orderOf (t : FieldPoints M.adModel F) ∣ Nat.card Gal(K/F) ∧
      (∀ σ, typeChange L.level.typeQuotient (representative σ) =
        typeChange L.level.typeQuotient
          (changeCoordinates L.coefficient a (stable.mover : FieldPoints M.adModel K) σ)) ∧
      (typeChange L.base.typeQuotient t = 1 → (t : FieldPoints M.adModel F) = 1) ∧
      representative frobenius = scalarPoints M.adModel (algebraMap F K) t

end MarkedLevel

/-- The marked simply connected fibre is identified with the original split
pinning. Its comparison over the unramified level is induced by the given
reference trivialization after extension to the separable closure. -/
def IsReferenceMarking
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {A : RootGroups.AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G} {E : SplitSequence P D l Q}
    {ω : Cocycle (trivialOuterAction (k := F) (S := SeparableClosure F) D.toBased)}
    (V : PinnedRepresentative (S := SeparableClosure F) E ω)
    (K : FiniteGaloisIntermediateField F (SeparableClosure F))
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    {n : ℕ} {M : MarkedExceptionalCover D.toBased n} {Q₀ : AdjointQuotient V.model.val}
    (L : MarkedUnramifiedLevel (K := K) M Q₀) : Prop :=
  let S := SeparableClosure F
  let R : RationalRealization.Realization M.scDatum A := ⟨P, D, inv (show D.toBased ⟶ M.scDatum from M.datum)⟩
  ∃ (j : (fibre F).obj M.scModel.group ≅ P.pair.G.val)
    (s : (fibre F).obj (splitTorus M.scDatum) ≅ P.pair.T.group),
    (fibre F).map M.scModel.torus ≫ j.hom = s.hom ≫ P.pair.T.inclusion ∧
    (∀ (α : M.scDatum.base.support) (U : TestAlgebra F) (z : U),
      forgetFibrePoint M.scModel.group U (RootGroups.rootPoint (R.rootMap α ≫ j.inv) U z) =
        M.scModel.line.point (integralRing U) z ≫ (M.scModel.root α.val).hom.hom) ∧
    ∀ (x : GroupPoints ((groupBaseChange F K).obj V.model.val.val) (CommAlgCat.of K K)),
      let xK := baseChangePoint F K V.model.val.val.X (CommAlgCat.of K K) x
      let xS := pointMap F K V.model.val.val.X K.toIntermediateField.val xK
      scalarPoints M.scModel K.toIntermediateField.val.toRingHom
        (forgetFibrePoint M.scModel.group (CommAlgCat.of K K) (x ≫ L.referenceIso.hom.hom.hom)) =
      forgetFibrePoint M.scModel.group (CommAlgCat.of F S)
        ((comparisonOnPoints V.trivialization).symm xS ≫ j.inv.hom.hom)

/-- For the specified pinned simply connected exceptional reference, the
adjoint cocycle on the separable closure has the marked alcove normal form
at a common finite unramified level. The neutral cases identify the given
twisted group with its reference over the ground field. -/
def ExceptionalAlcoveNormalForm : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    let S := SeparableClosure F
    ∀ {A : RootGroups.AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
      {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
      {E : SplitSequence P D l Q} {ω : Cocycle (trivialOuterAction (k := F) (S := S) D.toBased)}
      (V : PinnedRepresentative (S := S) E ω) (n : ℕ),
      (n = 6 ∨ n = 7 ∨ n = 8) → HasTypeE D n →
      IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
      (n = 6 ∨ ∀ σ, ω σ = 1) →
      ∀ (K₀ : FiniteGaloisIntermediateField F S),
        IsUnramified F K₀ →
        (∃ ω₀ : Gal(K₀/F) →* Aut D.toBased, ∀ σ, ω₀ (restriction K₀ σ) = ω σ) →
        ∀ (Q₀ : AdjointQuotient V.model.val) (a : PointCocycle (S := S) Q₀.quotient.val),
        ∃ (K : FiniteGaloisIntermediateField F S)
          (_ : ValuativeRel K) (_ : TopologicalSpace K)
          (_ : IsNonarchimedeanLocalField K) (_ : ValuativeExtension F K),
          K₀ ≤ K ∧ IsUnramifiedLocalExtension F K ∧
          ∃ (M : MarkedExceptionalCover D.toBased n)
            (L : MarkedUnramifiedLevel (K := K) M Q₀)
            (aK : Gal(K/F) → CohPoints F K Q₀.quotient.val.X)
            (N : AlcoveNormalForm L (fun σ => L.adjointPoint (aK σ))),
            let i := K.toIntermediateField.val
            let inner := ∀ σ, ω σ = 1
            IsReferenceMarking V K L ∧
            (L.diagram = 1 ↔ inner) ∧
            (∀ (σ : Gal(S/F)) (α : D.toBased.I),
              (markedDiagramEquiv L.marking.realization (L.diagram (restriction K σ))).asIso.hom.val.indexEquiv
                (M.cover.rootEquiv (M.datum.val.indexEquiv α)) =
                  M.cover.rootEquiv (M.datum.val.indexEquiv ((ω σ).asIso.hom.val.indexEquiv α))) ∧
            (∀ σ τ, aK (σ * τ) = aK σ * pointAction F K Q₀.quotient.val.X σ (aK τ)) ∧
            (∃ (b : CohPoints F S Q₀.quotient.val.X), ∀ σ,
              pointMap F K Q₀.quotient.val.X i (aK (restriction K σ)) =
                changeCoordinates (pointAction F S Q₀.quotient.val.X) a.val b σ) ∧
            (∃ (b : CohPoints F S Q₀.quotient.val.X), ∀ σ,
              pointMap F K Q₀.quotient.val.X i (L.adjointPoint.symm (N.representative (restriction K σ))) =
                changeCoordinates (pointAction F S Q₀.quotient.val.X) a.val b σ) ∧
            ∀ T : Twist a,
              (¬ inner → Nonempty (T.group.val ≅ V.model.val.val) ∧ IsQuasiSplit T.group) ∧
              (inner → (n = 8 ∨
                ∀ σ, typeChange L.level.typeQuotient (N.representative σ) = 1) →
                Nonempty (T.group.val ≅ V.model.val.val) ∧ IsSplitReductive T.group)

end

end LinearAlgebraicGroups.Specs.ExceptionalStableAlcoves
