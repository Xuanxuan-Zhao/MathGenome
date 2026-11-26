import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerIndices
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalLocalFormClassification

open AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints restrictIso)
open ExceptionalAffineBruhat (ExceptionalNumbering IsUnramifiedLocalExtension SplitLevel)
open ExceptionalAffineBuilding (SplitBuildingLevel lengthZeroNormalizer typeChange)
open ExceptionalFormsOverUnramifiedFields (HasTypeE)
open ExceptionalInnerIndices (HasInnerIndex e6Black e7Black)
open ExceptionalInnerStandardTorusDescent (IsMarkedTrivialization)
open ExceptionalLocalRootCoordinates (ramificationIndex)
open ExceptionalStableAlcoves (MarkedExceptionalCover changeCoordinates)
open ExceptionalStableAlcoveRepresentatives (IsArithmeticFrobenius)
open ExceptionalTwistedTraceComparison (PointCocycle Twist)
open GeometricBorelConjugacy (IsQuasiSplit)
open GeometricRadicals (IsSemisimple IsSplitReductive)
open IntegralSemisimpleModel (fibre forgetFibrePoint integerAlgebra)
open Pinning (AttachedDatum BasedIso PinnedGroup SplitBorelPair)
open QuasiSplitInnerForms (AreInnerForms PinnedRepresentative outerHom trivialOuterAction
  basedAutTopology fieldGalTopology)
open QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open RelativeFormComparison (IsInduced fieldTest transportedAut)
open RootGroups (AdditiveLine)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open SteinbergPinnedDescent (e6Involution)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology
  (Cocycle pointAction pointMap restriction)

attribute [local instance] basedAutTopology fieldGalTopology integerAlgebra

noncomputable section

variable {F : Type u} [Field F]

/-- A split pinned reference for the specified geometric pair of the actual group.
The torus comparison induces the coweight map of the based isomorphism. -/
structure SplitReference (G : AffineAlgebraicGroup F) {n : ℕ}
    {P : SplitBorelPair (SeparableClosure F)} (D : AttachedDatum P) (b : Fin n ≃ D.toBased.base.support)
    (g : P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj G.val) where
  line : AdditiveLine F
  pinned : PinnedGroup line
  attached : AttachedDatum pinned.pair
  datum : BasedIso D.toBased attached.toBased
  numbering : Fin n ≃ attached.toBased.base.support
  numbered : ExceptionalNumbering attached.toBased n numbering
  labels (j : Fin n) : datum.val.indexEquiv (b j).val = (numbering j).val
  coroots : corootLattice attached = ⊤
  semisimple : IsSemisimple pinned.pair.G
  simplyConnected : GeometricallySimplyConnected pinned.pair.G
  geometric : P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj pinned.pair.G.val
  torus : P.T.group ≅ (groupBaseChange F (SeparableClosure F)).obj pinned.pair.T.group
  borel : P.B.group ≅ (groupBaseChange F (SeparableClosure F)).obj pinned.pair.B.group
  torus_comm : P.T.inclusion ≫ geometric.hom =
    torus.hom ≫ (groupBaseChange F (SeparableClosure F)).map pinned.pair.T.inclusion
  borel_comm : P.B.inclusion ≫ geometric.hom =
    borel.hom ≫ (groupBaseChange F (SeparableClosure F)).map pinned.pair.B.inclusion
  units : MultiplicativeComparison F (SeparableClosure F)
  units_eq : PreservesUnits units
  coweights (y : attached.toBased.Y) :
    Additive.toMul (datum.val.coweightEquiv y) ≫ torus.hom =
      units.hom ≫ (groupBaseChange F (SeparableClosure F)).map (Additive.toMul y)
  lift : Aut attached.toBased ≃* Aut pinned
  adjoint : AdjointQuotient pinned.pair.G
  sequence : SplitSequence pinned attached lift adjoint
  trivialization : relativePoints pinned.pair.G.val (fieldTest F (SeparableClosure F)) ≅
    relativePoints G.val (fieldTest F (SeparableClosure F))
  trivialization_eq : IsInduced F (SeparableClosure F) (geometric.symm ≪≫ g) trivialization

section Comparisons

variable {G : AffineAlgebraicGroup F} {n : ℕ} {P : SplitBorelPair (SeparableClosure F)}
  {D : AttachedDatum P} {b : Fin n ≃ D.toBased.base.support}
  {g : P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj G.val}

/-- The diagram action of the form, measured in the chosen split coordinates. -/
def IsInner (R : SplitReference G D b g) : Prop :=
  ∀ σ, outerHom (S := (SeparableClosure F)) R.sequence (transportedAut F (SeparableClosure F) R.trivialization σ) = 1

/-- The inner-form criterion is unchanged under a ground-field pinned comparison
with another split simply connected datum of the same exceptional type. -/
def AgreesWithInnerForms (R : SplitReference G D b g) : Prop :=
  (IsInner R ↔ AreInnerForms (S := (SeparableClosure F)) R.pinned.pair.G G) ∧
  ∀ (A' : AdditiveLine F) (P' : PinnedGroup A') (D' : AttachedDatum P'.pair),
    corootLattice D' = ⊤ → HasTypeE D' n →
    ∃ (e : BasedIso R.attached.toBased D'.toBased)
      (j : R.pinned.pair.G.val ≅ P'.pair.G.val)
      (t : R.pinned.pair.T.group ≅ P'.pair.T.group)
      (q : R.pinned.pair.B.group ≅ P'.pair.B.group),
      R.pinned.pair.T.inclusion ≫ j.hom = t.hom ≫ P'.pair.T.inclusion ∧
      R.pinned.pair.B.inclusion ≫ j.hom = q.hom ≫ P'.pair.B.inclusion ∧
      (∀ y : D'.toBased.Y,
        Additive.toMul (e.val.coweightEquiv y) ≫ t.hom = Additive.toMul y) ∧
      (IsInner R ↔ AreInnerForms (S := (SeparableClosure F)) P'.pair.G G)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The nonidentity inner alcove representative gives an actual descended twist.
Its comparison with the given form is a coboundary comparison, and the same
marked split fibre and normalizer exhibit the index on the given group. -/
def HasMarkedInnerIndex (R : SplitReference G D b g) (r : ℕ) (black : Set (Fin n)) : Prop :=
  ∃ (K : FiniteGaloisIntermediateField F (SeparableClosure F))
    (_ : ValuativeRel K) (_ : TopologicalSpace K)
    (_ : IsNonarchimedeanLocalField K) (_ : ValuativeExtension F K),
    IsUnramifiedLocalExtension F K ∧
    ∃ (M : MarkedExceptionalCover R.attached.toBased n)
      (p : ℚ ⊗[ℤ] M.scDatum.Y) (p' : ℚ ⊗[ℤ] M.adDatum.Y)
      (e : (ℚ ⊗[ℤ] M.scDatum.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] M.adDatum.Y))
      (Y : SplitLevel K M.cover p p' e) (_ : SplitBuildingLevel Y)
      (iG : R.pinned.pair.G.val ≅ (fibre F).obj M.scModel.group)
      (iQ : R.adjoint.quotient.val ≅ (fibre F).obj M.adModel.group),
      (∀ i : Fin n, M.datum.val.indexEquiv (R.numbering i).val = (M.scNumbering i).val) ∧
      R.adjoint.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map M.cover.map ∧
      ∃ (a₀ : PointCocycle (S := (SeparableClosure F)) R.adjoint.quotient.val)
        (a : PointCocycle (S := K) R.adjoint.quotient.val) (T : Twist a)
        (σ : Gal(K/F)) (h : T.group.val ≅ G.val),
        (∀ τ, transportedAut F (SeparableClosure F) R.trivialization τ =
          R.sequence.toExactSequence.inner.app (op (fieldTest F (SeparableClosure F))) ⟨a₀.val τ⟩) ∧
        (∃ c,
          (∀ τ : Gal(SeparableClosure F/F),
            pointMap F K R.adjoint.quotient.val.X K.toIntermediateField.val
              (a.val (restriction K τ)) =
            changeCoordinates
              (pointAction F (SeparableClosure F) R.adjoint.quotient.val.X) a₀.val c τ) ∧
          let inclusionTest := (testSpec F).map (CommAlgCat.ofHom K.toIntermediateField.val).op
          let v := R.sequence.toExactSequence.inner.app (op (fieldTest F (SeparableClosure F))) ⟨c⟩
          IsInduced F (SeparableClosure F) ((groupBaseChange F (SeparableClosure F)).mapIso h)
            ((restrictIso inclusionTest T.trivialization).symm ≪≫ v.asIso ≪≫ R.trivialization)) ∧
        IsArithmeticFrobenius σ ∧
        (let t := forgetFibrePoint M.adModel.group (CommAlgCat.of F K)
            (a.val σ ≫ iQ.hom.hom.hom)
         t ∈ lengthZeroNormalizer Y.ad ∧ typeChange Y.typeQuotient t ≠ 1) ∧
        ∃ (j : (groupBaseChange F K).obj R.pinned.pair.G.val ≅
            (groupBaseChange F K).obj T.group.val)
          (fT : Y.sc_fibre.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj T.group.val),
          IsInduced F K j T.trivialization ∧
          IsMarkedTrivialization Y.sc_fibre iG j fT ∧
          HasInnerIndex M.scNumbering r black Y.sc_fibre
            (fT ≪≫ (groupBaseChange F K).mapIso h) Y.sc.N

/-- The nontrivial outer action factors through its separable quadratic diagram
field. The output is the actual pinned representative and a ground-field
isomorphism, for both unramified and ramified quadratic fields. -/
def HasOuterRepresentative (R : SplitReference G D b g) (h₆ : n = 6) : Prop :=
  ∃ (L : FiniteGaloisIntermediateField F (SeparableClosure F))
    (_ : ValuativeRel L) (_ : TopologicalSpace L)
    (_ : IsNonarchimedeanLocalField L) (_ : ValuativeExtension F L)
    (ωL : Gal(L/F) →* Aut R.attached.toBased),
    Module.finrank F L = 2 ∧ ωL ≠ 1 ∧
    (IsUnramifiedLocalExtension F L ∨ 1 < ramificationIndex F L) ∧
    (∀ σ : Gal(L/F), σ ≠ 1 → ∀ i : Fin n,
      (ωL σ).asIso.hom.val.indexEquiv (R.numbering i).val =
        (R.numbering (Fin.cast h₆.symm (e6Involution (Fin.cast h₆ i)))).val) ∧
    ∃ (ω : Cocycle (trivialOuterAction (k := F) (S := (SeparableClosure F)) R.attached.toBased))
      (V : PinnedRepresentative (S := (SeparableClosure F)) R.sequence ω)
      (_ : V.model.val.val ≅ G.val),
      IsQuasiSplit G ∧
      ∀ σ, outerHom (S := (SeparableClosure F)) R.sequence (transportedAut F (SeparableClosure F) R.trivialization σ) =
        ω (σ : Gal(SeparableClosure F/F)) ∧ ω σ = ωL (restriction L σ)

end Comparisons

/-- Classification on the input exceptional group, with the numbering of its
specified geometric pair. The inner alternatives have the indicated split
ranks and black nodes. Over the local field every outer E₆ is quasi-split. -/
def Classification : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : AffineAlgebraicGroup F), IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    ∀ (n : ℕ), (n = 6 ∨ n = 7 ∨ n = 8) →
    ∀ (P : SplitBorelPair (SeparableClosure F)) (D : AttachedDatum P) (b : Fin n ≃ D.toBased.base.support)
      (g : P.G.val ≅ (groupBaseChange F (SeparableClosure F)).obj G.val),
      (∀ i j, D.toBased.datum.pairing (b i) (b j) =
        ExceptionalAffineRootSystems.exceptionalCartan n i j) →
      corootLattice D = ⊤ ∧
      ∃ R : SplitReference G D b g,
        AgreesWithInnerForms R ∧
        ((IsInner R ∧ IsSplitReductive G ∧ Nonempty (R.pinned.pair.G.val ≅ G.val)) ∨
         (IsInner R ∧ ¬ IsSplitReductive G ∧
           ((∃ h : n = 6, HasMarkedInnerIndex R 2 (Fin.cast h ⁻¹' e6Black)) ∨
            (∃ h : n = 7, HasMarkedInnerIndex R 4 (Fin.cast h ⁻¹' e7Black)))) ∨
         (∃ h₆ : n = 6, ¬ IsInner R ∧ HasOuterRepresentative R h₆))

end

end LinearAlgebraicGroups.Specs.ExceptionalLocalFormClassification
