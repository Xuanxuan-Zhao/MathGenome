import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.CharacterPairing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.QuasiSplitOrbitTorusProduct

noncomputable section

open AdjointCocharacters (coordinateHopf coordinateHopfIso coordinateHopfMap)
open CharacterDescent (Character Cocharacter GeometricCharacters)
open SmoothnessAndIsogenies (pullbackCharacter)
open GeometricRadicals (IsSplitTorus IsTorus)
open Unipotent (closedSubgroupAlgebraicGroup)
open AdjointBorelCohomology (PermutedCharacterBasis)

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- The characters of the actual scalar extension, in its coordinate presentation. -/
abbrev CharacterLattice (K : Type u) [Field K] [Algebra F K]
    (T : AffineAlgebraicGroup F) :=
  Additive (GeometricCharacters K (coordinateHopf T))

/-- Integral cocharacters in the dual-lattice presentation. -/
abbrev CocharacterLattice (K : Type u) [Field K] [Algebra F K]
    (T : AffineAlgebraicGroup F) :=
  Module.Dual ℤ (CharacterLattice K T)

/-- Pullback along the actual scalar extension of a group morphism. -/
def characterRestriction (K : Type u) [Field K] [Algebra F K]
    {S T : AffineAlgebraicGroup F} (f : S.val ⟶ T.val) :
    CharacterLattice K T →ₗ[ℤ] CharacterLattice K S :=
  (pullbackCharacter K (coordinateHopfMap f)).toAdditive.toIntLinearMap

/-- The inclusion of the stabilizer field in the splitting field on test algebras,
with the tensor factors in coefficient-first order on the right. -/
def orbitFieldInclusion (R : TestAlgebra F) (J : Subgroup Gal(K/F)) :
    R ⊗[F] IntermediateField.fixedField J →ₐ[F] K ⊗[F] R :=
  (Algebra.TensorProduct.map (IntermediateField.val _ : IntermediateField.fixedField J →ₐ[F] K)
    (AlgHom.id F R)).comp (Algebra.TensorProduct.comm F R (IntermediateField.fixedField J)).toAlgHom

/-- Evaluation of a split character on the scalar extension of a test point. -/
def evaluateCharacter (T : AffineAlgebraicGroup F) (R : TestAlgebra F)
    (x : (groupPointsFunctor F).obj T.val |>.obj R)
    (χ : CharacterLattice K T) : (K ⊗[F] R)ˣ :=
  let f := ((algSpec.fullyFaithful (R := CommRingCat.of F)).preimage
    (x ≫ (coordinateHopfIso T).inv.hom.hom)).unop.hom
  Units.map (Algebra.TensorProduct.map (AlgHom.id K K) f).toMonoidHom
    (GroupLike.toUnits K χ.toMul)

/-- A closed subtorus of a torus split by the given field is split by that field. -/
def SplitClosedSubtorus : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    (T : AffineAlgebraicGroup F) (S : ClosedSubgroup T.val),
    IsSplitTorus ((groupBaseChange F K).obj T.val) → IsTorus S.group →
    IsSplitTorus ((groupBaseChange F K).obj S.group)

/-- The multiplication and Weil restriction identifications, with the latter
normalized by evaluation at any chosen vertex of its orbit. -/
def OrbitTorusDecomposition {I : Type u} [Finite I]
    (ρ : Gal(K/F) →* Equiv.Perm I) (T : AffineAlgebraicGroup F)
    (b : Module.Basis I ℤ (CocharacterLattice K T))
    (S : @MulAction.orbitRel.Quotient Gal(K/F) I _ (MulAction.compHom I ρ) →
      ClosedSubgroup T.val) : Prop := by
  classical
  letI : MulAction Gal(K/F) I := MulAction.compHom I ρ
  let O := MulAction.orbitRel.Quotient Gal(K/F) I
  let q : I → O := Quotient.mk (MulAction.orbitRel Gal(K/F) I)
  let A := fun o => closedSubgroupAlgebraicGroup (G := T) (S o)
  let j := fun o => characterRestriction K (S := A o) (T := T) (S o).inclusion
  exact
    ∃ hcomm : IsCommMonObj T.val.X,
    letI := hcomm
    ∃ (d : PermutedCharacterBasis K I T ρ),
      (∀ i l, b l (d.basis i) = if i = l then 1 else 0) ∧
      (∀ o, ∀ i, q i ≠ o → j o (d.basis i) = 0) ∧
      (∀ o, ∃ c : Module.Basis {i : I // q i = o} ℤ (CharacterLattice K (A o)),
        ∀ i, c i = j o (d.basis i.val)) ∧
      (∀ (P : Fan (fun o => (S o).group)), IsLimit P →
        ∃ e : P.pt ≅ T.val, ∀ (R : TestAlgebra F)
          (x : ((groupPointsFunctor F).obj P.pt).obj R),
          letI : Fintype O := Fintype.ofFinite _
          letI : CommGroup (((groupPointsFunctor F).obj T.val).obj R) :=
            CategoryTheory.Hom.commGroup
          ((groupPointsFunctor F).map e.hom).app R x =
            ∏ o : O, ((groupPointsFunctor F).map (P.proj o ≫ (S o).inclusion)).app R x) ∧
      (∀ (i : I),
        let E := IntermediateField.fixedField (MulAction.stabilizer Gal(K/F) i)
        ∃ (W : AffineAlgebraicGroup F) (e : (S (q i)).group ≅ W.val)
          (w : (groupPointsFunctor F).obj W.val ≅
            _root_.LinearAlgebraicGroups.WeilRestriction.extendedUnits F E),
        ∀ (R : TestAlgebra F) (x : ((groupPointsFunctor F).obj (S (q i)).group).obj R),
          Units.map (orbitFieldInclusion R (MulAction.stabilizer Gal(K/F) i)).toMonoidHom
            (w.hom.app R (((groupPointsFunctor F).map e.hom).app R x)) =
          evaluateCharacter T R
            (((groupPointsFunctor F).map (S (q i)).inclusion).app R x) (d.basis i))

/-- The orbit decomposition in the dual-lattice presentation. -/
def OrbitTorusProduct : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [Module.Finite F K] [IsGalois F K]
    {I : Type u} [Fintype I] (ρ : Gal(K/F) →* Equiv.Perm I) (T : AffineAlgebraicGroup F),
    IsSplitTorus ((groupBaseChange F K).obj T.val) →
    ∀ (b : Module.Basis I ℤ (CocharacterLattice K T)),
    (∀ (σ : Gal(K/F)) (i : I) (χ ψ : CharacterLattice K T),
      (Descent.SemilinearAction.scalarExtension (K := K) (coordinateHopf T)).act σ χ.toMul.val =
        ψ.toMul.val → b (ρ σ i) ψ = b i χ) →
    letI : MulAction Gal(K/F) I := MulAction.compHom I ρ
    let O := MulAction.orbitRel.Quotient Gal(K/F) I
    let q : I → O := Quotient.mk (MulAction.orbitRel Gal(K/F) I)
    ∀ (S : O → ClosedSubgroup T.val),
      let A := fun o => closedSubgroupAlgebraicGroup (G := T) (S o)
      let j := fun o => characterRestriction K (S := A o) (T := T) (S o).inclusion
      (∀ o, IsTorus (S o).group) →
      (∀ o, Function.Injective (j o).dualMap ∧
        LinearMap.range (j o).dualMap = Submodule.span ℤ (b '' {i | q i = o})) →
      OrbitTorusDecomposition ρ T b S

open DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open CharacterPairing (pairing)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (unitPoint)

/-- The canonical semilinear endomorphism of a base-changed scheme, regarded
as an absolute scheme map. It fixes the projection to the ground-field
scheme and acts on the field projection by the given automorphism. -/
def fieldConjugation (σ : Gal(K/F)) (T : GroupScheme F) :
    pullback T.X.hom (fieldSpecMap F K) ⟶ pullback T.X.hom (fieldSpecMap F K) :=
  pullback.lift (pullback.fst T.X.hom (fieldSpecMap F K))
    (pullback.snd T.X.hom (fieldSpecMap F K) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      have h : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ fieldSpecMap F K =
          fieldSpecMap F K := by
        rw [← Spec.map_comp]
        congr 1
        ext x
        exact σ.commutes x
      rw [Category.assoc, h, pullback.condition])

/-- The coefficient map on the split multiplicative group fixes its Laurent
monomials. -/
def multiplicativeFieldConjugation (σ : Gal(K/F)) :
    (specGroup (groupAlgebra K IntegerCharacters)).X.left ⟶
      (specGroup (groupAlgebra K IntegerCharacters)).X.left :=
  Spec.map (CommRingCat.ofHom
    (MonoidAlgebra.mapRingEquiv IntegerCharacters σ.toRingEquiv).toRingHom)

/-- The semilinear square for the left Galois action on an actual cocharacter.
On coordinate rings the square reads `y' ∘ σ_T = σ_Gm ∘ y`. -/
def CocharacterTransport (T : GroupScheme F) (σ : Gal(K/F))
    (y y' : Cocharacter ((groupBaseChange F K).obj T)) : Prop :=
  y'.hom.hom.left ≫ fieldConjugation σ T = multiplicativeFieldConjugation σ ≫ y.hom.hom.left

/-- The square describes the Galois action on the actual cocharacters.
The base change of the source multiplicative group uses its canonical unit
coordinate on every test algebra. -/
def CocharacterCoefficientAction : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K],
    let M := specGroup (groupAlgebra F IntegerCharacters)
    ∃ e : specGroup (groupAlgebra K IntegerCharacters) ≅ (groupBaseChange F K).obj M,
      (∀ (R : TestAlgebra K) (t : Rˣ),
        baseChangePoint F K M.X R (unitPoint R t ≫ e.hom.hom.hom) =
          unitPoint ((restrictTestAlgebra F K).obj R) t) ∧
      (∀ (T : GroupScheme F) (σ : Gal(K/F))
        (y y' : Cocharacter ((groupBaseChange F K).obj T)),
        CocharacterTransport T σ y y' ↔
          fieldConjugation σ M ≫ (e.inv ≫ y).hom.hom.left =
            (e.inv ≫ y').hom.hom.left ≫ fieldConjugation σ T) ∧
      ∀ (T : GroupScheme F) [IsCommMonObj ((groupBaseChange F K).obj T).X],
        ∃ action : DistribMulAction Gal(K/F) (Additive (Cocharacter ((groupBaseChange F K).obj T))),
          ∀ (σ : Gal(K/F)) (y y' : Cocharacter ((groupBaseChange F K).obj T)),
            action.smul σ (Additive.ofMul y) = Additive.ofMul y' ↔ CocharacterTransport T σ y y'

/-- Postcomposition on the integral cocharacters of the actual base changes. -/
def cocharacterPushforward {S T : GroupScheme F}
    [IsCommMonObj ((groupBaseChange F K).obj S).X]
    [IsCommMonObj ((groupBaseChange F K).obj T).X] (f : S ⟶ T) :
    Additive (Cocharacter ((groupBaseChange F K).obj S)) →ₗ[ℤ]
      Additive (Cocharacter ((groupBaseChange F K).obj T)) :=
  ({ toFun := fun y => Additive.ofMul (y.toMul ≫ (groupBaseChange F K).map f)
     map_zero' := by
       apply Additive.toMul.injective
       apply Grp.hom_ext
       exact MonObj.one_comp ((groupBaseChange F K).map f).hom.hom
     map_add' := by
       intro x y
       apply Additive.toMul.injective
       apply Grp.hom_ext
       exact MonObj.mul_comp x.toMul.hom.hom y.toMul.hom.hom
         ((groupBaseChange F K).map f).hom.hom } : _ →+ _).toIntLinearMap

/-- The coordinate presentation of scalar extension, including its projection
to the original group. -/
def ScalarExtensionComparison (K : Type u) [Field K] [Algebra F K]
    (T : AffineAlgebraicGroup F) :=
  {a : specGroup (extendedHopf K (coordinateHopf T)) ≅ (groupBaseChange F K).obj T.val //
    a.hom.hom.hom.left ≫ pullback.fst T.val.X.hom (fieldSpecMap F K) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : coordinateHopf T →ₐ[F]
          K ⊗[F] coordinateHopf T).toRingHom) ≫ (coordinateHopfIso T).hom.hom.hom.left}

/-- The Hopf pullback of an actual cocharacter of the base change. -/
def cocharacterPullback {T : AffineAlgebraicGroup F} (a : ScalarExtensionComparison K T)
    (y : Cocharacter ((groupBaseChange F K).obj T.val)) :
    extendedHopf K (coordinateHopf T) ⟶ groupAlgebra K IntegerCharacters :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of K)).preimage (y ≫ a.val.inv)).unop

/-- The dual-lattice description agrees with the scheme cocharacters by composition
with actual characters. It respects the inclusion maps and coefficient Galois action. -/
def SplitCocharacterDuality : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K],
    ∃ (a : ∀ T : AffineAlgebraicGroup F, ScalarExtensionComparison K T)
      (hcomm : ∀ (T : AffineAlgebraicGroup F), IsSplitTorus ((groupBaseChange F K).obj T.val) →
        IsCommMonObj ((groupBaseChange F K).obj T.val).X),
    ∃ e : ∀ (T : AffineAlgebraicGroup F)
      (hT : IsSplitTorus ((groupBaseChange F K).obj T.val)),
      letI := hcomm T hT
      Additive (Cocharacter ((groupBaseChange F K).obj T.val)) ≃ₗ[ℤ] CocharacterLattice K T,
      (∀ T hT (y : Cocharacter ((groupBaseChange F K).obj T.val)) (x : CharacterLattice K T)
        (χ : groupAlgebra K IntegerCharacters ⟶ extendedHopf K (coordinateHopf T)),
        χ.hom (MonoidAlgebra.of K IntegerCharacters integerGenerator) = x.toMul.val →
        e T hT (Additive.ofMul y) x =
          pairing _ ((a T).val.inv ≫ specGroupMap χ) y) ∧
      (∀ (S T : AffineAlgebraicGroup F) hS hT (f : S.val ⟶ T.val)
        (y : Cocharacter ((groupBaseChange F K).obj S.val)),
        e T hT (Additive.ofMul (y ≫ (groupBaseChange F K).map f)) =
          (characterRestriction K (S := S) (T := T) f).dualMap (e S hS (Additive.ofMul y))) ∧
      ∀ T hT (σ : Gal(K/F))
        (y y' : Cocharacter ((groupBaseChange F K).obj T.val)),
        CocharacterTransport T.val σ y y' →
        ∀ (x x' : CharacterLattice K T),
          (Descent.SemilinearAction.scalarExtension (K := K) (coordinateHopf T)).act σ x.toMul.val =
            x'.toMul.val →
          e T hT (Additive.ofMul y') x' = e T hT (Additive.ofMul y) x

/-- The product theorem on the actual integral cocharacter lattice.
Commutativity of the scalar extensions follows from the torus hypotheses.
The multiplication conclusion applies to every product cone, including
the canonical product of the given closed subgroups. -/
def OrbitTorusProductOnCocharacters : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [Module.Finite F K] [IsGalois F K]
    {I : Type u} [Fintype I] (ρ : Gal(K/F) →* Equiv.Perm I) (T : AffineAlgebraicGroup F),
    IsSplitTorus ((groupBaseChange F K).obj T.val) →
    ∃ hcomm : IsCommMonObj ((groupBaseChange F K).obj T.val).X,
    letI := hcomm
    ∀ (b : Module.Basis I ℤ (Additive (Cocharacter ((groupBaseChange F K).obj T.val)))),
    (∀ (σ : Gal(K/F)) (i : I), CocharacterTransport T.val σ (b i).toMul
      (b (ρ σ i)).toMul) →
    letI : MulAction Gal(K/F) I := MulAction.compHom I ρ
    let O := MulAction.orbitRel.Quotient Gal(K/F) I
    let q : I → O := Quotient.mk (MulAction.orbitRel Gal(K/F) I)
    ∀ (S : O → ClosedSubgroup T.val), (∀ o, IsTorus (S o).group) →
      ∃ hcommS : ∀ o, IsCommMonObj ((groupBaseChange F K).obj (S o).group).X,
      (∀ o,
        letI := hcommS o
        let j := cocharacterPushforward (K := K) (S o).inclusion
        Function.Injective j ∧
          LinearMap.range j = Submodule.span ℤ (b '' {i | q i = o})) →
      ∃ (a : ScalarExtensionComparison K T)
        (e : Additive (Cocharacter ((groupBaseChange F K).obj T.val)) ≃ₗ[ℤ]
          CocharacterLattice K T),
        (∀ i (x : CharacterLattice K T)
          (χ : groupAlgebra K IntegerCharacters ⟶ extendedHopf K (coordinateHopf T)),
          χ.hom (MonoidAlgebra.of K IntegerCharacters integerGenerator) = x.toMul.val →
          e (b i) x = pairing _ (a.val.inv ≫ specGroupMap χ) (b i).toMul) ∧
        OrbitTorusDecomposition ρ T (b.map e) S

end

end LinearAlgebraicGroups.Specs.QuasiSplitOrbitTorusProduct
