import Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalParahoricResidueDescent
import LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceReduction
import LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalResidueCorrection
import LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalUnramifiedCocycle
import LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalParahoricResidueDescent

open AlgebraicGeometry CategoryTheory IsLocalRing Opposite Topology ValuativeRel
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalAffineBruhat (RamifiedReference FoldedApartment coefficientPoints
  FieldPoints scalarPoints residue)
open Specs.ExceptionalIwahoriCongruence (integralRingMap)
open Specs.ExceptionalLocalRootCoordinates (residueMap)
open Specs.ExceptionalValuedTorusNormalizer (invariantApartment)
open Specs.IntegralFibreRootCoordinates (fibreAlgebraicGroup)
open Specs.IntegralSemisimpleModel (Model fibre forgetFibrePoint integerAlgebra)
open Specs.Pinning (BasedRootDatum)
open Specs.RamifiedExceptionalAuxiliaryTower
open Specs.RamifiedExceptionalFaceReduction
open Specs.RamifiedExceptionalLocalFaceCoordinates (MarkedLevel)
open Specs.RamifiedExceptionalParahoricResidueDescent
open Specs.RamifiedExceptionalResidueCorrection
open Specs.RamifiedExceptionalUnramifiedCocycle (Reduces)

noncomputable section

attribute [local instance] integerAlgebra ExceptionalLocalRootCoordinates.canonicalExtension
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

open private forgetFibrePoint_injective forgetFibrePoint_surjective
  forgetFibrePoint_mul forgetFibrePoint_natural
  from LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
open private residueLine_affine residueLine_finite_type residueLine_quasiCompact
  geometricReduction_natural mem_parahoricImage scalarPoints_comp_apply
  from LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalFaceReduction
open private carrier_range carrier_map
  from LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalResidueCorrection

private theorem connected_closedPoints {T : Type*} [TopologicalSpace T]
    [ConnectedSpace T] [JacobsonSpace T] : IsConnected (closedPoints T) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨p, _, hp⟩ := nonempty_inter_closedPoints
      (Z := (Set.univ : Set T)) Set.univ_nonempty isOpen_univ.isLocallyClosed
    exact ⟨p, hp⟩
  · intro U V hU hV hcover hleft hright
    have hAll : (Set.univ : Set T) ⊆ U ∪ V := by
      intro p _
      by_contra hp
      obtain ⟨z, hz, hz'⟩ := nonempty_inter_closedPoints
        (Z := (U ∪ V)ᶜ) ⟨p, hp⟩ (hU.union hV).isClosed_compl.isLocallyClosed
      exact hz (hcover hz')
    obtain ⟨p, _, hp⟩ := isPreconnected_univ U V hU hV hAll
      (hleft.mono (Set.inter_subset_inter_left U (Set.subset_univ _)))
      (hright.mono (Set.inter_subset_inter_left V (Set.subset_univ _)))
    obtain ⟨z, hz, hz'⟩ := nonempty_inter_closedPoints
      (Z := U ∩ V) ⟨p, hp⟩ (hU.inter hV).isLocallyClosed
    exact ⟨z, hz', hz⟩

private theorem geometric_image_connected {κ : Type u} [Field κ]
    {Y Z : SchemeOver κ} [LocallyOfFiniteType Y.hom] [GeometricallyConnected Y.hom]
    (f : Y ⟶ Z) :
    @IsConnected _ (geometricTopology Z) (Set.range fun p : GeometricPoints Y => p ≫ f) := by
  letI : TopologicalSpace (GeometricPoints Y) := geometricTopology Y
  letI : TopologicalSpace (GeometricPoints Z) := geometricTopology Z
  have hY : LocallyOfFiniteType (geometricScheme Y).hom :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd Y.hom
      (fieldSpecMap κ (AlgebraicClosure κ))))
  letI : GeometricallyConnected (geometricScheme Y).hom :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.snd Y.hom
      (fieldSpecMap κ (AlgebraicClosure κ))))
  letI : ConnectedSpace (geometricScheme Y).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (geometricScheme Y).hom
  letI : JacobsonSpace (geometricScheme Y).left :=
    LocallyOfFiniteType.jacobsonSpace (geometricScheme Y).hom
  have hInd : IsInducing (geometricCarrier (X := Y)) := ⟨rfl⟩
  have hconn : IsConnected (Set.univ : Set (GeometricPoints Y)) := by
    have hr : (geometricCarrier (X := Y)) '' (Set.univ : Set (GeometricPoints Y)) =
        closedPoints (geometricScheme Y).left := by
      rw [Set.image_univ, carrier_range]
    refine ⟨?_, hInd.isPreconnected_image.mp (hr ▸
      (connected_closedPoints (T := (geometricScheme Y).left)).isPreconnected)⟩
    rw [← Set.image_nonempty, hr]
    exact connected_closedPoints.nonempty
  have hc : Continuous (fun p : GeometricPoints Y => p ≫ f) := by
    have hInd' : IsInducing (geometricCarrier (X := Z)) := ⟨rfl⟩
    apply hInd'.continuous_iff.mpr
    convert ((baseChange κ (AlgebraicClosure κ)).map f).left.continuous.comp
      hInd.continuous using 1
    funext p
    exact carrier_map f p
  rw [← Set.image_univ]
  exact hconn.image _ hc.continuousOn

section Tower

variable {F L S : Type u} [Field F] [Field L] [Field S] [Algebra F L] [Algebra F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
  {D : BasedRootDatum.{u}} {M : Model D} {R : RamifiedReference F L M}
  {τ : Gal(L/F)} {A : FoldedApartment (R.diagram τ)}
  {X : ∀ k : UnramifiedLevel F S, MarkedLevel R τ A k.field}
  {J : Set (A.roots.SimpleWall A.basepoint)} {π : Lˣ} {d : ℕ} {y : D.Y}
  {ϖ : Fˣ} {x : invariantApartment D (R.diagram τ)}
  (P : ScaledParahoricTower X J π d y)

local notation "κ" => residue F
local notation "K" => AlgebraicClosure κ
local notation "Tκ" => CommAlgCat.of κ K

private def markedFibre : AffineAlgebraicGroup κ :=
  letI := M.affine
  letI := M.smooth
  fibreAlgebraicGroup κ M.group

private def fibrePointsEquiv :
    GeometricPoints (markedFibre (F := F) (M := M)).val.X ≃* FieldPoints M K :=
  MulEquiv.ofBijective (MonoidHom.mk' (forgetFibrePoint M.group Tκ)
    (forgetFibrePoint_mul M.group Tκ))
    ⟨forgetFibrePoint_injective M.group Tκ, forgetFibrePoint_surjective M.group Tκ⟩

private abbrev fibreImage : Subgroup (GeometricPoints (markedFibre (F := F) (M := M)).val.X) :=
  (RamifiedExceptionalFaceReduction.geometricParahoricSubgroup P).comap
    (fibrePointsEquiv (F := F) (M := M)).toMonoidHom

private def fibreReduction (k : UnramifiedLevel F S) :
    (X k).parahoric J →* GeometricPoints (markedFibre (F := F) (M := M)).val.X :=
  (fibrePointsEquiv (F := F) (M := M)).symm.toMonoidHom.comp (P.geometricReduction k)

private theorem fibrePointsEquiv_reduction (k : UnramifiedLevel F S) (g : (X k).parahoric J) :
    fibrePointsEquiv (F := F) (M := M) (fibreReduction P k g) = P.geometricReduction k g :=
  (fibrePointsEquiv (F := F) (M := M)).apply_symm_apply _

private theorem fibreReduction_image :
    (⋃ k, Set.range (fibreReduction P k)) = (fibreImage P : Set _) := by
  ext p
  rw [Set.mem_iUnion]
  change (∃ k, p ∈ Set.range (fibreReduction P k)) ↔
    fibrePointsEquiv (F := F) (M := M) p ∈ P.parahoricImage
  rw [mem_parahoricImage]
  constructor
  · rintro ⟨k, g, rfl⟩
    exact ⟨k, g, ((fibrePointsEquiv (F := F) (M := M)).apply_symm_apply _).symm⟩
  · rintro ⟨k, g, hg⟩
    exact ⟨k, g, (fibrePointsEquiv (F := F) (M := M)).injective
      (((fibrePointsEquiv (F := F) (M := M)).apply_symm_apply _).trans hg)⟩

private def fibreParameters (Q : GeometricReduction P ϖ x) :
    Parameterization (markedFibre (F := F) (M := M)) (fibreImage P) where
  Index := faceWeylGroup X (k := P.auxiliary.base) J
  finite := Q.finiteWeylGroup
  source w := (Q.doubleCosetMap w).source
  finiteType w := (Q.doubleCosetMap w).locallyFiniteType
  quasiCompact w := (Q.doubleCosetMap w).quasiCompact
  map w := (Q.doubleCosetMap w).morphism
  image_eq := by
    ext p
    change p ∈ ⋃ w, Set.range (fun v : GeometricPoints (Q.doubleCosetMap w).source =>
      v ≫ (Q.doubleCosetMap w).morphism) ↔
      fibrePointsEquiv (F := F) (M := M) p ∈ P.parahoricImage
    rw [Q.finite_image, Set.mem_iUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨w, v, rfl⟩
      exact ⟨w, v, rfl⟩
    · rintro ⟨w, v, hv⟩
      exact ⟨w, v, (fibrePointsEquiv (F := F) (M := M)).injective hv⟩

private def generatorSource (Q : GeometricReduction P ϖ x) :
    Unit ⊕ ULift.{u} ↥(residueRootDirections A J x) → AffineAlgebraicGroup κ
  | .inl _ => ⟨Q.torus, by
      obtain ⟨n, ⟨e⟩⟩ := Q.torus_split
      let f := ((Grp.forget (SchemeOver κ) ⋙ Over.forget _).mapIso e).hom
      letI : IsIso f := inferInstanceAs
        (IsIso ((Grp.forget (SchemeOver κ) ⋙ Over.forget _).mapIso e).hom)
      exact @IsAffine.of_isIso _ _ f ‹IsIso f›
        (StandardGroups.multiplicativePowerGroup κ (ULift.{u} (Fin n))).property.1,
      Q.torus_finite_type, Q.torus_quasiCompact⟩
  | .inr _ => ⟨(fibre κ).obj M.line.group, residueLine_affine,
      residueLine_finite_type, residueLine_quasiCompact⟩

private def generatorMap (Q : GeometricReduction P ϖ x) (i : Unit ⊕ ULift.{u} ↥(residueRootDirections A J x)) :
    (generatorSource P Q i).val ⟶ (markedFibre (F := F) (M := M)).val :=
  match i with
  | .inl _ => Q.torusMap
  | .inr a => Q.rootMaps a.down

private theorem generator_connected (Q : GeometricReduction P ϖ x)
    (i : Unit ⊕ ULift.{u} ↥(residueRootDirections A J x)) :
    GeometricallyConnected (generatorSource P Q i).val.X.hom := by
  cases i
  · exact Q.torus_connected
  · exact Q.root_connected

private def fibreGenerators (Q : GeometricReduction P ϖ x) :
    ConnectedGenerators (markedFibre (F := F) (M := M)) (fibreImage P) where
  Index := Unit ⊕ ULift.{u} ↥(residueRootDirections A J x)
  source := generatorSource P Q
  connected i :=
    letI := generator_connected P Q i
    GeometricallyConnected.connectedSpace_of_subsingleton (generatorSource P Q i).val.X.hom
  map := generatorMap P Q
  imageConnected i :=
    letI := generator_connected P Q i
    letI := (generatorSource P Q i).property.2.1
    geometric_image_connected (generatorMap P Q i).hom.hom
  generates := by
    let e := fibrePointsEquiv (F := F) (M := M)
    have himage (i : Unit ⊕ ULift.{u} ↥(residueRootDirections A J x)) :
        e '' Set.range (fun p : GeometricPoints (generatorSource P Q i).val.X =>
          p ≫ (generatorMap P Q i).hom.hom) =
        match i with
        | .inl _ => P.torusImage
        | .inr a => P.rootImage a.down.val := by
      rw [← Set.range_comp]
      cases i
      · exact Q.torus_image
      · exact Q.root_image _
    apply Subgroup.map_injective e.injective
    rw [MonoidHom.map_closure, Set.image_iUnion]
    change Subgroup.closure (⋃ i, e '' _) =
      ((RamifiedExceptionalFaceReduction.geometricParahoricSubgroup P).comap
        e.toMonoidHom).map e.toMonoidHom
    rw [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective]
    apply SetLike.coe_injective
    change _ = P.parahoricImage
    rw [Q.generation]
    have hUnion : (⋃ i, e '' Set.range
        (fun p : GeometricPoints (generatorSource P Q i).val.X =>
          p ≫ (generatorMap P Q i).hom.hom)) =
        P.torusImage ∪ ⋃ a : residueRootDirections A J x, P.rootImage a.val := by
      simp only [himage, Set.iUnion_sum, Set.iUnion_const]
      congr 1
      apply Set.ext
      intro v
      simp only [Set.mem_iUnion, ULift.exists]
    rw [hUnion]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L] in
private theorem coefficientPoints_comp {k k' k'' : Type u} [Field k] [Field k'] [Field k'']
    [Algebra F k] [Algebra F k'] [Algebra F k'']
    (f : k →ₐ[F] k') (g : k' →ₐ[F] k'')
    (p : AdjointRepresentation.GroupPoints R.descent.group.val (CommAlgCat.of F k)) :
    coefficientPoints R.descent.group.val (g.comp f) p =
      coefficientPoints R.descent.group.val g (coefficientPoints R.descent.group.val f p) := by
  exact ConcreteCategory.congr_hom
    (((groupPointsFunctor F).obj R.descent.group.val).map_comp
      (CommAlgCat.ofHom f) (CommAlgCat.ofHom g)) p

private theorem faceCoefficient_one (k : UnramifiedLevel F S) (p : (X k).parahoric J) :
    faceCoefficient P k 1 p = p := by
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (((groupPointsFunctor F).obj R.descent.group.val).map_id (CommAlgCat.of F k.field)) p.val

private theorem faceCoefficient_comp (k : UnramifiedLevel F S) (s t : Gal(k.field/F))
    (p : (X k).parahoric J) :
    faceCoefficient P k (s * t) p = faceCoefficient P k s (faceCoefficient P k t p) := by
  apply Subtype.ext
  exact coefficientPoints_comp t.toAlgHom s.toAlgHom p.val

private def faceAction (k : UnramifiedLevel F S) : Gal(k.field/F) →* MulAut ((X k).parahoric J) where
  toFun s :=
    { toFun := faceCoefficient P k s
      invFun := faceCoefficient P k s⁻¹
      left_inv := fun p => by rw [← faceCoefficient_comp, inv_mul_cancel, faceCoefficient_one]
      right_inv := fun p => by rw [← faceCoefficient_comp, mul_inv_cancel, faceCoefficient_one]
      map_mul' := fun p q => Subtype.ext (map_mul
        (coefficientPoints R.descent.group.val s.toAlgHom) p.val q.val) }
  map_one' := MulEquiv.ext (faceCoefficient_one P k)
  map_mul' s t := MulEquiv.ext (faceCoefficient_comp P k s t)

private theorem restrict_commutes {k k' : UnramifiedLevel F S} (h : k ≤ k')
    (s : Gal(k'.field/F)) (z : k.field) :
    s (UnramifiedLevel.inclusion h z) = UnramifiedLevel.inclusion h (restrictCoefficient h s z) := by
  let f := UnramifiedLevel.inclusion h
  letI : Algebra k.field k'.field := f.toRingHom.toAlgebra
  letI : IsScalarTower F k.field k'.field := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact (s.restrictNormal_commutes k.field z).symm

private theorem faceAction_extend {k k' : UnramifiedLevel F S} (h : k ≤ k')
    (s : Gal(k'.field/F)) (g : (X k).parahoric J) :
    faceInclusion X h J (P.face_comap h) (faceAction P k (restrictCoefficient h s) g) =
      faceAction P k' s (faceInclusion X h J (P.face_comap h) g) := by
  apply Subtype.ext
  change coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h)
      (coefficientPoints R.descent.group.val (restrictCoefficient h s).toAlgHom g.val) =
    coefficientPoints R.descent.group.val s.toAlgHom
      (coefficientPoints R.descent.group.val (UnramifiedLevel.inclusion h) g.val)
  have he : (UnramifiedLevel.inclusion h).comp (restrictCoefficient h s).toAlgHom =
      s.toAlgHom.comp (UnramifiedLevel.inclusion h) :=
    AlgHom.ext fun z => (restrict_commutes h s z).symm
  rw [← coefficientPoints_comp, ← coefficientPoints_comp, he]

open RamifiedExceptionalUnramifiedCocycle (residueGaloisComparison residueGaloisRestriction)

private theorem residueComparisonExists (k : UnramifiedLevel F S) :
    ∃ e : Gal(k.field/F) ≃* Gal(residue k.field / κ), ∀ s, Reduces s (e s) :=
  residueGaloisComparison F k.field k.unramified

private def residueComparison (k : UnramifiedLevel F S) :
    Gal(k.field/F) ≃* Gal(residue k.field / κ) :=
  (residueComparisonExists k).choose

private theorem residueComparison_reduces (k : UnramifiedLevel F S) (s : Gal(k.field/F)) :
    Reduces s (residueComparison k s) := (residueComparisonExists k).choose_spec s

private local instance residueFinite (E : Type u) [Field E] [ValuativeRel E]
    [TopologicalSpace E] [IsNonarchimedeanLocalField E] : Finite (residue E) :=
  IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation E

variable [Fintype (ExceptionalAffineBruhat.residue F)]

private def coefficientFrobenius (k : UnramifiedLevel F S) : Gal(k.field/F) :=
  (residueComparison k).symm (FiniteField.frobeniusAlgEquivOfAlgebraic κ (residue k.field))

private theorem residueComparison_frobenius (k : UnramifiedLevel F S) (z : residue k.field) :
    residueComparison k (coefficientFrobenius k) z = z ^ Fintype.card κ := by
  rw [coefficientFrobenius, MulEquiv.apply_symm_apply]
  rfl

private theorem coefficientFrobenius_cyclic (k : UnramifiedLevel F S) :
    Subgroup.zpowers (coefficientFrobenius k) = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
    κ (residue k.field)).surjective (residueComparison k s)
  refine ⟨(n.val : ℤ), (residueComparison k).injective ?_⟩
  rw [map_zpow, coefficientFrobenius, MulEquiv.apply_symm_apply, zpow_natCast]
  exact hn

open private valuativeEmbedding from LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

private theorem coefficientFrobenius_restrict {k k' : UnramifiedLevel F S} (h : k ≤ k') :
    restrictCoefficient h (coefficientFrobenius k') = coefficientFrobenius k := by
  let f := UnramifiedLevel.inclusion h
  letI : Algebra k.field k'.field := f.toRingHom.toAlgebra
  letI : IsScalarTower F k.field k'.field := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : ValuativeExtension k.field k'.field := ⟨fun a b => by
    rw [(valuation k'.field).vle_iff_le, (valuation k.field).vle_iff_le]
    exact valuativeEmbedding f a b⟩
  let s := coefficientFrobenius k'
  let t := restrictCoefficient h s
  have he := residueGaloisRestriction F k.field k'.field s
    (residueComparison k' s) (residueComparison k t)
    (residueComparison_reduces k' s) (residueComparison_reduces k t)
  apply (residueComparison k).injective
  ext z : 1
  apply (residueMap k.field k'.field).injective
  rw [residueComparison_frobenius, map_pow, ← he, residueComparison_frobenius]

open RamifiedExceptionalAuxiliaryTower (valuedAlgebraMap)

private theorem residue_action_through_tower {B H I E : Type u}
    [Field B] [Field H] [Field I] [Field E] [Algebra B H]
    [ValuativeRel B] [ValuativeRel H] [ValuativeRel I] [ValuativeRel E]
    [ValuativeExtension B H]
    {f : H →+* I} {g : I →+* E} {s : Gal(H/B)} {a : E →+* E}
    (i : ValuedFieldMap f) (j : ValuedFieldMap g) (v : ValuedFieldMap a)
    (t : Gal(residue H / residue B)) (ht : Reduces s t)
    (hs : ∀ b, a (g (f b)) = g (f (s b))) (z : residue H) :
    v.residue (j.residue (i.residue z)) = j.residue (i.residue (t z)) := by
  obtain ⟨b, rfl⟩ := residue_surjective z
  obtain ⟨c, hc, hred⟩ := ht b
  have hInt : v.integers (j.integers (i.integers b)) = j.integers (i.integers c) := by
    apply Subtype.ext
    simp only [v.field_eq, j.field_eq, i.field_eq, hc, hs]
  rw [hred]
  change IsLocalRing.residue _ (v.integers (j.integers (i.integers b))) =
    IsLocalRing.residue _ (j.integers (i.integers c))
  exact congrArg (IsLocalRing.residue _) hInt

private theorem auxiliary_residue_frobenius (k : UnramifiedLevel F S) :
    ∀ z : residue (P.auxiliary.extension k).field,
      (P.auxiliary.actionValued k (coefficientFrobenius k)).residue z = z ^ Fintype.card κ := by
  let C := (X k).compositum
  let E := P.auxiliary.extension k
  let s := coefficientFrobenius k
  let a := P.auxiliary.actionValued k s
  let i : ValuedFieldMap (algebraMap k.field C.field) := valuedAlgebraMap
  let j : ValuedFieldMap (algebraMap C.field E.field) := valuedAlgebraMap
  have hsurj : Function.Surjective (j.residue.comp i.residue) :=
    E.residue_bijective.2.comp (P.auxiliary.coefficientResidue_bijective k).2
  intro z
  obtain ⟨w, hw⟩ := hsurj z
  have hs (b : k.field) :
      P.auxiliary.action k s (algebraMap C.field E.field (algebraMap k.field C.field b)) =
        algebraMap C.field E.field (algebraMap k.field C.field (s b)) :=
    (P.auxiliary.action_extends k s _).trans
      (congrArg (algebraMap C.field E.field) (C.coefficient_extends s b))
  let r := j.residue.comp i.residue
  have h : a.residue (r w) = r (residueComparison k s w) :=
    residue_action_through_tower (B := F) (H := k.field) (I := C.field) (E := E.field)
      (s := s) i j a (residueComparison k s) (residueComparison_reduces k s) hs w
  have hq := residueComparison_frobenius k w
  calc
    a.residue z = a.residue (r w) := congrArg a.residue hw.symm
    _ = r (residueComparison k s w) := h
    _ = r (w ^ Fintype.card κ) := congrArg r hq
    _ = r w ^ Fintype.card κ := map_pow r w _
    _ = z ^ Fintype.card κ := congrArg (· ^ Fintype.card κ) hw

omit [Fintype (ExceptionalAffineBruhat.residue F)] in
private theorem scale_reduction_action (k : UnramifiedLevel F S) (s : Gal(k.field/F))
    (g : (X k).parahoric J) :
    (P.scale k).reduction (faceCoefficient P k s g) =
      scalarPoints M (P.auxiliary.actionValued k s).residue ((P.scale k).reduction g) := by
  let a := P.auxiliary.actionValued k s
  let a' : Specs.RamifiedExceptionalLocalFaceCoordinates.ValuedFieldMap
      (P.auxiliary.action k s).toRingHom :=
    { integers := a.integers
      isLocal := a.isLocal
      field_eq := a.field_eq }
  exact ((P.scale k).equivariant s (P.auxiliary.action k s) a'
    (P.auxiliary.action_extends k s) (P.auxiliary.action_fixes_root k s) g).2

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem fibrePointsEquiv_frobenius
    (p : GeometricPoints (markedFibre (F := F) (M := M)).val.X) :
    fibrePointsEquiv (F := F) (M := M) (frobeniusOnPoints Tκ p) =
      scalarPoints M (FiniteField.frobeniusAlgHom κ K).toRingHom
        (fibrePointsEquiv (F := F) (M := M) p) :=
  forgetFibrePoint_natural M.group (CommAlgCat.ofHom (FiniteField.frobeniusAlgHom κ K)) p

private theorem fibreReduction_frobenius (k : UnramifiedLevel F S) (g : (X k).parahoric J) :
    fibreReduction P k (faceAction P k (coefficientFrobenius k) g) =
      frobeniusOnPoints Tκ (fibreReduction P k g) := by
  let s := coefficientFrobenius k
  let f := P.auxiliary.residueEmbedding k
  let a := P.auxiliary.actionValued k s
  let b := FiniteField.frobeniusAlgHom κ K
  have hf : f.comp a.residue = b.toRingHom.comp f := by
    apply RingHom.ext
    intro z
    change f (a.residue z) = f z ^ Fintype.card κ
    rw [auxiliary_residue_frobenius P k, map_pow]
  apply (fibrePointsEquiv (F := F) (M := M)).injective
  rw [fibrePointsEquiv_reduction, fibrePointsEquiv_frobenius, fibrePointsEquiv_reduction]
  let z := (P.scale k).reduction g
  calc
    P.geometricReduction k (faceAction P k s g) = scalarPoints M f (scalarPoints M a.residue z) :=
      congrArg (scalarPoints M f) (scale_reduction_action P k s g)
    _ = scalarPoints M (f.comp a.residue) z := scalarPoints_comp_apply a.residue f z
    _ = scalarPoints M (b.toRingHom.comp f) z :=
      congrArg (fun e => scalarPoints M e z) hf
    _ = scalarPoints M b.toRingHom (P.geometricReduction k g) :=
      (scalarPoints_comp_apply f b.toRingHom z).symm

private def coefficientStages :
    CoefficientStages (markedFibre (F := F) (M := M)) (fibreImage P) (UnramifiedLevel F S) where
  Coeff k := GrpCat.of ((X k).parahoric J)
  Gal k := GrpCat.of Gal(k.field/F)
  galFinite _ := inferInstance
  generator := coefficientFrobenius
  cyclic := coefficientFrobenius_cyclic
  act := faceAction P
  extend h := faceInclusion X h J (P.face_comap h)
  restrict := restrictCoefficient
  restrict_generator := coefficientFrobenius_restrict
  reduction := fibreReduction P
  reduction_extend h z := congrArg (fibrePointsEquiv (F := F) (M := M)).symm
    (geometricReduction_natural P h z)
  reduction_generator := fibreReduction_frobenius P
  extend_action := faceAction_extend P
  image_eq := fibreReduction_image P

end Tower

/-- The first Lang correction on the scaled reduction image of the marked face. -/
theorem parahoricResidueDescent : ParahoricResidueDescent.{u} := by
  intro F L S _ _ _ _ _ _ _ _ _ _ _ _ _ _ D M R τ A X J π d y ϖ x P Q k c hc
  classical
  letI : Finite (residue F) :=
    IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation F
  letI : Fintype (residue F) := Fintype.ofFinite _
  letI : IsDirectedOrder (UnramifiedLevel F S) := ⟨P.auxiliary.directed⟩
  obtain ⟨l, h, b, hb⟩ := LinearAlgebraicGroups.RamifiedExceptionalResidueCorrection.residueLangCorrection
    (residue F) _ _ (fibreParameters P Q) (fibreGenerators P Q) _ (coefficientStages P) k c hc
  refine ⟨l, h, b, fun s => ?_⟩
  let f := P.auxiliary.residueEmbedding l
  have hgeom := congrArg (fibrePointsEquiv (F := F) (M := M)) (hb s)
  change fibrePointsEquiv (F := F) (M := M) (fibreReduction P l _) = _ at hgeom
  simp only [fibreReduction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, map_one] at hgeom
  apply RamifiedExceptionalLocalFaceCoordinates.changeRing_injective_of_affine M.affine
    (integralRingMap f) f.injective
  change scalarPoints M f _ = scalarPoints M f 1
  rw [map_one]
  exact hgeom

end

end LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalParahoricResidueDescent
