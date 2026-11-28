import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.JetEquivariantRestriction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertFiniteJetActions
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertProductAttachments
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open TopologicalSpace Topology Opposite
open scoped ZeroObject

namespace RepTheorySurvey.Geometric.EquivariantIntersectionComplexes

open Analytic Analytic.IntersectionComplex LocalSheaf
open EquivariantIntersectionComplexesSpecs SchubertIntersectionConstructibilitySpecs
open DerivedLocalSheaves (derivedInverseDirectAdjunctionData)

open ConvolutionConstantDescentSpec (shiftedConstantPullback)

open private closedInverseAdjunction pullbackIdentityIso strictMapBijective
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem derivedAdjunctionExists : Nonempty DerivedAdjunctions.{0} :=
  ⟨fun f => derivedInverseDirectAdjunctionData f⟩

theorem closedAdjunctionExists {X : TopCat.{0}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (boundedBelowInverseImage (closedInclusion Z) ⊣ LocalSheaf.closedExtensionPlus hZ) :=
  ⟨closedInverseAdjunction hZ⟩

/-- The map of parameter spaces induced by a map of the spaces acted on. -/
abbrev productMap (T : TopCat.{0}) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    TopCat.of (T × X) ⟶ TopCat.of (T × Y) :=
  SchubertProductAttachmentsSpecs.productMap T f

abbrev productProjection (T X : TopCat.{0}) : TopCat.of (T × X) ⟶ X :=
  SchubertProductAttachmentsSpecs.productProjection T X

theorem productMap_open (T : TopCat.{0}) {X Y : TopCat.{0}} {f : X ⟶ Y}
    (hf : IsOpenEmbedding f) : IsOpenEmbedding (productMap T f) :=
  SchubertProductAttachmentsSpecs.productMap_open T hf

theorem productSquare (T : TopCat.{0}) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    productMap T f ≫ productProjection T Y = productProjection T X ≫ f :=
  SchubertProductAttachmentsSpecs.projectionSquare T f

/-- A filtration on the product with a smooth parameter space of dimension `e`. -/
def productFiltration (T : TopCat.{0}) (e : ℕ) {X : TopCat.{0}} {s : ℕ} :
    DimensionFiltration X s → DimensionFiltration (TopCat.of (T × X)) (s + e)
  | .top X d => .top (TopCat.of (T × X)) (d + e)
  | .attach D j hj hs => .attach (productFiltration T e D) (productMap T j)
      (productMap_open T hj) (Nat.add_lt_add_right hs e)

/-- The stages before the final attachment determine a particular inclusion of the open top. -/
def topSpace {X : TopCat.{0}} {s : ℕ} : DimensionFiltration X s → TopCat.{0}
  | .top X _ => X
  | .attach D _ _ _ => topSpace D

def topDimension {X : TopCat.{0}} {s : ℕ} : DimensionFiltration X s → ℕ
  | .top _ d => d
  | .attach D _ _ _ => topDimension D

def topInclusion {X : TopCat.{0}} {s : ℕ} (D : DimensionFiltration X s) :
    topSpace D ⟶ X :=
  match D with
  | .top X _ => 𝟙 X
  | .attach D j _ _ => topInclusion D ≫ j

/-- Strictness at every attachment, with each earlier complex obtained by actual open
restriction. This describes the full subcategory on which restriction to the top is fully
faithful. -/
def StrictAlong {X : TopCat.{0}} {s : ℕ} (D : DimensionFiltration X s) :
    BoundedBelow X → Prop :=
  match D with
  | .top _ _ => fun _ => True
  | .attach D j hj _ => fun F =>
      IsStrictExtension hj s F ∧ StrictAlong D ((boundedBelowInverseImage j).obj F)

/-- The top identification uses the truncation inclusion and the derived counit at each
open attachment. -/
def topRestriction (a : DerivedAdjunctions) {X : TopCat.{0}} {s : ℕ}
    (D : DimensionFiltration X s) :
    (boundedBelowInverseImage (topInclusion D)).obj (complex D) ⟶
      shiftedConstant (topSpace D) (topDimension D) :=
  match D with
  | .top X d => ObjectProperty.homMk (shiftedConstantPullback (𝟙 X) d).hom
  | .attach D j hj _ =>
      (boundedBelowPullbackComposition (topInclusion D) j).hom.app _ ≫
        (boundedBelowInverseImage (topInclusion D)).map
          (attachmentRestriction D j hj (a j)) ≫ topRestriction a D

theorem topRestrictionBijective {X : TopCat.{0}} {s : ℕ} (D : DimensionFiltration X s) :
    ∀ (F G : BoundedBelow X), StrictAlong D F → StrictAlong D G →
      Function.Bijective ((boundedBelowInverseImage (topInclusion D)).map : (F ⟶ G) → _) := by
  induction D with
  | top X d =>
    intro F G _ _
    let e := pullbackIdentityIso X
    change Function.Bijective ((boundedBelowInverseImage (𝟙 X)).map : (F ⟶ G) → _)
    have h (f : F ⟶ G) :
        (boundedBelowInverseImage (𝟙 X)).map f = (Iso.homCongr (e.app F).symm (e.app G).symm) f := by
      change _ = (e.hom.app F) ≫ (𝟭 (BoundedBelow X)).map f ≫ e.inv.app G
      rw [← e.hom.naturality_assoc f, Iso.hom_inv_id_app, Category.comp_id]
    rw [funext h]
    exact Equiv.bijective _
  | @attach U X d s D j hj hs ih =>
    intro F G hF hG
    obtain ⟨hF, hFU⟩ : IsStrictExtension hj s F ∧
        StrictAlong D ((boundedBelowInverseImage j).obj F) := hF
    obtain ⟨hG, hGU⟩ : IsStrictExtension hj s G ∧
        StrictAlong D ((boundedBelowInverseImage j).obj G) := hG
    let P := boundedBelowInverseImage (topInclusion D)
    let L := boundedBelowInverseImage j
    let C := boundedBelowInverseImage (topInclusion D ≫ j)
    let e := boundedBelowPullbackComposition (topInclusion D) j
    let c := Iso.homCongr (e.app F).symm (e.app G).symm
    change Function.Bijective (C.map : (F ⟶ G) → _)
    have h (f : F ⟶ G) : C.map f = c (P.map (L.map f)) := by
      change _ = e.hom.app F ≫ (L ⋙ P).map f ≫ e.inv.app G
      rw [← e.hom.naturality_assoc f, Iso.hom_inv_id_app, Category.comp_id]
    rw [funext h]
    exact c.bijective.comp ((ih _ _ hFU hGU).comp (strictMapBijective hj s hF hG))

/-- An isomorphism of open top restrictions lifts with its prescribed map
when both complexes are strict through the filtration. -/
theorem liftTopIso {X : TopCat.{0}} {s : ℕ} (D : DimensionFiltration X s)
    {F G : BoundedBelow X} (hF : StrictAlong D F) (hG : StrictAlong D G)
    (c : (boundedBelowInverseImage (topInclusion D)).obj F ≅
      (boundedBelowInverseImage (topInclusion D)).obj G) :
    ∃ e : F ≅ G, (boundedBelowInverseImage (topInclusion D)).map e.hom = c.hom := by
  let R := boundedBelowInverseImage (topInclusion D)
  obtain ⟨f, hf⟩ := (topRestrictionBijective D F G hF hG).2 c.hom
  obtain ⟨g, hg⟩ := (topRestrictionBijective D G F hG hF).2 c.inv
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply (topRestrictionBijective D F F hF hF).1
    change R.map (f ≫ g) = R.map (𝟙 F)
    rw [R.map_comp, R.map_id, hf, hg, c.hom_inv_id]
  · apply (topRestrictionBijective D G G hG hG).1
    change R.map (g ≫ f) = R.map (𝟙 G)
    rw [R.map_comp, R.map_id, hf, hg, c.inv_hom_id]

private theorem derivedPullbackIsLE {X Y : TopCat.{0}} (f : X ⟶ Y) (F : Derived Y)
    (q : ℤ) (h : F.IsLE q) : ((derivedInverseImage f).obj F).IsLE q := by
  obtain ⟨K, e, hK⟩ := h
  let L := inverseImage f
  refine ⟨(L.mapHomologicalComplex (.up ℤ)).obj K,
    (derivedInverseImage f).mapIso e ≪≫ L.mapDerivedCategoryFactors.app K, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact L.map_isZero (K.isZero_of_isStrictlyLE q i hi)

private theorem derivedPullbackIsGE {X Y : TopCat.{0}} (f : X ⟶ Y) (F : Derived Y)
    (q : ℤ) (h : F.IsGE q) : ((derivedInverseImage f).obj F).IsGE q := by
  obtain ⟨K, e, hK⟩ := h
  let L := inverseImage f
  refine ⟨(L.mapHomologicalComplex (.up ℤ)).obj K,
    (derivedInverseImage f).mapIso e ≪≫ L.mapDerivedCategoryFactors.app K, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact L.map_isZero (K.isZero_of_isStrictlyGE q i hi)

/-- A distinguished truncation triangle is characterized by its degree bounds. -/
private theorem triangleLiftBijective {X : TopCat.{0}} {T : Triangle (Derived X)}
    (hT : T ∈ distTriang (Derived X)) (q : ℤ)
    (h₃ : T.obj₃.IsGE (q + 1)) (A : Derived X) (hA : A.IsLE q) :
    Function.Bijective (fun f : A ⟶ T.obj₁ => f ≫ T.mor₁) := by
  let t := DerivedCategory.TStructure.t (C := Sheaves X)
  letI : t.IsGE T.obj₃ (q + 1) := h₃
  have hInv : t.IsGE T.invRotate.obj₁ (q + 2) :=
    t.isGE_shift T.obj₃ (q + 1) (-1) (q + 2) (by omega)
  constructor
  · intro f g h
    have hh : (f - g) ≫ T.invRotate.mor₂ = 0 := by
      change (f - g) ≫ T.mor₁ = 0
      change f ≫ T.mor₁ = g ≫ T.mor₁ at h
      rw [Preadditive.sub_comp, h, sub_self]
    obtain ⟨m, hm⟩ := T.invRotate.coyoneda_exact₂ (inv_rot_of_distTriang T hT) _ hh
    exact sub_eq_zero.mp (by rw [hm, t.zero_of_isLE_of_isGE m q (q + 2)
      (by omega) hA hInv, zero_comp])
  · intro f
    obtain ⟨m, hm⟩ := T.coyoneda_exact₂ hT f
      (t.zero_of_isLE_of_isGE _ q (q + 1) (by omega) hA h₃)
    exact ⟨m, hm.symm⟩

set_option maxHeartbeats 400000 in
/-- Exact derived inverse image commutes with upper truncation, compatibly with the
map from the truncation to the original complex. -/
theorem pullbackTruncation {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℤ) :
    let L := derivedInverseImage f
    let t := DerivedCategory.TStructure.t (C := Sheaves Y)
    let u := DerivedCategory.TStructure.t (C := Sheaves X)
    ∃ c : t.truncLE q ⋙ L ≅ L ⋙ u.truncLE q,
      ∀ F : Derived Y, c.hom.app F ≫ (u.truncLEι q).app (L.obj F) =
        L.map ((t.truncLEι q).app F) := by
  let L := (inverseImage f).mapDerivedCategory
  let t := DerivedCategory.TStructure.t (C := Sheaves Y)
  let u := DerivedCategory.TStructure.t (C := Sheaves X)
  haveI : L.IsTriangulated := inferInstanceAs ((inverseImage f).mapDerivedCategory.IsTriangulated)
  haveI (F : Derived Y) : u.IsLE (L.obj ((t.truncLE q).obj F)) q :=
    derivedPullbackIsLE f _ q inferInstance
  let c (F : Derived Y) : L.obj ((t.truncLE q).obj F) ⟶ (u.truncLE q).obj (L.obj F) :=
    u.liftTruncLE (L.map ((t.truncLEι q).app F)) q
  have hc (F : Derived Y) : c F ≫ (u.truncLEι q).app (L.obj F) =
      L.map ((t.truncLEι q).app F) := u.liftTruncLE_ι _ _
  haveI (F : Derived Y) : IsIso (c F) := by
    let T := L.mapTriangle.obj ((t.triangleLEGT q).obj F)
    have hT : T ∈ distTriang (Derived X) :=
      L.map_distinguished _ (t.triangleLEGT_distinguished q F)
    have h₃ : T.obj₃.IsGE (q + 1) := derivedPullbackIsGE f _ _ (by
      change t.IsGE ((t.truncGE (q + 1)).obj F) (q + 1)
      infer_instance)
    let G := (u.truncLE q).obj (L.obj F)
    obtain ⟨d, hd⟩ := (triangleLiftBijective hT q h₃ G
      (by change u.IsLE ((u.truncLE q).obj (L.obj F)) q; infer_instance)).2
        ((u.truncLEι q).app (L.obj F))
    change d ≫ L.map ((t.truncLEι q).app F) = _ at hd
    refine ⟨d, ?_, ?_⟩
    · apply (triangleLiftBijective hT q h₃ T.obj₁ (by
        change u.IsLE (L.obj ((t.truncLE q).obj F)) q
        infer_instance)).1
      change (c F ≫ d) ≫ L.map ((t.truncLEι q).app F) =
        𝟙 _ ≫ L.map ((t.truncLEι q).app F)
      rw [Category.assoc, hd, hc, Category.id_comp]
    · apply u.to_truncLE_obj_ext
      rw [Category.assoc, hc, hd, Category.id_comp]
  refine ⟨NatIso.ofComponents (fun F => asIso (c F)) (fun {F G} g => ?_), hc⟩
  change L.map ((t.truncLE q).map g) ≫ c G = c F ≫ (u.truncLE q).map (L.map g)
  apply u.to_truncLE_obj_ext
  rw [Category.assoc, hc, Category.assoc, (u.truncLEι q).naturality, ← Category.assoc, hc]
  simp only [Functor.id_map, ← L.map_comp]
  exact congrArg L.map ((t.truncLEι q).naturality g)

def HasOpenComplexCoordinates (T : TopCat.{0}) (e : ℕ) : Prop :=
  ∃ V : Opens (Fin e → ℂ), Nonempty (T ≃ₜ V)

section JetParameters

open LatticeModelSpecs BoundedLatticeSpecs Matrix

/-- The matrix entries of the regular representation detect the units of a
finite-dimensional algebra, and recover their inverses continuously. -/
private theorem inducedUnitsTopology {A ι : Type} [Ring A] [Algebra ℂ A] [TopologicalSpace A]
    [IsModuleTopology ℂ A] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ A) :
    @IsTopologicalGroup Aˣ (TopologicalSpace.induced (Units.val : Aˣ → A) inferInstance)
      inferInstance ∧ IsOpen {x : A | IsUnit x} := by
  let M : A →ₐ[ℂ] Matrix ι ι ℂ :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul ℂ A)
  have hM : Continuous M := IsModuleTopology.continuous_of_linearMap M.toLinearMap
  have hUnit (x : A) : IsUnit x ↔ (M x).det ≠ 0 := by
    change IsUnit x ↔
      (LinearMap.toMatrixAlgEquiv b (Algebra.lmul ℂ A x)).det ≠ 0
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    let e := LinearMap.toMatrixAlgEquiv b
    exact Algebra.lmul_isUnit_iff.symm.trans
      (isUnit_map_of_leftInverse e.symm.toAlgHom e.symm_apply_apply).symm
  haveI : Module.Finite ℂ A := Module.Finite.of_basis b
  letI : IsTopologicalRing A := IsModuleTopology.isTopologicalRing ℂ A
  letI : TopologicalSpace Aˣ := .induced (Units.val : Aˣ → A) inferInstance
  change IsTopologicalGroup Aˣ ∧ _
  have hv : Continuous (Units.val : Aˣ → A) := continuous_induced_dom
  let E : Matrix ι ι ℂ →ₗ[ℂ] A :=
    (LinearMap.applyₗ' ℂ (1 : A)).comp (Matrix.toLinAlgEquiv b).toLinearMap
  letI : IsModuleTopology ℂ (Matrix ι ι ℂ) :=
    inferInstanceAs (IsModuleTopology ℂ (ι → ι → ℂ))
  have hE : Continuous E := IsModuleTopology.continuous_of_linearMap E
  have hInv (u : Aˣ) : E ((M u.val)⁻¹) = (u⁻¹).val := by
    let v := Units.map M.toMonoidHom u
    have hv' : (M u.val)⁻¹ = M (u⁻¹).val := (Matrix.GeneralLinearGroup.coe_inv v).symm
    rw [hv']
    change (Matrix.toLinAlgEquiv b (LinearMap.toMatrixAlgEquiv b
      (Algebra.lmul ℂ A (u⁻¹).val))) 1 = (u⁻¹).val
    rw [← LinearMap.toMatrixAlgEquiv_symm, AlgEquiv.symm_apply_apply]
    exact mul_one _
  have hMatInv : Continuous (fun u : Aˣ => (M u.val)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hd : (M u.val).det ≠ 0 := (hUnit u.val).mp u.isUnit
    have hi : ContinuousAt Ring.inverse (M u.val).det := by
      rw [show (Ring.inverse : ℂ → ℂ) = Inv.inv from funext Ring.inverse_eq_inv]
      exact continuousAt_inv₀ hd
    have hInput : ContinuousAt (fun v : Aˣ => M v.val) u :=
      (hM.comp hv).continuousAt
    exact ContinuousAt.comp_of_eq (continuousAt_matrix_inv _ hi) hInput rfl
  refine ⟨{ continuous_mul := continuous_induced_rng.mpr (hv.fst'.mul hv.snd')
            continuous_inv := ?_ }, ?_⟩
  · apply continuous_induced_rng.mpr
    exact (hE.comp hMatInv).congr hInv
  · convert isOpen_ne_fun (hM.matrix_det) continuous_const using 1
    exact Set.ext hUnit

private def jetCoefficientHomeomorph (n : ℕ) : JetRing n ≃ₜ (Fin n → ℂ) :=
  (jetCoefficients n).toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

private def jetMatrixCoordinates (n : ℕ) :
    Matrix (Fin 2) (Fin 2) (JetRing n) ≃L[ℂ] JetMatrixCoefficients 2 n where
  toLinearEquiv := LinearEquiv.piCongrRight (fun _ : Fin 2 =>
    LinearEquiv.piCongrRight (fun _ : Fin 2 => jetCoefficients n))
  continuous_toFun := continuous_id.matrix_map (jetCoefficientHomeomorph n).continuous
  continuous_invFun := continuous_id.matrix_map (jetCoefficientHomeomorph n).symm.continuous

private lemma jetCoefficients_truncate {m n : ℕ} (h : m ≤ n) (x : JetRing n) (i : Fin m) :
    jetCoefficients m (truncateJet h x) i = jetCoefficients n x (Fin.castLE h i) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  change jetCoefficients m (jetReduction m s) i =
    jetCoefficients n (jetReduction n s) (Fin.castLE h i)
  rw [jetCoefficients_reduce, jetCoefficients_reduce]
  rfl

private theorem continuous_truncateJet {m n : ℕ} (h : m ≤ n) :
    Continuous (truncateJet h) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  simp only [Function.comp_apply, jetCoefficients_truncate]
  exact (continuous_apply (Fin.castLE h i)).comp continuous_induced_dom

private theorem jetMatrixOfUnitOpen (k : ℕ) :
    IsTopologicalGroup (PositiveJet k) ∧
      IsOpenEmbedding (fun g : PositiveJet k => jetMatrixCoefficients g.val) := by
  let n := k + 1
  let C := jetMatrixCoordinates n
  letI : IsModuleTopology ℂ (JetMatrixCoefficients 2 n) :=
    inferInstanceAs (IsModuleTopology ℂ (Fin 2 → Fin 2 → Fin n → ℂ))
  letI : IsModuleTopology ℂ (Matrix (Fin 2) (Fin 2) (JetRing n)) :=
    IsModuleTopology.iso C.symm
  let flatten : JetMatrixCoefficients 2 n ≃ₗ[ℂ] (Fin 2 × Fin 2 × Fin n → ℂ) :=
    { toFun := fun a i => a i.1 i.2.1 i.2.2
      invFun := fun a i j k => a (i, j, k)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let B := Module.Basis.ofEquivFun (C.toLinearEquiv ≪≫ₗ flatten)
  obtain ⟨hGroup, hOpen⟩ := inducedUnitsTopology B
  have hVal : IsOpenEmbedding (fun g : PositiveJet k => g.val) := by
    refine ⟨⟨⟨rfl⟩, Units.val_injective⟩, ?_⟩
    convert hOpen using 1
    exact Set.ext (fun _ => Iff.rfl)
  exact ⟨hGroup, C.toHomeomorph.isOpenEmbedding.comp hVal⟩

/-- The coefficient topology on the positive GL₂ jets and its continuous truncations. -/
theorem gl2JetParameters : GL2JetParameters where
  topologicalGroup k := (jetMatrixOfUnitOpen k).1
  truncation {k l} h := by
    apply continuous_induced_rng.mpr
    have hv : @Continuous (PositiveJet l) (Matrix (Fin 2) (Fin 2) (JetRing (l + 1)))
        (glJetTopology 2 (l + 1) (Nat.succ_pos l)) _ Units.val :=
      continuous_induced_dom
    exact hv.matrix_map (continuous_truncateJet (Nat.succ_le_succ h))
  coefficientOpen k := (jetMatrixOfUnitOpen k).2

private def jetMatrixFlatten (n : ℕ) : JetMatrixCoefficients 2 n ≃ₜ (Fin (4 * n) → ℂ) := by
  let I := Fin 2 × Fin 2 × Fin n
  let indices : I ≃ Fin (4 * n) := Fintype.equivFinOfCardEq (by
    simp only [I, Fintype.card_prod, Fintype.card_fin]
    omega)
  let e : JetMatrixCoefficients 2 n ≃ (I → ℂ) :=
    { toFun := fun a i => a i.1 i.2.1 i.2.2
      invFun := fun a i j k => a (i, j, k)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let c : JetMatrixCoefficients 2 n ≃ₜ (I → ℂ) :=
    { toEquiv := e
      continuous_toFun := continuous_pi fun i => (continuous_apply i.2.2).comp
        ((continuous_apply i.2.1).comp (continuous_apply i.1))
      continuous_invFun := continuous_matrix fun i j => continuous_pi fun r =>
        continuous_apply ((i, j, r) : I) }
  exact c.trans (Homeomorph.piCongrLeft (Y := fun _ => ℂ) indices)

theorem gl2JetCoordinates (J : GL2JetParameters) (k : ℕ) :
    HasOpenComplexCoordinates (J.toJetSystem.group k).space (4 * (k + 1)) := by
  have h := (jetMatrixFlatten (k + 1)).isOpenEmbedding.comp (J.coefficientOpen k)
  exact ⟨⟨_, h.isOpen_range⟩, ⟨h.isEmbedding.toHomeomorph⟩⟩

theorem gl2JetProductCoordinates (J : GL2JetParameters) (k l : ℕ) :
    HasOpenComplexCoordinates
      (TopCat.of ((J.toJetSystem.group k).space × (J.toJetSystem.group l).space))
      (4 * (k + 1) + 4 * (l + 1)) := by
  have h₁ := (jetMatrixFlatten (k + 1)).isOpenEmbedding.comp (J.coefficientOpen k)
  have h₂ := (jetMatrixFlatten (l + 1)).isOpenEmbedding.comp (J.coefficientOpen l)
  let a := 4 * (k + 1)
  let b := 4 * (l + 1)
  let e : ((Fin a → ℂ) × (Fin b → ℂ)) ≃ₜ (Fin (a + b) → ℂ) :=
    (Homeomorph.sumPiEquivProdPi (Fin a) (Fin b) (fun _ => ℂ)).symm.trans
      (Homeomorph.piCongrLeft (Y := fun _ => ℂ) finSumFinEquiv)
  have h := e.isOpenEmbedding.comp (h₁.prodMap h₂)
  exact ⟨⟨_, h.isOpen_range⟩, ⟨h.isEmbedding.toHomeomorph⟩⟩

end JetParameters

def RealizesProductStrata (T : TopCat.{0}) (e : ℕ) {X : TopCat.{0}}
    (P : Stratification X) (Q : Stratification (TopCat.of (T × X))) : Prop :=
  ∃ b : P.Index ≃ Q.Index, ∀ i : P.Index,
    Set.range (Q.stratum (b i)).inclusion =
      (productProjection T X) ⁻¹' Set.range (P.stratum i).inclusion ∧
    (Q.stratum (b i)).complexDimension = (P.stratum i).complexDimension + e

section ProductStrata

private def productStratumProjection (T : TopCat.{0}) {X : TopCat.{0}} (S : Stratum X) :
    (Opens.map (productProjection T X)).obj S.ambientOpen → S.ambientOpen :=
  fun p => ⟨p.val.2, p.property⟩

def productStratum (T : TopCat.{0}) (e : ℕ) {X : TopCat.{0}} (S : Stratum X) :
    Stratum (TopCat.of (T × X)) where
  ambientOpen := (Opens.map (productProjection T X)).obj S.ambientOpen
  subset := productStratumProjection T S ⁻¹' S.subset
  closed := S.closed.preimage
    (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _)
  complexDimension := S.complexDimension + e

theorem productStratum_range (T : TopCat.{0}) (e : ℕ) {X : TopCat.{0}} (S : Stratum X) :
    Set.range (productStratum T e S).inclusion =
      productProjection T X ⁻¹' Set.range S.inclusion := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨⟨productStratumProjection T S q.val, q.property⟩, rfl⟩
  · rintro ⟨q, hq⟩
    have hp : p.2 = q.val.val := hq.symm
    obtain ⟨t, x⟩ := p
    dsimp only at hp
    subst x
    exact ⟨⟨⟨(t, q.val.val), q.val.property⟩, q.property⟩, rfl⟩

/-- Use the actual locally closed product subspaces as the product stratification. -/
def productStratification (T : TopCat.{0}) (e : ℕ) {X : TopCat.{0}} (P : Stratification X) :
    Stratification (TopCat.of (T × X)) where
  Index := P.Index
  stratum i := productStratum T e (P.stratum i)
  partition p := by
    change ∃! i : P.Index, p ∈ Set.range (productStratum T e (P.stratum i)).inclusion
    have h (i : P.Index) : p ∈ Set.range (productStratum T e (P.stratum i)).inclusion ↔
        p.2 ∈ Set.range (P.stratum i).inclusion :=
      Set.ext_iff.mp (productStratum_range T e (P.stratum i)) p
    obtain ⟨i, hi, hu⟩ := P.partition p.2
    exact ⟨i, (h i).mpr hi, fun j hj => hu j ((h j).mp hj)⟩

theorem productStratification_realizes (T : TopCat.{0}) (e : ℕ)
    {X : TopCat.{0}} (P : Stratification X) :
    RealizesProductStrata T e P (productStratification T e P) :=
  ⟨Equiv.refl _, fun i => ⟨productStratum_range T e (P.stratum i), rfl⟩⟩

private theorem productMap_range (T : TopCat.{0}) {U X : TopCat.{0}}
    (j : U ⟶ X) : Set.range (productMap T j) = productProjection T X ⁻¹' Set.range j := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.2, rfl⟩
  · rintro ⟨u, hu⟩
    exact ⟨(p.1, u), Prod.ext rfl hu⟩

private theorem productMap_image_preimage (T : TopCat.{0}) {U X : TopCat.{0}}
    (j : U ⟶ X) (S : Set U) :
    productMap T j '' (productProjection T U ⁻¹' S) = productProjection T X ⁻¹' (j '' S) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.2, hq, rfl⟩
  · rintro ⟨u, hu, hq⟩
    exact ⟨(p.1, u), hu, Prod.ext rfl hq⟩

/-- Taking a product carries each open attachment to the attachment of the product
closed stratum, with every dimension raised by the parameter dimension. -/
def productAttachmentStratification (T : TopCat.{0}) (e : ℕ) {U X : TopCat.{0}}
    {j : U ⟶ X} {s : ℕ} {P : Stratification U} {Q : Stratification X}
    (h : AttachmentStratification j s P Q) :
    AttachmentStratification (productMap T j) (s + e)
      (productStratification T e P) (productStratification T e Q) where
  closedIndex := h.closedIndex
  previousIndex := h.previousIndex
  closedRange := by
    change Set.range (productStratum T e (Q.stratum h.closedIndex)).inclusion =
      boundary (productMap T j)
    rw [productStratum_range, h.closedRange, boundary, boundary, productMap_range]
    rfl
  closedDimension := congrArg (· + e) h.closedDimension
  previousRange p := by
    change Set.range (productStratum T e (Q.stratum (h.previousIndex p).val)).inclusion =
      productMap T j '' Set.range (productStratum T e (P.stratum p)).inclusion
    rw [productStratum_range, productStratum_range, h.previousRange p, productMap_image_preimage]
  previousDimension p := congrArg (· + e) (h.previousDimension p)
  dimension_lt p := Nat.add_lt_add_right (h.dimension_lt p) e

end ProductStrata

section ActionOnOpenStages

/-- Acting by a continuously specified element of the group gives a homeomorphism
over the parameter space. This includes the product of two successive group elements. -/
def parameterTwist {H : AnalyticGroup.{0}} {X T : TopCat.{0}} (p : T ⟶ H.space)
    (A : AnalyticAction H X) : (T × X) ≃ₜ (T × X) where
  toFun v := (v.1, A.act (p v.1, v.2))
  invFun v := (v.1, A.act ((p v.1)⁻¹, v.2))
  left_inv v := Prod.ext rfl (by
    change A.act ((p v.1)⁻¹, A.act (p v.1, v.2)) = v.2
    rw [← A.mul_act, inv_mul_cancel, A.one_act])
  right_inv v := Prod.ext rfl (by
    change A.act (p v.1, A.act ((p v.1)⁻¹, v.2)) = v.2
    rw [← A.mul_act, mul_inv_cancel, A.one_act])
  continuous_toFun := continuous_fst.prodMk
    (A.act.hom.continuous.comp ((p.hom.continuous.comp continuous_fst).prodMk continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (A.act.hom.continuous.comp ((p.hom.continuous.comp continuous_fst).inv.prodMk continuous_snd))

/-- The homeomorphism converting the projection to the action on a parameter product. -/
def actionTwist {H : AnalyticGroup.{0}} {X : TopCat.{0}} (A : AnalyticAction H X) :
    (H.space × X) ≃ₜ (H.space × X) :=
  parameterTwist (𝟙 H.space) A

def invariantRange {H : AnalyticGroup.{0}} {X U : TopCat.{0}}
    (A : AnalyticAction H X) (j : U ⟶ X) : Prop :=
  ∀ h : H.space, ∀ u : U, A.act (h, j u) ∈ Set.range j

private def restrictActionFun {H : AnalyticGroup.{0}} {X U : TopCat.{0}}
    {A : AnalyticAction H X} {j : U ⟶ X} (h : invariantRange A j) (p : H.space × U) : U :=
  Classical.choose (h p.1 p.2)

private theorem restrictActionFun_apply {H : AnalyticGroup.{0}} {X U : TopCat.{0}}
    {A : AnalyticAction H X} {j : U ⟶ X} (h : invariantRange A j) (p : H.space × U) :
    j (restrictActionFun h p) = A.act (p.1, j p.2) :=
  Classical.choose_spec (h p.1 p.2)

/-- An invariant subspace inherits the analytic action through its embedding. -/
def restrictAction {H : AnalyticGroup.{0}} {X U : TopCat.{0}}
    {A : AnalyticAction H X} {j : U ⟶ X} (hj : IsEmbedding j) (h : invariantRange A j) :
    AnalyticAction H U where
  act := TopCat.ofHom ⟨restrictActionFun h, hj.isInducing.continuous_iff.mpr (by
    change Continuous (fun p => j (restrictActionFun h p))
    simp_rw [restrictActionFun_apply]
    exact A.act.hom.continuous.comp (continuous_fst.prodMk
      (j.hom.continuous.comp continuous_snd)))⟩
  one_act u := hj.injective ((restrictActionFun_apply h (1, u)).trans (A.one_act (j u)))
  mul_act g k u := hj.injective (by
    change j (restrictActionFun h (g * k, u)) =
      j (restrictActionFun h (g, restrictActionFun h (k, u)))
    rw [restrictActionFun_apply, restrictActionFun_apply, restrictActionFun_apply, A.mul_act])

theorem restrictAction_square {H : AnalyticGroup.{0}} {X U : TopCat.{0}}
    {A : AnalyticAction H X} {j : U ⟶ X} (hj : IsEmbedding j) (h : invariantRange A j) :
    productMap H.space j ≫ A.act = (restrictAction hj h).act ≫ j :=
  TopCat.ext (fun p => (restrictActionFun_apply h p).symm)

def restrictJetAction {J : JetSystem.{0}} {X U : TopCat.{0}}
    (A : JetAction J X) {j : U ⟶ X} (hj : IsEmbedding j)
    (h : ∀ k hk, invariantRange (A.action k hk) j) : JetAction J U where
  cutoff := A.cutoff
  action k hk := restrictAction hj (h k hk)
  factors hk hkl := by
    apply TopCat.ext
    intro p
    apply hj.injective
    change j (restrictActionFun (h _ hk) (_, p.2)) =
      j (restrictActionFun (h _ (hk.trans hkl)) p)
    simp only [restrictActionFun_apply]
    exact congrArg (fun f : TopCat.of ((J.group _).space × X) ⟶ X => f (p.1, j p.2))
      (A.factors hk hkl)

theorem restrictJetAction_commutes {J : JetSystem.{0}} {X U : TopCat.{0}}
    (A : JetAction J X) {j : U ⟶ X} (hj : IsEmbedding j)
    (h : ∀ k hk, invariantRange (A.action k hk) j) :
    JetMapsCommute (restrictJetAction A hj h) A j := by
  intro k _ hk
  exact restrictAction_square hj (h k hk)

theorem topInclusion_open {X : TopCat.{0}} {s : ℕ} (D : DimensionFiltration X s) :
    IsOpenEmbedding (topInclusion D) := by
  induction D with
  | top => exact IsOpenEmbedding.id
  | attach D j hj _ ih => exact hj.comp ih

open LatticeModelSpecs RankTwoSchubertStrataSpecs

theorem topInclusion_range {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {X : TopCat.{0}} {s k : ℕ} {f : X ⟶ SchubertSpace ab N hN} {P : Stratification X}
    {D : DimensionFiltration X s} (h : IsNormalizedOrbitIC ab N hN f k P D) :
    Set.range (topInclusion D ≫ f) = stagePoints ab N hN 0 := by
  induction h with
  | top f P stage _ =>
    change Set.range ((𝟙 _) ≫ f) = _
    rw [Category.id_comp]
    exact stage.2.1
  | attach f P Q j hj hs previous stage strata hBoundary hImage perverse strict ih =>
    change Set.range ((topInclusion _ ≫ j) ≫ f) = _
    rw [Category.assoc]
    exact ih

theorem topInclusion_invariant {J : GL2JetParameters} {ab : DominantPair} {N : ℕ}
    {hN : OrbitBound ab N} (A : SchubertJetAction J ab N hN)
    {s k : ℕ} {P : Stratification (SchubertSpace ab N hN)}
    {D : DimensionFiltration (SchubertSpace ab N hN) s}
    (h : IsNormalizedOrbitIC ab N hN (𝟙 _) k P D)
    (l : ℕ) (hl : A.action.cutoff ≤ l) :
    invariantRange (A.action.action l hl) (topInclusion D) := by
  have hTop := topInclusion_range h
  rw [Category.comp_id] at hTop
  intro g x
  have hx : topInclusion D x ∈ stagePoints ab N hN 0 :=
    hTop ▸ Set.mem_range_self x
  rw [hTop]
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨i, hi, (A.actual.2.2 l hl g (topInclusion D x) i).mpr hx⟩

end ActionOnOpenStages

section TopNormalization

theorem strictAlong_of_iso {X : TopCat.{0}} {s : ℕ} (D : DimensionFiltration X s)
    {F G : BoundedBelow X} (e : F ≅ G) (h : StrictAlong D F) : StrictAlong D G := by
  induction D with
  | top => trivial
  | @attach U X d s D j hj hs ih =>
    obtain ⟨⟨hL, hR⟩, hU⟩ : IsStrictExtension hj s F ∧
        StrictAlong D ((boundedBelowInverseImage j).obj F) := h
    change IsStrictExtension hj s G ∧ StrictAlong D ((boundedBelowInverseImage j).obj G)
    refine ⟨?_, ih ((boundedBelowInverseImage j).mapIso e) hU⟩
    let t := DerivedCategory.Plus.TStructure.t (C := Sheaves (TopCat.of (boundary j)))
    exact ⟨t.isLE_of_iso ((boundedBelowInverseImage (closedInclusion (boundary j))).mapIso e) _,
      t.isGE_of_iso ((derivedExtraordinaryInverseImage (boundary_isClosed hj)).mapIso e) _⟩

/-- The supplied normalized orbit filtration is strict through the whole filtration,
and its canonical top restriction is the specified shifted constant complex. -/
theorem normalizedOrbitIC_top {ab : LatticeModelSpecs.DominantPair} {N : ℕ}
    {hN : LatticeModelSpecs.OrbitBound ab N} {X : TopCat.{0}} {s k : ℕ}
    {f : X ⟶ SchubertSpace ab N hN} {P : Stratification X} {D : DimensionFiltration X s}
    (h : IsNormalizedOrbitIC ab N hN f k P D) (a : DerivedAdjunctions) :
    IsMiddlePerverse P (complex D).obj ∧ StrictAlong D (complex D) ∧
      IsIso (topRestriction a D) := by
  induction h with
  | @top Y f P stage hp =>
    refine ⟨hp, trivial, ?_⟩
    haveI : IsIso ((DerivedCategory.Plus.ι (C := Sheaves Y)).map
        (topRestriction a (.top Y (RankTwoSchubertStrataSpecs.difference ab)))) :=
      inferInstanceAs (IsIso (shiftedConstantPullback (𝟙 Y)
        (RankTwoSchubertStrataSpecs.difference ab)).hom)
    exact isIso_of_reflects_iso _ (DerivedCategory.Plus.ι (C := Sheaves Y))
  | @attach U X d k D f P Q j hj hs hPrev hStage H hBoundary hImage hPerverse hStrict ih =>
    let s := orbitDimension ab (k + 1)
    let E := (attachment j hj s).obj (complex D)
    let L := boundedBelowInverseImage j
    let r : L.obj E ⟶ complex D :=
      L.map ((attachmentInclusion j hj s).app (complex D)) ≫ (a j).counit.app (complex D)
    haveI : IsIso r :=
      (MiddleExtension.attachmentIsMiddleExtension j hj s Q P H (complex D) ih.1 hBoundary).2.2 (a j)
    let e := asIso r
    refine ⟨hPerverse, ⟨hStrict, strictAlong_of_iso D e.symm ih.2.1⟩, ?_⟩
    haveI : IsIso (topRestriction a D) := ih.2.2
    change IsIso ((boundedBelowPullbackComposition (topInclusion D) j).hom.app E ≫
      (boundedBelowInverseImage (topInclusion D)).map r ≫ topRestriction a D)
    infer_instance

end TopNormalization

section ClosedBaseChange

open private embeddingIsoOfRange embeddingIsoOfRange_comp pullbackEquivalence
  derivedDirectImageComposition derivedClosedDirectIso pullbackStalkIso
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private def closedImageHomeomorphism {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsClosedEmbedding j) : U ≅ TopCat.of (Set.range j) :=
  embeddingIsoOfRange j (closedInclusion (Set.range j)) hj.isEmbedding
    IsEmbedding.subtypeVal Subtype.range_coe.symm

private theorem closedImageHomeomorphism_comp {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsClosedEmbedding j) :
    (closedImageHomeomorphism hj).hom ≫ closedInclusion (Set.range j) = j :=
  embeddingIsoOfRange_comp _ _ _ _ _

private def derivedClosedImageFactor {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsClosedEmbedding j) :
    derivedDirectImage j ≅ derivedDirectImage (closedImageHomeomorphism hj).hom ⋙
      closedExtensionPlus hj.isClosed_range :=
  eqToIso (congrArg (fun f => derivedDirectImage f) (closedImageHomeomorphism_comp hj).symm) ≪≫
    derivedDirectImageComposition (closedImageHomeomorphism hj).hom (closedInclusion (Set.range j)) ≪≫
    Functor.isoWhiskerLeft _ (derivedClosedDirectIso hj.isClosed_range)

private theorem derivedClosedImage_supported {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsClosedEmbedding j) (F : BoundedBelow U) :
    DerivedSupportedOn (Set.range j) ((derivedDirectImage j).obj F) :=
  (DerivedLocalSheaves.derivedSupportedEssentialImage hj.isClosed_range _).mp
    ⟨(derivedDirectImage (closedImageHomeomorphism hj).hom).obj F,
      ⟨((derivedClosedImageFactor hj).app F).symm⟩⟩

private theorem derivedClosedImageCounit_isIso {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsClosedEmbedding j) (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (F : BoundedBelow U) : IsIso (a.counit.app F) := by
  let v := closedImageHomeomorphism hj
  let e := pullbackEquivalence v
  letI : (boundedBelowInverseImage v.hom).IsEquivalence := e.isEquivalence_functor
  letI : (derivedDirectImage v.hom).IsEquivalence :=
    (derivedInverseDirectAdjunctionData v.hom).isEquivalence_right_of_isEquivalence_left
  obtain ⟨ff⟩ := DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hj.isClosed_range
  letI := ff.full
  letI := ff.faithful
  let a' := a.ofNatIsoRight (derivedClosedImageFactor hj)
  haveI : IsIso a'.counit := Adjunction.counit_isIso_of_R_fully_faithful a'
  have he : IsIso ((boundedBelowInverseImage j).map ((derivedClosedImageFactor hj).hom.app F)) :=
    (boundedBelowInverseImage j).map_isIso _
  let m := (boundedBelowInverseImage j).map ((derivedClosedImageFactor hj).hom.app F)
  have hc : m ≫ a'.counit.app F = a.counit.app F := by
    change m ≫ (boundedBelowInverseImage j).map ((derivedClosedImageFactor hj).inv.app F) ≫
      a.counit.app F = _
    unfold m
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, (boundedBelowInverseImage j).map_id,
      Category.id_comp]
  rw [← hc]
  infer_instance

private theorem closedPullback_reflectsIso {X : TopCat.{0}} {S : Set X} (hS : IsClosed S)
    {F G : BoundedBelow X} (v : F ⟶ G)
    (hF : DerivedSupportedOn S F) (hG : DerivedSupportedOn S G)
    (h : IsIso ((boundedBelowInverseImage (closedInclusion S)).map v)) : IsIso v := by
  let L := boundedBelowInverseImage (closedInclusion S)
  let R := closedExtensionPlus hS
  let a := closedInverseAdjunction hS
  obtain ⟨ff⟩ := DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hS
  letI := ff.full
  letI := ff.faithful
  have hUnit (E : BoundedBelow X) (hE : DerivedSupportedOn S E) : IsIso (a.unit.app E) := by
    obtain ⟨B, ⟨e⟩⟩ := (DerivedLocalSheaves.derivedSupportedEssentialImage hS E).mpr hE
    rw [← NatTrans.isIso_app_iff_of_iso a.unit e]
    letI : IsIso (a.counit.app B) := inferInstance
    haveI : IsIso (R.map (a.counit.app B)) := R.map_isIso _
    haveI : IsIso (a.unit.app (R.obj B) ≫ R.map (a.counit.app B)) := by
      rw [a.right_triangle_components]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (R.map (a.counit.app B))
  haveI : IsIso (a.unit.app F) := hUnit F hF
  haveI : IsIso (a.unit.app G) := hUnit G hG
  haveI : IsIso (R.map (L.map v)) := R.map_isIso _
  haveI : IsIso (v ≫ a.unit.app G) := by
    have hn := a.unit.naturality v
    change v ≫ a.unit.app G = a.unit.app F ≫ R.map (L.map v) at hn
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (a.unit.app G)

private theorem isIso_map_of_natIso {C D : Type*} [Category* C] [Category* D]
    {L R : C ⥤ D} (c : L ≅ R) {A B : C} (m : A ⟶ B) (h : IsIso (L.map m)) :
    IsIso (R.map m) := by
  have hi : IsIso (c.hom.app A ≫ R.map m) := by
    rw [← c.hom.naturality m]
    infer_instance
  exact IsIso.of_isIso_comp_left (c.hom.app A) _

private theorem closedEmbedding_reflectsIso {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsClosedEmbedding j) {F G : BoundedBelow X} (m : F ⟶ G)
    (hF : DerivedSupportedOn (Set.range j) F) (hG : DerivedSupportedOn (Set.range j) G)
    (h : IsIso ((boundedBelowInverseImage j).map m)) : IsIso m := by
  let w := closedImageHomeomorphism hj
  let i := closedInclusion (Set.range j)
  let c := boundedBelowPullbackComposition w.hom i
  have hMap : IsIso ((boundedBelowInverseImage (w.hom ≫ i)).map m) := by
    rw [closedImageHomeomorphism_comp hj]
    exact h
  haveI : IsIso ((boundedBelowInverseImage w.hom).map ((boundedBelowInverseImage i).map m)) :=
    isIso_map_of_natIso c m hMap
  let V := pullbackEquivalence w
  letI : (boundedBelowInverseImage w.hom).IsEquivalence := V.isEquivalence_functor
  exact closedPullback_reflectsIso hj.isClosed_range m hF hG
    (isIso_of_reflects_iso _ (boundedBelowInverseImage w.hom))

private theorem squareMap_counit_isIso {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D] {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R : D ⥤ B}
    (α : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R) (F : D)
    (hA : IsIso (a.counit.app (V.obj F))) (hB : IsIso (b.counit.app F)) :
    IsIso (J.map (adjointSquareMap α a b F)) := by
  let m := adjointSquareMap α a b F
  have h : J.map m ≫ a.counit.app (V.obj F) =
      α.hom.app (R.obj F) ≫ V.map (b.counit.app F) := by
    calc
      _ = (a.homEquiv (E.obj (R.obj F)) (V.obj F)).symm m :=
        (a.homEquiv_counit _ _ m).symm
      _ = _ := (a.homEquiv _ _).symm_apply_apply _
  haveI : IsIso (J.map m ≫ a.counit.app (V.obj F)) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right _ (a.counit.app (V.obj F))

private theorem pullback_supported {X Y : TopCat.{0}} (e : X ⟶ Y) (Z : Set Y)
    (G : BoundedBelow Y) (h : DerivedSupportedOn Z G) :
    DerivedSupportedOn (e ⁻¹' Z) ((boundedBelowInverseImage e).obj G) := by
  intro q x hx
  exact (h q (e x) hx).of_iso (pullbackStalkIso e G q x)

/-- Base change along a closed subset for the canonical map of derived images. -/
theorem closedBaseChange_isIso {U X Y : TopCat.{0}} {j : U ⟶ X} {Z : Set Y}
    (hj : IsClosedEmbedding j) (hZ : IsClosed Z) {e : X ⟶ Y} {v : U ⟶ TopCat.of Z}
    (h : j ≫ e = v ≫ closedInclusion Z) (hC : Set.range j = e ⁻¹' Z)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ)
    (F : BoundedBelow (TopCat.of Z)) :
    IsIso (adjointSquareMap (pullbackSquare h) a b F) := by
  let E := (closedExtensionPlus hZ).obj F
  let B := (boundedBelowInverseImage v).obj F
  let m := adjointSquareMap (pullbackSquare h) a b F
  obtain ⟨ff⟩ := DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hZ
  letI := ff.full
  letI := ff.faithful
  have hE : DerivedSupportedOn Z E :=
    (DerivedLocalSheaves.derivedSupportedEssentialImage hZ E).mp ⟨F, ⟨Iso.refl E⟩⟩
  exact closedEmbedding_reflectsIso hj m
    (hC ▸ pullback_supported e Z E hE)
    (derivedClosedImage_supported hj B)
    (squareMap_counit_isIso (pullbackSquare h) a b F (derivedClosedImageCounit_isIso hj a B)
      inferInstance)

theorem productMap_closed {U X : TopCat.{0}} (T : TopCat.{0}) {j : U ⟶ X}
    (hj : IsClosedEmbedding j) : IsClosedEmbedding (productMap T j) := by
  have h : IsClosedEmbedding (@id T) := ⟨IsEmbedding.id, by
    rw [Set.range_id]
    exact isClosed_univ⟩
  exact h.prodMap hj

theorem action_preimage_closed {H : AnalyticGroup.{0}} {X : TopCat.{0}} {Z : Set X}
    (A : AnalyticAction H X) (B : AnalyticAction H (TopCat.of Z))
    (h : productMap H.space (closedInclusion Z) ≫ A.act = B.act ≫ closedInclusion Z) :
    A.act ⁻¹' Z = productProjection H.space X ⁻¹' Z := by
  have hPoint (g : H.space) (z : Z) : A.act (g, z.val) = (B.act (g, z)).val :=
    congrArg (fun f : TopCat.of (H.space × (TopCat.of Z)) ⟶ X => f (g, z)) h
  ext p
  obtain ⟨g, x⟩ := p
  change A.act (g, x) ∈ Z ↔ x ∈ Z
  constructor
  · intro hx
    have hz : A.act (g⁻¹, A.act (g, x)) ∈ Z := by
      rw [hPoint g⁻¹ ⟨A.act (g, x), hx⟩]
      exact (B.act (g⁻¹, ⟨A.act (g, x), hx⟩)).property
    rwa [← A.mul_act, inv_mul_cancel, A.one_act] at hz
  · intro hx
    rw [hPoint g ⟨x, hx⟩]
    exact (B.act (g, ⟨x, hx⟩)).property

theorem closedProjectionBaseChange_isIso {X : TopCat.{0}} {Z : Set X} (hZ : IsClosed Z)
    (T : TopCat.{0}) (a : DerivedAdjunctions) (b : boundedBelowInverseImage (closedInclusion Z) ⊣
      LocalSheaf.closedExtensionPlus hZ)
    (F : BoundedBelow (TopCat.of Z)) :
    IsIso (adjointSquareMap (pullbackSquare (productSquare T (closedInclusion Z)))
      (a (productMap T (closedInclusion Z))) b F) := by
  refine closedBaseChange_isIso (productMap_closed T hZ.isClosedEmbedding_subtypeVal) hZ _ ?_ _ _ _
  rw [productMap_range, show Set.range (closedInclusion Z) = Z from Subtype.range_coe]

theorem closedActionBaseChange_isIso {H : AnalyticGroup.{0}} {X : TopCat.{0}} {Z : Set X}
    (hZ : IsClosed Z) (A : AnalyticAction H X) (B : AnalyticAction H (TopCat.of Z))
    (h : productMap H.space (closedInclusion Z) ≫ A.act = B.act ≫ closedInclusion Z)
    (a : DerivedAdjunctions) (b : boundedBelowInverseImage (closedInclusion Z) ⊣
      LocalSheaf.closedExtensionPlus hZ) (F : BoundedBelow (TopCat.of Z)) :
    IsIso (adjointSquareMap (pullbackSquare h) (a (productMap H.space (closedInclusion Z))) b F) := by
  refine closedBaseChange_isIso (productMap_closed H.space hZ.isClosedEmbedding_subtypeVal)
    hZ h ?_ _ _ _
  rw [productMap_range, show Set.range (closedInclusion Z) = Z from Subtype.range_coe,
    action_preimage_closed A B h]

/-- On an invariant closed stage the comparison mates are isomorphisms, so the
extension by zero inherits the datum with the same identity and cocycle. -/
theorem closedExtensionCompatibility (J : JetSystem.{0}) : ClosedExtensionCompatibility J := by
  intro X Z hZ A B h a b F β
  have hIso : ClosedEquivarianceExtensionSpecs.ComparisonsAreIso hZ h a b F := by
    intro k hk
    let hx := (le_max_left A.cutoff B.cutoff).trans hk
    let hz := (le_max_right A.cutoff B.cutoff).trans hk
    exact ⟨closedActionBaseChange_isIso hZ (A.action k hx) (B.action k hz) (h k hx hz) a b F,
      closedProjectionBaseChange_isIso hZ (J.group k).space a b F⟩
  exact ⟨hIso, ClosedEquivarianceExtension.closedEquivarianceExtension hZ A B h a b F β hIso⟩

end ClosedBaseChange

/-- Base change for ordinary derived direct image at every attachment. -/
def ProjectionBaseChange (a : DerivedAdjunctions) (T : TopCat.{0})
    {X : TopCat.{0}} {s : ℕ} (D : DimensionFiltration X s) : Prop :=
  match D with
  | .top _ _ => True
  | @DimensionFiltration.attach _U _Y _d _ E j _ _ =>
      ProjectionBaseChange a T E ∧
        IsIso (directImageComparison (productSquare T j) (a (productMap T j)) (a j) (complex E))

/-- Exact projection pullback commutes with ordinary truncation and its canonical
map into the untruncated complex. -/

def shiftConstantAdd (X : TopCat.{0}) (d e : ℕ) :
    (shiftedConstant X d).obj⟦(e : ℤ)⟧ ≅ (shiftedConstant X (d + e)).obj :=
  ((shiftFunctorAdd' (Derived X) (d : ℤ) (e : ℤ) ((d + e : ℕ) : ℤ)
    (by rw [Nat.cast_add])).symm.app ((DerivedCategory.singleFunctor (Sheaves X) 0).obj (rational X)))

section ProductComplex

/-- Shifting a truncation lowers its cohomological cutoff by the shift. -/
def truncationShiftIso (X : TopCat.{0}) (F : Derived X) (q n : ℤ) :
    ((DerivedCategory.TStructure.t (C := Sheaves X)).truncLE q).obj F⟦n⟧ ≅
      ((DerivedCategory.TStructure.t (C := Sheaves X)).truncLE (q - n)).obj (F⟦n⟧) := by
  let t := DerivedCategory.TStructure.t (C := Sheaves X)
  let A := (t.triangleLEGT q).obj F
  let T := (Triangle.shiftFunctor (Derived X) n).obj A
  have hT : T ∈ distTriang (Derived X) := A.shift_distinguished (t.triangleLEGT_distinguished q F) n
  haveI : t.IsLE T.obj₁ (q - n) := t.isLE_shift ((t.truncLE q).obj F) q n (q - n)
  have h₃ : t.IsGE T.obj₃ (q - n + 1) :=
    t.isGE_shift ((t.truncGE (q + 1)).obj F) (q + 1) n (q - n + 1)
  haveI : IsIso ((t.truncLE (q - n)).map T.mor₁) :=
    t.isIso₁_truncLE_map_of_isGE T hT (q - n) (q - n + 1) rfl h₃
  haveI : IsIso ((t.truncLEι (q - n)).app T.obj₁) :=
    (t.isLE_iff_isIso_truncLEι_app (q - n) T.obj₁).mp inferInstance
  exact (asIso ((t.truncLEι (q - n)).app T.obj₁)).symm ≪≫
    asIso ((t.truncLE (q - n)).map T.mor₁)

private def directImageShiftIso {U X : TopCat.{0}} (j : U ⟶ X) (F : BoundedBelow U) (n : ℤ) :
    (derivedDirectImage j |>.obj F).obj⟦n⟧ ≅ (derivedDirectImage j |>.obj (F⟦n⟧)).obj :=
  let R := (directImage j).rightDerivedFunctorPlus
  let i := DerivedCategory.Plus.ι (C := Sheaves X)
  ((i.commShiftIso n).app (R.obj F)).symm ≪≫ i.mapIso ((R.commShiftIso n).app F).symm

/-- Given the ordinary derived base-change isomorphism, one attachment commutes
with projection pullback with its smooth shift and the shifted cutoff. -/
private theorem productAttachmentIso
    (a : DerivedAdjunctions) (T : TopCat.{0}) (e : ℕ) {U X : TopCat.{0}}
    (j : U ⟶ X) (hj : IsOpenEmbedding j) (s : ℕ) (F : BoundedBelow U)
    (G : BoundedBelow (TopCat.of (T × U)))
    (h : IsIso (directImageComparison (productSquare T j) (a (productMap T j)) (a j) F))
    (c : ((derivedInverseImage (productProjection T U)).obj F.obj)⟦(e : ℤ)⟧ ≅ G.obj) :
    Nonempty (((derivedInverseImage (productProjection T X)).obj
      ((attachment j hj s).obj F).obj)⟦(e : ℤ)⟧ ≅
      ((attachment (productMap T j) (productMap_open T hj) (s + e)).obj G).obj) := by
  let j' := productMap T j
  let p := productProjection T X
  let q := productProjection T U
  let m : ℤ := -(s : ℤ) - 1
  let n : ℤ := e
  let u := DerivedCategory.TStructure.t (C := Sheaves (TopCat.of (T × X)))
  let P := (derivedDirectImage j).obj F
  let Q := (boundedBelowInverseImage q).obj F
  let i := DerivedCategory.Plus.ι (C := Sheaves (TopCat.of (T × X)))
  let R := derivedDirectImage j'
  obtain ⟨τ, _⟩ := pullbackTruncation p m
  let bc : ((derivedInverseImage p).obj P.obj) ≅ (R.obj Q).obj :=
    i.mapIso (asIso (directImageComparison (productSquare T j) (a j') (a j) F))
  let tc : (Q⟦n⟧) ≅ G :=
    ObjectProperty.isoMk _ (((DerivedCategory.Plus.ι (C := Sheaves (TopCat.of (T × U)))).commShiftIso n).app Q ≪≫ c)
  have hs : m - n = -((s + e : ℕ) : ℤ) - 1 := by
    simp only [m, n, Nat.cast_add]
    omega
  refine ⟨(shiftFunctor _ n).mapIso (τ.app P.obj ≪≫ (u.truncLE m).mapIso bc) ≪≫
    truncationShiftIso (TopCat.of (T × X)) (R.obj Q).obj m n ≪≫
    (u.truncLE (m - n)).mapIso (directImageShiftIso j' Q n ≪≫ i.mapIso (R.mapIso tc)) ≪≫ ?_⟩
  exact eqToIso (congrArg (fun z => (u.truncLE z).obj (R.obj G).obj) hs)

/-- The ordinary direct-image comparisons at the attachments imply the underlying
product intersection-complex isomorphism with the smooth shift. -/
theorem productComplexIso (a : DerivedAdjunctions) (T : TopCat.{0}) (e : ℕ)
    {X : TopCat.{0}} {s : ℕ} (D : DimensionFiltration X s) (h : ProjectionBaseChange a T D) :
    Nonempty (((derivedInverseImage (productProjection T X)).obj (complex D).obj)⟦(e : ℤ)⟧ ≅
      (complex (productFiltration T e D)).obj) := by
  induction D with
  | top X d =>
    let p := productProjection T X
    exact ⟨(shiftFunctor _ (e : ℤ)).mapIso (shiftedConstantPullback p d) ≪≫
      shiftConstantAdd (TopCat.of (T × X)) d e⟩
  | @attach U X d s D j hj hs ih =>
    obtain ⟨hU, hX⟩ := h
    obtain ⟨c⟩ := ih hU
    exact productAttachmentIso a T e j hj s (complex D) (complex (productFiltration T e D)) hX c

end ProductComplex

section TransportOfOrbitStages

open LatticeModelSpecs RankTwoSchubertStrataSpecs

def PreservesOrbitStrata {ab cd : DominantPair} {N M : ℕ}
    {hN : OrbitBound ab N} {hM : OrbitBound cd M}
    (f : SchubertSpace ab N hN ≅ SchubertSpace cd M hM) : Prop :=
  ∃ e : OrbitIndex ab ≃ OrbitIndex cd, ∀ j : OrbitIndex ab,
    f.hom ⁻¹' orbitPoints cd M hM (e j) = orbitPoints ab N hN j ∧
    orbitDimension cd (e j).val = orbitDimension ab j.val

private theorem orbitIndex_le_half (ab : DominantPair) (i : OrbitIndex ab) :
    2 * i.val ≤ difference ab := by
  have h : i.val < difference ab / 2 + 1 := i.isLt
  omega

private theorem orbitDimension_preserving_index {ab cd : DominantPair}
    (e : OrbitIndex ab ≃ OrbitIndex cd)
    (h : ∀ i, orbitDimension cd (e i).val = orbitDimension ab i.val) :
    difference ab = difference cd ∧ ∀ i, (e i).val = i.val := by
  let x : OrbitIndex ab := ⟨0, Nat.succ_pos _⟩
  let y : OrbitIndex cd := ⟨0, Nat.succ_pos _⟩
  have h₁ : difference cd - 2 * (e x).val = difference ab - 2 * 0 := h x
  have h₂ := h (e.symm y)
  rw [e.apply_symm_apply] at h₂
  change difference cd - 2 * 0 = difference ab - 2 * (e.symm y).val at h₂
  have hd : difference ab = difference cd := by omega
  refine ⟨hd, fun i => ?_⟩
  have hi := orbitIndex_le_half ab i
  have he := orbitIndex_le_half cd (e i)
  have h' : difference cd - 2 * (e i).val = difference ab - 2 * i.val := h i
  omega

/-- A dimension-preserving bijection of the rank-two orbit strata preserves the
successive open unions of the highest-dimensional strata. -/
theorem orbitStage_preimage_of_iso {ab cd : DominantPair} {N M : ℕ}
    {hN : OrbitBound ab N} {hM : OrbitBound cd M}
    (f : SchubertSpace ab N hN ≅ SchubertSpace cd M hM)
    (h : PreservesOrbitStrata f) (k : ℕ) :
    f.hom ⁻¹' stagePoints cd M hM k = stagePoints ab N hN k := by
  obtain ⟨e, he⟩ := h
  obtain ⟨hd, hn⟩ := orbitDimension_preserving_index e (fun i => (he i).2)
  ext x
  change (∃ i : OrbitIndex cd, i.val ≤ k ∧ f.hom x ∈ orbitPoints cd M hM i) ↔
    (∃ i : OrbitIndex ab, i.val ≤ k ∧ x ∈ orbitPoints ab N hN i)
  constructor
  · rintro ⟨i, hi, hx⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨j, hn j ▸ hi, (he j).1 ▸ hx⟩
  · rintro ⟨i, hi, hx⟩
    refine ⟨e i, (hn i).symm ▸ hi, ?_⟩
    change x ∈ f.hom ⁻¹' orbitPoints cd M hM (e i)
    rw [(he i).1]
    exact hx

theorem orbitTopDimension_eq_of_iso {ab cd : DominantPair} {N M : ℕ}
    {hN : OrbitBound ab N} {hM : OrbitBound cd M}
    {f : SchubertSpace ab N hN ≅ SchubertSpace cd M hM} (h : PreservesOrbitStrata f) :
    difference ab = difference cd := by
  obtain ⟨e, he⟩ := h
  exact (orbitDimension_preserving_index e (fun i => (he i).2)).1

end TransportOfOrbitStages

section Common

open Analytic Analytic.IntersectionComplex
open EquivariantIntersectionComplexesSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion)
open Analytic.DerivedPullbackPasting.Expected (identityValue)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Changing either object by an isomorphism preserves bijectivity of a Hom map. -/
theorem mapBijectiveOfIso {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {X Y X' Y' : C} (a : X ≅ X') (b : Y ≅ Y')
    (h : Function.Bijective (L.map : (X' ⟶ Y') → _)) :
    Function.Bijective (L.map : (X ⟶ Y) → _) := by
  have he : (L.map : (X ⟶ Y) → _) =
      ((L.mapIso a).homCongr (L.mapIso b)).symm ∘ (L.map ∘ a.homCongr b) := by
    funext f
    change L.map f = L.map a.hom ≫ L.map (a.inv ≫ f ≫ b.hom) ≫ L.map b.inv
    rw [← L.map_comp_assoc, ← L.map_comp, a.hom_inv_id_assoc, Category.assoc,
      b.hom_inv_id, Category.comp_id]
  rw [he]
  exact (Equiv.bijective _).comp (h.comp (Equiv.bijective _))

theorem mapBijectiveOfNatIso {C D : Type*} [Category* C] [Category* D] {L M : C ⥤ D}
    (a : L ≅ M) (X Y : C) (h : Function.Bijective (L.map : (X ⟶ Y) → _)) :
    Function.Bijective (M.map : (X ⟶ Y) → _) := by
  have he : (M.map : (X ⟶ Y) → _) = (a.app X).homCongr (a.app Y) ∘ L.map := by
    funext f
    change M.map f = a.inv.app X ≫ L.map f ≫ a.hom.app Y
    rw [a.hom.naturality, Iso.inv_hom_id_app_assoc]
  rw [he]
  exact (Equiv.bijective _).comp h

/-- Pullback by a homeomorphism is an equivalence of the actual derived categories. -/
def derivedInverseImageEquivalence {X Y : TopCat.{0}} (e : X ≅ Y) : Derived Y ≌ Derived X :=
  CategoryTheory.Equivalence.mk (derivedInverseImage e.hom) (derivedInverseImage e.inv)
    ((identityValue Y).symm ≪≫
      eqToIso (congrArg (fun f => derivedInverseImage f) e.inv_hom_id.symm) ≪≫
      derivedInverseImageComposition e.inv e.hom)
    ((derivedInverseImageComposition e.hom e.inv).symm ≪≫
      eqToIso (congrArg (fun f => derivedInverseImage f) e.hom_inv_id) ≪≫
      identityValue X)

def parameterIso (H : AnalyticGroup.{0}) {X Y : TopCat.{0}} (e : X ≅ Y) :
    AnalyticAction.Parameters H X ≅ AnalyticAction.Parameters H Y :=
  TopCat.isoOfHomeo ((Homeomorph.refl H.space).prodCongr (TopCat.homeoOfIso e))

theorem pullbackSquareMapBijective {U X V Y : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ Y} (e : X ≅ Y) (v : U ≅ V)
    (h : i ≫ e.hom = v.hom ≫ j) (F G : Derived Y)
    (h' : Function.Bijective ((derivedInverseImage j).map : (F ⟶ G) → _)) :
    Function.Bijective ((derivedInverseImage i).map :
      ((derivedInverseImage e.hom).obj F ⟶ (derivedInverseImage e.hom).obj G) → _) := by
  let E := derivedInverseImageEquivalence e
  let V' := derivedInverseImageEquivalence v
  let r := Analytic.DerivedPullbackPasting.Expected.squareValue h
  have hp : Function.Bijective ((derivedInverseImage j ⋙ V'.functor).map : (F ⟶ G) → _) :=
    (V'.fullyFaithfulFunctor.map_bijective _ _).comp h'
  have hp' := mapBijectiveOfNatIso r.symm F G hp
  exact (Function.Bijective.of_comp_iff _ (E.fullyFaithfulFunctor.map_bijective F G)).mp hp'

end Common

section Geometry

open Analytic Analytic.IntersectionComplex
open EquivariantIntersectionComplexesSpecs SchubertIntersectionConstructibilitySpecs
open LatticeModelSpecs RankTwoSchubertStrataSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem intertwines_apply {J : JetSystem.{0}} {X Y : TopCat.{0}}
    {A : JetAction J X} {B : JetAction J Y} {f : X ⟶ Y} (h : Intertwines A B f)
    (k : ℕ) (hx : A.cutoff ≤ k) (hy : B.cutoff ≤ k) (g : (J.group k).space) (x : X) :
    (B.action k hy).act (g, f x) = f ((A.action k hx).act (g, x)) :=
  congrArg (fun m : AnalyticAction.Parameters (J.group k) X ⟶ Y => m (g, x)) (h k hx hy)

theorem intertwines_comp {J : JetSystem.{0}} {U X Y : TopCat.{0}}
    {C : JetAction J U} {A : JetAction J X} {B : JetAction J Y}
    {j : U ⟶ X} {f : X ⟶ Y} (hC : C.cutoff = A.cutoff)
    (hj : Intertwines C A j) (hf : Intertwines A B f) :
    Intertwines C B (j ≫ f) := by
  intro k hc hb
  let ha := hC ▸ hc
  refine TopCat.ext fun p => ?_
  change (B.action k hb).act (p.1, f (j p.2)) = f (j ((C.action k hc).act p))
  rw [intertwines_apply hf k ha hb, intertwines_apply hj k hc ha]

theorem jetAction_ext {J : JetSystem.{0}} {X : TopCat.{0}}
    {A B : JetAction J X} (hc : A.cutoff = B.cutoff)
    (h : ∀ k ha hb, (A.action k ha).act = (B.action k hb).act) : A = B := by
  rcases A with ⟨m, a, ha⟩
  rcases B with ⟨n, b, hb⟩
  change m = n at hc
  subst n
  have h' : a = b := by
    funext k hk
    have hact := h k hk hk
    have ht {H : AnalyticGroup.{0}} {x y : AnalyticAction H X}
        (hxy : x.act = y.act) : x = y := by
      cases x
      cases y
      cases hxy
      rfl
    exact ht hact
  subst b
  rfl

theorem actionOnEmbedding_unique {J : JetSystem.{0}} {U X : TopCat.{0}}
    {B C : JetAction J U} {A : JetAction J X} {j : U ⟶ X}
    (hj : Function.Injective j) (hB : B.cutoff = A.cutoff) (hC : C.cutoff = A.cutoff)
    (hcB : Intertwines B A j) (hcC : Intertwines C A j) : B = C := by
  refine jetAction_ext (hB.trans hC.symm) fun k hb hc => TopCat.ext fun p => ?_
  let ha := hB ▸ hb
  apply hj
  exact (intertwines_apply hcB k hb ha p.1 p.2).symm.trans
    (intertwines_apply hcC k hc ha p.1 p.2)

theorem orbitStageRealizes {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {X : TopCat.{0}} {s k : ℕ} {f : X ⟶ SchubertSpace ab N hN}
    {P : Stratification X} {D : DimensionFiltration X s}
    (h : IsNormalizedOrbitIC ab N hN f k P D) : RealizesOrbitStage f k P := by
  cases h with
  | top _ _ h _ => exact h
  | attach _ _ _ _ _ _ _ h _ _ _ _ _ => exact h

theorem orbitAttachment_invariant {c : ContinuousJets} {ab : DominantPair} {N : ℕ}
    {hN : OrbitBound ab N} {A : JetAction (jetSystem c) (SchubertSpace ab N hN)}
    (hA : ActualSchubertAction ab N hN A)
    {U X : TopCat.{0}} {j : U ⟶ X} {f : X ⟶ SchubertSpace ab N hN}
    {P : Stratification X} {Q : Stratification U} {d k : ℕ}
    {D : DimensionFiltration U d}
    (prev : IsNormalizedOrbitIC ab N hN (j ≫ f) k Q D)
    (curr : RealizesOrbitStage f (k + 1) P)
    {B : JetAction (jetSystem c) X} (hcut : B.cutoff = A.cutoff)
    (hB : Intertwines B A f) (l : ℕ) (hl : B.cutoff ≤ l) :
    invariantRange (B.action l hl) j := by
  have hr := (orbitStageRealizes prev).2.1
  intro g u
  have hu : f (j u) ∈ stagePoints ab N hN k := hr ▸ Set.mem_range_self u
  obtain ⟨i, hi, hm⟩ := hu
  let ha := hcut ▸ hl
  have hmem : (A.action l ha).act (g, f (j u)) ∈ stagePoints ab N hN k :=
    ⟨i, hi, (hA.2.2 l ha g (f (j u)) i).mpr hm⟩
  rw [← hr] at hmem
  obtain ⟨u', hu'⟩ := hmem
  refine ⟨u', curr.1.injective ?_⟩
  exact hu'.trans (intertwines_apply hB l hl ha g (j u))

/-- Each preceding open stage carries a restricted action. -/
def PreservesFiltration {H : AnalyticGroup.{0}} {X : TopCat.{0}} {s : ℕ}
    (D : DimensionFiltration X s) : AnalyticAction H X → Prop :=
  match D with
  | .top _ _ => fun _ => True
  | .attach E j _ _ => fun A =>
      ∃ B : AnalyticAction H _, parameterInclusion H j ≫ A.act = B.act ≫ j ∧
        PreservesFiltration E B

theorem orbitAction_preservesFiltration {c : ContinuousJets} {ab : DominantPair} {N : ℕ}
    {hN : OrbitBound ab N} {A : JetAction (jetSystem c) (SchubertSpace ab N hN)}
    (hA : ActualSchubertAction ab N hN A)
    {X : TopCat.{0}} {s k : ℕ} {f : X ⟶ SchubertSpace ab N hN}
    {P : Stratification X} {D : DimensionFiltration X s}
    (h : IsNormalizedOrbitIC ab N hN f k P D) :
    ∀ {B : JetAction (jetSystem c) X}, B.cutoff = A.cutoff → Intertwines B A f →
      ∀ (l : ℕ) (hl : B.cutoff ≤ l), PreservesFiltration D (B.action l hl) := by
  induction h with
  | top => intro B hc hB l hl; trivial
  | @attach U X d k D f P Q j hj hs previous stage strata bd coho perverse strict ih =>
    intro B hc hB l hl
    let hInv := orbitAttachment_invariant hA previous stage hc hB
    let C := restrictJetAction B hj.isEmbedding hInv
    have hCB := restrictJetAction_commutes B hj.isEmbedding hInv
    have hC := intertwines_comp (C := C) (A := B) rfl hCB hB
    exact ⟨C.action l hl, hCB l hl hl, ih (B := C) hc hC l hl⟩

def parameterTwistIso {H : AnalyticGroup.{0}} {X T : TopCat.{0}} (p : T ⟶ H.space)
    (A : AnalyticAction H X) : TopCat.of (T × X) ≅ TopCat.of (T × X) :=
  TopCat.isoOfHomeo (parameterTwist p A)

theorem parameterTwist_filtration {H : AnalyticGroup.{0}} {T : TopCat.{0}} (p : T ⟶ H.space)
    (e : ℕ) {X : TopCat.{0}} {s : ℕ} (D : DimensionFiltration X s) :
    ∀ (A : AnalyticAction H X), PreservesFiltration D A →
      FiltrationIso (parameterTwistIso p A) (productFiltration T e D) (productFiltration T e D) := by
  induction D with
  | top X d =>
    intro A _
    exact .top _ _
  | @attach U X d s E j hj hs ih =>
    intro A h
    obtain ⟨B, hAB, hB⟩ := h
    refine FiltrationIso.attach (ih B hB) (TopCat.ext fun v => Prod.ext rfl ?_)
    exact congrArg (fun m : AnalyticAction.Parameters H U ⟶ X => m (p v.1, v.2)) hAB

def doubleParameterIso (H : AnalyticGroup.{0}) (X : TopCat.{0}) :
    AnalyticAction.TwoParameters H X ≅ TopCat.of (TopCat.of (H.space × H.space) × X) :=
  TopCat.isoOfHomeo (Homeomorph.prodAssoc H.space H.space X).symm

theorem doubleParameterIso_square (H : AnalyticGroup.{0}) {U X : TopCat.{0}} (j : U ⟶ X) :
    parameterInclusion H (parameterInclusion H j) ≫ (doubleParameterIso H X).hom =
      (doubleParameterIso H U).hom ≫ productMap (TopCat.of (H.space × H.space)) j :=
  TopCat.ext fun _ => rfl

def parameterMultiply (H : AnalyticGroup.{0}) : TopCat.of (H.space × H.space) ⟶ H.space :=
  TopCat.ofHom ⟨fun v => v.1 * v.2, continuous_fst.mul continuous_snd⟩

end Geometry

section JetAction

open Analytic
open EquivariantIntersectionComplexesSpecs SchubertIntersectionConstructibilitySpecs
open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs

set_option autoImplicit false

def jetActionOfMulAction (J : JetSystem.{0}) (X : TopCat.{0}) (m : ℕ)
    (ρ : ∀ k : ℕ, m ≤ k → MulAction (J.group k).space X)
    (hContinuous : ∀ k hk, Continuous (fun x : (J.group k).space × X => (ρ k hk).smul x.1 x.2))
    (hTransition : ∀ ⦃k l : ℕ⦄ (h : k ≤ l) (hk : m ≤ k) (g : (J.group l).space) (x : X),
      (ρ k hk).smul (J.truncate k l h g) x = (ρ l (hk.trans h)).smul g x) :
    JetAction J X where
  cutoff := m
  action k hk :=
    { act := TopCat.ofHom ⟨fun x => (ρ k hk).smul x.1 x.2, hContinuous k hk⟩
      one_act := (ρ k hk).one_smul
      mul_act := (ρ k hk).mul_smul }
  factors hk h := TopCat.ext fun p => hTransition h hk p.1 p.2

theorem jetTruncationContinuous (J : ContinuousJets) :
    ∀ ⦃k l : ℕ⦄ (h : k ≤ l),
      @Continuous (PositiveJet l) (PositiveJet k)
        (glJetTopology 2 (l + 1) (Nat.succ_pos l)) (glJetTopology 2 (k + 1) (Nat.succ_pos k))
        (Matrix.GeneralLinearGroup.map (n := Fin 2) (truncateJet (Nat.succ_le_succ h))) := by
  intro k l h
  exact J.truncation h

theorem schubertJetActionExists (J : GL2JetParameters) (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) : Nonempty (SchubertJetAction J ab N hN) := by
  have hex :=
    SchubertFiniteJetActions.schubertFiniteJetActions J.coefficientOpen
      (jetTruncationContinuous J) ab N hN
  obtain ⟨ρ, hContinuous, hTransition, hOrbit, hLoop, _⟩ := hex
  let A := jetActionOfMulAction (jetSystem J) (SchubertSpace ab N hN) (difference ab - 1)
    ρ hContinuous hTransition
  refine ⟨⟨A, ?_⟩⟩
  exact ⟨rfl, hLoop, hOrbit⟩

end JetAction

section Product

open Analytic Analytic.IntersectionComplex
open EquivariantIntersectionComplexesSpecs SchubertIntersectionConstructibilitySpecs
open LatticeModelSpecs RankTwoSchubertStrataSpecs
open ConvolutionConstantDescentSpec (shiftedConstantPullback)

open private shiftedConstant_isMiddlePerverse from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem orbitStageZeroRange {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {X : TopCat.{0}} {f : X ⟶ SchubertSpace ab N hN} {P : Stratification X}
    (h : RealizesOrbitStage f 0 P) (p : P.Index) :
    Set.range (P.stratum p).inclusion = Set.univ := by
  obtain ⟨_, hRange, indexing, hi⟩ := h
  rw [(hi p).1]
  apply Set.eq_univ_of_forall
  intro x
  have hx : f x ∈ stagePoints ab N hN 0 := hRange ▸ Set.mem_range_self x
  obtain ⟨i, hi0, hmem⟩ := hx
  have hp0 := (indexing p).property
  have he : i = (indexing p).val := Fin.ext (by omega)
  exact he ▸ hmem

theorem orbitStageZeroDimension {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {X : TopCat.{0}} {f : X ⟶ SchubertSpace ab N hN} {P : Stratification X}
    (h : RealizesOrbitStage f 0 P) (p : P.Index) :
    (P.stratum p).complexDimension = difference ab := by
  obtain ⟨_, _, indexing, hi⟩ := h
  have he := Nat.eq_zero_of_le_zero (indexing p).property
  rw [(hi p).2, he]
  simp [orbitDimension]

theorem productTopPerverse (T : TopCat.{0}) (e : ℕ)
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {X : TopCat.{0}} {f : X ⟶ SchubertSpace ab N hN} {P : Stratification X}
    (h : RealizesOrbitStage f 0 P) :
    IsMiddlePerverse (productStratification T e P)
      (shiftedConstant (TopCat.of (T × X)) (difference ab + e)).obj := by
  apply shiftedConstant_isMiddlePerverse
  · intro p
    change Set.range (productStratum T e (P.stratum p)).inclusion = Set.univ
    rw [productStratum_range, orbitStageZeroRange h p, Set.preimage_univ]
  · intro p
    change (P.stratum p).complexDimension + e = difference ab + e
    rw [orbitStageZeroDimension h p]

/-- The product of the normalized Schubert filtration with smooth parameters
has the strict product intersection complex and the projection comparison with its dimension shift. -/
theorem normalizedProductIC (a : DerivedAdjunctions.{0}) (T : TopCat.{0}) (e : ℕ)
    (hT : HasOpenComplexCoordinates T e)
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {X : TopCat.{0}} {s k : ℕ} {f : X ⟶ SchubertSpace ab N hN}
    {P : Stratification X} {D : DimensionFiltration X s}
    (h : IsNormalizedOrbitIC ab N hN f k P D) :
    IsMiddlePerverse (productStratification T e P) (complex (productFiltration T e D)).obj ∧
      StrictAlong (productFiltration T e D) (complex (productFiltration T e D)) ∧
      Nonempty (((derivedInverseImage (productProjection T X)).obj (complex D).obj)⟦(e : ℤ)⟧ ≅
        (complex (productFiltration T e D)).obj) := by
  induction h with
  | top f P stage perverse =>
    exact ⟨productTopPerverse T e stage, trivial, ⟨
      (shiftFunctor _ (e : ℤ)).mapIso (shiftedConstantPullback (productProjection T _) _) ≪≫
        shiftConstantAdd _ _ e⟩⟩
  | @attach U X d k D f P Q j hj hs previous stage strata bd coho perverse strict ih =>
    obtain ⟨hp, hsU, ⟨c⟩⟩ := ih
    let G := complex (productFiltration T e D)
    let jT := productMap T j
    let ht := productMap_open T hj
    let t := orbitDimension ab (k + 1) + e
    let aT := a jT
    obtain ⟨hpT, hsT, hrT, cT, _⟩ :=
      SchubertProductAttachments.shiftedProductAttachment T e hT ab N hN k j hj f Q P D
        previous stage strata bd _ _ (productAttachmentStratification T e strata)
        G hp c aT (a j)
    let r := attachmentRestriction (s := t) (productFiltration T e D) jT ht aT
    haveI : IsIso r := hrT
    refine ⟨hpT, ⟨hsT, ?_⟩, ⟨cT⟩⟩
    exact strictAlong_of_iso _ (asIso r).symm hsU

end Product

section Hom

open Analytic Analytic.IntersectionComplex

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem derivedStrictMapBijective {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsOpenEmbedding j) (s : ℕ) {F G : BoundedBelow X}
    (hF : IsStrictExtension hj s F) (hG : IsStrictExtension hj s G) :
    Function.Bijective ((derivedInverseImage j).map : (F.obj ⟶ G.obj) → _) := by
  let IX := DerivedCategory.Plus.ι (C := Sheaves X)
  let IU := DerivedCategory.Plus.ι (C := Sheaves U)
  have hx := (Functor.FullyFaithful.ofFullyFaithful IX).map_bijective F G
  have hu := (Functor.FullyFaithful.ofFullyFaithful IU).map_bijective
    ((boundedBelowInverseImage j).obj F) ((boundedBelowInverseImage j).obj G)
  exact (Function.Bijective.of_comp_iff _ hx).mp (hu.comp (strictMapBijective hj s hF hG))

theorem pullbackMapBijectiveOfShift {U X : TopCat.{0}} (j : U ⟶ X) (n : ℤ)
    (F G : Derived X)
    (h : Function.Bijective ((derivedInverseImage j).map : (F⟦n⟧ ⟶ G⟦n⟧) → _)) :
    Function.Bijective ((derivedInverseImage j).map : (F ⟶ G) → _) := by
  let S := (shiftFunctor (Derived X) n).asEquivalence
  let T := (shiftFunctor (Derived U) n).asEquivalence
  let L := (inverseImage j).mapDerivedCategory
  have hs : Function.Bijective ((S.functor ⋙ L).map : (F ⟶ G) → _) :=
    h.comp (S.fullyFaithfulFunctor.map_bijective F G)
  have ht := mapBijectiveOfNatIso (L.commShiftIso n) F G hs
  exact (Function.Bijective.of_comp_iff'
    (T.fullyFaithfulFunctor.map_bijective (L.obj F) (L.obj G)) _).mp ht

theorem pullbackMapBijectiveOfShiftedStrict {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsOpenEmbedding j) (s : ℕ) (n : ℤ) {K : BoundedBelow X}
    (hK : IsStrictExtension hj s K) {F G : Derived X} (a : F⟦n⟧ ≅ K.obj)
    (b : G⟦n⟧ ≅ K.obj) :
    Function.Bijective ((derivedInverseImage j).map : (F ⟶ G) → _) :=
  pullbackMapBijectiveOfShift j n F G <|
    mapBijectiveOfIso (derivedInverseImage j) a b (derivedStrictMapBijective hj s hK hK)

end Hom

section Lift

open Analytic Analytic.IntersectionComplex
open EquivariantIntersectionComplexesSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open ConvolutionConstantDescentSpec (shiftedConstantPullback)

open private pullback_constantTransition from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionConstantDescent
open private jetEquivariance_ext from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.JetEquivariantRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem commutes_iff {J : JetSystem.{0}} {U X : TopCat.{0}}
    {B : JetAction J U} {A : JetAction J X} {j : U ⟶ X}
    (h : Intertwines B A j) {G : Derived U} {F : Derived X}
    (β : B.Equivariance G) (α : A.Equivariance F)
    (v : G ⟶ (derivedInverseImage j).obj F)
    (k : ℕ) (hu : B.cutoff ≤ k) (hx : A.cutoff ≤ k) :
    JetEquivariantRestrictionSpecs.Commutes (h k hu hx) (β.datum k hu) (α.datum k hx) v ↔
      (derivedInverseImage (B.action k hu).act).map v ≫ restrictedArrow h α k hu hx =
        (β.datum k hu).iso.hom ≫ (derivedInverseImage (Analytic.AnalyticAction.projection (J.group k) U)).map v := by
  simp only [JetEquivariantRestrictionSpecs.Commutes, restrictedArrow, squareValue,
    pullbackMorphism, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    NatTrans.comp_app, eqToIso.inv, eqToIso.hom, eqToHom_app, Category.assoc]

/-- These are the Hom maps used to lift the datum and compare its three identities. -/
structure RestrictionHomConditions {J : JetSystem.{0}} {U X : TopCat.{0}}
    (A : JetAction J X) (j : U ⟶ X) (F : Derived X) : Prop where
  identity :
    let E := (derivedInverseImage (𝟙 X)).obj F
    Function.Injective ((derivedInverseImage j).map : (E ⟶ E) → _)
  parameter : ∀ (k : ℕ) (hk : A.cutoff ≤ k),
    let H := J.group k
    let Q := (derivedInverseImage (A.action k hk).act).obj F
    let P := (derivedInverseImage (Analytic.AnalyticAction.projection H X)).obj F
    ∀ (S T : Derived (AnalyticAction.Parameters H X)),
      (S = Q ∨ S = P) → (T = Q ∨ T = P) →
        Function.Bijective ((derivedInverseImage (parameterInclusion H j)).map : (S ⟶ T) → _)
  multiplication : ∀ (k : ℕ) (hk : A.cutoff ≤ k),
    let H := J.group k
    let m := Analytic.AnalyticAction.multiplyParameters H X
    let Q := (derivedInverseImage (m ≫ (A.action k hk).act)).obj F
    let P := (derivedInverseImage (m ≫ Analytic.AnalyticAction.projection H X)).obj F
    let i := parameterInclusion H (parameterInclusion H j)
    Function.Injective ((derivedInverseImage i).map : (Q ⟶ P) → _)

theorem liftEquivariance {J : JetSystem.{0}} {U X : TopCat.{0}}
    {B : JetAction J U} {A : JetAction J X} {j : U ⟶ X}
    (hc : B.cutoff ≤ A.cutoff) (hin : Intertwines B A j)
    {G : Derived U} {F : Derived X} (v : G ≅ (derivedInverseImage j).obj F)
    (β : B.Equivariance G) (h : RestrictionHomConditions A j F) :
    ∃! α : A.Equivariance F, IntertwinesPullback hin β α v.hom := by
  obtain ⟨α, hα, hunique⟩ :=
    JetEquivariantRestriction.equivarianceLifting j hc (fun k hk => hin k (hc.trans hk) hk)
      v β h.identity h.parameter h.multiplication
  refine ⟨α, ?_, ?_⟩
  · intro k hu hx
    exact (commutes_iff hin β α v.hom k hu hx).mp (hα k hx)
  · intro γ hγ
    apply hunique
    intro k hx
    exact (commutes_iff hin β γ v.hom k (hc.trans hx) hx).mpr (hγ k (hc.trans hx) hx)

theorem homeomorphRestrictionHom {J : JetSystem.{0}} {U X : TopCat.{0}}
    (A : JetAction J X) (e : U ≅ X) (F : Derived X) :
    RestrictionHomConditions A e.hom F where
  identity := ((derivedInverseImageEquivalence e).fullyFaithfulFunctor.map_bijective _ _).1
  parameter k _ S T _ _ :=
    (derivedInverseImageEquivalence (parameterIso (J.group k) e)).fullyFaithfulFunctor.map_bijective S T
  multiplication k _ :=
    ((derivedInverseImageEquivalence (parameterIso (J.group k)
      (parameterIso (J.group k) e))).fullyFaithfulFunctor.map_bijective _ _).1

def constantDatum {H : AnalyticGroup.{0}} {X : TopCat.{0}} (A : AnalyticAction H X) (d : ℕ) :
    A.Equivariance (shiftedConstant X d).obj :=
  Classical.choose (ConvolutionConstantDescent.normalizedEquivariance A d)

theorem constantDatum_iso {H : AnalyticGroup.{0}} {X : TopCat.{0}} (A : AnalyticAction H X) (d : ℕ) :
    (constantDatum A d).iso = shiftedConstantPullback A.act d ≪≫
      (shiftedConstantPullback (Analytic.AnalyticAction.projection H X) d).symm :=
  Classical.choose_spec (ConvolutionConstantDescent.normalizedEquivariance A d)

def constantJetDatum {J : JetSystem.{0}} {X : TopCat.{0}} (A : JetAction J X) (d : ℕ) :
    A.Equivariance (shiftedConstant X d).obj where
  datum k hk := constantDatum (A.action k hk) d
  compatibility {k l} hk h := by
    let p := J.parameterMap h (𝟙 X)
    have hp : p ≫ Analytic.AnalyticAction.projection (J.group k) X = Analytic.AnalyticAction.projection (J.group l) X :=
      TopCat.ext fun _ => rfl
    change pullbackMorphism p (A.factors hk h) hp (constantDatum (A.action k hk) d).iso.hom =
      (constantDatum (A.action l (hk.trans h)) d).iso.hom
    rw [constantDatum_iso, pullback_constantTransition, constantDatum_iso]

theorem normalizedConstantDatum {J : JetSystem.{0}} (a : DerivedAdjunctions.{0})
    {X : TopCat.{0}} (A : JetAction J X) (d : ℕ) :
    NormalizedICDatum a A (.top X d) (constantJetDatum A d) :=
  .top _ (fun k hk => constantDatum_iso (A.action k hk) d)

theorem normalizedConstantDatum_iso {J : JetSystem.{0}} (a : DerivedAdjunctions.{0})
    {X : TopCat.{0}} {A : JetAction J X} {d : ℕ} {α : A.Equivariance (shiftedConstant X d).obj}
    (h : NormalizedICDatum a A (.top X d) α) (k : ℕ) (hk : A.cutoff ≤ k) :
    (α.datum k hk).iso = (constantJetDatum A d |>.datum k hk).iso := by
  cases h with
  | top _ coeff => exact (coeff k hk).trans (constantDatum_iso (A.action k hk) d).symm

theorem normalizedTopUnique {J : JetSystem.{0}} (a : DerivedAdjunctions.{0})
    {X : TopCat.{0}} (A : JetAction J X) (d : ℕ) :
    ∃! α : A.Equivariance (complex (.top X d)).obj, NormalizedICDatum a A (.top X d) α := by
  refine ⟨constantJetDatum A d, normalizedConstantDatum a A d, ?_⟩
  intro α h
  apply jetEquivariance_ext
  funext k hk
  have he := normalizedConstantDatum_iso a h k hk
  generalize α.datum k hk = u at he ⊢
  generalize (constantJetDatum A d).datum k hk = v at he ⊢
  cases u
  cases v
  cases he
  rfl

end Lift

section ActionHom

open Analytic Analytic.IntersectionComplex
open EquivariantIntersectionComplexesSpecs SchubertIntersectionConstructibilitySpecs
open LatticeModelSpecs RankTwoSchubertStrataSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion)
open Analytic.DerivedPullbackPasting.Expected (identityValue)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem shiftedActionPullback {H : AnalyticGroup.{0}} {T X : TopCat.{0}}
    (p : T ⟶ H.space) (A : AnalyticAction H X) (e : ℕ)
    {s : ℕ} (D : DimensionFiltration X s) (hA : PreservesFiltration D A)
    (c : ((derivedInverseImage (productProjection T X)).obj (complex D).obj)⟦(e : ℤ)⟧ ≅
      (complex (productFiltration T e D)).obj) :
    Nonempty (((derivedInverseImage ((parameterTwistIso p A).hom ≫ productProjection T X)).obj
      (complex D).obj)⟦(e : ℤ)⟧ ≅ (complex (productFiltration T e D)).obj) := by
  let τ := parameterTwistIso p A
  let P := productFiltration T e D
  let F := complex D
  let n : ℤ := e
  obtain ⟨u⟩ := MiddleExtension.complexTransport τ P P (parameterTwist_filtration p e D A hA)
  let it := DerivedCategory.Plus.ι (C := Sheaves (TopCat.of (T × X)))
  exact ⟨(shiftFunctor _ n).mapIso ((derivedInverseImageComposition τ.hom
      (productProjection T X)).app F.obj) ≪≫
    (((inverseImage τ.hom).mapDerivedCategory.commShiftIso n).app
      ((derivedInverseImage (productProjection T X)).obj F.obj)).symm ≪≫
    (derivedInverseImage τ.hom).mapIso c ≪≫ it.mapIso u⟩

theorem productRestrictionBijective (a : DerivedAdjunctions.{0}) {H : AnalyticGroup.{0}}
    (T : TopCat.{0}) (e : ℕ) (hT : HasOpenComplexCoordinates T e)
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {U X : TopCat.{0}} {s d k : ℕ} {f : X ⟶ SchubertSpace ab N hN}
    {P : Stratification X} {D : DimensionFiltration U d} {j : U ⟶ X}
    {hj : IsOpenEmbedding j} {hs : s < d}
    (h : IsNormalizedOrbitIC ab N hN f k P (DimensionFiltration.attach D j hj hs))
    (A : AnalyticAction H X) (hA : PreservesFiltration (.attach D j hj hs) A) (p : T ⟶ H.space) :
    let F := (complex (.attach D j hj hs)).obj
    let Q := (derivedInverseImage ((parameterTwistIso p A).hom ≫ productProjection T X)).obj F
    let P₀ := (derivedInverseImage (productProjection T X)).obj F
    ∀ (S R : Derived (TopCat.of (T × X))), (S = Q ∨ S = P₀) → (R = Q ∨ R = P₀) →
      Function.Bijective ((derivedInverseImage (productMap T j)).map : (S ⟶ R) → _) := by
  let E := DimensionFiltration.attach D j hj hs
  let K := complex (productFiltration T e E)
  obtain ⟨_, hstrict, ⟨c⟩⟩ := normalizedProductIC a T e hT h
  obtain ⟨u⟩ := shiftedActionPullback p A e E hA c
  have hK : IsStrictExtension (productMap_open T hj) (s + e) K :=
    (show StrictAlong (productFiltration T e E) K from hstrict).1
  intro F Q₀ P₁ S R hS hR
  obtain rfl | rfl := hS <;> obtain rfl | rfl := hR
  · exact pullbackMapBijectiveOfShiftedStrict (productMap_open T hj) _ _ hK u u
  · exact pullbackMapBijectiveOfShiftedStrict (productMap_open T hj) _ _ hK u c
  · exact pullbackMapBijectiveOfShiftedStrict (productMap_open T hj) _ _ hK c u
  · exact pullbackMapBijectiveOfShiftedStrict (productMap_open T hj) _ _ hK c c

theorem doubleParameterRestrictionBijective {H : AnalyticGroup.{0}}
    {U X : TopCat.{0}} {j : U ⟶ X} (A : AnalyticAction H X) (F : Derived X)
    (h : Function.Bijective ((derivedInverseImage (productMap (TopCat.of (H.space × H.space)) j)).map :
      ((derivedInverseImage ((parameterTwistIso (parameterMultiply H) A).hom ≫
        productProjection (TopCat.of (H.space × H.space)) X)).obj F ⟶
       (derivedInverseImage (productProjection (TopCat.of (H.space × H.space)) X)).obj F) → _)) :
    Function.Bijective ((derivedInverseImage (parameterInclusion H (parameterInclusion H j))).map :
      ((derivedInverseImage (Analytic.AnalyticAction.multiplyParameters H X ≫ A.act)).obj F ⟶
        (derivedInverseImage (Analytic.AnalyticAction.multiplyParameters H X ≫ Analytic.AnalyticAction.projection H X)).obj F) → _) := by
  let T := TopCat.of (H.space × H.space)
  let ε := doubleParameterIso H X
  let p := productProjection T X
  let q := (parameterTwistIso (parameterMultiply H) A).hom ≫ p
  have ha : Analytic.AnalyticAction.multiplyParameters H X ≫ A.act = ε.hom ≫ q := TopCat.ext fun _ => rfl
  have hp : Analytic.AnalyticAction.multiplyParameters H X ≫ Analytic.AnalyticAction.projection H X = ε.hom ≫ p := TopCat.ext fun _ => rfl
  rw [ha, hp]
  apply mapBijectiveOfIso (derivedInverseImage (parameterInclusion H (parameterInclusion H j)))
    ((derivedInverseImageComposition ε.hom q).app F) ((derivedInverseImageComposition ε.hom p).app F)
  exact pullbackSquareMapBijective ε (doubleParameterIso H U) (doubleParameterIso_square H j) _ _ h

/-- Strictness on the stage and on the smooth parameter products supplies all
restrictions needed for the identity, multiplication and jet-transition laws. -/
theorem schubertRestrictionHom (a : DerivedAdjunctions.{0}) {c : ContinuousJets}
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {U X : TopCat.{0}} {s d k : ℕ} {f : X ⟶ SchubertSpace ab N hN}
    {P : Stratification X} {D : DimensionFiltration U d} {j : U ⟶ X}
    {hj : IsOpenEmbedding j} {hs : s < d}
    (h : IsNormalizedOrbitIC ab N hN f k P (DimensionFiltration.attach D j hj hs))
    {B : JetAction (jetSystem c) X}
    (hB : ∀ l hl, PreservesFiltration (.attach D j hj hs) (B.action l hl)) :
    RestrictionHomConditions B j (complex (.attach D j hj hs)).obj := by
  let E := DimensionFiltration.attach D j hj hs
  let F := complex E
  refine ⟨?_, ?_, ?_⟩
  · have hsX : IsStrictExtension hj s F := (normalizedOrbitIC_top h a).2.1.1
    exact (mapBijectiveOfIso (derivedInverseImage j) ((identityValue X).app F.obj)
      ((identityValue X).app F.obj) (derivedStrictMapBijective hj s hsX hsX)).1
  · intro l hl H Q₀ P₁ S T hS hT
    exact productRestrictionBijective a _ _ (gl2JetCoordinates c l) h
      (B.action l hl) (hB l hl) (𝟙 _) S T hS hT
  · intro l hl
    let H := (jetSystem c).group l
    exact (doubleParameterRestrictionBijective (B.action l hl) F.obj
      (productRestrictionBijective a _ _ (gl2JetProductCoordinates c l l) h
        (B.action l hl) (hB l hl) (parameterMultiply H) _ _ (Or.inl rfl) (Or.inr rfl))).1

end ActionHom

section Normalize

open Analytic Analytic.IntersectionComplex
open EquivariantIntersectionComplexesSpecs SchubertIntersectionConstructibilitySpecs
open LatticeModelSpecs RankTwoSchubertStrataSpecs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem normalizedAttachmentUnique {J : JetSystem.{0}} (a : DerivedAdjunctions.{0})
    {U X : TopCat.{0}} {d s : ℕ} {D : DimensionFiltration U d}
    {j : U ⟶ X} {hj : IsOpenEmbedding j} {hs : s < d}
    {B : JetAction J U} {A : JetAction J X} (hB : B.cutoff = A.cutoff) (h : Intertwines B A j)
    (hR : IsIso (attachmentRestriction (s := s) D j hj (a j)))
    (hHom : RestrictionHomConditions A j (complex (.attach D j hj hs)).obj)
    (prev : ∃! β : B.Equivariance (complex D).obj, NormalizedICDatum a B D β) :
    ∃! α : A.Equivariance (complex (.attach D j hj hs)).obj,
      NormalizedICDatum a A (.attach D j hj hs) α := by
  obtain ⟨β, hβ, hβuniq⟩ := prev
  let r := @asIso _ _ _ _ _ hR
  let v := (DerivedCategory.Plus.ι (C := Sheaves U)).mapIso r.symm
  obtain ⟨α, hα, huniq⟩ := liftEquivariance hB.le h v β hHom
  refine ⟨α, NormalizedICDatum.attach (D := D) (hj := hj) (hs := hs) hB h α β hβ hR hα, ?_⟩
  intro α' h'
  cases h' with
  | @attach _ _ _ _ _ _ _ _ _ B' hB' h' _ β' hβ' hR' hcomm =>
    have he : B' = B := actionOnEmbedding_unique hj.injective hB' hB h' h
    subst B'
    have he' : β' = β := hβuniq β' hβ'
    subst β'
    exact huniq α' hcomm

theorem normalizedOrbitICEquivariance {c : ContinuousJets} (a : DerivedAdjunctions.{0})
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {A : JetAction (jetSystem c) (SchubertSpace ab N hN)} (hA : ActualSchubertAction ab N hN A)
    {X : TopCat.{0}} {s k : ℕ} {f : X ⟶ SchubertSpace ab N hN}
    {P : Stratification X} {D : DimensionFiltration X s}
    (h : IsNormalizedOrbitIC ab N hN f k P D) :
    ∀ (B : JetAction (jetSystem c) X), B.cutoff = A.cutoff → Intertwines B A f →
      ∃! α : B.Equivariance (complex D).obj, NormalizedICDatum a B D α := by
  induction h with
  | top f P stage h𝒫 =>
    intro B _ _
    exact normalizedTopUnique a B (difference ab)
  | @attach U X d k D f P Q j hj hs previous stage strata bd coho perverse strict ih =>
    intro B hCut hB
    let hInv := orbitAttachment_invariant hA previous stage hCut hB
    let C := restrictJetAction B hj.isEmbedding hInv
    have hCB : Intertwines C B j := restrictJetAction_commutes B hj.isEmbedding hInv
    have hC : Intertwines C A (j ≫ f) := intertwines_comp rfl hCB hB
    let s := orbitDimension ab (k + 1)
    have hR : IsIso (attachmentRestriction (s := s) D j hj (a j)) :=
      (MiddleExtension.attachmentIsMiddleExtension j hj s Q P strata (complex D)
        (normalizedOrbitIC_top previous a).1 bd).2.2 (a j)
    have hNew : IsNormalizedOrbitIC ab N hN f (k + 1) P (.attach D j hj hs) :=
      .attach f P Q j hj hs previous stage strata bd coho perverse strict
    exact normalizedAttachmentUnique a (B := C) rfl hCB hR
      (schubertRestrictionHom a hNew (orbitAction_preservesFiltration hA hNew hCut hB))
      (ih C hCut hC)

theorem normalizedSchubertEquivariance {c : ContinuousJets} (a : DerivedAdjunctions.{0})
    {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}
    {A : JetAction (jetSystem c) (SchubertSpace ab N hN)} (hA : ActualSchubertAction ab N hN A)
    {s k : ℕ} {P : Stratification (SchubertSpace ab N hN)}
    {D : DimensionFiltration (SchubertSpace ab N hN) s}
    (h : IsNormalizedOrbitIC ab N hN (𝟙 _) k P D) :
    ∃! α : A.Equivariance (complex D).obj, NormalizedICDatum a A D α :=
  normalizedOrbitICEquivariance a hA h A rfl (fun _ _ _ => TopCat.ext fun _ => rfl)

end Normalize

section TransportConstant

open Analytic Analytic.IntersectionComplex
open EquivariantIntersectionComplexesSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open ConvolutionConstantDescentSpec (shiftedConstantPullback)

open private square_hom from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

theorem constantComparisonOfEq {V X : TopCat.{0}} {p q : V ⟶ X} (h : p = q) (d : ℕ) :
    eqToHom (congrArg (fun j => (derivedInverseImage j).obj (shiftedConstant X d).obj) h) ≫
      (shiftedConstantPullback q d).hom = (shiftedConstantPullback p d).hom := by
  subst q
  simp

theorem constantPullbackSquare {U X V Y : TopCat.{0}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
    (h : j ≫ e = v ≫ k) (d : ℕ) :
    (squareValue h).hom.app (shiftedConstant Y d).obj ≫
      (derivedInverseImage v).map (shiftedConstantPullback k d).hom ≫
      (shiftedConstantPullback v d).hom =
    (derivedInverseImage j).map (shiftedConstantPullback e d).hom ≫
      (shiftedConstantPullback j d).hom := by
  rw [square_hom h]
  simp only [Category.assoc]
  rw [ConvolutionConstantDescent.shiftedPullbackComposition v k d, constantComparisonOfEq h d]
  exact ((derivedInverseImageComposition j e).app (shiftedConstant Y d).obj).inv_comp_eq.mpr
    (ConvolutionConstantDescent.shiftedPullbackComposition j e d).symm

theorem constantDatum_commutes {H : AnalyticGroup.{0}} {U X : TopCat.{0}}
    {B : AnalyticAction H U} {A : AnalyticAction H X} {j : U ⟶ X}
    (h : JetEquivariantRestrictionSpecs.ActionSquare B A j) (d : ℕ)
    {β : B.Equivariance (shiftedConstant U d).obj}
    {α : A.Equivariance (shiftedConstant X d).obj}
    (hβ : β.iso = shiftedConstantPullback B.act d ≪≫ (shiftedConstantPullback (Analytic.AnalyticAction.projection H U) d).symm)
    (hα : α.iso = shiftedConstantPullback A.act d ≪≫ (shiftedConstantPullback (Analytic.AnalyticAction.projection H X) d).symm) :
    JetEquivariantRestrictionSpecs.Commutes h β α (shiftedConstantPullback j d).inv := by
  let p := Analytic.AnalyticAction.projection H U
  let r := shiftedConstantPullback j d
  let u := (derivedInverseImage p).map r.hom ≫ (shiftedConstantPullback p d).hom
  haveI : IsIso u := by dsimp only [u]; infer_instance
  unfold JetEquivariantRestrictionSpecs.Commutes
  apply (cancel_mono u).mp
  rw [hβ, hα]
  simp only [u, p, r, Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [constantPullbackSquare (projectionSquare H j) d]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← constantPullbackSquare h d, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

end TransportConstant

section TransportIso

open Analytic Analytic.IntersectionComplex EquivariantIntersectionComplexesSpecs
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open RepTheorySurvey.Geometric.DerivedPullbackPasting (squareBoundedBelowCompatibility)

open private square_hom from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
open private adjointSquareMap_counit from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
open private pullbackEquivalence from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- The attachment restriction on an arbitrary bounded-below coefficient complex. -/
def attachmentRestrictionApp {U X : TopCat.{0}} (j : U ⟶ X)
    (hj : IsOpenEmbedding j) (s : ℕ) (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (F : BoundedBelow U) : (boundedBelowInverseImage j).obj ((attachment j hj s).obj F) ⟶ F :=
  (boundedBelowInverseImage j).map ((attachmentInclusion j hj s).app F) ≫ a.counit.app F

theorem attachmentRestriction_naturality {U X : TopCat.{0}} (j : U ⟶ X)
    (hj : IsOpenEmbedding j) (s : ℕ) (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    {F G : BoundedBelow U} (v : F ⟶ G) :
    (boundedBelowInverseImage j).map ((attachment j hj s).map v) ≫ attachmentRestrictionApp j hj s a G =
      attachmentRestrictionApp j hj s a F ≫ v := by
  unfold attachmentRestrictionApp
  rw [← Functor.map_comp_assoc, (attachmentInclusion j hj s).naturality v, Functor.map_comp,
    Category.assoc]
  exact congrArg (fun g => (boundedBelowInverseImage j).map ((attachmentInclusion j hj s).app F) ≫ g)
    (a.counit.naturality v) |>.trans (Category.assoc _ _ _).symm

theorem mateCounitNaturality {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R : D ⥤ B}
    (α : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R) (F : D) {T : B}
    (u : T ⟶ R.obj F) :
    J.map (E.map u) ≫ J.map (adjointSquareMap α a b F) ≫ a.counit.app (V.obj F) =
      α.hom.app T ≫ V.map (K.map u ≫ b.counit.app F) := by
  rw [adjointSquareMap_counit, ← Category.assoc]
  change ((E ⋙ J).map u ≫ α.hom.app (R.obj F)) ≫ V.map (b.counit.app F) = _
  rw [α.hom.naturality, Category.assoc]
  change α.hom.app T ≫ V.map (K.map u) ≫ V.map (b.counit.app F) = _
  rw [V.map_comp]

set_option maxHeartbeats 350000 in
theorem attachmentTransport_counit {U X V Y : TopCat.{0}}
    {j : U ⟶ X} {k : V ⟶ Y} (hj : IsOpenEmbedding j) (hk : IsOpenEmbedding k)
    {e : X ≅ Y} {v : U ≅ V} (h : j ≫ e.hom = v.hom ≫ k)
    (s : ℕ) (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage k ⊣ derivedDirectImage k) (F : BoundedBelow V)
    (τ : attachment k hk s ⋙ boundedBelowInverseImage e.hom ≅
      boundedBelowInverseImage v.hom ⋙ attachment j hj s)
    (hτ : τ.hom.app F ≫ (attachmentInclusion j hj s).app ((boundedBelowInverseImage v.hom).obj F) =
      (boundedBelowInverseImage e.hom).map ((attachmentInclusion k hk s).app F) ≫
        directImageComparison h a b F) :
    (boundedBelowInverseImage j).map (τ.hom.app F) ≫
      attachmentRestrictionApp j hj s a ((boundedBelowInverseImage v.hom).obj F) =
    (pullbackSquare h).hom.app ((attachment k hk s).obj F) ≫
      (boundedBelowInverseImage v.hom).map (attachmentRestrictionApp k hk s b F) := by
  unfold attachmentRestrictionApp
  rw [← Functor.map_comp_assoc, hτ, Functor.map_comp, Category.assoc]
  exact mateCounitNaturality (pullbackSquare h) a b F ((attachmentInclusion k hk s).app F)

theorem attachmentIsoTransport {U X V Y : TopCat.{0}}
    {j : U ⟶ X} {k : V ⟶ Y} (hj : IsOpenEmbedding j) (hk : IsOpenEmbedding k)
    {e : X ≅ Y} {v : U ≅ V} (h : j ≫ e.hom = v.hom ≫ k)
    (s : ℕ) (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage k ⊣ derivedDirectImage k)
    {F : BoundedBelow U} {G : BoundedBelow V}
    (c : F ≅ (boundedBelowInverseImage v.hom).obj G) :
    ∃ z : (attachment j hj s).obj F ≅ (boundedBelowInverseImage e.hom).obj ((attachment k hk s).obj G),
      (boundedBelowInverseImage j).map z.hom ≫
        (pullbackSquare h).hom.app ((attachment k hk s).obj G) ≫
        (boundedBelowInverseImage v.hom).map (attachmentRestrictionApp k hk s b G) =
      attachmentRestrictionApp j hj s a F ≫ c.hom := by
  obtain ⟨τ, hτ⟩ := MiddleExtension.attachmentTransport j k hj hk e v h s a b
  have hRest := attachmentTransport_counit hj hk h s a b G τ (hτ G)
  let E := attachment j hj s
  let ζ := (τ.app G).symm
  let z := E.mapIso c ≪≫ ζ
  refine ⟨z, ?_⟩
  rw [← hRest]
  let L := boundedBelowInverseImage j
  let I := τ.app G
  change L.map (E.map c.hom ≫ I.inv) ≫ L.map I.hom ≫ _ = _
  rw [L.map_comp, Category.assoc, ← L.map_comp_assoc I.inv I.hom, I.inv_hom_id,
    L.map_id, Category.id_comp]
  exact attachmentRestriction_naturality j hj s a c.hom

theorem restrictionIsoOfTransport {U X V Y : TopCat.{0}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ≅ Y} {v : U ≅ V}
    (h : j ≫ e.hom = v.hom ≫ k)
    {F : BoundedBelow U} {G : BoundedBelow V} {E : BoundedBelow X} {K : BoundedBelow Y}
    (c : F ≅ (boundedBelowInverseImage v.hom).obj G)
    (z : E ≅ (boundedBelowInverseImage e.hom).obj K)
    {r : (boundedBelowInverseImage j).obj E ⟶ F}
    {r' : (boundedBelowInverseImage k).obj K ⟶ G} [IsIso r]
    (he : (boundedBelowInverseImage j).map z.hom ≫ (pullbackSquare h).hom.app K ≫
      (boundedBelowInverseImage v.hom).map r' = r ≫ c.hom) :
    IsIso r' := by
  let B := boundedBelowInverseImage v.hom
  let w := (boundedBelowInverseImage j).mapIso z ≪≫ (pullbackSquare h).app K
  have he' : w.hom ≫ B.map r' = r ≫ c.hom := by
    simpa only [w, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using he
  have hMap : B.map r' = w.inv ≫ r ≫ c.hom := w.eq_inv_comp.mpr he'
  haveI : IsIso (B.map r') := by rw [hMap]; infer_instance
  haveI : B.ReflectsIsomorphisms :=
    inferInstanceAs (pullbackEquivalence v).functor.ReflectsIsomorphisms
  exact isIso_of_reflects_iso r' B

theorem restrictionCompositeEq {U X V Y : TopCat.{0}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ k)
    {F : BoundedBelow U} {G : BoundedBelow V} {E : BoundedBelow X} {K : BoundedBelow Y}
    {c : F ≅ (boundedBelowInverseImage v).obj G}
    {z : E ≅ (boundedBelowInverseImage e).obj K}
    (r : (boundedBelowInverseImage j).obj E ≅ F)
    (r' : (boundedBelowInverseImage k).obj K ≅ G)
    (he : (boundedBelowInverseImage j).map z.hom ≫ (pullbackSquare h).hom.app K ≫
      (boundedBelowInverseImage v).map r'.hom = r.hom ≫ c.hom) :
    (r.inv.hom ≫ (derivedInverseImage j).map z.hom.hom ≫
      (derivedInverseImageComposition j e).inv.app K.obj) ≫
        eqToHom (congrArg (fun f => (derivedInverseImage f).obj K.obj) h) =
      c.hom.hom ≫ (derivedInverseImage v).map r'.inv.hom ≫
        (derivedInverseImageComposition v k).inv.app K.obj := by
  have h₁ := r.inv_comp_eq.mpr he
  let w := (boundedBelowInverseImage v).mapIso r'
  have h₂ : r.inv ≫ (boundedBelowInverseImage j).map z.hom ≫ (pullbackSquare h).hom.app K =
      c.hom ≫ (boundedBelowInverseImage v).map r'.inv :=
    (w.eq_comp_inv.mpr (by simpa only [Category.assoc, w, Functor.mapIso_hom] using h₁))
  have h₃ := congrArg (DerivedCategory.Plus.ι (C := Sheaves U)).map h₂
  simp only [CategoryTheory.Functor.map_comp] at h₃
  change r.inv.hom ≫ (derivedInverseImage j).map z.hom.hom ≫
      ((pullbackSquare h).hom.app K).hom =
    c.hom.hom ≫ (derivedInverseImage v).map r'.inv.hom at h₃
  rw [squareBoundedBelowCompatibility h K, square_hom h] at h₃
  let m := (derivedInverseImageComposition v k).app K.obj
  let q := (r.inv.hom ≫ (derivedInverseImage j).map z.hom.hom ≫
      (derivedInverseImageComposition j e).inv.app K.obj) ≫
        eqToHom (congrArg (fun f => (derivedInverseImage f).obj K.obj) h)
  have h₄ : q ≫ m.hom = c.hom.hom ≫ (derivedInverseImage v).map r'.inv.hom := by
    simpa only [q, m, Iso.app_hom, Category.assoc] using h₃
  exact (m.eq_comp_inv.mpr h₄).trans (Category.assoc _ _ _)

end TransportIso

section TransportGeometry

open Analytic EquivariantIntersectionComplexesSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion)
open JetEquivariantRestrictionSpecs (ActionSquare Commutes)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem openSquare_apply {U X V Y : TopCat.{0}} {j : U ⟶ X} {k : V ⟶ Y}
    {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ k) (x : U) :
    e (j x) = k (v x) :=
  congrArg (fun (m : U ⟶ Y) => m x) h

theorem invariantRange_of_equivariantIso {J : JetSystem.{0}} {U X V Y : TopCat.{0}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ≅ Y} {v : U ≅ V}
    (q : j ≫ e.hom = v.hom ≫ k)
    {A₀ : JetAction J U} {A : JetAction J X} {B : JetAction J Y}
    (hc : A₀.cutoff = A.cutoff) (hle : A.cutoff ≤ B.cutoff)
    (hJ : Intertwines A₀ A j) (hE : Intertwines A B e.hom)
    (l : ℕ) (hb : B.cutoff ≤ l) :
    invariantRange (B.action l hb) k := by
  let ha := hle.trans hb
  let hu := hc.symm ▸ ha
  intro g z
  let x := v.inv z
  have hx : v.hom x = z :=
    congrArg (fun f : V ⟶ V => f z) v.inv_hom_id
  refine ⟨v.hom ((A₀.action l hu).act (g, x)), ?_⟩
  rw [← openSquare_apply q, ← intertwines_apply hJ l hu ha, ← intertwines_apply hE l ha hb,
    openSquare_apply q, hx]

theorem intertwines_openSquare {J : JetSystem.{0}} {U X V Y : TopCat.{0}}
    {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
    (q : j ≫ e = v ≫ k) (hk : Function.Injective k)
    {A₀ : JetAction J U} {A : JetAction J X} {B₀ : JetAction J V} {B : JetAction J Y}
    (hca : A₀.cutoff = A.cutoff) (hcb : B₀.cutoff = B.cutoff)
    (hJ : Intertwines A₀ A j) (hE : Intertwines A B e) (hK : Intertwines B₀ B k) :
    Intertwines A₀ B₀ v := by
  intro l ha hb
  let hx := hca ▸ ha
  let hy := hcb ▸ hb
  refine TopCat.ext fun p => hk ?_
  change k ((B₀.action l hb).act (p.1, v p.2)) = k (v ((A₀.action l ha).act p))
  rw [← intertwines_apply hK l hb hy, ← openSquare_apply q,
    intertwines_apply hE l hx hy, intertwines_apply hJ l ha hx, openSquare_apply q]

theorem actionSquare_comp {H : AnalyticGroup.{0}} {U X Y : TopCat.{0}}
    {B : AnalyticAction H U} {A : AnalyticAction H X} {C : AnalyticAction H Y}
    {j : U ⟶ X} {k : X ⟶ Y} (h : ActionSquare B A j) (h' : ActionSquare A C k) :
    ActionSquare B C (j ≫ k) := by
  refine TopCat.ext fun p => ?_
  change C.act (p.1, k (j p.2)) = k (j (B.act p))
  have e₁ := congrArg (fun f : AnalyticAction.Parameters H X ⟶ Y => f (p.1, j p.2)) h'
  have e₂ := congrArg (fun f : AnalyticAction.Parameters H U ⟶ X => f p) h
  exact e₁.trans (congrArg k e₂)

theorem commutes_along_eq {H : AnalyticGroup.{0}} {U X : TopCat.{0}}
    {B : AnalyticAction H U} {A : AnalyticAction H X} {j k : U ⟶ X} (h : j = k)
    (hj : ActionSquare B A j) (hk : ActionSquare B A k)
    {G : Derived U} {F : Derived X} (β : B.Equivariance G) (α : A.Equivariance F)
    {v : G ⟶ (derivedInverseImage j).obj F} {w : G ⟶ (derivedInverseImage k).obj F}
    (hv : v ≫ eqToHom (congrArg (fun f => (derivedInverseImage f).obj F) h) = w)
    (hc : Commutes hj β α v) : Commutes hk β α w := by
  subst k
  simp only [eqToHom_refl, Category.comp_id] at hv
  subst w
  exact hc

/-- In a commuting square, compatibility of the two paths reflects through
an equivariant isomorphism on the preceding open stage. -/
theorem equivarianceOnTransportedRestriction {H : AnalyticGroup.{0}}
    {U X V Y : TopCat.{0}} {j : U ⟶ X} {k : V ⟶ Y} {e : X ⟶ Y} {v : U ≅ V}
    (p : j ≫ e = v.hom ≫ k)
    {A₀ : AnalyticAction H U} {A : AnalyticAction H X}
    {B₀ : AnalyticAction H V} {B : AnalyticAction H Y}
    (hJ : ActionSquare A₀ A j) (hE : ActionSquare A B e)
    (hV : ActionSquare A₀ B₀ v.hom) (hK : ActionSquare B₀ B k)
    {E₀ : Derived U} {E : Derived X} {F₀ : Derived V} {F : Derived Y}
    (α₀ : A₀.Equivariance E₀) (α : A.Equivariance E)
    (β₀ : B₀.Equivariance F₀) (β : B.Equivariance F)
    (u : E₀ ⟶ (derivedInverseImage j).obj E) (z : E ⟶ (derivedInverseImage e).obj F)
    (c : E₀ ≅ (derivedInverseImage v.hom).obj F₀)
    (w : F₀ ⟶ (derivedInverseImage k).obj F)
    (he : (u ≫ (derivedInverseImage j).map z ≫ (derivedInverseImageComposition j e).inv.app F) ≫
      eqToHom (congrArg (fun t => (derivedInverseImage t).obj F) p) =
      c.hom ≫ (derivedInverseImage v.hom).map w ≫ (derivedInverseImageComposition v.hom k).inv.app F)
    (h₁ : Commutes hJ α₀ α u) (h₂ : Commutes hE α β z)
    (h₃ : Commutes hV α₀ β₀ c.hom) : Commutes hK β₀ β w := by
  let hL := actionSquare_comp hJ hE
  let hR := actionSquare_comp hV hK
  have h₄ := (JetEquivariantRestriction.equivariancePasting hJ hE hL
    α₀ α β u z h₁).1 h₂
  have h₅ := commutes_along_eq p hL hR α₀ β he h₄
  have hf : (derivedInverseImage (parameterInclusion H v.hom)).Faithful :=
    (derivedInverseImageEquivalence (parameterIso H v)).fullyFaithfulFunctor.faithful
  exact (JetEquivariantRestriction.equivariancePasting hV hK hR α₀ β₀ β c.hom w h₃).2
    (inferInstance : IsIso c.hom) hf h₅

end TransportGeometry

section OrbitTransport

open Analytic Analytic.IntersectionComplex EquivariantIntersectionComplexesSpecs
open LatticeModelSpecs RankTwoSchubertStrataSpecs SchubertIntersectionConstructibilitySpecs
open private embeddingIsoOfRange embeddingIsoOfRange_comp from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem transportedOpenRange {U X V Y Z W : TopCat.{0}}
    (j : U ⟶ X) (k : V ⟶ Y) (e : X ≅ Y) (f : X ⟶ Z) (g : Y ⟶ W) (p : Z ⟶ W)
    (comm : f ≫ p = e.hom ≫ g) (hf : Function.Injective f) (hg : Function.Injective g)
    {S : Set Z} {T : Set W}
    (hS : Set.range (j ≫ f) = S) (hT : Set.range (k ≫ g) = T) (h : p ⁻¹' T = S) :
    Set.range (j ≫ e.hom) = Set.range k := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    have hx : f (j u) ∈ S := hS ▸ Set.mem_range_self u
    have hpx : p (f (j u)) ∈ T := show f (j u) ∈ p ⁻¹' T from h.symm ▸ hx
    rw [← hT] at hpx
    obtain ⟨v, hv⟩ := hpx
    exact ⟨v, hg (hv.trans (openSquare_apply comm (j u)))⟩
  · rintro ⟨v, rfl⟩
    let x := e.inv (k v)
    have hx : e.hom x = k v := congrArg (fun m : Y ⟶ Y => m (k v)) e.inv_hom_id
    have hy : g (k v) ∈ T := hT ▸ Set.mem_range_self v
    have hpy : p (f x) ∈ T := by rw [openSquare_apply comm x, hx]; exact hy
    have hfx : f x ∈ S := h ▸ (show f x ∈ p ⁻¹' T from hpy)
    rw [← hS] at hfx
    obtain ⟨u, hu⟩ := hfx
    exact ⟨u, (congrArg e.hom (hf hu)).trans hx⟩

theorem filtrationIsoTopCast {X Y : TopCat.{0}} (e : X ≅ Y) {d d' : ℕ} (h : d' = d) :
    FiltrationIso e (.top X d) (h ▸ DimensionFiltration.top Y d') := by
  subst d'
  exact .top e d

theorem filtrationIsoAttachCast {U X V Y : TopCat.{0}} {d d' s s' : ℕ}
    {D : DimensionFiltration U d} {E : DimensionFiltration V d'}
    {e : X ≅ Y} {v : U ≅ V} {j : U ⟶ X} {k : V ⟶ Y}
    {hj : IsOpenEmbedding j} {hk : IsOpenEmbedding k} {hD : s < d} {hE : s' < d'}
    (hd : d' = d) (hs : s' = s) (h : j ≫ e.hom = v.hom ≫ k)
    (prev : FiltrationIso v D (hd ▸ E)) :
    FiltrationIso e (.attach D j hj hD) (hs ▸ DimensionFiltration.attach E k hk hE) := by
  subst d'
  subst s'
  exact .attach prev h

/-- Dimension-preserving transport of the actual orbit strata identifies every
open inclusion of the two normalized orbit filtrations. -/
theorem orbitFiltrationIso {ab cd : DominantPair} {N M : ℕ}
    {hN : OrbitBound ab N} {hM : OrbitBound cd M}
    (p : SchubertSpace ab N hN ≅ SchubertSpace cd M hM)
    (hp : PreservesOrbitStrata p)
    {X : TopCat.{0}} {s l : ℕ} {f : X ⟶ SchubertSpace ab N hN}
    {P : Stratification X} {D : DimensionFiltration X s}
    (hD : IsNormalizedOrbitIC ab N hN f l P D) :
    ∀ {Y : TopCat.{0}} {s' : ℕ} {g : Y ⟶ SchubertSpace cd M hM}
      {Q : Stratification Y} {E : DimensionFiltration Y s'},
      IsNormalizedOrbitIC cd M hM g l Q E → ∀ (e : X ≅ Y),
      f ≫ p.hom = e.hom ≫ g →
      ∃ hs : s' = s, FiltrationIso e D (hs ▸ E) := by
  have hd := (orbitTopDimension_eq_of_iso hp).symm
  induction hD with
  | top f P htop perverse =>
    intro Y s' g Q E hE e h
    cases hE with
    | top g Q htop' perverse' => exact ⟨hd, filtrationIsoTopCast e hd⟩
  | @attach U X d l D f P Q j hj hs previous stage strata bd coho perverse strict ih =>
    intro Y s' g R E hE e h
    cases hE with
    | @attach V Y d' l' E g R S k hk hs' previous' stage' strata' bd' coho' perverse' strict' =>
      have hr := transportedOpenRange j k e f g p.hom h stage.1.injective stage'.1.injective
        (orbitStageRealizes previous).2.1 (orbitStageRealizes previous').2.1
        (orbitStage_preimage_of_iso p hp l)
      have hEmbed : IsEmbedding (j ≫ e.hom : U ⟶ Y) :=
        (TopCat.homeoOfIso e).isEmbedding.comp hj.isEmbedding
      let v := embeddingIsoOfRange (j ≫ e.hom) k hEmbed hk.isEmbedding hr
      have hq : j ≫ e.hom = v.hom ≫ k :=
        (embeddingIsoOfRange_comp (j ≫ e.hom) k hEmbed hk.isEmbedding hr).symm
      have hPrev : (j ≫ f) ≫ p.hom = v.hom ≫ (k ≫ g) := by
        rw [Category.assoc, h, ← Category.assoc j e.hom g, hq, Category.assoc]
      obtain ⟨hInner, hIso⟩ := ih previous' v hPrev
      have hOuter : orbitDimension cd (l + 1) = orbitDimension ab (l + 1) := by
        unfold orbitDimension
        rw [hd]
      exact ⟨hOuter, filtrationIsoAttachCast (hj := hj) (hk := hk) (hD := hs) (hE := hs')
        hInner hOuter hq hIso⟩

end OrbitTransport

section Transport

open Analytic Analytic.IntersectionComplex EquivariantIntersectionComplexesSpecs
open ConvolutionConstantDescentSpec (shiftedConstantPullback)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem transportNormalizedAttachment {J : JetSystem.{0}} (a : DerivedAdjunctions.{0})
    {U X V Y : TopCat.{0}} {s d : ℕ} {D : DimensionFiltration U d} {E : DimensionFiltration V d}
    {j : U ⟶ X} {k : V ⟶ Y} {hj : IsOpenEmbedding j} {hk : IsOpenEmbedding k} {hs : s < d}
    {e : X ≅ Y} {v : U ≅ V} (sq : j ≫ e.hom = v.hom ≫ k)
    {A₀ : JetAction J U} {A : JetAction J X} {B₀ : JetAction J V} {B : JetAction J Y}
    (ha₀ : A₀.cutoff = A.cutoff) (hb₀ : B₀.cutoff = B.cutoff) (hle : A.cutoff ≤ B.cutoff)
    (hJ : Intertwines A₀ A j) (hE : Intertwines A B e.hom)
    (hV : Intertwines A₀ B₀ v.hom) (hK : Intertwines B₀ B k)
    {α₀ : A₀.Equivariance (complex D).obj}
    {α : A.Equivariance (complex (.attach D j hj hs)).obj}
    {β₀ : B₀.Equivariance (complex E).obj} (hβ₀ : NormalizedICDatum a B₀ E β₀)
    (hR : IsIso (attachmentRestriction (s := s) D j hj (a j)))
    (hα : IntertwinesPullback hJ α₀ α ((@asIso _ _ _ _ _ hR).inv.hom))
    (u : complex D ≅ (boundedBelowInverseImage v.hom).obj (complex E))
    (hU : IntertwinesPullback hV α₀ β₀ u.hom.hom) :
    ∃ (β : B.Equivariance (complex (.attach E k hk hs)).obj)
      (z : complex (.attach D j hj hs) ≅ (boundedBelowInverseImage e.hom).obj
        (complex (.attach E k hk hs))),
      NormalizedICDatum a B (.attach E k hk hs) β ∧ IntertwinesPullback hE α β z.hom.hom := by
  let F := complex (.attach E k hk hs)
  let r := @asIso _ _ _ _ _ hR
  obtain ⟨z, hz⟩ := attachmentIsoTransport hj hk sq s (a j) (a k) u
  let zv := (DerivedCategory.Plus.ι (C := Sheaves X)).mapIso z
  let uv := (DerivedCategory.Plus.ι (C := Sheaves U)).mapIso u
  obtain ⟨β, hZ, _⟩ := liftEquivariance hle hE zv α (homeomorphRestrictionHom B e F.obj)
  letI : IsIso (attachmentRestrictionApp j hj s (a j) (complex D)) := hR
  have hR' : IsIso (attachmentRestriction (s := s) E k hk (a k)) :=
    restrictionIsoOfTransport sq u z hz
  let r' := @asIso _ _ _ _ _ hR'
  have hComp := restrictionCompositeEq sq (z := z) (c := u) r r' hz
  have hRestrict : IntertwinesPullback hK β₀ β r'.inv.hom := by
    intro l hv hb
    let hx := hle.trans hb
    let hu := ha₀.symm ▸ hx
    apply (commutes_iff hK β₀ β r'.inv.hom l hv hb).mp
    exact equivarianceOnTransportedRestriction sq (hJ l hu hx) (hE l hx hb)
      (hV l hu hv) (hK l hv hb) (α₀.datum l hu) (α.datum l hx)
      (β₀.datum l hv) (β.datum l hb) r.inv.hom zv.hom uv r'.inv.hom hComp
      ((commutes_iff hJ α₀ α r.inv.hom l hu hx).mpr (hα l hu hx))
      ((commutes_iff hE α β zv.hom l hx hb).mpr (hZ l hx hb))
      ((commutes_iff hV α₀ β₀ uv.hom l hu hv).mpr (hU l hu hv))
  refine ⟨β, z, ?_, hZ⟩
  exact NormalizedICDatum.attach (D := E) (hj := hk) (hs := hs) hb₀ hK β β₀ hβ₀ hR' hRestrict

/-- Transport of normalized equivariance along a homeomorphism of filtrations,
using the actual constant identification on the top stratum. -/
theorem normalizedEquivarianceTransport {J : JetSystem.{0}} (a : DerivedAdjunctions.{0})
    {X Y : TopCat.{0}} {s : ℕ} {e : X ≅ Y}
    {D : DimensionFiltration X s} {E : DimensionFiltration Y s} (he : FiltrationIso e D E) :
    ∀ {A : JetAction J X} {B : JetAction J Y} (h : Intertwines A B e.hom),
      A.cutoff ≤ B.cutoff →
      ∀ {α : A.Equivariance (complex D).obj}, NormalizedICDatum a A D α →
      ∃ (β : B.Equivariance (complex E).obj)
        (v : complex D ≅ (boundedBelowInverseImage e.hom).obj (complex E)),
        NormalizedICDatum a B E β ∧ IntertwinesPullback h α β v.hom.hom := by
  induction he with
  | @top X Y e d =>
    intro A B h _ α hα
    let β := constantJetDatum B d
    let v : shiftedConstant X d ≅ (boundedBelowInverseImage e.hom).obj (shiftedConstant Y d) :=
      ObjectProperty.isoMk _ (shiftedConstantPullback e.hom d).symm
    refine ⟨β, v, normalizedConstantDatum a B d, ?_⟩
    intro l ha hb
    apply (commutes_iff h α β v.hom.hom l ha hb).mp
    apply constantDatum_commutes (h l ha hb) d
    · exact (normalizedConstantDatum_iso a hα l ha).trans (constantDatum_iso (A.action l ha) d)
    · exact constantDatum_iso (B.action l hb) d
  | @attach U X V Y d s D E e v j k hj hk hs prior sq ih =>
    intro A B hE hle α hα
    cases hα with
    | @attach _ _ _ _ _ _ _ _ _ A₀ hA₀ hJ _ α₀ hNorm₀ hR hα =>
      let hInv := invariantRange_of_equivariantIso sq hA₀ hle hJ hE
      let B₀ := restrictJetAction B hk.isEmbedding hInv
      have hK : Intertwines B₀ B k := restrictJetAction_commutes B hk.isEmbedding hInv
      have hv : Intertwines A₀ B₀ v.hom := intertwines_openSquare sq hk.injective hA₀ rfl hJ hE hK
      obtain ⟨β₀, u, hβ₀, hU⟩ := ih hv (hA₀.le.trans hle) hNorm₀
      exact transportNormalizedAttachment a sq hA₀ rfl hle hJ hE hv hK hβ₀ hR hα u hU

end Transport

section TransportOrbits

open Analytic Analytic.IntersectionComplex EquivariantIntersectionComplexesSpecs
open LatticeModelSpecs RankTwoSchubertStrataSpecs SchubertIntersectionConstructibilitySpecs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Equivariant orbit-preserving homeomorphisms of actual Schubert closures
transport the normalized complexes and their finite-jet data. -/
theorem normalizedEquivarianceTransportOnOrbits (a : DerivedAdjunctions.{0}) {c : ContinuousJets}
    {ab cd : DominantPair} {N M : ℕ} {hN : OrbitBound ab N} {hM : OrbitBound cd M}
    {A : JetAction (jetSystem c) (SchubertSpace ab N hN)}
    {B : JetAction (jetSystem c) (SchubertSpace cd M hM)}
    (hA : ActualSchubertAction ab N hN A) (hB : ActualSchubertAction cd M hM B)
    (e : SchubertSpace ab N hN ≅ SchubertSpace cd M hM) (he : PreservesOrbitStrata e)
    (h : Intertwines A B e.hom)
    {s t : ℕ} {P : Stratification (SchubertSpace ab N hN)}
    {Q : Stratification (SchubertSpace cd M hM)}
    {D : DimensionFiltration (SchubertSpace ab N hN) s}
    {E : DimensionFiltration (SchubertSpace cd M hM) t}
    (hD : IsNormalizedOrbitIC ab N hN (𝟙 _) (difference ab / 2) P D)
    (hE : IsNormalizedOrbitIC cd M hM (𝟙 _) (difference cd / 2) Q E)
    {α : A.Equivariance (complex D).obj} (hα : NormalizedICDatum a A D α) :
    ∃ (β : B.Equivariance (complex E).obj)
      (v : (complex D).obj ≅ (derivedInverseImage e.hom).obj (complex E).obj),
      NormalizedICDatum a B E β ∧ IntertwinesPullback h α β v.hom := by
  have hd := orbitTopDimension_eq_of_iso he
  have hc : A.cutoff ≤ B.cutoff := by rw [hA.1, hB.1, hd]
  have hl : difference cd / 2 = difference ab / 2 := by rw [hd]
  rw [hl] at hE
  obtain ⟨ht, hi⟩ := orbitFiltrationIso e he hD hE e (by simp)
  subst t
  obtain ⟨β, v, hβ, hv⟩ := normalizedEquivarianceTransport a hi h hc hα
  exact ⟨β, (DerivedCategory.Plus.ι (C := Sheaves (SchubertSpace ab N hN))).mapIso v, hβ, hv⟩

end TransportOrbits

open Analytic Analytic.IntersectionComplex
open EquivariantIntersectionComplexesSpecs SchubertIntersectionConstructibilitySpecs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The normalized rational intersection complexes on the actual rank-two
Schubert stages have canonical finite-jet equivariance, compatible with
homeomorphisms of the stratification and closed extension. -/
theorem equivariantIntersectionComplexes : Expected.EquivariantIntersectionComplexes := by
  refine ⟨derivedAdjunctionExists, fun hZ => closedAdjunctionExists hZ,
    closedExtensionCompatibility, gl2JetParameters, ?_, ?_, ?_⟩
  · intro a ab N hN
    obtain ⟨A⟩ := schubertJetActionExists gl2JetParameters ab N hN
    obtain ⟨P, D, hD⟩ :=
      SchubertIntersectionConstructibility.schubertIntersectionConstructibility ab N hN
    obtain ⟨α, hα, _⟩ := normalizedSchubertEquivariance a A.actual hD
    exact ⟨A, P, D, hD, α, hα⟩
  · intro a ab N hN A hA P D hD
    exact normalizedSchubertEquivariance a hA hD
  · intro a X Y s A B e h D E hle he α hα
    obtain ⟨β, v, hβ, hv⟩ := normalizedEquivarianceTransport a he h hle hα
    exact ⟨β, (DerivedCategory.Plus.ι (C := Sheaves X)).mapIso v, hβ, hv⟩

end RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
