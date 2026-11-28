import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.CentralTranslationBoundedJetSupport
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImage
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantClosedDirectImageComposition
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ShiftedStableWindows
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.CentralSchubertComparison
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.CentralFrameDescent

noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open LinearAlgebraicGroups (Points SchemeOver testSpec)
open scoped MatrixGroups TensorProduct

namespace RepTheorySurvey.Geometric.CentralLatticeTranslationSpecs

open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open Analytic Analytic.IntersectionComplex LocalSheaf
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open ClosedEquivarianceExtensionSpecs (above)
open CentralTranslationBoundedJetSupportSpecs (BoundedSchubertSupport)
open EquivariantHomeomorphismDirectImageSpecs (EquivariantDirectImageComparison PullbackIntertwines)
open EquivariantClosedDirectImageCompositionSpecs (ClosedExtensionArrow)

abbrev Loop := GL (Fin 2) K
abbrev Positive := PositiveGL 2

def scalarLoop (a : ℤ) : Loop :=
  (loopLinearEquiv 2).symm (diagonalEquiv (fun _ ↦ a))

abbrev translate := CentralSchubertComparisonSpecs.translate
abbrev shiftPair := CentralSchubertComparisonSpecs.shiftPair
abbrev shiftWindow := ShiftedStableWindowsSpecs.shiftWindow
abbrev centralPair := CentralFrameDescentSpecs.centralPair

def ScalarTranslation : Prop :=
  (∀ a, translate a (standardLattice 2) = scalarLattice 2 a) ∧
  (∀ a b L, translate a (translate b L) = translate (a + b) L) ∧
  (∀ L, translate 0 L = L) ∧
  (∀ (a : ℤ) (g : Loop), scalarLoop a * g = g * scalarLoop a) ∧
  (∀ (a : ℤ) (h : Positive), (h : Loop) • scalarLattice 2 a = scalarLattice 2 a) ∧
  (∀ a ab, translate a '' gl2Orbit ab = gl2Orbit (shiftPair a ab) ∧
    translate a '' closureLattices ab = closureLattices (shiftPair a ab)) ∧
  ∀ a, Continuous (translate a) ∧ Continuous (translate (-a))

/-- The stable-window isomorphisms and inclusions for scalar translation. -/
def WindowTranslation : Prop := ShiftedStableWindowsSpecs.WindowTranslation

abbrev SchubertTranslationData := CentralSchubertComparisonSpecs.SchubertTranslationData

def SchubertTranslation : Prop :=
  ∀ (a : ℤ) (ab : DominantPair) (N M : ℕ)
    (hN : OrbitBound ab N) (hM : OrbitBound (shiftPair a ab) M),
    Nonempty (SchubertTranslationData a ab N M hN hM)

def centralFirst (a : ℤ) : Set (Grassmannian Positive) := {coset Positive (scalarLoop a)}

def schubertFirst (ab : DominantPair) : Set (Grassmannian Positive) :=
  coset Positive '' {g : Loop | g • standardLattice 2 ∈ closureLattices ab}

def centralSecond (a : ℤ) : Set GL2Lattice := {scalarLattice 2 a}

theorem schubertStable (ab : DominantPair) : StableStage Positive (closureLattices ab) := by
  intro h L hL
  obtain ⟨cd, hcd, g, rfl⟩ := hL
  exact ⟨cd, hcd, h * g, mul_smul _ _ _⟩

theorem centralStable (a : ℤ) : StableStage Positive (centralSecond a) := by
  intro h L hL
  have hEq : L = scalarLattice 2 a := hL
  obtain ⟨g, hg⟩ := h.property
  rw [hEq, ← hg]
  exact positiveGL_preserves_scalar g a

abbrev LeftOrdered (a : ℤ) (ab : DominantPair) :=
  TwistedProduct Positive (centralFirst a) (closureLattices ab) (schubertStable ab)

abbrev RightOrdered (a : ℤ) (ab : DominantPair) :=
  TwistedProduct Positive (schubertFirst ab) (centralSecond a) (centralStable a)

abbrev leftTerminal (a : ℤ) (ab : DominantPair) :=
  terminalMap (A := centralFirst a) Positive (schubertStable ab)

abbrev rightTerminal (a : ℤ) (ab : DominantPair) :=
  terminalMap (A := schubertFirst ab) Positive (centralStable a)

def leftRepresentative (a : ℤ) (ab : DominantPair) (h : Positive) (L : closureLattices ab) :
    Representatives Positive (centralFirst a) (closureLattices ab) :=
  ⟨(scalarLoop a * (h : Loop), L.val), by
    refine ⟨?_, L.property⟩
    change coset Positive (scalarLoop a * (h : Loop)) = coset Positive (scalarLoop a)
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr (by simp [mul_assoc])⟩

def rightRepresentative (a : ℤ) (ab : DominantPair) (g : Loop)
    (hg : g • standardLattice 2 ∈ closureLattices ab) :
    Representatives Positive (schubertFirst ab) (centralSecond a) :=
  ⟨(g, scalarLattice 2 a), ⟨⟨g, hg, rfl⟩, rfl⟩⟩

/-- Both canonical charts for the actual common twisted-product relation.
On the left the change of basis acts on the second modification.
On the right the parameter is the first lattice and the second modification is fixed. -/
structure OrderedCharts (a : ℤ) (ab : DominantPair) where
  left : LeftOrdered a ab ≃ closureLattices ab
  right : RightOrdered a ab ≃ closureLattices ab
  leftChart (h : Positive) (L : closureLattices ab) :
    (left (Quotient.mk _ (leftRepresentative a ab h L))).val = (h : Loop) • L.val
  rightChart (g : Loop) (hg : g • standardLattice 2 ∈ closureLattices ab) :
    (right (Quotient.mk _ (rightRepresentative a ab g hg))).val = g • standardLattice 2
  leftMap (q : LeftOrdered a ab) : leftTerminal a ab q = translate a (left q).val
  rightMap (q : RightOrdered a ab) : rightTerminal a ab q = translate a (right q).val

def OrderedCentralProducts : Prop :=
  ∀ (a : ℤ) (ab : DominantPair), Nonempty (OrderedCharts a ab)

abbrev centralPointUnitMap := @CentralFrameDescentSpecs.centralPointUnitMap
abbrev CentralPointCoefficients := @CentralFrameDescentSpecs.CentralPointCoefficients

def complexBaseMap (X : SchemeOver ℂ) : X ⟶ (testSpec ℂ).obj (Opposite.op complexAlgebra) :=
  Over.homMk X.hom (by
    simp only [algSpec_obj_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id,
      Spec.map_id]
    exact Category.comp_id X.hom)

/-- The algebraic ordered spaces are presented by the non-point Schubert scheme.
The first modifications are respectively the central point and the identity projection.
The common terminal projection is the scalar translation, including on the twisted quotient. -/
structure RealizesOrderedSchemes {J : GL2JetParameters} {a : ℤ} {ab : DominantPair} {N M C : ℕ}
    {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    {hC : OrbitBound (centralPair a) C}
    (A : SchubertJetAction J ab N hN)
    (T : SchubertTranslationData a ab N M hN hM) (W : OrderedCharts a ab)
    (point : occupiedSchubert (centralPair a) C hC ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)) where
  E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N
  onSubspaces (p : SchubertSpace ab N hN) : schubertPointSubspace p = boundedSubspace (E p).val
  left : SchubertSpace ab N hN ≃ LeftOrdered a ab
  right : SchubertSpace ab N hN ≃ RightOrdered a ab
  onRepresentatives :
      ∀ p : SchubertSpace ab N hN,
        (W.left (left p)).val = (E p).val.val ∧
        (W.right (right p)).val = (E p).val.val ∧
        firstProjection Positive (schubertStable ab) (left p) =
          ⟨coset Positive (scalarLoop a), rfl⟩ ∧
        (∀ (k : ℕ) (hk : A.action.cutoff ≤ k) (g : GL (Fin 2) O),
          left ((A.action.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)) =
            Quotient.mk _ (leftRepresentative a ab ⟨positiveGLMap 2 g, ⟨g, rfl⟩⟩
              ⟨(E p).val.val, (E p).property⟩)) ∧
        (∀ (g : Loop) (hg : g • standardLattice 2 = (E p).val.val),
          (firstProjection Positive (centralStable a) (right p)).val = coset Positive g ∧
          right p = Quotient.mk _ (rightRepresentative a ab g
            (hg.symm ▸ (E p).property))) ∧
        schubertPointSubspace (p ≫ complexBaseMap _ ≫ point.inv) =
          latticeSubspace (-(C : ℤ)) (2 * C) (scalarLattice 2 a) ∧
        schubertPointSubspace (p ≫ T.schemeIso.hom) =
          latticeSubspace (-(M : ℤ)) (2 * M) (leftTerminal a ab (left p)) ∧
        schubertPointSubspace (p ≫ T.schemeIso.hom) =
          latticeSubspace (-(M : ℤ)) (2 * M) (rightTerminal a ab (right p))

section RightFrames

variable {ab : DominantPair} {N : ℕ} {hN : OrbitBound ab N}

/-- The frame topology records each Laurent coefficient of each entry of the loop.
Over the bounded Schubert stage the frame graph also carries the analytic topology
of the lattice. -/
structure LoopFrame where
  loop : Loop

instance : TopologicalSpace LoopFrame :=
  TopologicalSpace.induced
    (fun g : LoopFrame ↦ fun i j : Fin 2 ↦ fun n : ℤ ↦ (g.loop.val i j).coeff n) inferInstance

/-- Right representatives are a basis of the first lattice and the fixed scalar
second modification. The first coordinate names the actual first lattice. -/
def RightFrameSpace (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) : TopCat.{0} :=
  TopCat.of {v : SchubertSpace ab N hN × LoopFrame //
    v.2.loop • standardLattice 2 = (E v.1).val.val}

def rightFrameProjection (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) :
    RightFrameSpace E ⟶ SchubertSpace ab N hN :=
  TopCat.ofHom ⟨fun x ↦ x.val.1, continuous_fst.comp continuous_subtype_val⟩

def rightFrameRepresentative (a : ℤ)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) (x : RightFrameSpace E) :
    Representatives Positive (schubertFirst ab) (centralSecond a) :=
  rightRepresentative a ab x.val.2.loop (x.property.symm ▸ (E x.val.1).property)

/-- Each pair of representatives related by a change of basis is tested with
the actual finite jet of that change. The underlying change fixes the first lattice. -/
def RightFrameChanges (J : GL2JetParameters)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) (k : ℕ) : TopCat.{0} :=
  TopCat.of {v : RightFrameSpace E × RightFrameSpace E × (J.toJetSystem.group k).space //
    v.1.val.1 = v.2.1.val.1 ∧
    ∃ h : GL (Fin 2) O, v.2.1.val.2.loop = v.1.val.2.loop * positiveGLMap 2 h ∧
      v.2.2 = reduceGL 2 (k + 1) (Nat.succ_pos k) h}

def rightFrameSource (J : GL2JetParameters)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) (k : ℕ) :
    RightFrameChanges J E k ⟶ RightFrameSpace E :=
  TopCat.ofHom ⟨fun v ↦ v.val.1, continuous_fst.comp continuous_subtype_val⟩

def rightFrameTarget (J : GL2JetParameters)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) (k : ℕ) :
    RightFrameChanges J E k ⟶ RightFrameSpace E :=
  TopCat.ofHom ⟨fun v ↦ v.val.2.1, continuous_fst.comp
    (continuous_snd.comp continuous_subtype_val)⟩

def rightFrameJetPoint (J : GL2JetParameters)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    {C : TopCat.{0}} (x : C) (k : ℕ) :
    RightFrameChanges J E k ⟶ TopCat.of ((J.toJetSystem.group k).space × C) :=
  TopCat.ofHom ⟨fun v ↦ (v.val.2.2, x),
    (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)).prodMk continuous_const⟩

theorem rightFrameChange_twistRel (J : GL2JetParameters) (a : ℤ)
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N) (k : ℕ)
    (v : RightFrameChanges J E k) :
    (twistRel Positive (schubertFirst ab) (centralSecond a)).r
      (rightFrameRepresentative a E (rightFrameSource J E k v))
      (rightFrameRepresentative a E (rightFrameTarget J E k v)) := by
  obtain ⟨_, h, hg, _⟩ := v.property
  let h' : Positive := ⟨positiveGLMap 2 h, ⟨h, rfl⟩⟩
  refine ⟨h', hg, ?_⟩
  exact (centralStable a h'⁻¹ (show scalarLattice 2 a ∈ centralSecond a from rfl)).symm

end RightFrames

section OrderedIncidence

variable {a : ℤ} {ab : DominantPair} {N M C : ℕ}
  {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
  {hC : OrbitBound (centralPair a) C}

/-- With a central first modification, the terminal lattice is arbitrary in the
translated closure. The first and terminal coordinates use their analytic topologies. -/
abbrev LeftIncidence (a : ℤ) (ab : DominantPair) (C M : ℕ)
    (hC : OrbitBound (centralPair a) C) (hM : OrbitBound (shiftPair a ab) M) :=
  SchubertSpace (centralPair a) C hC × SchubertSpace (shiftPair a ab) M hM

/-- The incidence condition on the two lattices for a central second modification.
The topology is the subspace topology from the two occupied analytic stages. -/
def RightIncidence (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (a : ℤ) (M : ℕ) (hM : OrbitBound (shiftPair a ab) M) : Set
      (SchubertSpace ab N hN × SchubertSpace (shiftPair a ab) M hM) :=
  {v | schubertPointSubspace v.2 =
    latticeSubspace (-(M : ℤ)) (2 * M) (translate a (E v.1).val.val)}

/-- For the left order the algebraic incidence is the product of the point
scheme and the translated Schubert scheme. -/
abbrev LeftIncidenceScheme (a : ℤ) (ab : DominantPair) (C M : ℕ)
    (hC : OrbitBound (centralPair a) C) (hM : OrbitBound (shiftPair a ab) M) : SchemeOver ℂ :=
  Limits.prod (occupiedSchubert (centralPair a) C hC) (occupiedSchubert (shiftPair a ab) M hM)

/-- The right incidence scheme is the graph of the algebraic scalar map.
As a pullback it represents ordered pairs with the prescribed terminal lattice. -/
abbrev RightIncidenceScheme (T : SchubertTranslationData a ab N M hN hM) : SchemeOver ℂ :=
  pullback T.schemeIso.hom (𝟙 (occupiedSchubert (shiftPair a ab) M hM))

/-- The graph and product realize the actual ordered lattice spaces. The
geometric projections agree on complex points and the coefficient topology
on right representatives induces the displayed incidence topology. -/
structure OrderedIncidenceComparison {J : GL2JetParameters}
    {A : SchubertJetAction J ab N hN} {T : SchubertTranslationData a ab N M hN hM}
    {W : OrderedCharts a ab}
    {point : occupiedSchubert (centralPair a) C hC ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)}
    (S : RealizesOrderedSchemes A T W point) where
  leftScheme : occupiedSchubert ab N hN ≅ LeftIncidenceScheme a ab C M hC hM
  rightScheme : occupiedSchubert ab N hN ≅ RightIncidenceScheme T
  leftFirst : leftScheme.hom ≫ prod.fst = complexBaseMap _ ≫ point.inv
  leftTerminal : leftScheme.hom ≫ prod.snd = T.schemeIso.hom
  rightFirst : rightScheme.hom ≫ pullback.fst _ _ = 𝟙 _
  rightTerminal : rightScheme.hom ≫ pullback.snd _ _ = T.schemeIso.hom
  leftAnalytic : SchubertSpace ab N hN ≃ₜ LeftIncidence a ab C M hC hM
  rightAnalytic : SchubertSpace ab N hN ≃ₜ RightIncidence S.E a M hM
  leftPoints (p : SchubertSpace ab N hN) :
    leftAnalytic p = (p ≫ leftScheme.hom ≫ prod.fst, p ≫ leftScheme.hom ≫ prod.snd)
  rightPoints (p : SchubertSpace ab N hN) :
    (rightAnalytic p).val =
      (p ≫ rightScheme.hom ≫ pullback.fst _ _, p ≫ rightScheme.hom ≫ pullback.snd _ _)
  rightQuotient : IsQuotientMap (fun r : RightFrameSpace S.E ↦
    rightAnalytic (rightFrameProjection S.E r))
  rightFrameClasses (r r' : RightFrameSpace S.E) :
    rightAnalytic (rightFrameProjection S.E r) = rightAnalytic (rightFrameProjection S.E r') ↔
      (twistRel Positive (schubertFirst ab) (centralSecond a)).r
        (rightFrameRepresentative a S.E r) (rightFrameRepresentative a S.E r')

end OrderedIncidence

section PointTensor

open MonoidalCategory
open ConvolutionConstantDescentSpec (scalars tensorPresheaf coefficientTensor constantSections
  shiftedConstantPullback)

set_option backward.isDefEq.respectTransparency false in
/-- The maps on the sheafified sectionwise tensor act on both coefficients. -/
def coefficientTensorMap {R : TopCat.{0}} {F F' G G' : Sheaves R}
    (f : F ⟶ F') (g : G ⟶ G') : coefficientTensor F G ⟶ coefficientTensor F' G' :=
  (presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}).map
    { app U := f.hom.app U ⊗ₘ g.hom.app U
      naturality U V i := by
        change (F.obj.map i ⊗ₘ G.obj.map i) ≫ (f.hom.app V ⊗ₘ g.hom.app V) =
          (f.hom.app U ⊗ₘ g.hom.app U) ≫ (F'.obj.map i ⊗ₘ G'.obj.map i)
        rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
          f.hom.naturality, g.hom.naturality] }

set_option backward.isDefEq.respectTransparency false in
theorem coefficientTensorMap_id {R : TopCat.{0}} (F G : Sheaves R) :
    coefficientTensorMap (𝟙 F) (𝟙 G) = 𝟙 _ := by
  unfold coefficientTensorMap
  change (presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}).map _ =
    𝟙 ((presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}).obj (tensorPresheaf F G))
  rw [← (presheafToSheaf (Opens.grothendieckTopology R) Coeff.{0}).map_id (tensorPresheaf F G)]
  congr 1
  apply NatTrans.ext
  funext U
  change (𝟙 (F.obj.obj U)) ⊗ₘ (𝟙 (G.obj.obj U)) = 𝟙 _
  rw [tensorHom_id, id_whiskerRight]

set_option backward.isDefEq.respectTransparency false in
theorem coefficientTensorMap_comp {R : TopCat.{0}}
    {F₁ F₂ F₃ G₁ G₂ G₃ : Sheaves R} (f : F₁ ⟶ F₂) (f' : F₂ ⟶ F₃)
    (g : G₁ ⟶ G₂) (g' : G₂ ⟶ G₃) :
    coefficientTensorMap (f ≫ f') (g ≫ g') =
      coefficientTensorMap f g ≫ coefficientTensorMap f' g' := by
  unfold coefficientTensorMap
  rw [← Functor.map_comp]
  congr 1
  apply NatTrans.ext
  funext U
  change (f.hom.app U ≫ f'.hom.app U) ⊗ₘ (g.hom.app U ≫ g'.hom.app U) = _
  exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-- Tensoring with the rational point coefficient in the specified order. -/
def rationalTensor (R : TopCat.{0}) (left : Bool) : Sheaves R ⥤ Sheaves R :=
  if left then
    { obj F := coefficientTensor (rational R) F
      map f := coefficientTensorMap (𝟙 (rational R)) f
      map_id F := coefficientTensorMap_id _ F
      map_comp f g := by rw [← coefficientTensorMap_comp, Category.id_comp] }
  else
    { obj F := coefficientTensor F (rational R)
      map f := coefficientTensorMap f (𝟙 (rational R))
      map_id F := coefficientTensorMap_id F _
      map_comp f g := by rw [← coefficientTensorMap_comp, Category.id_comp] }

/-- A coefficient map acts on the point factor of the tensor. -/
def rationalTensorCoefficient {R : TopCat.{0}} (left : Bool) (v : rational R ⟶ rational R) :
    rationalTensor R left ⟶ rationalTensor R left := by
  cases left
  · exact
      { app F := coefficientTensorMap (𝟙 F) v
        naturality _ _ f := by
          change coefficientTensorMap f (𝟙 _) ≫ coefficientTensorMap (𝟙 _) v =
            coefficientTensorMap (𝟙 _) v ≫ coefficientTensorMap f (𝟙 _)
          simp only [← coefficientTensorMap_comp, Category.comp_id, Category.id_comp] }
  · exact
      { app F := coefficientTensorMap v (𝟙 F)
        naturality _ _ f := by
          change coefficientTensorMap (𝟙 _) f ≫ coefficientTensorMap v (𝟙 _) =
            coefficientTensorMap v (𝟙 _) ≫ coefficientTensorMap (𝟙 _) f
          simp only [← coefficientTensorMap_comp, Category.comp_id, Category.id_comp] }

def scalarActionLeft (V : Coeff.{0}) : scalars ⊗ V ⟶ V :=
  ModuleCat.ofHom (TensorProduct.lift ((LinearMap.id.smulRight (LinearMap.id : V →ₗ[ℚ] V)).comp
    (ULift.moduleEquiv : ULift.{0} ℚ ≃ₗ[ℚ] ℚ).toLinearMap))

def scalarActionRight (V : Coeff.{0}) : V ⊗ scalars ⟶ V :=
  (β_ V scalars).hom ≫ scalarActionLeft V

/-- The isomorphism is scalar multiplication on the generators from the
section presheaf, in the selected tensor order. -/
structure RationalTensorUnit (R : TopCat.{0}) (left : Bool) where
  scalar : rationalTensor R left ≅ 𝟭 (Sheaves R)
  onSections : match left with
    | true => ∀ (F : Sheaves R) (U : (Opens R)ᵒᵖ),
        (constantSections R U ⊗ₘ 𝟙 (F.obj.obj U)) ≫
            ((sheafificationAdjunction (Opens.grothendieckTopology R) Coeff.{0}).unit.app
              (tensorPresheaf (rational R) F)).app U ≫
              (scalar.hom.app F).hom.app U = scalarActionLeft (F.obj.obj U)
    | false => ∀ (F : Sheaves R) (U : (Opens R)ᵒᵖ),
        (𝟙 (F.obj.obj U) ⊗ₘ constantSections R U) ≫
            ((sheafificationAdjunction (Opens.grothendieckTopology R) Coeff.{0}).unit.app
              (tensorPresheaf F (rational R))).app U ≫
              (scalar.hom.app F).hom.app U = scalarActionRight (F.obj.obj U)

namespace RationalTensorUnit

variable {R V : TopCat.{0}} {left : Bool} (μ : RationalTensorUnit R left)

/-- With a degree-zero flat point factor, the ordinary degreewise sheaf tensor
computes the derived tensor. This functor localizes that degreewise tensor. -/
def derived : Derived R ⥤ Derived R :=
  letI : PreservesFiniteLimits (rationalTensor R left) := preservesFiniteLimits_of_natIso μ.scalar.symm
  letI : PreservesFiniteColimits (rationalTensor R left) :=
    preservesFiniteColimits_of_natIso μ.scalar.symm
  letI : (rationalTensor R left).Additive := Functor.additive_of_preserves_binary_products _
  (rationalTensor R left).mapDerivedCategory

def derivedUnit : μ.derived ≅ 𝟭 (Derived R) := by
  letI : PreservesFiniteLimits (rationalTensor R left) := preservesFiniteLimits_of_natIso μ.scalar.symm
  letI : PreservesFiniteColimits (rationalTensor R left) :=
    preservesFiniteColimits_of_natIso μ.scalar.symm
  letI : (rationalTensor R left).Additive := Functor.additive_of_preserves_binary_products _
  change (rationalTensor R left).mapDerivedCategory ≅ 𝟭 (Derived R)
  exact (Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaves R) (.up ℤ))
    ((rationalTensor R left).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((𝟭 (Sheaves R)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    ((rationalTensor R left).mapDerivedCategory) ((𝟭 (Sheaves R)).mapDerivedCategory)
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex μ.scalar _)
      (DerivedCategory.Q (C := Sheaves R)))) ≪≫ Functor.mapDerivedCategoryIdIso (Sheaves R)

def derivedCoefficient (v : rational R ⟶ rational R) : μ.derived ⟶ μ.derived := by
  letI : PreservesFiniteLimits (rationalTensor R left) := preservesFiniteLimits_of_natIso μ.scalar.symm
  letI : PreservesFiniteColimits (rationalTensor R left) :=
    preservesFiniteColimits_of_natIso μ.scalar.symm
  letI : (rationalTensor R left).Additive := Functor.additive_of_preserves_binary_products _
  exact (rationalTensorCoefficient left v).mapDerivedCategory

/-- Inverse image of the degree-zero tensor compares by the scalar maps and
the canonical identification of the pullback of the rational constant. -/
def pullback (ν : RationalTensorUnit V left) (s : V ⟶ R) (F : Derived R) :
    (derivedInverseImage s).obj (μ.derived.obj F) ≅ ν.derived.obj ((derivedInverseImage s).obj F) :=
  (derivedInverseImage s).mapIso (μ.derivedUnit.app F) ≪≫
    (ν.derivedUnit.app ((derivedInverseImage s).obj F)).symm

end RationalTensorUnit

/-- A map of the normalized degree-zero coefficients in the derived model. -/
def derivedPointMap {V : TopCat.{0}} (v : rational V ⟶ rational V) :
    (shiftedConstant V 0).obj ⟶ (shiftedConstant V 0).obj :=
  (shiftFunctor (Derived V) (0 : ℤ)).map ((DerivedCategory.singleFunctor (Sheaves V) 0).map v)

/-- Identifies the actual point pullback, after further restriction to an
overlap, with the degree-zero coefficient used in the tensor model. -/
def pointFrameUnit {V R Y : TopCat.{0}} (s : V ⟶ R) (z : R ⟶ Y) {P : Derived Y}
    (c : P ≅ (shiftedConstant Y 0).obj) :
    (derivedInverseImage s).obj ((derivedInverseImage z).obj P) ⟶ (shiftedConstant V 0).obj :=
  (derivedInverseImage s).map (centralPointUnitMap z c) ≫ (shiftedConstantPullback s 0).hom

/-- The actual equivariance arrow pulled back to the two frame maps. -/
def rebaseFrameArrow {V R U X : TopCat.{0}} (s t : V ⟶ R) (p : R ⟶ X)
    (u : V ⟶ U) {f g : U ⟶ X} (hf : u ≫ f = s ≫ p) (hg : u ≫ g = t ≫ p)
    {F : Derived X} (e : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F) :
    (derivedInverseImage s).obj ((derivedInverseImage p).obj F) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage p).obj F) :=
  (derivedInverseImageComposition s p).inv.app F ≫ pullbackMorphism u hf hg e ≫
    (derivedInverseImageComposition t p).hom.app F

/-- The representative tensor is computed after identifying the actual
pullback of the point IC with the rational sheaf in degree zero. -/
structure RepresentativeTensor {R X Y : TopCat.{0}} (left : Bool) (q p : R ⟶ X) (z : R ⟶ Y)
    {P : Derived Y} (c : P ≅ (shiftedConstant Y 0).obj) (F G : Derived X)
    (d : (derivedInverseImage q).obj G ⟶ (derivedInverseImage p).obj F) where
  pointUnit : IsIso (centralPointUnitMap z c)
  tensor : RationalTensorUnit R left
  comparison : (derivedInverseImage q).obj G ≅ tensor.derived.obj ((derivedInverseImage p).obj F)
  multiplication : comparison.hom ≫ tensor.derivedUnit.hom.app ((derivedInverseImage p).obj F) = d

/-- The same comparison descends through the tensor of the actual two frame
arrows. The lifted degree-zero map comes from the point arrow by its given
normalization, while the other arrow acts on the arbitrary derived factor. -/
def TensorFrameComparison {V R X Y : TopCat.{0}} {left : Bool} {q p : R ⟶ X} {z : R ⟶ Y}
    {P : Derived Y} {c : P ≅ (shiftedConstant Y 0).obj} {F G : Derived X}
    {d : (derivedInverseImage q).obj G ⟶ (derivedInverseImage p).obj F}
    (D : RepresentativeTensor left q p z c F G d) (s t : V ⟶ R)
    (b : (derivedInverseImage s).obj ((derivedInverseImage q).obj G) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage q).obj G))
    (v : (derivedInverseImage s).obj ((derivedInverseImage z).obj P) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage z).obj P))
    (w : (derivedInverseImage s).obj ((derivedInverseImage p).obj F) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage p).obj F)) : Prop :=
  ∃ (ν : RationalTensorUnit V left) (v₀ : rational V ⟶ rational V),
    pointFrameUnit s z c ≫ derivedPointMap v₀ = v ≫ pointFrameUnit t z c ∧
    b ≫ (derivedInverseImage t).map D.comparison.hom =
      (derivedInverseImage s).map D.comparison.hom ≫
        (D.tensor.pullback ν s ((derivedInverseImage p).obj F)).hom ≫
        ν.derived.map w ≫
        (ν.derivedCoefficient v₀).app ((derivedInverseImage t).obj ((derivedInverseImage p).obj F)) ≫
        (D.tensor.pullback ν t ((derivedInverseImage p).obj F)).inv

/-- A frame change after identifying the point coefficient with the tensor unit. -/
def NormalizedFrameComparison {V R X Y : TopCat.{0}} {q p : R ⟶ X} {z : R ⟶ Y}
    {P : Derived Y} (c : P ≅ (shiftedConstant Y 0).obj) {F G : Derived X}
    (d : (derivedInverseImage q).obj G ⟶ (derivedInverseImage p).obj F) (s t : V ⟶ R)
    (b : (derivedInverseImage s).obj ((derivedInverseImage q).obj G) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage q).obj G))
    (v : (derivedInverseImage s).obj ((derivedInverseImage z).obj P) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage z).obj P))
    (w : (derivedInverseImage s).obj ((derivedInverseImage p).obj F) ⟶
      (derivedInverseImage t).obj ((derivedInverseImage p).obj F)) : Prop :=
  v ≫ pointFrameUnit t z c = pointFrameUnit s z c ∧
    b ≫ (derivedInverseImage t).map d = (derivedInverseImage s).map d ≫ w

/-- Scalar multiplication carries the actual representative tensor transitions
to the normalized arrows. The same comparison works after any further pullback. -/
def TensorFrameNaturality {R X Y : TopCat.{0}} {left : Bool} {q p : R ⟶ X} {z : R ⟶ Y}
    {P : Derived Y} {c : P ≅ (shiftedConstant Y 0).obj} {F G : Derived X}
    {d : (derivedInverseImage q).obj G ⟶ (derivedInverseImage p).obj F}
    (D : RepresentativeTensor left q p z c F G d) : Prop :=
  ∀ {V : TopCat.{0}} (s t : V ⟶ R) (b v w),
    NormalizedFrameComparison c d s t b v w → TensorFrameComparison D s t b v w

/-- The multiplication equation of the acted-on coefficient, written with
the canonical comparisons for the three pullbacks. -/
def FrameMultiplicationEquation {V R X : TopCat.{0}} (s t u : V ⟶ R) {q p : R ⟶ X}
    (hq : s ≫ q = t ≫ q) (hf : s ≫ p = u ≫ q) (hp : u ≫ p = t ≫ p)
    {F : Derived X} (e : (derivedInverseImage q).obj F ⟶ (derivedInverseImage p).obj F) : Prop :=
  pullbackMorphism t rfl rfl e = pullbackMorphism s hq hf e ≫ pullbackMorphism u rfl hp e

/-- For a fixed first modification the multiplication equation induces the
actual tensor comparison for the frame change `(g,hL) ∼ (gh,L)`. -/
def TensorFrameMultiplication {R X Y : TopCat.{0}} {q p : R ⟶ X} {z : R ⟶ Y}
    {P : Derived Y} {c : P ≅ (shiftedConstant Y 0).obj} {F : Derived X}
    {e : (derivedInverseImage q).obj F ⟶ (derivedInverseImage p).obj F}
    (D : RepresentativeTensor true q p z c F F e) : Prop :=
  ∀ {V : TopCat.{0}} (s t u : V ⟶ R) (hq : s ≫ q = t ≫ q)
    (hf : s ≫ p = u ≫ q) (hp : u ≫ p = t ≫ p) (hz : s ≫ z = t ≫ z),
    FrameMultiplicationEquation s t u hq hf hp e →
      TensorFrameComparison D s t ((squareValue hq).hom.app F) ((squareValue hz).hom.app P)
        (rebaseFrameArrow s t p u hf.symm hp e)

end PointTensor

/-- The pullback of the point coefficient action on an overlap. -/
def PointCoefficientOverlap {J : GL2JetParameters} {a : ℤ} {C : ℕ}
    {hC : OrbitBound (centralPair a) C} (B : SchubertJetAction J (centralPair a) C hC)
    {P : Derived (SchubertSpace (centralPair a) C hC)} (η : B.action.Equivariance P)
    (c : P ≅ (shiftedConstant (SchubertSpace (centralPair a) C hC) 0).obj)
    (k : ℕ) (hk : B.action.cutoff ≤ k) {R V : TopCat.{0}}
    (x : SchubertSpace (centralPair a) C hC) (s t : V ⟶ R)
    (u : V ⟶ AnalyticAction.Parameters (J.toJetSystem.group k) (SchubertSpace (centralPair a) C hC)) :
    Prop :=
  let Y := SchubertSpace (centralPair a) C hC
  let z : R ⟶ Y := TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩
  let π := AnalyticAction.projection (J.toJetSystem.group k) Y
  let act := (B.action.action k hk).act
  u ≫ act = s ≫ z ∧ u ≫ π = t ≫ z ∧
    (derivedInverseImage u).map ((η.datum k hk).iso.hom ≫ centralPointUnitMap π c) =
      (derivedInverseImage u).map (centralPointUnitMap act c)

/-- Pulling back the coefficient comparison along either frame gives the same
arrow under the inverse-image comparison over the first lattice. -/
def FrameProjectionOverlap {X R V : TopCat.{0}} (p : R ⟶ X) (s t : V ⟶ R)
    (F G : Derived X) (d : (derivedInverseImage p).obj G ≅ (derivedInverseImage p).obj F) : Prop :=
  ∃ h : s ≫ p = t ≫ p,
    (squareValue h).hom.app G ≫ (derivedInverseImage t).map d.hom =
      (derivedInverseImage s).map d.hom ≫ (squareValue h).hom.app F

/-- Compatibility on the actual right frame overlap, where the quotient and
the non-point factor both read the first lattice. -/
def RightFrameOverlap {J : GL2JetParameters} {a : ℤ} {ab : DominantPair} {N C : ℕ}
    {hN : OrbitBound ab N} {hC : OrbitBound (centralPair a) C}
    (E : SchubertSpace ab N hN ≃ₜ schubertLatticeSet ab N)
    (B : SchubertJetAction J (centralPair a) C hC)
    (x : SchubertSpace (centralPair a) C hC)
    {P : Derived (SchubertSpace (centralPair a) C hC)} (η : B.action.Equivariance P)
    (c : P ≅ (shiftedConstant (SchubertSpace (centralPair a) C hC) 0).obj)
    (F G : Derived (SchubertSpace ab N hN))
    (d : (derivedInverseImage (rightFrameProjection E)).obj G ≅
      (derivedInverseImage (rightFrameProjection E)).obj F) : Prop :=
  ∀ (k : ℕ) (hk : B.action.cutoff ≤ k),
    let s := rightFrameSource J E k
    let t := rightFrameTarget J E k
    let u := rightFrameJetPoint J E x k
    FrameProjectionOverlap (rightFrameProjection E) s t F G d ∧
      PointCoefficientOverlap B η c k hk x s t u

/-- In the degree-zero point case the representative exterior product is the
pullback of the other IC, using the displayed canonical identification with the
tensor unit. On the left the quotient in finite frame coordinates is the action.
On the right the quotient is induced from the actual frame graph with its
right-basis-change relation. -/
def CentralDescent {J : GL2JetParameters} {a : ℤ} {ab : DominantPair} {N M C : ℕ}
    {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    {hC : OrbitBound (centralPair a) C}
    {A : SchubertJetAction J ab N hN} {T : SchubertTranslationData a ab N M hN hM}
    {W : OrderedCharts a ab}
    {point : occupiedSchubert (centralPair a) C hC ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)}
    (S : RealizesOrderedSchemes A T W point)
    (B : SchubertJetAction J (centralPair a) C hC)
    {P : Derived (SchubertSpace (centralPair a) C hC)} (η : B.action.Equivariance P)
    (c : P ≅ (shiftedConstant (SchubertSpace (centralPair a) C hC) 0).obj)
    (F G : A.action.Object) (i : G ≅ F) (left : Bool) : Prop :=
  let X := SchubertSpace ab N hN
  let Y := SchubertSpace (centralPair a) C hC
  let x : Y := 𝟙 _ ≫ point.inv
  if left then
    ∀ (k : ℕ) (hk : A.action.cutoff ≤ k),
      let H := J.toJetSystem.group k
      let Aₖ := A.action.action k hk
      let R := AnalyticAction.Parameters H X
      let p : R ⟶ X := AnalyticAction.projection H X
      let q : R ⟶ X := Aₖ.act
      let z : R ⟶ Y := TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩
      Function.Surjective q ∧
      (∀ (g : GL (Fin 2) O) (L : X),
        S.left (q (reduceGL 2 (k + 1) (Nat.succ_pos k) g, L)) =
          Quotient.mk _ (leftRepresentative a ab ⟨positiveGLMap 2 g, ⟨g, rfl⟩⟩
            ⟨(S.E L).val.val, (S.E L).property⟩)) ∧
      IsIso (centralPointUnitMap z c) ∧
      ∃ d : (derivedInverseImage q).obj G.obj ≅ (derivedInverseImage p).obj F.obj,
        d.hom = (derivedInverseImage q).map i.hom.hom ≫ (F.equivariance.datum k hk).iso.hom ∧
        -- The two representatives of `(g h, L) ∼ (g, h L)` in finite frame
        -- coordinates. The first coefficient is constant and the second uses
        -- the action-to-projection arrow of the Schubert IC.
        let s := AnalyticAction.firstAfterSecond Aₖ
        let t := AnalyticAction.multiplyParameters H X
        let u := AnalyticAction.secondParameter H X
        let b := (derivedInverseImage q).map i.inv.hom ≫ d.hom
        pullbackMorphism t rfl rfl b =
          pullbackMorphism s (AnalyticAction.multiply_act Aₖ) (AnalyticAction.first_projection Aₖ) b ≫
          pullbackMorphism u rfl AnalyticAction.multiply_projection (F.equivariance.datum k hk).iso.hom
  else
    let R := RightFrameSpace S.E
    let p : R ⟶ X := rightFrameProjection S.E
    let z : R ⟶ Y := TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩
    Function.Surjective p ∧
    (∀ r, S.right (p r) = Quotient.mk _ (rightFrameRepresentative a S.E r)) ∧
    IsIso (centralPointUnitMap z c) ∧
    ∃ d : (derivedInverseImage p).obj G.obj ≅ (derivedInverseImage p).obj F.obj,
      d.hom = (derivedInverseImage p).map i.hom.hom ∧
      RightFrameOverlap S.E B x η c F.obj G.obj d

/-- The coefficient descent diagrams at a fixed jet level of the non-point factor. -/
def LeftTensorDescentAtLevel {H : AnalyticGroup.{0}} {X Y : TopCat.{0}}
    (A : AnalyticAction H X) (x : Y) {F : Derived X} (ε : A.Equivariance F)
    {P : Derived Y} (c : P ≅ (shiftedConstant Y 0).obj)
    {pointLevel : Prop} (B : pointLevel → AnalyticAction H Y)
    (η : ∀ h, (B h).Equivariance P) : Prop :=
  let R := AnalyticAction.Parameters H X
  let p := AnalyticAction.projection H X
  let q := A.act
  let z : R ⟶ Y := TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩
  let s := AnalyticAction.firstAfterSecond A
  let t := AnalyticAction.multiplyParameters H X
  let u := AnalyticAction.secondParameter H X
  IsQuotientMap (fun r : R ↦ q r) ∧
  ∃ D : RepresentativeTensor true q p z c F F ε.iso.hom,
    TensorFrameNaturality D ∧
    TensorFrameMultiplication D ∧
    s ≫ z = t ≫ z ∧
    FrameMultiplicationEquation s t u (AnalyticAction.multiply_act A)
      (AnalyticAction.first_projection A) AnalyticAction.multiply_projection ε.iso.hom ∧
    ∀ (hkC : pointLevel),
      let u₀ : AnalyticAction.TwoParameters H X ⟶ AnalyticAction.Parameters H Y :=
        TopCat.ofHom ⟨fun v ↦ (v.1, x), continuous_fst.prodMk continuous_const⟩
      let act := (B hkC).act
      let π := AnalyticAction.projection H Y
      ∃ (ha : u₀ ≫ act = t ≫ z) (hπ : u₀ ≫ π = u ≫ z),
        NormalizedFrameComparison c ε.iso.hom t u
          (rebaseFrameArrow t u q s (AnalyticAction.multiply_act A)
            (AnalyticAction.first_projection A) ε.iso.hom)
          (rebaseFrameArrow t u z u₀ ha hπ (η hkC).iso.hom)
          ((squareValue (AnalyticAction.multiply_projection (H := H) (X := X)).symm).hom.app F)

/-- Tensor descent over the same ordered spaces as `CentralDescent`. The left
frame change acts on the non-point factor and the right frame change acts on
the point factor. Each uses the actual coefficient arrow at the indicated jet. -/
def CentralTensorDescent {J : GL2JetParameters} {a : ℤ} {ab : DominantPair} {N M C : ℕ}
    {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    {hC : OrbitBound (centralPair a) C}
    {A : SchubertJetAction J ab N hN} {T : SchubertTranslationData a ab N M hN hM}
    {W : OrderedCharts a ab}
    {point : occupiedSchubert (centralPair a) C hC ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)}
    (S : RealizesOrderedSchemes A T W point)
    (B : SchubertJetAction J (centralPair a) C hC)
    {P : Derived (SchubertSpace (centralPair a) C hC)} (η : B.action.Equivariance P)
    (c : P ≅ (shiftedConstant (SchubertSpace (centralPair a) C hC) 0).obj)
    (F : A.action.Object) (left : Bool) : Prop :=
  let X := SchubertSpace ab N hN
  let Y := SchubertSpace (centralPair a) C hC
  let x : Y := 𝟙 _ ≫ point.inv
  if left then
    ∀ (k : ℕ) (hk : A.action.cutoff ≤ k),
      LeftTensorDescentAtLevel (A.action.action k hk) x (F.equivariance.datum k hk) c
        (B.action.action k) (η.datum k)
  else
    let R := RightFrameSpace S.E
    let p := rightFrameProjection S.E
    let z : R ⟶ Y := TopCat.ofHom ⟨fun _ ↦ x, continuous_const⟩
    ∃ D : RepresentativeTensor false p p z c F.obj F.obj (𝟙 _),
      (∀ (k : ℕ) (hk : B.action.cutoff ≤ k),
        let s := rightFrameSource J S.E k
        let t := rightFrameTarget J S.E k
        let u := rightFrameJetPoint J S.E x k
        let act := (B.action.action k hk).act
        let π := AnalyticAction.projection (J.toJetSystem.group k) Y
        ∃ (hp : s ≫ p = t ≫ p) (ha : u ≫ act = s ≫ z) (hπ : u ≫ π = t ≫ z),
          TensorFrameComparison D s t ((squareValue hp).hom.app F.obj)
            (rebaseFrameArrow s t z u ha hπ (η.datum k hk).iso.hom)
            ((squareValue hp).hom.app F.obj)) ∧
      -- Left multiplication acts on the first lattice and fixes the second
      -- modification. The right projection reads this same first lattice.
      ∀ (k : ℕ) (hk : A.action.cutoff ≤ k) {V : TopCat.{0}} (s t : V ⟶ R)
        (u : V ⟶ AnalyticAction.Parameters (J.toJetSystem.group k) X)
        (ha : u ≫ (A.action.action k hk).act = s ≫ p)
        (hπ : u ≫ AnalyticAction.projection (J.toJetSystem.group k) X = t ≫ p),
        TensorFrameComparison D s t
          (rebaseFrameArrow s t p u ha hπ (F.equivariance.datum k hk).iso.hom)
          ((squareValue (show s ≫ z = t ≫ z from TopCat.ext (fun _ ↦ rfl))).hom.app P)
          (rebaseFrameArrow s t p u ha hπ (F.equivariance.datum k hk).iso.hom)

abbrev ClosedAdjunctions :=
  ∀ {X : TopCat.{0}} {Z : Set X} (hZ : IsClosed Z),
    boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ

/-- The terminal direct image followed by extension to a closed ambient stage
uses the equivariance of the actual extension by zero. -/
def ClosedSupportTransport {J : JetSystem.{0}} {X Y : TopCat.{0}}
    (adj : DerivedAdjunctions) (cl : ClosedAdjunctions)
    (A₁ : JetAction J X) (A₂ : JetAction J Y) (f : X ⟶ Y)
    (F : BoundedBelow X) (α : A₁.Equivariance F.obj)
    (G : BoundedBelow Y) (β : A₂.Equivariance G.obj) : Prop :=
  ∀ {W : TopCat.{0}} {Z : Set W} (hZ : IsClosed Z)
    (B : JetAction J W) (A_Z : JetAction J (TopCat.of Z))
    (v : Y ≅ TopCat.of Z)
    (hv : JetMapsCommute A₂ A_Z v.hom)
    (hi : JetMapsCommute A_Z B (closedInclusion Z)),
    let j := closedInclusion Z
    ∃ (G_Z : BoundedBelow (TopCat.of Z)) (β_Z : A_Z.Equivariance G_Z.obj)
      (c : derivedDirectImage j ≅ closedExtensionPlus hZ),
      (∀ K : BoundedBelow (TopCat.of Z),
        (boundedBelowInverseImage j).map (c.hom.app K) ≫ (cl hZ).counit.app K =
          (adj j).counit.app K) ∧
      EquivariantDirectImageComparison adj A₂ A_Z v.hom hv G β G_Z β_Z ∧
      ∃ (β_W : (above B A_Z.cutoff).Equivariance ((closedExtensionPlus hZ).obj G_Z).obj)
        (hm : JetMapsCommute A₁ (above B A_Z.cutoff) (f ≫ v.hom ≫ j)),
        ClosedExtensionArrow adj hZ (cl hZ) A_Z B hi G_Z β_Z β_W ∧
        EquivariantDirectImageComparison adj A₁ (above B A_Z.cutoff)
          (f ≫ v.hom ≫ j) hm F α ((closedExtensionPlus hZ).obj G_Z) β_W

/-- The normalized IC transport and the comparisons after scalar multiplication
on the frames, at every common finite jet level and in every occupied window. -/
def CentralConvolutionTransport : Prop :=
  ∃ (J : GL2JetParameters) (adj : DerivedAdjunctions) (cl : ClosedAdjunctions),
    ClosedExtensionCompatibility J.toJetSystem ∧
    ∃ (A : ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N), SchubertJetAction J ab N hN),
      (∀ ab N hN,
        ∃ (P : Stratification (SchubertSpace ab N hN))
          (D : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2))),
          IsNormalizedOrbitIC ab N hN (𝟙 _) (difference ab / 2) P D) ∧
      ∃ (ε : ∀ (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
            (P : Stratification (SchubertSpace ab N hN))
            (D : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2))),
          IsNormalizedOrbitIC ab N hN (𝟙 _) (difference ab / 2) P D →
            (A ab N hN).action.Equivariance (complex D).obj),
        (∀ ab N hN P D hD, NormalizedICDatum adj (A ab N hN).action D (ε ab N hN P D hD)) ∧
        ∀ (a : ℤ) (ab : DominantPair) (N M C : ℕ)
          (hN : OrbitBound ab N) (hM : OrbitBound (shiftPair a ab) M)
          (hC : OrbitBound (centralPair a) C)
          P D hD Q E hE,
          let A₁ := (A ab N hN).action
          let A₂ := (A (shiftPair a ab) M hM).action
          let F := complex D
          let G := complex E
          let α := ε ab N hN P D hD
          let β := ε (shiftPair a ab) M hM Q E hE
          ∃ (T : SchubertTranslationData a ab N M hN hM) (W : OrderedCharts a ab)
            (point : occupiedSchubert (centralPair a) C hC ≅
              (testSpec ℂ).obj (Opposite.op complexAlgebra))
            (h : JetMapsCommute A₁ A₂ T.analyticIso.hom),
            ∃ S : RealizesOrderedSchemes (A ab N hN) T W point,
            BoundedSchubertSupport (A (shiftPair a ab) M hM) ∧
            (∃ c : (boundedBelowInverseImage T.analyticIso.hom).obj G ≅ F,
              PullbackIntertwines h α β c) ∧
            ∀ P₀ Dp (hDp : IsNormalizedOrbitIC (centralPair a) C hC (𝟙 _)
                  (difference (centralPair a) / 2) P₀ Dp),
              let B := A (centralPair a) C hC
              let η := ε (centralPair a) C hC P₀ Dp hDp
              ∃ c : (complex Dp).obj ≅ (shiftedConstant (SchubertSpace (centralPair a) C hC) 0).obj,
                CentralPointCoefficients B η c ∧
                ∀ left : Bool,
                  let K : A₁.Object := ⟨F.obj, α⟩
                  CentralDescent S B η c K K (Iso.refl K) left ∧
                  EquivariantDirectImageComparison adj A₁ A₂ T.analyticIso.hom h F α G β ∧
                  ClosedSupportTransport adj cl A₁ A₂ T.analyticIso.hom F α G β

/-- The direct image in `CentralConvolutionTransport` is the ordered
convolution. For its same scheme and frame charts and its same coefficient
objects, the incidence models and the tensor before multiplication agree
with the twisted product and its two normalized frame actions. -/
def CentralConvolution : Prop :=
  CentralConvolutionTransport ∧
  ∀ {J : GL2JetParameters} {a : ℤ} {ab : DominantPair} {N M C : ℕ}
    {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
    {hC : OrbitBound (centralPair a) C}
    {A : SchubertJetAction J ab N hN} {T : SchubertTranslationData a ab N M hN hM}
    {W : OrderedCharts a ab}
    {point : occupiedSchubert (centralPair a) C hC ≅
      (testSpec ℂ).obj (Opposite.op complexAlgebra)}
    (S : RealizesOrderedSchemes A T W point),
    Nonempty (OrderedIncidenceComparison S) ∧
      ∀ (B : SchubertJetAction J (centralPair a) C hC)
        {P : Derived (SchubertSpace (centralPair a) C hC)} (η : B.action.Equivariance P)
        (c : P ≅ (shiftedConstant (SchubertSpace (centralPair a) C hC) 0).obj),
        CentralPointCoefficients B η c →
        ∀ (F : A.action.Object) (left : Bool),
          CentralTensorDescent S B η c F left

end RepTheorySurvey.Geometric.CentralLatticeTranslationSpecs
