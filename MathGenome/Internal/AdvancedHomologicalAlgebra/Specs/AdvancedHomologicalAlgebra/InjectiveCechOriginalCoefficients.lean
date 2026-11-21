import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Čech cochains on the original site and with the original coefficients. -/

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.Cech
open AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.SheafUniverseTransport

universe u r m v a

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 3500

namespace AdvancedHomologicalAlgebra.CechOriginal
variable {X : TopCat.{u}} {U : Opens X} {I : Type v}

/-- The same indexing on the homeomorphic lifted space. -/
def liftCover (c : Cover U I) :
    Cover ((opensEquiv.{max m u r} X).symm U) I where
  opens i := (opensEquiv.{max m u r} X).symm (c.opens i)
  le i := (opensEquiv.{max m u r} X).symm.monotone (c.le i)
  covers := by
    rw [← OrderIso.map_iSup, c.covers]

theorem liftCover_tuple (c : Cover U I) {p : ℕ} (t : Fin (p + 1) → I) :
    opensEquiv.{max m u r} X (tupleOpen (liftCover.{u,m,r,v} c) t) = tupleOpen c t := by
  induction p with
  | zero => exact (opensEquiv _).apply_symm_apply _
  | succ p ih =>
    rw [tupleOpen, tupleOpen, OrderIso.map_inf, ih]
    exact congrArg (fun W ↦ W ⊓ tupleOpen c (t ∘ Fin.succ))
      ((opensEquiv _).apply_symm_apply _)

variable (R : X.Sheaf RingCat.{r}) (M : AmbientSheaves.{m} R)

/-- Section identification along a specified equality of opens. -/
def sectionAt (W : Opens (liftedSpace.{max m u r} X)) (V : Opens X)
    (h : opensEquiv.{max m u r} X W = V) :
    M.val.obj (op V) ≃+ ((transport.{m} R).obj M).val.obj (op W) :=
  h ▸ sectionEquiv.{m} R M W

/-- The product comparison uses the same tuple and the same coefficient section. -/
def cochainComparison (c : Cover U I) (p : ℕ) :
    Cochains R M.val c p ≃+
      Cochains (liftedRing.{m} R) ((transport.{m} R).obj M).val
        (liftCover.{u,m,r,v} c) p :=
  AddEquiv.piCongrRight (fun t ↦ sectionAt.{u,r,m} R M _ _ (liftCover_tuple.{u,r,m,v} c t))

end AdvancedHomologicalAlgebra.CechOriginal

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

/-- Transport compares the prescribed augmentation and alternating restrictions. -/
def cochainComparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (M : AmbientSheaves.{m} R)
    {U : Opens X} {I : Type v} (c : Cover U I),
    let N := (transport.{m} R).obj M
    let d := liftCover.{u,m,r,v} c
    (∀ s, cochainComparison.{u,r,m,v} R M c 0 (augmentation R M.val c s) =
      augmentation (liftedRing.{m} R) N.val d
        (sectionAt.{u,r,m} R M _ U ((opensEquiv.{max m u r} X).apply_symm_apply U) s)) ∧
    (∀ p s, cochainComparison.{u,r,m,v} R M c (p + 1) (differential R M.val c p s) =
      differential (liftedRing.{m} R) N.val d p (cochainComparison.{u,r,m,v} R M c p s))

/-- Every injective in its original ambient category is acyclic for the full
ordered-tuple Čech cochains, including exactness at the augmentation. -/
def injectiveExactness : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X}
    {I : Type v} (c : Cover U I) (M : AmbientSheaves.{m} R), Injective M →
    Function.Injective (augmentation R M.val c) ∧
      (∀ z, differential R M.val c 0 z = 0 → ∃ s, augmentation R M.val c s = z) ∧
      ∀ p z, differential R M.val c (p + 1) z = 0 → ∃ y, differential R M.val c p y = z

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace AdvancedHomologicalAlgebra.CechOriginal

open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport (OpenTransportData)

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})

/-- Normalized extensions by zero supplied by the transport of the open adjunction. -/
abbrev OpenUnits :=
  ∀ W : Opens (liftedSpace.{max m u r} X), OpenTransportData.{m} R W

variable (D : OpenUnits.{u,r,m} R)

abbrev extendedUnit (V : Opens X) : AmbientSheaves.{m} R :=
  originalExtendedUnitOf.{m} R _ (D ((opensEquiv.{max m u r} X).symm V)).overExtension

def unitGenerator (V : Opens X) : (extendedUnit.{u,r,m} R D V).val.obj (op V) :=
  (opensEquiv.{max m u r} X).apply_symm_apply V ▸
    originalExtendedGeneratorOf.{m} R _ (D ((opensEquiv.{max m u r} X).symm V)).overExtension
      (D ((opensEquiv.{max m u r} X).symm V)).overAdjunction

def unitEvaluation (V : Opens X) (M : AmbientSheaves.{m} R) :
    (extendedUnit.{u,r,m} R D V ⟶ M) ≃+ M.val.obj (op V) :=
  (opensEquiv.{max m u r} X).apply_symm_apply V ▸
    (D ((opensEquiv.{max m u r} X).symm V)).sectionRepresentation M

def unitMap {V W : Opens X} (h : V ≤ W) : extendedUnit.{u,r,m} R D V ⟶ extendedUnit.{u,r,m} R D W :=
  (unitEvaluation.{u,r,m} R D V _).symm ((extendedUnit.{u,r,m} R D W).val.map (homOfLE h).op (unitGenerator.{u,r,m} R D W))

def unitRightMul (V : Opens X) (c : sectionRing R V) : extendedUnit.{u,r,m} R D V ⟶ extendedUnit.{u,r,m} R D V :=
  (unitEvaluation.{u,r,m} R D V _).symm (c • unitGenerator.{u,r,m} R D V)

-- The topology is transported to a small equivalent site in the carrier universe.
private def smallOpenSite (X : TopCat.{u}) [UnivLE.{u,a}] :
    Σ C : Type a, Σ _ : SmallCategory C, Opens X ≌ C := by
  let C := ShrinkHoms.{u} (Opens X)
  letI : Small.{a} C := UnivLE.small (Opens X)
  let e := ShrinkHoms.equivalence.{a,u,u} (Opens X)
  let f := CategoryTheory.Shrink.equivalence.{a,a,u} C
  exact ⟨Shrink.{a} C, inferInstance, e.trans f⟩

scoped instance originalSheafification [UnivLE.{u,a}] :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{a} := by
  obtain ⟨C, hC, e⟩ := smallOpenSite.{u,a} X
  letI : SmallCategory C := hC
  let K := e.inverse.inducedTopology (Opens.grothendieckTopology X)
  let h : HasSheafify K AddCommGrpCat.{a} := inferInstance
  exact e.hasSheafify (Opens.grothendieckTopology X) K AddCommGrpCat.{a}

scoped instance originalSheafificationLocalEquivalences [UnivLE.{u,a}] :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{a} := by
  obtain ⟨C, hC, e⟩ := smallOpenSite.{u,a} X
  letI : SmallCategory C := hC
  let K := e.inverse.inducedTopology (Opens.grothendieckTopology X)
  let h : K.WEqualsLocallyBijective AddCommGrpCat.{a} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.transport _ K e.inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

variable {U : Opens X} {I : Type v} (c : Cover U I)
variable (E : OpenUnits.{u,r,max m v} R)

/-- The family indexed by the actual full tuples on the original site. -/
abbrev tupleUnits (p : ℕ) : (Fin (p + 1) → I) → AmbientSheaves.{max m v} R :=
  fun t ↦ extendedUnit.{u,r,max m v} R E (tupleOpen c t)

/-- The sheaf coproduct in the joint universe. -/
abbrev term (p : ℕ) : AmbientSheaves.{max m v} R := ∐ tupleUnits.{u,r,m,v} R c E p

/-- Each summand map is the extension-by-zero inclusion to the corresponding deleted tuple. -/
def face {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) : term.{u,r,m,v} R c E q ⟶ term.{u,r,m,v} R c E p :=
  Sigma.desc fun t ↦ unitMap.{u,r,max m v} R E (tupleOpen_reindex_le c f t) ≫
    Sigma.ι (tupleUnits.{u,r,m,v} R c E p) (t ∘ f)

def boundary (p : ℕ) : term.{u,r,m,v} R c E (p + 1) ⟶ term.{u,r,m,v} R c E p :=
  ∑ a : Fin (p + 2), (-1 : ℤ) ^ a.val • face.{u,r,m,v} R c E a.succAbove

def chainAugmentation : term.{u,r,m,v} R c E 0 ⟶ extendedUnit.{u,r,max m v} R E U :=
  Sigma.desc fun t ↦ unitMap.{u,r,max m v} R E (tupleOpen_le c t)

def termRightMul (p : ℕ) (a : sectionRing R U) : term.{u,r,m,v} R c E p ⟶ term.{u,r,m,v} R c E p :=
  Sigma.desc fun t ↦ unitRightMul.{u,r,max m v} R E (tupleOpen c t)
    (R.obj.map (homOfLE (tupleOpen_le c t)).op a) ≫ Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t

/-- Evaluation on the coproduct inclusions and the normalized open-unit generators. -/
def homCochains (M : AmbientSheaves.{max m v} R) (p : ℕ) :
    (term.{u,r,m,v} R c E p ⟶ M) ≃+ Cochains R M.val c p where
  toFun f t := unitEvaluation.{u,r,max m v} R E (tupleOpen c t) M (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t ≫ f)
  invFun s := Sigma.desc fun t ↦ (unitEvaluation.{u,r,max m v} R E (tupleOpen c t) M).symm (s t)
  left_inv f := by
    apply Sigma.hom_ext
    intro t
    simp only [Sigma.ι_comp_desc, AddEquiv.symm_apply_apply]
  right_inv s := by
    funext t
    simp only [Sigma.ι_comp_desc, AddEquiv.apply_symm_apply]
  map_add' f g := by
    funext t
    simp only [Preadditive.comp_add, map_add, Pi.add_apply]

/-- The structure sheaf regarded as its own module, with its carrier in the
ambient category over the original site and original ring. -/
abbrev ambientUnit : AmbientSheaves.{m} R :=
  (liftSheafCoefficients.{max m u r,u,r,r} R).obj (SheafOfModules.unit R)

end AdvancedHomologicalAlgebra.CechOriginal

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

/-- On the original site the Hom identification is given by the canonical
generators and intertwines the full Čech augmentation, differential and scalars. -/
def originalHomType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X}
    {I : Type v} (c : Cover U I) (E : OpenUnits.{u,r,max m v} R)
    (M : AmbientSheaves.{max m v} R),
    (∀ (f : extendedUnit.{u,r,max m v} R E U ⟶ M),
      homCochains.{u,r,m,v} R c E M 0 (chainAugmentation.{u,r,m,v} R c E ≫ f) =
        augmentation R M.val c (unitEvaluation.{u,r,max m v} R E U M f)) ∧
    (∀ p (f : term.{u,r,m,v} R c E p ⟶ M),
      homCochains.{u,r,m,v} R c E M (p + 1) (boundary.{u,r,m,v} R c E p ≫ f) =
        differential R M.val c p (homCochains.{u,r,m,v} R c E M p f)) ∧
    ∀ p,
      (∀ (f : term.{u,r,m,v} R c E p ⟶ M) t,
        homCochains.{u,r,m,v} R c E M p f t =
          (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t ≫ f).val.app (op (tupleOpen c t))
            (unitGenerator.{u,r,max m v} R E (tupleOpen c t))) ∧
      (∀ (N : AmbientSheaves.{max m v} R) (g : M ⟶ N)
          (f : term.{u,r,m,v} R c E p ⟶ M) t,
        homCochains.{u,r,m,v} R c E N p (f ≫ g) t =
          g.val.app (op (tupleOpen c t)) (homCochains.{u,r,m,v} R c E M p f t)) ∧
      ∃ inst : Module (sectionRing R U) (term.{u,r,m,v} R c E p ⟶ M),
        letI := inst
        (∀ (a : sectionRing R U) (f : term.{u,r,m,v} R c E p ⟶ M),
          a • f = termRightMul.{u,r,m,v} R c E p a ≫ f) ∧
        ∃ L : (term.{u,r,m,v} R c E p ⟶ M) ≃ₗ[sectionRing R U] Cochains R M.val c p,
          ∀ f, L f = homCochains.{u,r,m,v} R c E M p f

/-- The chain on the original site has exactly the stated terms and maps. -/
def originalChainType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X}
    {I : Type v} (c : Cover U I) (E : OpenUnits.{u,r,max m v} R),
    boundary.{u,r,m,v} R c E 0 ≫ chainAugmentation.{u,r,m,v} R c E = 0 ∧
    (∀ p, boundary.{u,r,m,v} R c E (p + 1) ≫ boundary.{u,r,m,v} R c E p = 0) ∧
    ∃ K : ChainComplex (AmbientSheaves.{max m v} R) ℕ,
      ∃ iso : ∀ p, K.X p ≅ term.{u,r,m,v} R c E p,
        ∀ p, K.d (p + 1) p ≫ (iso p).hom =
          (iso (p + 1)).hom ≫ boundary.{u,r,m,v} R c E p

/-- The original augmented sheaf chain is exact, including surjectivity of
its augmentation as a morphism of sheaves. -/
def originalChainExactType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X}
    {I : Type v} (c : Cover U I) (E : OpenUnits.{u,r,max m v} R),
    Epi (chainAugmentation.{u,r,m,v} R c E) ∧
    (∃ h : boundary.{u,r,m,v} R c E 0 ≫ chainAugmentation.{u,r,m,v} R c E = 0,
      (ShortComplex.mk (boundary.{u,r,m,v} R c E 0) (chainAugmentation.{u,r,m,v} R c E) h).Exact) ∧
    ∀ p, ∃ h : boundary.{u,r,m,v} R c E (p + 1) ≫ boundary.{u,r,m,v} R c E p = 0,
      (ShortComplex.mk (boundary.{u,r,m,v} R c E (p + 1)) (boundary.{u,r,m,v} R c E p) h).Exact

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace AdvancedHomologicalAlgebra.CechOriginal

variable {X : TopCat.{u}} {U : Opens X} {I : Type v} (c : Cover U I) (x : X)

/-- An actual ordered tuple whose intersection contains the point. -/
abbrev SupportedTuple (p : ℕ) := {t : Fin (p + 1) → I // x ∈ tupleOpen c t}

def supportedFace {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) (t : SupportedTuple c x q) :
    SupportedTuple c x p :=
  ⟨t.1 ∘ f, tupleOpen_reindex_le c f t.1 t.2⟩

def supportedPrepend (i : I) (hi : x ∈ c.opens i) {p : ℕ} (t : SupportedTuple c x p) :
    SupportedTuple c x (p + 1) :=
  ⟨Fin.cons i t.1, by
    rw [tupleOpen, Fin.cons_zero, Fin.cons_comp_succ]
    exact ⟨hi, t.2⟩⟩

/-- Transporting the space keeps every entry of a supported tuple. -/
def liftSupportedTuple (p : ℕ) :
    SupportedTuple c x p ≃
      SupportedTuple (liftCover.{u,m,r,v} c) (X.uliftFunctorObjHomeo.{max m u r} x) p where
  toFun t := ⟨t.val, by
    apply (mem_opensEquiv X _ x).mp
    rw [liftCover_tuple]
    exact t.property⟩
  invFun t := ⟨t.val, by
    rw [← liftCover_tuple.{u,r,m,v} c t.val]
    exact (mem_opensEquiv X _ x).mpr t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma liftCover_mem (i : I) (hi : x ∈ c.opens i) :
    X.uliftFunctorObjHomeo.{max m u r} x ∈ (liftCover.{u,m,r,v} c).opens i := by
  apply (mem_opensEquiv X _ x).mp
  change x ∈ (opensEquiv.{max m u r} X) ((opensEquiv.{max m u r} X).symm (c.opens i))
  rw [OrderIso.apply_symm_apply]
  exact hi

variable (A : Type*) [Ring A]

/-- The free chain maps in stalk coordinates. -/
def freeBoundary (p : ℕ) :
    (SupportedTuple c x (p + 1) →₀ A) →ₗ[A] (SupportedTuple c x p →₀ A) :=
  ∑ a : Fin (p + 2), (-1 : ℤ) ^ a.val • Finsupp.lmapDomain A A (supportedFace c x a.succAbove)

def freeAugmentation : (SupportedTuple c x 0 →₀ A) →ₗ[A] A :=
  Finsupp.linearCombination A (fun _ ↦ (1 : A))

/-- The source's contraction sends the generator of a tuple to the tuple
with the chosen covering index prepended. -/
def freePrepend (i : I) (hi : x ∈ c.opens i) (p : ℕ) :
    (SupportedTuple c x p →₀ A) →ₗ[A] (SupportedTuple c x (p + 1) →₀ A) :=
  Finsupp.lmapDomain A A (supportedPrepend c x i hi)

def freePrependAugmentation (i : I) (hi : x ∈ c.opens i) :
    A →ₗ[A] (SupportedTuple c x 0 →₀ A) :=
  Finsupp.lsingle ⟨fun _ ↦ i, hi⟩

end AdvancedHomologicalAlgebra.CechOriginal

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

/-- The augmented alternating chain in free tuple coordinates is contracted
by prepending any chosen covering index, including in degree minus one. -/
def prependContractionType : Prop :=
  ∀ {X : TopCat.{u}} {U : Opens X} {I : Type v} (c : Cover U I)
    (x : X) (A : Type m) [Ring A] (i : I) (hi : x ∈ c.opens i),
    (freeAugmentation c x A).comp (freePrependAugmentation c x A i hi) = LinearMap.id ∧
    (freeBoundary c x A 0).comp (freePrepend c x A i hi 0) +
      (freePrependAugmentation c x A i hi).comp (freeAugmentation c x A) = LinearMap.id ∧
    ∀ p, (freeBoundary c x A (p + 1)).comp (freePrepend c x A i hi (p + 1)) +
      (freePrepend c x A i hi p).comp (freeBoundary c x A p) = LinearMap.id

/-- The labels of the free stalk basis commute with prepending, including
the chosen vertex in degree zero. -/
def prependTransportType : Prop :=
  ∀ {X : TopCat.{u}} {U : Opens X} {I : Type v} (c : Cover U I)
    (x : X) (i : I) (hi : x ∈ c.opens i),
    (∀ p (t : SupportedTuple c x p),
      liftSupportedTuple.{u,r,m,v} c x (p + 1) (supportedPrepend c x i hi t) =
        supportedPrepend (liftCover.{u,m,r,v} c) _ i (liftCover_mem.{u,r,m,v} c x i hi)
          (liftSupportedTuple.{u,r,m,v} c x p t)) ∧
    liftSupportedTuple.{u,r,m,v} c x 0 ⟨fun _ ↦ i, hi⟩ =
      ⟨fun _ ↦ i, liftCover_mem.{u,r,m,v} c x i hi⟩

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace AdvancedHomologicalAlgebra.CechOriginal

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X}
  {I : Type v} (c : Cover U I) (E : OpenUnits.{u,r,max m v} R) (x : X) (p : ℕ)

/-- The germ in the actual original-site sheaf coproduct obtained by including
the adjunction generator of the supported tuple's extended unit. -/
def tupleGerm (t : SupportedTuple c x p) :
    (originalStalkFunctor.{max m v} R x).obj (term.{u,r,m,v} R c E p) :=
  originalModuleGerm.{max m v} R x (term.{u,r,m,v} R c E p).val (tupleOpen c t.val) t.property
    ((Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t.val).val.app (op (tupleOpen c t.val))
      (unitGenerator.{u,r,max m v} R E (tupleOpen c t.val)))

/-- The inverse direction of the stalk coordinates, from free generators
to the original germs, extended linearly. -/
def tupleStalkMap :
    ModuleCat.of (originalStalkRing.{max m v} R x)
      (SupportedTuple c x p →₀ originalStalkRing.{max m v} R x) ⟶
    (originalStalkFunctor.{max m v} R x).obj (term.{u,r,m,v} R c E p) :=
  ModuleCat.ofHom (Finsupp.linearCombination _ (tupleGerm.{u,r,m,v} R c E x p))

end AdvancedHomologicalAlgebra.CechOriginal

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

/-- The stalk of the original coproduct is the free module on supported
ordered tuples, using precisely the adjunction generators. -/
def originalTupleStalkType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {I : Type v}
    (c : Cover U I) (E : OpenUnits.{u,r,max m v} R) (x : X) (p : ℕ),
    IsIso (tupleStalkMap.{u,r,m,v} R c E x p) ∧
      ∀ t, tupleStalkMap.{u,r,m,v} R c E x p (Finsupp.single t 1) = tupleGerm.{u,r,m,v} R c E x p t

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

/-- In the original stalk coordinates the alternating boundary is the
alternating deletion map on the free module. -/
def originalStalkBoundaryType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {I : Type v}
    (c : Cover U I) (E : OpenUnits.{u,r,max m v} R) (x : X) (p : ℕ),
    tupleStalkMap.{u,r,m,v} R c E x (p + 1) ≫
        (originalStalkFunctor.{max m v} R x).map (boundary.{u,r,m,v} R c E p) =
      ModuleCat.ofHom (freeBoundary c x (originalStalkRing.{max m v} R x) p) ≫
        tupleStalkMap.{u,r,m,v} R c E x p

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

/-- The top-open comparison takes the canonical generator to one in the
structure sheaf. Applying this on the actual open subspace gives the
augmentation to its structure sheaf. -/
def topUnitComparisonType :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (E : OpenUnits.{u,r,m} R),
    {e : extendedUnit.{u,r,m} R E ⊤ ≅ ambientUnit.{u,r,m} R //
      e.hom.val.app (op ⊤) (unitGenerator.{u,r,m} R E ⊤) =
        ULift.up (1 : sectionRing R (⊤ : Opens X))}

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace AdvancedHomologicalAlgebra.CechOriginal

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (E : OpenUnits.{u,r,m} R)
  (x : X) (U : Opens X) (hx : x ∈ U)

def unitGerm : (originalStalkFunctor.{m} R x).obj (extendedUnit.{u,r,m} R E U) :=
  originalModuleGerm.{m} R x (extendedUnit.{u,r,m} R E U).val U hx (unitGenerator.{u,r,m} R E U)

def unitStalkMap :
    ModuleCat.of (originalStalkRing.{m} R x) (originalStalkRing.{m} R x) ⟶
      (originalStalkFunctor.{m} R x).obj (extendedUnit.{u,r,m} R E U) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (unitGerm R E x U hx))

end AdvancedHomologicalAlgebra.CechOriginal

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

/-- The augmented stalk map sends every supported tuple in degree zero to
the generator of the stalk of the unit on the covered open. -/
def originalStalkAugmentationType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {I : Type v}
    (c : Cover U I) (E : OpenUnits.{u,r,max m v} R) (x : X) (hx : x ∈ U),
    IsIso (unitStalkMap.{u,r,max m v} R E x U hx) ∧
      tupleStalkMap.{u,r,m,v} R c E x 0 ≫
          (originalStalkFunctor.{max m v} R x).map (chainAugmentation.{u,r,m,v} R c E) =
        ModuleCat.ofHom (freeAugmentation c x (originalStalkRing.{max m v} R x)) ≫
          unitStalkMap.{u,r,max m v} R E x U hx

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

def normalizedUnitsType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}), Nonempty (OpenUnits.{u,r,m} R)

/-- A normalized comparison to the upstream extension-by-zero units.
It preserves their adjunction generators and every inclusion of opens. -/
def unitTransportType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (E : OpenUnits.{u,r,max m v} R),
    let e := opensEquiv.{max m v u r} X
    let S := liftedRing.{max m v} R
    let T := transport.{max m v} R
    let P := AdvancedHomologicalAlgebra.CechChains.SectionPresentation.{max m v u r,v}
    ∃ J : ∀ (V : Opens X) (V' : Opens (liftedSpace.{max m v u r} X)) (_ : e V' = V),
      T.obj (extendedUnit.{u,r,max m v} R E V) ≅
        AdvancedHomologicalAlgebra.CechChains.largeOpenUnit.{max m v u r,v} S V',
    (∀ (V : Opens X) (V' : Opens (liftedSpace.{max m v u r} X)) (h : e V' = V),
      (J V V' h).hom.val.app (op V')
        (sectionAt.{u,r,max m v} R (extendedUnit.{u,r,max m v} R E V) V' V h
          (unitGenerator.{u,r,max m v} R E V)) =
        AdvancedHomologicalAlgebra.CechChains.largeOpenUnitGenerator.{max m v u r,v} S V') ∧
    ∀ (p : P S) {V W : Opens X} {V' W' : Opens (liftedSpace.{max m v u r} X)}
      (hV : e V' = V) (hW : e W' = W) (h : V ≤ W) (h' : V' ≤ W'),
      T.map (unitMap.{u,r,max m v} R E h) ≫ (J W W' hW).hom =
        (J V V' hV).hom ≫ p.inclusion h'

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal
open _root_.AdvancedHomologicalAlgebra.CechChains
  (SectionPresentation largeOpenUnit largeOpenUnitGenerator largeGerm)
open Specs.AdvancedHomologicalAlgebra.SheafUniverseTransport (OriginalStalkSkyscraperComparison)

/-- Transport on each degree commutes with the individual coproduct
inclusions and the individual faces, the alternating boundary,
the augmentation, the Hom identification, and the germs of the supported
tuple generators. -/
def chainTransportType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {I : Type v}
    (c : Cover U I) (E : OpenUnits.{u,r,max m v} R),
    let e := opensEquiv.{max m v u r} X
    let S := liftedRing.{max m v} R
    let T := transport.{max m v} R
    let d := liftCover.{u,max m v,r,v} c
    ∀ P : SectionPresentation.{max m v u r,v} S,
    ∃ J : ∀ (V : Opens X) (V' : Opens (liftedSpace.{max m v u r} X)) (_ : e V' = V),
        T.obj (extendedUnit.{u,r,max m v} R E V) ≅ largeOpenUnit.{max m v u r,v} S V',
    ∃ L : ∀ p, T.obj (term.{u,r,m,v} R c E p) ≅
        _root_.AdvancedHomologicalAlgebra.CechChains.term S d p,
      (∀ (V : Opens X) (V' : Opens (liftedSpace.{max m v u r} X)) (h : e V' = V),
        (J V V' h).hom.val.app (op V')
          (sectionAt.{u,r,max m v} R (extendedUnit.{u,r,max m v} R E V) V' V h
            (unitGenerator.{u,r,max m v} R E V)) = largeOpenUnitGenerator.{max m v u r,v} S V') ∧
      (∀ p (t : Fin (p + 1) → I),
        let h := liftCover_tuple.{u,r,max m v,v} c t
        T.map (Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t) ≫ (L p).hom =
          (J (tupleOpen c t) (tupleOpen d t) h).hom ≫
            Sigma.ι (fun s : Fin (p + 1) → I ↦ largeOpenUnit.{max m v u r,v} S (tupleOpen d s)) t) ∧
      (∀ p q (f : Fin (p + 1) → Fin (q + 1)), T.map (face.{u,r,m,v} R c E f) ≫ (L p).hom =
        (L q).hom ≫ P.reindex d f) ∧
      (∀ p, T.map (boundary.{u,r,m,v} R c E p) ≫ (L p).hom =
        (L (p + 1)).hom ≫ P.boundary d p) ∧
      (T.map (chainAugmentation.{u,r,m,v} R c E) ≫
          (J U _ (e.apply_symm_apply U)).hom = (L 0).hom ≫ P.augmentation d) ∧
      (∀ (M : AmbientSheaves.{max m v} R) p (f : term.{u,r,m,v} R c E p ⟶ M),
        P.homCochains d (T.obj M) p ((L p).inv ≫ T.map f) =
          cochainComparison.{u,r,max m v,v} R M c p (homCochains.{u,r,m,v} R c E M p f)) ∧
      ∀ (x : X), ∃ D : OriginalStalkSkyscraperComparison.{max m v} R x,
        let y := X.uliftFunctorObjHomeo.{max m v u r} x
        ∀ p (t : SupportedTuple c x p),
          let t' := liftSupportedTuple.{u,r,max m v,v} c x p t
          (stalkFunctor S y).map (L p).hom
            ((D.stalkIso.inv.app (term.{u,r,m,v} R c E p)) (tupleGerm.{u,r,m,v} R c E x p t)) =
          largeGerm S (_root_.AdvancedHomologicalAlgebra.CechChains.term S d p) y
            (tupleOpen d t.val) t'.property
            ((Sigma.ι (fun s : Fin (p + 1) → I ↦ largeOpenUnit.{max m v u r,v} S (tupleOpen d s))
              t.val).val.app (op (tupleOpen d t.val))
                (largeOpenUnitGenerator.{max m v u r,v} S (tupleOpen d t.val)))

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace AdvancedHomologicalAlgebra.CechOriginal

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (M : AmbientSheaves.{m} R)
  {U : Opens X} {I : Type v} (c : Cover U I)

/-- Raising the coefficients for the chain category changes each section by
the carrier equivalence and preserves its original section-ring action. -/
def coefficientCochains (p : ℕ) :
    Cochains R M.val c p ≃ₗ[sectionRing R U]
      Cochains R ((liftSheafCoefficients.{v} R).obj M).val c p where
  toFun s t := ULift.up (s t)
  invFun s t := (s t).down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The corresponding original-to-lifted section-ring isomorphism. -/
def ringAt (V' : Opens (liftedSpace.{max m u r} X)) (V : Opens X)
    (h : opensEquiv.{max m u r} X V' = V) :
    sectionRing R V ≃+* sectionRing (liftedRing.{m} R) V' :=
  h ▸ sectionRingEquiv.{m} R V'

end AdvancedHomologicalAlgebra.CechOriginal

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal

def coefficientCochainsType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (M : AmbientSheaves.{m} R)
    {U : Opens X} {I : Type v} (c : Cover U I),
    let M' := (liftSheafCoefficients.{v} R).obj M
    (∀ s, coefficientCochains.{u,r,m,v} R M c 0 (augmentation R M.val c s) =
      augmentation R M'.val c (ULift.up s)) ∧
    ∀ p s, coefficientCochains.{u,r,m,v} R M c (p + 1) (differential R M.val c p s) =
      differential R M'.val c p (coefficientCochains.{u,r,m,v} R M c p s)

def cochainScalarsType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (M : AmbientSheaves.{m} R)
    {U : Opens X} {I : Type v} (c : Cover U I)
    (a : sectionRing R U) (p : ℕ) (s : Cochains R M.val c p),
    cochainComparison.{u,r,m,v} R M c p (a • s) =
      ringAt.{u,r,m} R ((opensEquiv.{max m u r} X).symm U) U
        ((opensEquiv.{max m u r} X).apply_symm_apply U) a •
      cochainComparison.{u,r,m,v} R M c p s

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

/-- The source's complex on the actual covered open, augmented to the
structure sheaf of that open. -/
def onOpenChainType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {I : Type v} (c : Cover U I),
    let Y := (Opens.toTopCat X).obj U
    let S : Y.Sheaf RingCat.{r} := U.sheafRestrict.obj R
    let d := _root_.AdvancedHomologicalAlgebra.CechChains.internalCover c
    ∃ E : OpenUnits.{u,r,max m v} S,
    ∃ K : ChainComplex (AmbientSheaves.{max m v} S) ℕ,
    ∃ b : ∀ p, K.X p ≅ term.{u,r,m,v} S d E p,
    ∃ j : extendedUnit.{u,r,max m v} S E ⊤ ≅ ambientUnit.{u,r,max m v} S,
      (∀ p, K.d (p + 1) p ≫ (b p).hom = (b (p + 1)).hom ≫ boundary.{u,r,m,v} S d E p) ∧
      j.hom.val.app (op ⊤) (unitGenerator.{u,r,max m v} S E ⊤) =
        ULift.up (1 : sectionRing S (⊤ : Opens Y)) ∧
      boundary.{u,r,m,v} S d E 0 ≫ (chainAugmentation.{u,r,m,v} S d E ≫ j.hom) = 0 ∧
      (∀ (M : AmbientSheaves.{max m v} S) (f : ambientUnit.{u,r,max m v} S ⟶ M),
        homCochains.{u,r,m,v} S d E M 0 ((chainAugmentation.{u,r,m,v} S d E ≫ j.hom) ≫ f) =
          augmentation S M.val d (f.val.app (op ⊤) (ULift.up (1 : sectionRing S (⊤ : Opens Y))))) ∧
      ∀ x : Y, ∃ i : I, ∃ hi : x ∈ d.opens i,
        let A := originalStalkRing.{max m v} S x
        let F := originalStalkFunctor.{max m v} S x
        let q := unitStalkMap.{u,r,max m v} S E x ⊤ (show x ∈ (⊤ : Opens Y) from trivial) ≫ F.map j.hom
        IsIso q ∧
        (∀ p, IsIso (tupleStalkMap.{u,r,m,v} S d E x p)) ∧
        (tupleStalkMap.{u,r,m,v} S d E x 0 ≫ F.map (chainAugmentation.{u,r,m,v} S d E ≫ j.hom) =
          ModuleCat.ofHom (freeAugmentation d x A) ≫ q) ∧
        (∀ p, tupleStalkMap.{u,r,m,v} S d E x (p + 1) ≫ F.map (boundary.{u,r,m,v} S d E p) =
          ModuleCat.ofHom (freeBoundary d x A p) ≫ tupleStalkMap.{u,r,m,v} S d E x p) ∧
        (freeAugmentation d x A).comp (freePrependAugmentation d x A i hi) = LinearMap.id ∧
        (freeBoundary d x A 0).comp (freePrepend d x A i hi 0) +
          (freePrependAugmentation d x A i hi).comp (freeAugmentation d x A) = LinearMap.id ∧
        ∀ p, (freeBoundary d x A (p + 1)).comp (freePrepend d x A i hi (p + 1)) +
          (freePrepend d x A i hi p).comp (freeBoundary d x A p) = LinearMap.id

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

namespace AdvancedHomologicalAlgebra.CechOriginal

open scoped AdvancedHomologicalAlgebra.CechOriginal

section NativeUnits

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (D : OpenUnits.{u,r,m} R)

/-- Raise the carrier of the extension by zero constructed in the native
ambient category over the original site and ring. -/
abbrev liftedNativeUnit (V : Opens X) : AmbientSheaves.{max m v} R :=
  (liftSheafCoefficients.{v} R).obj (extendedUnit.{u,r,m} R D V)

/-- The image of the native adjunction generator under the carrier lift. -/
def liftedNativeGenerator (V : Opens X) : (liftedNativeUnit.{u,r,m,v} R D V).val.obj (op V) :=
  ULift.up (unitGenerator.{u,r,m} R D V)

/-- Comparison with the extension by zero constructed in the joined category. -/
structure UnitCarrierComparison (E : OpenUnits.{u,r,max m v} R) where
  iso (V : Opens X) :
    liftedNativeUnit.{u,r,m,v} R D V ≅ extendedUnit.{u,r,max m v} R E V
  generator (V : Opens X) :
    (iso V).hom.val.app (op V) (liftedNativeGenerator.{u,r,m,v} R D V) =
      unitGenerator.{u,r,max m v} R E V
  inclusion {V W : Opens X} (h : V ≤ W) :
    (liftSheafCoefficients.{v} R).map (unitMap.{u,r,m} R D h) ≫ (iso W).hom =
      (iso V).hom ≫ unitMap.{u,r,max m v} R E h
  rightMul (V : Opens X) (a : sectionRing R V) :
    (liftSheafCoefficients.{v} R).map (unitRightMul.{u,r,m} R D V a) ≫ (iso V).hom =
      (iso V).hom ≫ unitRightMul.{u,r,max m v} R E V a

end NativeUnits

section NativeChain

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X}
  {I : Type v} (c : Cover U I) (D : OpenUnits.{u,r,m} R)

abbrev liftedNativeTupleUnits (p : ℕ) (t : Fin (p + 1) → I) : AmbientSheaves.{max m v} R :=
  liftedNativeUnit.{u,r,m,v} R D (tupleOpen c t)

/-- The coproduct of the individually lifted native units on the original site. -/
abbrev liftedNativeTerm (p : ℕ) : AmbientSheaves.{max m v} R :=
  ∐ liftedNativeTupleUnits.{u,r,m,v} R c D p

def liftedNativeFace {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    liftedNativeTerm.{u,r,m,v} R c D q ⟶ liftedNativeTerm.{u,r,m,v} R c D p :=
  Sigma.desc fun t ↦
    (liftSheafCoefficients.{v} R).map (unitMap.{u,r,m} R D (tupleOpen_reindex_le c f t)) ≫
      Sigma.ι (liftedNativeTupleUnits.{u,r,m,v} R c D p) (t ∘ f)

def liftedNativeBoundary (p : ℕ) :
    liftedNativeTerm.{u,r,m,v} R c D (p + 1) ⟶ liftedNativeTerm.{u,r,m,v} R c D p :=
  ∑ a : Fin (p + 2), (-1 : ℤ) ^ a.val • liftedNativeFace.{u,r,m,v} R c D a.succAbove

def liftedNativeAugmentation :
    liftedNativeTerm.{u,r,m,v} R c D 0 ⟶ liftedNativeUnit.{u,r,m,v} R D U :=
  Sigma.desc fun t ↦
    (liftSheafCoefficients.{v} R).map (unitMap.{u,r,m} R D (tupleOpen_le c t))

def liftedNativeRightMul (p : ℕ) (a : sectionRing R U) :
    liftedNativeTerm.{u,r,m,v} R c D p ⟶ liftedNativeTerm.{u,r,m,v} R c D p :=
  Sigma.desc fun t ↦ (liftSheafCoefficients.{v} R).map
      (unitRightMul.{u,r,m} R D (tupleOpen c t) (R.obj.map (homOfLE (tupleOpen_le c t)).op a)) ≫
    Sigma.ι (liftedNativeTupleUnits.{u,r,m,v} R c D p) t

/-- Evaluation on the lift of each native generator, using the same tuple and
the original ring of sections. -/
def liftedNativeHomCochains (M : AmbientSheaves.{max m v} R) (p : ℕ)
    (f : liftedNativeTerm.{u,r,m,v} R c D p ⟶ M) : Cochains R M.val c p :=
  fun t ↦ (Sigma.ι (liftedNativeTupleUnits.{u,r,m,v} R c D p) t ≫ f).val.app (op (tupleOpen c t))
    (liftedNativeGenerator.{u,r,m,v} R D (tupleOpen c t))

def liftedNativeTupleGerm (x : X) (p : ℕ) (t : SupportedTuple c x p) :
    (originalStalkFunctor.{max m v} R x).obj (liftedNativeTerm.{u,r,m,v} R c D p) :=
  originalModuleGerm.{max m v} R x (liftedNativeTerm.{u,r,m,v} R c D p).val
    (tupleOpen c t.val) t.property
    ((Sigma.ι (liftedNativeTupleUnits.{u,r,m,v} R c D p) t.val).val.app (op (tupleOpen c t.val))
      (liftedNativeGenerator.{u,r,m,v} R D (tupleOpen c t.val)))

/-- The comparison on genuine coproducts over the original site and ring,
with the same normalization at every term and at the augmentation. -/
structure ChainCarrierComparison (E : OpenUnits.{u,r,max m v} R)
    (J : UnitCarrierComparison.{u,r,m,v} R D E) where
  iso (p : ℕ) : liftedNativeTerm.{u,r,m,v} R c D p ≅ term.{u,r,m,v} R c E p
  summand (p : ℕ) (t : Fin (p + 1) → I) :
    Sigma.ι (liftedNativeTupleUnits.{u,r,m,v} R c D p) t ≫ (iso p).hom =
      (J.iso (tupleOpen c t)).hom ≫ Sigma.ι (tupleUnits.{u,r,m,v} R c E p) t
  face {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1)) :
    liftedNativeFace.{u,r,m,v} R c D f ≫ (iso p).hom =
      (iso q).hom ≫ CechOriginal.face.{u,r,m,v} R c E f
  boundary (p : ℕ) :
    liftedNativeBoundary.{u,r,m,v} R c D p ≫ (iso p).hom =
      (iso (p + 1)).hom ≫ CechOriginal.boundary.{u,r,m,v} R c E p
  augmentation :
    liftedNativeAugmentation.{u,r,m,v} R c D ≫ (J.iso U).hom =
      (iso 0).hom ≫ chainAugmentation.{u,r,m,v} R c E
  rightMul (p : ℕ) (a : sectionRing R U) :
    liftedNativeRightMul.{u,r,m,v} R c D p a ≫ (iso p).hom =
      (iso p).hom ≫ termRightMul.{u,r,m,v} R c E p a
  unitEvaluation (M : AmbientSheaves.{max m v} R) (f : liftedNativeUnit.{u,r,m,v} R D U ⟶ M) :
    f.val.app (op U) (liftedNativeGenerator.{u,r,m,v} R D U) =
      CechOriginal.unitEvaluation.{u,r,max m v} R E U M ((J.iso U).inv ≫ f)
  homEvaluation (M : AmbientSheaves.{max m v} R) (p : ℕ)
      (f : liftedNativeTerm.{u,r,m,v} R c D p ⟶ M) :
    liftedNativeHomCochains.{u,r,m,v} R c D M p f =
      homCochains.{u,r,m,v} R c E M p ((iso p).inv ≫ f)
  tupleGerm (x : X) (p : ℕ) (t : SupportedTuple c x p) :
    (originalStalkFunctor.{max m v} R x).map (iso p).hom
        (liftedNativeTupleGerm.{u,r,m,v} R c D x p t) =
      CechOriginal.tupleGerm.{u,r,m,v} R c E x p t

end NativeChain

end AdvancedHomologicalAlgebra.CechOriginal

namespace Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

open _root_.AdvancedHomologicalAlgebra.CechOriginal
open scoped _root_.AdvancedHomologicalAlgebra.CechOriginal

def unitCarrierComparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (D : OpenUnits.{u,r,m} R)
    (E : OpenUnits.{u,r,max m v} R), Nonempty (UnitCarrierComparison.{u,r,m,v} R D E)

def chainCarrierComparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X} {I : Type v}
    (c : Cover U I) (D : OpenUnits.{u,r,m} R) (E : OpenUnits.{u,r,max m v} R),
    ∃ J : UnitCarrierComparison.{u,r,m,v} R D E, Nonempty (ChainCarrierComparison.{u,r,m,v} R c D E J)

/-- On the covered space itself, the augmentation targets the structure
sheaf. Its carrier comparison sends a twice-lifted scalar to the same scalar
in the joined carrier, including the unit section. -/
def topUnitCarrierComparisonType : Prop :=
  ∀ {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) (D : OpenUnits.{u,r,m} R)
    (E : OpenUnits.{u,r,max m v} R) (J : UnitCarrierComparison.{u,r,m,v} R D E)
    (j : {i : extendedUnit.{u,r,m} R D ⊤ ≅ ambientUnit.{u,r,m} R //
      i.hom.val.app (op ⊤) (unitGenerator.{u,r,m} R D ⊤) =
        ULift.up (1 : sectionRing R (⊤ : Opens X))})
    (k : {i : extendedUnit.{u,r,max m v} R E ⊤ ≅ ambientUnit.{u,r,max m v} R //
      i.hom.val.app (op ⊤) (unitGenerator.{u,r,max m v} R E ⊤) =
        ULift.up (1 : sectionRing R (⊤ : Opens X))}),
    let F := liftSheafCoefficients.{v} R
    ∃ K : F.obj (ambientUnit.{u,r,m} R) ≅ ambientUnit.{u,r,max m v} R,
      (∀ (W : Opens X) (s : (F.obj (ambientUnit.{u,r,m} R)).val.obj (op W)),
        K.hom.val.app (op W) s = ULift.up s.down.down) ∧
      (F.map j.val.hom ≫ K.hom = (J.iso ⊤).hom ≫ k.val.hom) ∧
      ∀ {I : Type v} (c : Cover (⊤ : Opens X) I)
        (L : ChainCarrierComparison.{u,r,m,v} R c D E J),
        (liftedNativeAugmentation.{u,r,m,v} R c D ≫ F.map j.val.hom) ≫ K.hom =
          (L.iso 0).hom ≫ (chainAugmentation.{u,r,m,v} R c E ≫ k.val.hom)

end Specs.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients
