import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
HA-R15 (classification portion), source lines 2208–2298.

An exact augmented row is represented by its complex in degrees -n,...,0,
with its left term identified with Y. Exactness of the augmented row is
expressed by the augmentation being a quasi-isomorphism to X[0]. This
condition concerns the row itself, not the classification of its class.
No injective or projective objects, or small Ext hypothesis, are required.

The classification clauses specify both the normalized roof and the actual
geometric Baer operation, with no classification certificate among the hypotheses.
-/

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The last differential and augmentation of any augmented complex. -/
noncomputable def augmentedTop {X : 𝒜} {K : CochainComplex 𝒜 ℤ}
    (s : K ⟶ (CochainComplex.singleFunctor 𝒜 0).obj X) : ShortComplex 𝒜 :=
  ShortComplex.mk (K.d (-1) 0) (s.f 0) (by
    simpa [CochainComplex.singleFunctor] using (s.comm (-1) 0).symm)

/-- The augmented exact row 0 → Y → E_(n-1) → ... → E_0 → X → 0,
encoded by its complex C_E and augmentation. The isomorphism `left` fixes
which copy of Y is the left endpoint. This type is empty in degree zero. -/
structure Extension (X Y : 𝒜) (n : ℕ) where
  positive : 0 < n
  complex : CochainComplex 𝒜 ℤ
  supportedGE : complex.IsStrictlyGE (-(n : ℤ))
  supportedLE : complex.IsStrictlyLE 0
  left : complex.X (-(n : ℤ)) ≅ Y
  augmentation : complex ⟶ (CochainComplex.singleFunctor 𝒜 0).obj X
  exact : QuasiIso augmentation

attribute [instance] Extension.supportedGE Extension.supportedLE Extension.exact

namespace Extension
variable {X Y X' Y' : 𝒜} {n : ℕ}

lemma augmentation_zero (E : Extension X Y n) :
    E.complex.d (-1) 0 ≫ E.augmentation.f 0 = 0 := by
  simpa [CochainComplex.singleFunctor] using (E.augmentation.comm (-1) 0).symm

/-- The last two arrows in the augmented row. The target is canonically X
via `singleObjXSelf`. -/
noncomputable def top (E : Extension X Y n) : ShortComplex 𝒜 :=
  augmentedTop E.augmentation

/-- The ordinary short complex underlying a degree-one row. -/
noncomputable def degreeOneSequence (E : Extension X Y 1) : ShortComplex 𝒜 :=
  ShortComplex.mk (E.left.inv ≫ E.complex.d (-1) 0)
    (E.augmentation.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom)
    (by rw [← Category.assoc, Category.assoc E.left.inv, E.augmentation_zero]; simp)

/-- A map of extension rows with specified maps on both endpoints. -/
structure Morphism (E : Extension X Y n) (F : Extension X' Y' n)
    (x : X ⟶ X') (y : Y ⟶ Y') where
  hom : E.complex ⟶ F.complex
  left_comm : hom.f (-(n : ℤ)) ≫ F.left.hom = E.left.hom ≫ y
  right_comm : hom ≫ F.augmentation =
    E.augmentation ≫ (CochainComplex.singleFunctor 𝒜 0).map x

/-- A map of augmented rows inducing the identity on the two endpoints. -/
structure Map (E F : Extension X Y n) where
  hom : E.complex ⟶ F.complex
  left_comm : hom.f (-(n : ℤ)) ≫ F.left.hom = E.left.hom
  right_comm : hom ≫ F.augmentation = E.augmentation

/-- The generating relation is directed; equivalence is its equivalence closure. -/
def Related (E F : Extension X Y n) : Prop := Nonempty (Map E F)

def Equivalent (E F : Extension X Y n) : Prop := Relation.EqvGen Related E F

instance extensionSetoid (X Y : 𝒜) (n : ℕ) : Setoid (Extension X Y n) where
  r := Equivalent
  iseqv := ⟨fun _ => Relation.EqvGen.refl _,
    fun {_ _} h => Relation.EqvGen.symm _ _ h,
    fun {_ _ _} h h' => Relation.EqvGen.trans _ _ _ h h'⟩

/-- Positive projection onto the left endpoint, before identifying the stalk
in degree -n with Y[0][n]. -/
noncomputable def projection (E : Extension X Y n) :
    E.complex ⟶ (CochainComplex.singleFunctor 𝒜 (-(n : ℤ))).obj Y :=
  HomologicalComplex.mkHomToSingle E.left.hom (by
    intro i hi
    apply (E.complex.isZero_of_isStrictlyGE (-(n : ℤ)) i (by
      change i + 1 = -(n : ℤ) at hi
      omega)).eq_of_src)

/-- Termwise direct sums preserve quasi-isomorphisms. -/
lemma quasiIso_biprod_map {K L K' L' : CochainComplex 𝒜 ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') [QuasiIso f] [QuasiIso g] :
    QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor 𝒜 (.up ℤ) i
  have hf : IsIso (H.map f) := (quasiIsoAt_iff_isIso_homologyMap f i).mp inferInstance
  have hg : IsIso (H.map g) := (quasiIsoAt_iff_isIso_homologyMap g i).mp inferInstance
  let : PreservesBinaryBiproduct K K' H :=
    preservesBinaryBiproduct_of_preservesBinaryProduct H
  let : PreservesBinaryBiproduct L L' H :=
    preservesBinaryBiproduct_of_preservesBinaryProduct H
  have he : H.map (biprod.map f g) = (H.mapBiprod K K').hom ≫
      biprod.map (H.map f) (H.map g) ≫ (H.mapBiprod L L').inv := by
    apply (cancel_mono (H.mapBiprod L L').hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, comp_id]
    ext <;> simp [← Functor.map_comp, biprod.map]
  have : IsIso (biprod.map (H.map f) (H.map g)) :=
    (biprod.mapIso (asIso (H.map f)) (asIso (H.map g))).isIso_hom
  change IsIso (H.map _)
  rw [he]
  infer_instance

attribute [local instance] preservesBinaryBiproduct_of_preservesBinaryProduct

noncomputable def directSum {X Y X' Y' : 𝒜} {n : ℕ}
    (E : Extension X Y n) (F : Extension X' Y' n) :
    Extension (X ⊞ X') (Y ⊞ Y') n where
  positive := E.positive
  complex := E.complex ⊞ F.complex
  supportedGE := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact ((biprod_isZero_iff _ _).mpr ⟨E.complex.isZero_of_isStrictlyGE _ i hi,
      F.complex.isZero_of_isStrictlyGE _ i hi⟩).of_iso
        (HomologicalComplex.biprodXIso E.complex F.complex i)
  supportedLE := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact ((biprod_isZero_iff _ _).mpr ⟨E.complex.isZero_of_isStrictlyLE _ i hi,
      F.complex.isZero_of_isStrictlyLE _ i hi⟩).of_iso
        (HomologicalComplex.biprodXIso E.complex F.complex i)
  left := HomologicalComplex.biprodXIso E.complex F.complex _ ≪≫
    biprod.mapIso E.left F.left
  augmentation := biprod.map E.augmentation F.augmentation ≫
    ((CochainComplex.singleFunctor 𝒜 0).mapBiprod X X').inv
  exact := by
    have := quasiIso_biprod_map E.augmentation F.augmentation
    infer_instance

noncomputable def directSumInl {X Y X' Y' : 𝒜} {n : ℕ}
    (E : Extension X Y n) (F : Extension X' Y' n) :
    E.Morphism (directSum E F) biprod.inl biprod.inl where
  hom := biprod.inl
  left_comm := by
    dsimp [directSum]
    rw [← HomologicalComplex.inl_biprodXIso_inv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_map]
  right_comm := by
    dsimp [directSum]
    simp [biprod.map]

noncomputable def directSumInr {X Y X' Y' : 𝒜} {n : ℕ}
    (E : Extension X Y n) (F : Extension X' Y' n) :
    F.Morphism (directSum E F) biprod.inr biprod.inr where
  hom := biprod.inr
  left_comm := by
    dsimp [directSum]
    rw [← HomologicalComplex.inr_biprodXIso_inv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_map]
  right_comm := by
    dsimp [directSum]
    simp [biprod.map]

noncomputable def directSumFst {X Y X' Y' : 𝒜} {n : ℕ}
    (E : Extension X Y n) (F : Extension X' Y' n) :
    (directSum E F).Morphism E biprod.fst biprod.fst where
  hom := biprod.fst
  left_comm := by
    dsimp [directSum]
    simp only [Category.assoc, biprod.map_fst]
    rw [← Category.assoc, HomologicalComplex.biprodXIso_hom_fst]
  right_comm := by
    dsimp [directSum]
    apply biprod.hom_ext' <;> simp [biprod.map, Category.assoc, ← Functor.map_comp]

noncomputable def directSumSnd {X Y X' Y' : 𝒜} {n : ℕ}
    (E : Extension X Y n) (F : Extension X' Y' n) :
    (directSum E F).Morphism F biprod.snd biprod.snd where
  hom := biprod.snd
  left_comm := by
    dsimp [directSum]
    simp only [Category.assoc, biprod.map_snd]
    rw [← Category.assoc, HomologicalComplex.biprodXIso_hom_snd]
  right_comm := by
    dsimp [directSum]
    apply biprod.hom_ext' <;> simp [biprod.map, Category.assoc, ← Functor.map_comp]

section Derived
variable [HasDerivedCategory.{w} 𝒜]

/-- The unscaled positive-projection roof. The inverse of `shiftIso` has
positive identity component on Y; it introduces no triangular boundary sign. -/
noncomputable def roof (E : Extension X Y n) :
    Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (n : ℤ) :=
  inv (_root_.DerivedCategory.Q.map E.augmentation) ≫
    _root_.DerivedCategory.Q.map E.projection ≫
    ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso
      (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app Y

/-- The source's cochain normalization (-1)^(n(n-1)/2). -/
def normalization (n : ℕ) : ℤˣ := ((n * (n - 1) / 2 : ℕ) : ℤ).negOnePow

noncomputable def yonedaClass (E : Extension X Y n) :
    Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (n : ℤ) :=
  normalization n • E.roof

end Derived

/-- An actual pushout at the left endpoint, with the remaining terms unchanged
up to the canonical comparison isomorphisms. -/
structure PushoutData {X Y Y' : 𝒜} {n : ℕ} (E : Extension X Y n) (y : Y ⟶ Y') where
  row : Extension X Y' n
  comparison : E.Morphism row (𝟙 X) y
  endpoint : IsPushout (E.left.inv ≫ E.complex.d (-(n:ℤ)) (-(n:ℤ)+1)) y
    (comparison.hom.f (-(n:ℤ)+1))
    (row.left.inv ≫ row.complex.d (-(n:ℤ)) (-(n:ℤ)+1))
  unchanged : ∀ i : ℤ, i ≠ -(n:ℤ) → i ≠ -(n:ℤ)+1 → IsIso (comparison.hom.f i)

/-- An actual pullback at the right endpoint, with the other terms unchanged. -/
structure PullbackData {X X' Y : 𝒜} {n : ℕ} (E : Extension X Y n) (x : X' ⟶ X) where
  row : Extension X' Y n
  comparison : row.Morphism E x (𝟙 Y)
  endpoint : IsPullback (row.augmentation.f 0) (comparison.hom.f 0)
    (((CochainComplex.singleFunctor 𝒜 0).map x).f 0) (E.augmentation.f 0)
  unchanged : ∀ i : ℤ, i ≠ 0 → IsIso (comparison.hom.f i)
end Extension

/-- Positive-degree classes are the quotient by the equivalence generated by
endpoint-identity maps. In degree zero they are ordinary morphisms (with a harmless universe lift). -/
def Classes (X Y : 𝒜) : ℕ → Type (max u v)
  | 0 => ULift.{u} (X ⟶ Y)
  | n + 1 => Quotient (Extension.extensionSetoid X Y (n + 1))

/-- The degree-zero classes have the ordinary lifted additive group of Hom. -/
instance classesZeroAddCommGroup (X Y : 𝒜) : AddCommGroup (Classes X Y 0) :=
  inferInstanceAs (AddCommGroup (ULift.{u} (X ⟶ Y)))

/-- Degree-zero endpoint maps act by ordinary precomposition and postcomposition. -/
noncomputable def zeroMap {X X' Y Y' : 𝒜} (a : X' ⟶ X) (b : Y ⟶ Y') :
    Classes X Y 0 →+ Classes X' Y' 0 where
  toFun f := ⟨a ≫ f.down ≫ b⟩
  map_zero' := by apply ULift.ext; simp
  map_add' f g := by
    apply ULift.ext
    change a ≫ (f.down + g.down) ≫ b = a ≫ f.down ≫ b + a ≫ g.down ≫ b
    simp [Preadditive.comp_add, Preadditive.add_comp]

/-- The degree-zero comparison is the accepted stalk comparison. -/
noncomputable def zeroClass [HasDerivedCategory.{w} 𝒜] {X Y : 𝒜}
    (f : Classes X Y 0) : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y 0 :=
  Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom f.down

/-- Additive classification in degree zero, with its actual value on every morphism. -/
def zeroClassificationType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y : 𝒜),
  ∃ e : Classes X Y 0 ≃+ Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y 0,
    ∀ f : X ⟶ Y, e ⟨f⟩ = Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.zeroHom f

/-- Degree-zero naturality is ordinary composition on Hom and shifted composition in D. -/
def zeroNaturalityType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X X' Y Y' : 𝒜) (a : X' ⟶ X) (b : Y ⟶ Y')
    (f : Classes X Y 0),
  zeroClass (zeroMap a b f) =
    Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap a b 0 (zeroClass f)

/-- Bijectivity of the normalized class map in every positive degree. -/
def classificationType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y : 𝒜) (n : ℕ),
  ∃ e : Quotient (Extension.extensionSetoid X Y (n + 1)) ≃
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y ((n + 1 : ℕ) : ℤ),
    ∀ E : Extension X Y (n + 1), e ⟦E⟧ = E.yonedaClass

/-- Invariance under all zigzags, not just isomorphisms of middle terms. -/
def invariantType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y : 𝒜) (n : ℕ)
    (E F : Extension X Y n), E.Equivalent F → E.yonedaClass = F.yonedaClass

def degreeOneType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y : 𝒜) (E : Extension X Y 1),
  E.yonedaClass = E.roof

/-- The complete degree-one sign comparison, for the short exact sequence
underlying every degree-one row. -/
def degreeOneBoundaryType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y : 𝒜) (E : Extension X Y 1),
  ∃ hS : E.degreeOneSequence.ShortExact, E.yonedaClass = -hS.singleδ

/-- The augmentation condition recovers the exact ordinary augmented row. -/
def exactRowType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X Y : 𝒜) (n : ℕ) (E : Extension X Y n),
  (∀ i : ℤ, i ≠ 0 → E.complex.ExactAt i) ∧
    Mono (E.complex.d (-(n : ℤ)) (-(n : ℤ) + 1)) ∧
    E.top.Exact ∧ Epi (E.augmentation.f 0)

/-- Every ordinary exact augmented row yields the required augmentation.
This is the converse bridge for the cohomological encoding of exactness. -/
def rowAugmentationType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X : 𝒜) (K : CochainComplex 𝒜 ℤ) [K.IsStrictlyLE 0]
    (s : K ⟶ (CochainComplex.singleFunctor 𝒜 0).obj X),
  (∀ i : ℤ, i ≠ 0 → K.ExactAt i) → (augmentedTop s).Exact →
    Epi (s.f 0) → QuasiIso s

def mapNaturalityType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y X' Y' : 𝒜) (n : ℕ)
    (E : Extension X Y n) (F : Extension X' Y' n)
    (x : X ⟶ X') (y : Y ⟶ Y') (_f : E.Morphism F x y),
  E.yonedaClass ≫ ((_root_.DerivedCategory.singleFunctor 𝒜 0).map y)⟦(n : ℤ)⟧' =
    (_root_.DerivedCategory.singleFunctor 𝒜 0).map x ≫ F.yonedaClass

def quotientMapType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y : 𝒜) (n : ℕ),
  ∃ f : Quotient (Extension.extensionSetoid X Y (n + 1)) →
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y ((n + 1 : ℕ) : ℤ),
    ∀ E : Extension X Y (n + 1), f ⟦E⟧ = E.yonedaClass


def pushoutType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X Y Y' : 𝒜) (n : ℕ) (E : Extension X Y n) (y : Y ⟶ Y'),
  Nonempty (E.PushoutData y)

def pullbackType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X X' Y : 𝒜) (n : ℕ) (E : Extension X Y n) (x : X' ⟶ X),
  Nonempty (E.PullbackData x)

/-- The group law is the geometric Baer construction: termwise direct sum,
diagonal pullback at X, and codiagonal pushout at Y. -/
def baerClassificationType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y : 𝒜) (n : ℕ),
  ∃ g : AddCommGroup (Quotient (Extension.extensionSetoid X Y (n+1))), letI := g
    ∃ e : Quotient (Extension.extensionSetoid X Y (n+1)) ≃+
        Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y ((n+1:ℕ):ℤ),
      (∀ E : Extension X Y (n+1), e ⟦E⟧ = E.yonedaClass) ∧
      (∀ E F : Extension X Y (n+1),
        ∃ P : (Extension.directSum E F).PullbackData (biprod.lift (𝟙 X) (𝟙 X)),
        ∃ O : P.row.PushoutData (biprod.desc (𝟙 Y) (𝟙 Y)),
          ((⟦E⟧ : Quotient (Extension.extensionSetoid X Y (n+1))) +
            (⟦F⟧ : Quotient (Extension.extensionSetoid X Y (n+1)))) = ⟦O.row⟧)

/-- Naturality is implemented by geometric pullback and pushout of rows. -/
def endpointNaturalityType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X X' Y Y' : 𝒜) (n : ℕ)
    (E : Extension X Y n) (x : X' ⟶ X) (y : Y ⟶ Y'),
  ∃ P : E.PullbackData x, ∃ O : P.row.PushoutData y,
    O.row.yonedaClass =
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap x y (n:ℤ) E.yonedaClass

/-- The existing row model also has the full degree-one set classification. -/
def degreeOneClassificationType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (X Y : 𝒜),
  ∃ e : Quotient (Extension.extensionSetoid X Y 1) ≃
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (1:ℤ),
    ∀ E : Extension X Y 1, e ⟦E⟧ = E.yonedaClass

/-- Natural additive classification on the actual quotient. The additive group
law is geometric Baer sum, and the endpoint homomorphism is geometric pullback
followed by pushout on every representative. -/
def naturalAdditiveClassificationType : Prop := ∀ (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (n : ℕ),
  ∃ g : ∀ (X Y : 𝒜), AddCommGroup (Quotient (Extension.extensionSetoid X Y (n+1))),
    letI (X Y : 𝒜) : AddCommGroup (Quotient (Extension.extensionSetoid X Y (n+1))) := g X Y
    ∃ e : ∀ (X Y : 𝒜), Quotient (Extension.extensionSetoid X Y (n+1)) ≃+
        Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y ((n+1:ℕ):ℤ),
      (∀ (X Y : 𝒜) (E : Extension X Y (n+1)), e X Y ⟦E⟧ = E.yonedaClass) ∧
      (∀ (X Y : 𝒜) (E F : Extension X Y (n+1)),
        ∃ P : (Extension.directSum E F).PullbackData (biprod.lift (𝟙 X) (𝟙 X)),
        ∃ O : P.row.PushoutData (biprod.desc (𝟙 Y) (𝟙 Y)),
          (⟦E⟧ : Quotient (Extension.extensionSetoid X Y (n+1))) + ⟦F⟧ = ⟦O.row⟧) ∧
      ∀ (X X' Y Y' : 𝒜) (a : X' ⟶ X) (b : Y ⟶ Y'),
        ∃ φ : Quotient (Extension.extensionSetoid X Y (n+1)) →+
            Quotient (Extension.extensionSetoid X' Y' (n+1)),
          (∀ E : Extension X Y (n+1),
            ∃ P : E.PullbackData a, ∃ O : P.row.PushoutData b,
              φ ⟦E⟧ = ⟦O.row⟧) ∧
          ∀ q, e X' Y' (φ q) =
            Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap a b ((n+1:ℕ):ℤ) (e X Y q)

end Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses
