import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Localization.Away.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidAlgebra BigOperators DirectSum TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.EquivariantAffineModules

open CharacterDescent (Character)

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k : Type u} [Field k]
variable {T : GroupScheme k} {X Y Z : SchemeOver k}

abbrev Pull (f : Y ⟶ X) (F : X.left.Modules) :=
  (Scheme.Modules.pullback f.left).obj F

/-- Compare two pullbacks along equal maps over the field. -/
def pullCongr (F : X.left.Modules) {f g : Y ⟶ X} (h : f = g) :
    Pull f F ≅ Pull g F :=
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app F

/-- Compare the pullback along a composite with successive pullbacks. -/
def pullComp (F : X.left.Modules) (f : Z ⟶ Y) (g : Y ⟶ X) :
    Pull f (Pull g F) ≅ Pull (f ≫ g) F :=
  (Scheme.Modules.pullbackComp f.left g.left).app F

abbrev actOn (a : ModObj T.X X) (t : Y ⟶ T.X) (x : Y ⟶ X) : Y ⟶ X :=
  lift t x ≫ a.smul

/-- Transport in a linearization, obtained by pulling its universal isomorphism
back along the given pair of morphisms. -/
def transport (a : ModObj T.X X) {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    (t : Y ⟶ T.X) (x : Y ⟶ X) : Pull x F ≅ Pull (actOn a t x) F :=
  (pullCongr F (by simp : lift t x ≫ snd T.X X = x)).symm ≪≫
    (pullComp F (lift t x) (snd T.X X)).symm ≪≫
    (Scheme.Modules.pullback (lift t x).left).mapIso θ ≪≫
    pullComp F (lift t x) a.smul

def ComposesTo {C : Type*} [Category C] {A B D E : C}
    (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (i : A ⟶ E) : Prop :=
  f ≫ g ≫ h = i

/-- Composition of transports at two scheme-valued points of the acting group. -/
def TransportComposition {a : ModObj T.X X} {F : X.left.Modules}
    (θ : Pull (snd T.X X) F ≅ Pull a.smul F)
    (s t : Y ⟶ T.X) (x : Y ⟶ X)
    (h : actOn a s (actOn a t x) = actOn a (s * t) x) : Prop :=
  ComposesTo (transport a θ t x).hom (transport a θ s (actOn a t x)).hom
    (pullCongr F h).hom (transport a θ (s * t) x).hom

/-- A scheme-theoretic linearization for the left action. The transport
isomorphism is covariant on the fibers. -/
structure Linearization (a : ModObj T.X X) (F : X.left.Modules) where
  iso : Pull (snd T.X X) F ≅ Pull a.smul F
  unit : ∀ (Y : SchemeOver k) (x : Y ⟶ X),
    ∃ h : actOn a (1 : Y ⟶ T.X) x = x,
      (transport a iso 1 x).hom ≫ (pullCongr F h).hom = 𝟙 _
  mul : ∀ (Y : SchemeOver k) (s t : Y ⟶ T.X) (x : Y ⟶ X),
    ∃ h : actOn a s (actOn a t x) = actOn a (s * t) x, TransportComposition iso s t x h



/-- A quasi-coherent module sheaf with a scheme-theoretic linearization. -/
structure EquivariantQuasicoherent (a : ModObj T.X X) where
  sheaf : X.left.Modules
  quasicoherent : sheaf.IsQuasicoherent
  lin : Linearization a sheaf

/-- Equivariance of a map between two specified linearizations. -/
def IsLinearizedMap {a : ModObj T.X X} {F H : X.left.Modules}
    (lF : Linearization a F) (lH : Linearization a H) (f : F ⟶ H) : Prop :=
  lF.iso.hom ≫ (Scheme.Modules.pullback a.smul.left).map f =
    (Scheme.Modules.pullback (snd T.X X).left).map f ≫ lH.iso.hom

/-- On the locally noetherian schemes used here coherence is equivalent to
local finite presentation of a module sheaf. -/
structure EquivariantCoherent (a : ModObj T.X X) where
  sheaf : X.left.Modules
  coherent : sheaf.IsFinitePresentation
  lin : Linearization a sheaf

/-- Equivariance of a map of sheaves for the specified linearizations. -/
def EquivariantHom {a : ModObj T.X X} {F H : EquivariantCoherent a}
    (f : F.sheaf ⟶ H.sheaf) : Prop :=
  F.lin.iso.hom ≫ (Scheme.Modules.pullback a.smul.left).map f =
    (Scheme.Modules.pullback (snd T.X X).left).map f ≫ H.lin.iso.hom

/-- Regular scalar multiplication on a module sheaf. -/
def multiply {X : SchemeOver k} (F : X.left.Modules) (c : Γ(X.left, ⊤)) : F ⟶ F where
  val :=
    { app := fun U =>
        let r : X.left.ringCatSheaf.obj.obj U := (X.left.presheaf.map U.unop.leTop.op).hom c
        ModuleCat.ofHom
          { toFun := fun v => r • v
            map_add' := smul_add r
            map_smul' := by
              intro t v
              change r • (t • v) = t • (r • v)
              rw [← mul_smul, ← mul_smul]
              exact congrArg (fun z : X.left.ringCatSheaf.obj.obj U => z • v)
                (mul_comm (G := Γ(X.left, U.unop)) r t) }
      naturality := by
        intro U V i
        ext v
        let rU : X.left.ringCatSheaf.obj.obj U := (X.left.presheaf.map U.unop.leTop.op).hom c
        let rV : X.left.ringCatSheaf.obj.obj V := (X.left.presheaf.map V.unop.leTop.op).hom c
        simp only [ModuleCat.hom_ofHom, ModuleCat.restrictScalars,
          ModuleCat.RestrictScalars.map']
        change rV • (F.val.map i v : F.val.obj V) = (F.val.map i (rU • v) : F.val.obj V)
        rw [PresheafOfModules.map_smul]
        have h : U.unop.leTop.op ≫ i = V.unop.leTop.op := Subsingleton.elim _ _
        have e := (X.left.presheaf.map_comp U.unop.leTop.op i).symm.trans
          (congrArg X.left.presheaf.map h)
        have ev := congrArg (fun f : Γ(X.left, ⊤) ⟶ Γ(X.left, V.unop) => f c) e
        exact congrArg (fun r : X.left.ringCatSheaf.obj.obj V =>
          r • (F.val.map i v : F.val.obj V)) ev.symm }

/-- Pull back the standard coordinate on the multiplicative group. -/
def characterFunction (χ : Character T) : Γ(T.X.left, ⊤) :=
  χ.hom.hom.left.appTop
    ((Scheme.ΓSpecIso _).inv (MonoidAlgebra.of k _
      DiagonalizableGroups.integerGenerator))

/-- The given sheaf with its linearization tensored by a character. -/
def IsTwist {a : ModObj T.X X} (χ : Character T) (F H : EquivariantCoherent a) : Prop :=
  ∃ e : F.sheaf ≅ H.sheaf,
    H.lin.iso.hom =
      (Scheme.Modules.pullback (snd T.X X).left).map e.inv ≫ F.lin.iso.hom ≫
        multiply _ ((fst T.X X).left.appTop (characterFunction χ)) ≫
        (Scheme.Modules.pullback a.smul.left).map e.hom

abbrev CharacterRing (T : GroupScheme k) := MonoidAlgebra ℤ (Character T)

/-- The integral basis element given by a character. -/
def eChar (χ : Character T) : CharacterRing T := MonoidAlgebra.of ℤ _ χ

/-- The relations from exact sequences and from tensoring by a character. -/
def relations (a : ModObj T.X X) : Set (EquivariantCoherent a →₀ CharacterRing T) :=
  let gen := fun F : EquivariantCoherent a => Finsupp.single F (1 : CharacterRing T)
  { r | (∃ (F H K : EquivariantCoherent a) (f : F.sheaf ⟶ H.sheaf)
            (g : H.sheaf ⟶ K.sheaf) (w : f ≫ g = 0),
          EquivariantHom f ∧ EquivariantHom g ∧ (ShortComplex.mk f g w).ShortExact ∧
            r = gen H - gen F - gen K) ∨
        (∃ (χ : Character T) (F H : EquivariantCoherent a),
          IsTwist χ F H ∧ r = gen H - eChar χ • gen F) }

abbrev relationSubmodule (a : ModObj T.X X) :=
  Submodule.span (CharacterRing T) (relations a)

/-- Equivariant coherent Grothendieck group as a module over the character
ring, with the scalar action induced by tensoring by character lines. -/
abbrev GZero (a : ModObj T.X X) := (EquivariantCoherent a →₀ CharacterRing T) ⧸ relationSubmodule a

def classOf {a : ModObj T.X X} (F : EquivariantCoherent a) : GZero a :=
  (relationSubmodule a).mkQ (Finsupp.single F 1)

/-- Pullback comparison for a linearized sheaf along an equivariant morphism.
The equality is on transport over arbitrary schemes. -/
def IsEquivariantPullback {a : ModObj T.X X} {b : ModObj T.X Y} (f : Y ⟶ X)
    (F : EquivariantCoherent a) (H : EquivariantCoherent b)
    (e : Pull f F.sheaf ≅ H.sheaf) : Prop :=
  ∀ (S : SchemeOver k) (t : S ⟶ T.X) (y : S ⟶ Y),
    ∃ h : actOn a t (y ≫ f) = actOn b t y ≫ f,
      (Scheme.Modules.pullback y.left).map e.inv ≫ (pullComp F.sheaf y f).hom ≫
        (transport a F.lin.iso t (y ≫ f)).hom ≫ (pullCongr F.sheaf h).hom ≫
        (pullComp F.sheaf (actOn b t y) f).inv ≫
        (Scheme.Modules.pullback (actOn b t y).left).map e.hom =
      (transport b H.lin.iso t y).hom

/-- An equivariant pushforward is characterized by its equivariant adjunction
counit, with the direct image as its underlying module sheaf. -/
def IsEquivariantPushforward {a : ModObj T.X X} {b : ModObj T.X Y} (f : Y ⟶ X)
    (H : EquivariantCoherent b) (F : EquivariantCoherent a)
    (e : F.sheaf ≅ (Scheme.Modules.pushforward f.left).obj H.sheaf) : Prop :=
  ∀ (S : SchemeOver k) (t : S ⟶ T.X) (y : S ⟶ Y),
    ∃ h : actOn a t (y ≫ f) = actOn b t y ≫ f,
      let c := ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv
        F.sheaf H.sheaf).symm e.hom
      (pullComp F.sheaf y f).hom ≫ (transport a F.lin.iso t (y ≫ f)).hom ≫
        (pullCongr F.sheaf h).hom ≫ (pullComp F.sheaf (actOn b t y) f).inv ≫
        (Scheme.Modules.pullback (actOn b t y).left).map c =
      (Scheme.Modules.pullback y.left).map c ≫ (transport b H.lin.iso t y).hom

def IsEquivariantMap (a : ModObj T.X X) (b : ModObj T.X Y) (f : Y ⟶ X) : Prop :=
  b.smul ≫ f = (𝟙 T.X ⊗ₘ f) ≫ a.smul

/-- Weight of a function for the left action on functions. Thus the pullback
along the action itself multiplies by the inverse character. -/
def HasFunctionWeight (a : ModObj T.X X) (f : Γ(X.left, ⊤)) (χ : Character T) : Prop :=
  a.smul.left.appTop f =
    (fst T.X X).left.appTop (characterFunction χ⁻¹) * (snd T.X X).left.appTop f

/-- An internal grading by a multiplicatively written character group. -/
structure WeightGrading (k : Type u) (Λ : Type u) (V : Type u)
    [Field k] [CommGroup Λ] [AddCommGroup V] [Module k V] where
  piece : Λ → Submodule k V
  internal : DirectSum.IsInternal piece

/-- Multiplication respects the grading on the coordinate algebra. -/
structure RingGrading (k : Type u) (Λ : Type u) (A : Type u)
    [Field k] [CommGroup Λ] [CommRing A] [Algebra k A]
    extends WeightGrading k Λ A where
  one_mem : (1 : A) ∈ piece 1
  mul_mem {i j : Λ} {r s : A} : r ∈ piece i → s ∈ piece j → r * s ∈ piece (i * j)

/-- Module scalar multiplication respects the gradings. -/
structure ModuleGrading {k Λ A : Type u} [Field k] [CommGroup Λ] [CommRing A] [Algebra k A]
    (G : RingGrading k Λ A) (V : Type u)
    [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]
    extends WeightGrading k Λ V where
  smul_mem {i j : Λ} {r : A} {v : V} :
    r ∈ G.piece i → v ∈ piece j → r • v ∈ piece (i * j)

def PreservesWeight {Λ V W : Type u} [CommGroup Λ]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (G : WeightGrading k Λ V) (H : WeightGrading k Λ W) (f : V →ₗ[k] W) : Prop :=
  ∀ (i : Λ) ⦃v : V⦄, v ∈ G.piece i → f v ∈ H.piece i

/-- Comparison of character summands with the basis of the coordinate Hopf algebra. -/
def GradingCoactionComparison : Prop :=
  ∀ {k Λ V : Type u} [Field k] [CommGroup Λ] [AddCommGroup V] [Module k V],
    ∃ e : WeightGrading k Λ V ≃
        RightComodule k (DiagonalizableGroups.groupAlgebra k Λ) V,
      ∀ G i, WeightDecomposition.weightSpace (e G) i = G.piece i

/-- Graded exactness restricts to every character summand. -/
def ExactOnWeights : Prop :=
  ∀ {k Λ V W U : Type u} [Field k] [CommGroup Λ]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup U] [Module k U]
    (G : WeightGrading k Λ V) (H : WeightGrading k Λ W) (J : WeightGrading k Λ U)
    (f : V →ₗ[k] W) (g : W →ₗ[k] U)
    (hf : PreservesWeight G H f) (hg : PreservesWeight H J g),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    ∀ i,
      let fᵢ : G.piece i →ₗ[k] H.piece i := f.restrict (hf i)
      let gᵢ : H.piece i →ₗ[k] J.piece i := g.restrict (hg i)
      Function.Injective fᵢ ∧ Function.Exact fᵢ gᵢ ∧ Function.Surjective gᵢ

/-- A finite-dimensional graded vector space has an integral character.
The character is additive in exact sequences and shifts under a character twist. -/
def GradedCharacterLaws : Prop :=
  ∀ {k Λ : Type u} [Field k] [CommGroup Λ],
    ∃ ch : ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V],
        WeightGrading k Λ V → MonoidAlgebra ℤ Λ,
      (∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V]
        (G : WeightGrading k Λ V) (i : Λ), (ch V G).coeff i = (Module.finrank k (G.piece i) : ℤ)) ∧
      (∀ {V W U : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
        [AddCommGroup W] [Module k W] [Module.Finite k W]
        [AddCommGroup U] [Module k U] [Module.Finite k U]
        (G : WeightGrading k Λ V) (H : WeightGrading k Λ W) (J : WeightGrading k Λ U)
        (f : V →ₗ[k] W) (g : W →ₗ[k] U),
        PreservesWeight G H f → PreservesWeight H J g →
        Function.Injective f → Function.Exact f g → Function.Surjective g →
        ch W H = ch V G + ch U J) ∧
      (∀ {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
        (G H : WeightGrading k Λ V) (χ : Λ),
        (∀ ψ, H.piece (χ * ψ) = G.piece ψ) →
        ch V H = MonoidAlgebra.of ℤ Λ χ * ch V G)

/-- Finite presentation specializes the affine comparison on Noetherian charts. -/
def AffineFinitePresentation : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (F : (Spec R).Modules) [F.IsQuasicoherent],
    F.IsFinitePresentation ↔ Module.FinitePresentation R ((moduleSpecΓFunctor (R := R)).obj F)

/-- Restriction of a linearization along an equivariant scheme map,
with its transport over arbitrary test schemes. -/
def LinearizationPullback : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X Y : SchemeOver k}
    {a : ModObj T.X X} {b : ModObj T.X Y} (f : Y ⟶ X),
    IsEquivariantMap a b f → ∀ {F : X.left.Modules} (L : Linearization a F),
      ∃ H : Linearization b (Pull f F),
        ∀ (Z : SchemeOver k) (t : Z ⟶ T.X) (y : Z ⟶ Y),
          ∃ h : actOn a t (y ≫ f) = actOn b t y ≫ f,
            (transport b H.iso t y).hom ≫ (pullComp F (actOn b t y) f).hom =
              (pullComp F y f).hom ≫ (transport a L.iso t (y ≫ f)).hom ≫
                (pullCongr F h).hom

section Coaction

open _root_.LinearAlgebraicGroups.WeightDecomposition (tensorCoactionMap)
open DiagonalizableGroups (groupAlgebra)

variable {Λ A V : Type u} [CommGroup Λ] [CommRing A] [Algebra k A]
  [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]

/-- Linearization of the scalar action over the ground field. -/
def scalarTensor : A ⊗[k] V →ₗ[k] V :=
  TensorProduct.lift (Algebra.lsmul k k V : A →ₐ[k] Module.End k V).toLinearMap

/-- The coaction preserves the module multiplication. This is the
semilinearity relation over the coordinate-ring coaction. -/
def IsModuleCoaction (ρ : RightComodule k (groupAlgebra k Λ) A)
    (δ : RightComodule k (groupAlgebra k Λ) V) : Prop :=
  δ.coaction ∘ₗ scalarTensor =
    scalarTensor.rTensor (MonoidAlgebra k Λ) ∘ₗ tensorCoactionMap ρ δ

/-- The coordinate coaction preserves the ring unit and multiplication. -/
def IsRingCoaction (ρ : RightComodule k (groupAlgebra k Λ) A) : Prop :=
  ρ.coaction 1 = (1 : A) ⊗ₜ[k] (1 : MonoidAlgebra k Λ) ∧ IsModuleCoaction ρ ρ

def AlgebraComoduleComparison : Prop :=
  ∀ {k Λ A : Type u} [Field k] [CommGroup Λ] [CommRing A] [Algebra k A],
    ∃ (E : RingGrading k Λ A ≃ {ρ : RightComodule k (groupAlgebra k Λ) A // IsRingCoaction ρ}),
      (∀ G i, WeightDecomposition.weightSpace (E G).val i = G.piece i) ∧
      ∀ (G : RingGrading k Λ A) (V : Type u) [AddCommGroup V]
        [Module A V] [Module k V] [IsScalarTower k A V],
        ∃ e : ModuleGrading G V ≃
            {δ : RightComodule k (groupAlgebra k Λ) V // IsModuleCoaction (E G).val δ},
          ∀ H i, WeightDecomposition.weightSpace (e H).val i = H.piece i

end Coaction

/-- The pullback of a top section along a scheme morphism. -/
def pullSection {U V : Scheme.{u}} (f : V ⟶ U) (F : U.Modules)
    (s : Γ(F, ⊤)) : Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op ⊤) s

/-- The standard base change map on arbitrary quasi-coherent coefficients,
specified on the global sections of the associated sheaf. -/
def AffineSectionBaseChange : Prop :=
  ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) (F : (Spec R).Modules) [F.IsQuasicoherent],
    let M := (moduleSpecΓFunctor (R := R)).obj F
    ∃ e : (moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj F) ≅
        (ModuleCat.extendScalars.{u,u,u} φ.hom).obj M,
      ∀ s : M, e.hom (pullSection (Spec.map φ) F s) =
        (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M s

/-- Exactness of the global-section functor on short exact sequences of
quasi-coherent sheaves over an affine scheme. -/
def AffineSectionsExact : Prop :=
  ∀ {R : CommRingCat.{u}} (K : ShortComplex (Spec R).Modules)
    [K.X₁.IsQuasicoherent] [K.X₂.IsQuasicoherent] [K.X₃.IsQuasicoherent],
    K.ShortExact →
      Function.Injective ((moduleSpecΓFunctor (R := R)).map K.f) ∧
      Function.Exact ((moduleSpecΓFunctor (R := R)).map K.f)
        ((moduleSpecΓFunctor (R := R)).map K.g) ∧
      Function.Surjective ((moduleSpecΓFunctor (R := R)).map K.g)

/-- The weight is tested on the full product of the torus and the scheme.
The covariant transport multiplies a pulled-back section of weight χ by χ. -/
def HasSectionWeight {a : ModObj T.X X} {F : X.left.Modules}
    (L : Linearization a F) (s : Γ(F, ⊤)) (χ : Character T) : Prop :=
  L.iso.hom.val.app (op ⊤) (pullSection (snd T.X X).left F s) =
    (fst T.X X).left.appTop (characterFunction χ) • pullSection a.smul.left F s

abbrev affineScheme (R : TestAlgebra k) : SchemeOver k := (testSpec k).obj (op R)

abbrev affineRing (R : TestAlgebra k) : CommRingCat.{u} := CommRingCat.of R

abbrev affineSections (R : TestAlgebra k) :
    (affineScheme R).left.Modules ⥤ ModuleCat.{u} R :=
  moduleSpecΓFunctor (R := affineRing R)

instance moduleOverBaseField (R : TestAlgebra k) (M : ModuleCat.{u} R) : Module k M :=
  Module.compHom M (algebraMap k R)

instance moduleOverBaseField_tower (R : TestAlgebra k) (M : ModuleCat.{u} R) :
    IsScalarTower k R M :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- A split torus is a finite power of the multiplicative group. -/
def IsSplitTorus (T : GroupScheme k) : Prop :=
  ∃ r : ℕ, Nonempty (T ≅
    (StandardGroups.multiplicativePowerGroup k (ULift.{u} (Fin r))).val)

/-- The character basis consists of the pullbacks of the standard
multiplicative coordinate along the actual characters of the torus. -/
def CoordinateCharacters : Prop :=
  ∀ {k : Type u} [Field k] (T : GroupScheme k), IsSplitTorus T →
    ∃ e : MonoidAlgebra k (Character T) ≃+* Γ(T.X.left, ⊤),
      ∀ χ, e (MonoidAlgebra.of k _ χ) = characterFunction χ

def AffineGrading (R : TestAlgebra k) (a : ModObj T.X (affineScheme R)) :
    Type u :=
  { G : RingGrading k (Character T) R // ∀ χ r,
    r ∈ G.piece χ ↔ HasFunctionWeight a ((Scheme.ΓSpecIso (affineRing R)).inv r) χ }

def AffineModuleComparison (R : TestAlgebra k) (a : ModObj T.X (affineScheme R))
    (G : AffineGrading R a) :=
  ∀ (F : (affineScheme R).left.Modules), F.IsQuasicoherent →
    Linearization a F ≃ ModuleGrading (k := k) (Λ := Character T) (A := ↥R) G.val ((affineSections R).obj F)

/-- The comparison uses the affine global sections and the actual universal
linearization, and identifies morphisms on these specific objects. -/
def EquivariantAffineComparison : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k}, IsSplitTorus T →
    ∀ (R : TestAlgebra k) (a : ModObj T.X (affineScheme R)),
      ∃ (G : AffineGrading R a) (E : AffineModuleComparison R a G),
      (∀ (F : (affineScheme R).left.Modules) (hF : F.IsQuasicoherent),
        Nonempty (tilde ((affineSections R).obj F) ≅ F) ∧
        ∀ (L : Linearization a F) (χ : Character T) (s : (affineSections R).obj F),
          s ∈ (E F hF L).piece χ ↔ HasSectionWeight L s χ) ∧
      (∀ (F H : (affineScheme R).left.Modules)
        (hF : F.IsQuasicoherent) (hH : H.IsQuasicoherent)
        (L : Linearization a F) (K : Linearization a H) (f : F ⟶ H),
        IsLinearizedMap L K f ↔
          ∀ χ s, s ∈ (E F hF L).piece χ → (affineSections R).map f s ∈ (E H hH K).piece χ) ∧
      (∀ (F : (affineScheme R).left.Modules) (hF : F.IsQuasicoherent)
        (L K : Linearization a F) (χ : Character T),
        K.iso.hom = L.iso.hom ≫ multiply _ ((fst T.X (affineScheme R)).left.appTop
          (characterFunction χ)) →
        ∀ ψ, (E F hF K).piece (χ * ψ) = (E F hF L).piece ψ)

/-- The nonvanishing locus of an eigenfunction is preserved by the action. -/
def HomogeneousBasicOpenInvariant : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k}
    (a : ModObj T.X X) (r : Γ(X.left, ⊤)) (χ : Character T),
    HasFunctionWeight a r χ →
    a.smul.left ⁻¹ᵁ (X.left.basicOpen r) = (snd T.X X).left ⁻¹ᵁ (X.left.basicOpen r)

abbrev openSubscheme (X : SchemeOver k) (U : X.left.Opens) : SchemeOver k :=
  Over.mk (U.ι ≫ X.hom)

abbrev openEmbedding (X : SchemeOver k) (U : X.left.Opens) : openSubscheme X U ⟶ X :=
  Over.homMk U.ι rfl

/-- Invariant open subschemes admit the restricted action. -/
def InvariantOpenAction : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k} {X : SchemeOver k}
    (a : ModObj T.X X) (U : X.left.Opens),
    a.smul.left ⁻¹ᵁ U = (snd T.X X).left ⁻¹ᵁ U →
    ∃ b : ModObj T.X (openSubscheme X U), IsEquivariantMap a b (openEmbedding X U)

set_option backward.isDefEq.respectTransparency false in
/-- On an equivariant affine open, the scalar extension with its homogeneous
generators computes the grading of the restricted sheaf. -/
def AffineGradingRestriction : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k}, IsSplitTorus T →
    ∀ {R S : TestAlgebra k} (φ : R ⟶ S),
      let f := (testSpec k).map φ.op
      ∀ {a : ModObj T.X (affineScheme R)} {b : ModObj T.X (affineScheme S)},
        IsOpenImmersion f.left → IsEquivariantMap a b f →
        ∀ (F : (affineScheme R).left.Modules), F.IsQuasicoherent →
          ∀ L : Linearization a F,
            let M := (affineSections R).obj F
            let ψ : R →+* S := φ.hom.toRingHom
            ∃ (K : Linearization b (Pull f F))
              (e : (affineSections S).obj (Pull f F) ≅
                (ModuleCat.extendScalars.{u,u,u} ψ).obj M),
              (Pull f F).IsQuasicoherent ∧
              (∀ (Z : SchemeOver k) (t : Z ⟶ T.X) (y : Z ⟶ affineScheme S),
                ∃ h : actOn a t (y ≫ f) = actOn b t y ≫ f,
                  (transport b K.iso t y).hom ≫ (pullComp F (actOn b t y) f).hom =
                    (pullComp F y f).hom ≫ (transport a L.iso t (y ≫ f)).hom ≫
                      (pullCongr F h).hom) ∧
              (∀ s : M, e.hom (pullSection f.left F s) =
                (ModuleCat.extendRestrictScalarsAdj ψ).unit.app M s) ∧
              (∀ (χ : Character T) (s : M), HasSectionWeight L s χ →
                HasSectionWeight K (pullSection f.left F s) χ) ∧
              (∀ (χ δ : Character T) (r : S) (s : M),
                HasFunctionWeight b ((Scheme.ΓSpecIso (affineRing S)).inv r) δ →
                HasSectionWeight L s χ →
                HasSectionWeight K
                  (((Scheme.ΓSpecIso (affineRing S)).inv r) • pullSection f.left F s) (δ * χ))

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary fraction formula on a homogeneous principal open, applied to
sections homogeneous before restriction. -/
def AffineGradingPrincipalOpen : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k}, IsSplitTorus T →
    ∀ {R : TestAlgebra k} (r : R)
      (a : ModObj T.X (affineScheme R)),
      let S : TestAlgebra k := .of k (Localization.Away r)
      let φ : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (Localization.Away r))
      let f := (testSpec k).map φ.op
      ∀ (b : ModObj T.X (affineScheme S)),
        IsEquivariantMap a b f →
        ∀ (δ : Character T),
          HasFunctionWeight a ((Scheme.ΓSpecIso (affineRing R)).inv r) δ →
          ∀ (F : (affineScheme R).left.Modules), F.IsQuasicoherent →
            ∀ L : Linearization a F, ∃ K : Linearization b (Pull f F),
              (∀ (Z : SchemeOver k) (t : Z ⟶ T.X) (y : Z ⟶ affineScheme S),
                ∃ h : actOn a t (y ≫ f) = actOn b t y ≫ f,
                  (transport b K.iso t y).hom ≫ (pullComp F (actOn b t y) f).hom =
                    (pullComp F y f).hom ≫ (transport a L.iso t (y ≫ f)).hom ≫
                      (pullCongr F h).hom) ∧
              ∀ (χ : Character T) (s : (affineSections R).obj F) (n : ℕ),
                HasSectionWeight L s χ →
                HasSectionWeight K
                  (((Scheme.ΓSpecIso (affineRing S)).inv
                    (IsLocalization.Away.invSelf (S := Localization.Away r) r ^ n)) •
                    pullSection f.left F s)
                  ((δ⁻¹) ^ n * χ)

/-- At a rational point the trivial action is the projection. -/
abbrev pointAction (T : GroupScheme k) : ModObj T.X (affineScheme (CommAlgCat.of k k)) :=
  ModObj.trivialAction _ _

/-- The class module of the rational point, with normalization on the
structure sheaf and the character of an equivariant exact sequence. -/
def PointCharacterComparison : Prop :=
  ∀ {k : Type u} [Field k] (T : GroupScheme k), IsSplitTorus T →
    let R := CommAlgCat.of k k
    let a := pointAction T
    ∃ (G : AffineGrading R a) (E : AffineModuleComparison R a G)
      (e : GZero a ≃ₗ[CharacterRing T] CharacterRing T),
      (∀ (F : EquivariantCoherent a) (χ : Character T) (s : (affineSections R).obj F.sheaf),
        s ∈ (E F.sheaf F.coherent.exists_quasicoherentData.choose.isQuasicoherent F.lin).piece χ ↔
          HasSectionWeight F.lin s χ) ∧
      (∀ F χ, (e (classOf F)).coeff χ =
        (Module.finrank k ((E F.sheaf (F.coherent.exists_quasicoherentData.choose.isQuasicoherent) F.lin).piece χ) : ℤ)) ∧
      (∀ (F : EquivariantCoherent a) (_i : tilde (ModuleCat.of k k) ≅ F.sheaf),
        F.lin.iso.hom = 𝟙 _ → e (classOf F) = 1) ∧
      (∀ {F H K : EquivariantCoherent a} (f : F.sheaf ⟶ H.sheaf) (g : H.sheaf ⟶ K.sheaf)
        (w : f ≫ g = 0), EquivariantHom f → EquivariantHom g →
        (ShortComplex.mk f g w).ShortExact →
        e (classOf H) = e (classOf F) + e (classOf K))


end

end LinearAlgebraicGroups.Specs.EquivariantAffineModules
