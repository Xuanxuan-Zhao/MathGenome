import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.EquivariantAffineModules
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.OrderedCechComparison
import Mathlib.Algebra.Homology.HomologySequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

noncomputable section

universe u

namespace LinearAlgebraicGroups.Specs.CoherentCohomologyAlgebraBaseChange

open FlagCohomology

variable {k : Type u} [Field k] (R : TestAlgebra k) (X : SchemeOver k)

/-- The comparison sends the scalar extension of an original class via the
actual unit of pullback and pushforward. -/
def IsBaseChange {F : X.left.Modules} (n : ℕ)
    (b : (extendToAlgebra (k := k) (K := R)).obj ((cohomology X n).obj F) ⟶
      (cohomology ((extendScheme R).obj X) n).obj
        ((Scheme.Modules.pullback (extensionProjection R X)).obj F)) : Prop :=
  IsCohomologyMap (algebraMap k R) (extensionProjection R X) (extensionProjection_over R X)
    ((Scheme.Modules.pullbackPushforwardAdjunction (extensionProjection R X)).unit.app F) n
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ b)

/-- Scalar extension of actual cohomology with arbitrary quasi-coherent
coefficients on a scheme with a finite affine-intersection cover. -/
def BaseChange : Prop :=
  ∀ {k : Type u} [Field k] (X : SchemeOver k), HasFiniteAffineCover X →
    ∀ (R : TestAlgebra k) (F : X.left.Modules) [F.IsQuasicoherent] (n : ℕ),
    ∃ b : (extendToAlgebra (k := k) (K := R)).obj ((cohomology X n).obj F) ≅
        (cohomology ((extendScheme R).obj X) n).obj
          ((Scheme.Modules.pullback (extensionProjection R X)).obj F),
      IsBaseChange R X n b.hom

/-- Naturality in morphisms of the actual sheaves of modules. -/
def BaseChangeNaturality : Prop :=
  ∀ {k : Type u} [Field k] (X : SchemeOver k) (R : TestAlgebra k) {F G : X.left.Modules}
    (a : F ⟶ G) (n : ℕ) {bF bG},
    IsBaseChange R X (F := F) n bF → IsBaseChange R X (F := G) n bG →
    (extendToAlgebra (k := k) (K := R)).map ((cohomology X n).map a) ≫ bG =
      bF ≫ (cohomology ((extendScheme R).obj X) n).map
        ((Scheme.Modules.pullback (extensionProjection R X)).map a)


/-- The coefficient map for a morphism of scalar extensions. It uses the
functoriality of the ordinary pullback of sheaves of modules. -/
def towerCoefficient {k : Type u} [Field k] {R S : TestAlgebra k} {X : SchemeOver k}
    (F : X.left.Modules) (q : ((extendScheme S).obj X).left ⟶ ((extendScheme R).obj X).left)
    (hq : q ≫ extensionProjection R X = extensionProjection S X) :
    (Scheme.Modules.pullback (extensionProjection R X)).obj F ⟶
      (Scheme.Modules.pushforward q).obj ((Scheme.Modules.pullback (extensionProjection S X)).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _
    (((Scheme.Modules.pullbackComp q (extensionProjection R X)).app F ≪≫
      (Scheme.Modules.pullbackCongr hq).app F).hom)

/-- Compatibility with the actual derived pullback along a flat map of
test algebras. Here the second pullback has its own injective-lift comparison. -/
def FlatBaseChangeTower : Prop :=
  ∀ {k : Type u} [Field k] (X : SchemeOver k) {R S : TestAlgebra k} (j : R ⟶ S)
    (q : ((extendScheme S).obj X).left ⟶ ((extendScheme R).obj X).left) [Flat q]
    (hq : q ≫ extensionProjection R X = extensionProjection S X)
    (wq : q ≫ ((extendScheme R).obj X).hom =
      ((extendScheme S).obj X).hom ≫ Spec.map (CommRingCat.ofHom j.hom.toRingHom))
    (F : X.left.Modules) (n : ℕ) {bR bS m},
    IsBaseChange R X (F := F) n bR → IsBaseChange S X (F := F) n bS →
    IsCohomologyMap j.hom.toRingHom q wq (towerCoefficient F q hq) n m →
    ∀ x : (cohomology X n).obj F,
      m ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ bR x) =
        (ModuleCat.extendRestrictScalarsAdj (algebraMap k S)).homEquiv _ _ bS x


/-- The ordered Čech comparison comes from the two augmentations of the
actual injective resolution. -/
def IsResolutionComparison (c : OrderedCechComparison.ComparisonFamily.{u}) : Prop :=
  ∀ {A : Type u} [CommRing A] (X : SchemeOverRing A)
    {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens)
    (hU : (⨆ i, U i) = ⊤) (F : X.left.Modules)
    (hF : OrderedCechComparison.IntersectionAcyclic U F) (J : InjectiveResolution F) (n : ℕ),
    OrderedCechComparison.IsComparisonFromResolution U J n (c X U hU F hF n)

/-- The map between the actual cohomology groups for any morphism of test
algebras. Its geometric normalization is pullback of sections on the
induced cover. -/
def BaseChangeTower : Prop :=
  ∃ c : OrderedCechComparison.ComparisonFamily.{u},
    IsResolutionComparison c ∧
    ∀ {k : Type u} [Field k] (X : SchemeOver k) {R S : TestAlgebra k} (j : R ⟶ S)
      (q : ((extendScheme S).obj X).left ⟶ ((extendScheme R).obj X).left)
      (hq : q ≫ extensionProjection R X = extensionProjection S X)
      (wq : q ≫ ((extendScheme R).obj X).hom =
        ((extendScheme S).obj X).hom ≫ Spec.map (CommRingCat.ofHom j.hom.toRingHom))
      (F : X.left.Modules) [F.IsQuasicoherent] {I : Type u} [LinearOrder I] [Fintype I]
      (U : I → X.left.Opens) (hU : (⨆ i, U i) = ⊤)
      (_ : ∀ (n : ℕ) (i : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen U i))
      (n : ℕ) {bR bS},
      IsBaseChange R X (F := F) n bR → IsBaseChange S X (F := F) n bS →
      let p := extensionProjection R X
      let XR := (extendScheme R).obj X
      let XS := (extendScheme S).obj X
      let G := (Scheme.Modules.pullback p).obj F
      let H := (Scheme.Modules.pullback (extensionProjection S X)).obj F
      let V := OrderedCechComparison.pullbackCover p U
      let W := OrderedCechComparison.pullbackCover q V
      let hV := p.iSup_preimage_eq_top hU
      let hW := q.iSup_preimage_eq_top hV
      ∃ (hG : OrderedCechComparison.IntersectionAcyclic V G)
        (hH : OrderedCechComparison.IntersectionAcyclic W H),
        let Q := ModuleCat.restrictScalars.{u} j.hom.toRingHom
        let t := OrderedCechComparison.cechPullback j.hom.toRingHom q wq V
          (towerCoefficient F q hq)
        let d := (c XR V hV G hG n).hom ≫ HomologicalComplex.homologyMap t n ≫
          (OrderedCechComparison.restrictCohomologyIso j.hom.toRingHom
            (OrderedCechComparison.SheafCech W H) n).inv ≫ Q.map (c XS W hW H hH n).inv
        ∀ x : (cohomology X n).obj F,
          d ((ModuleCat.extendRestrictScalarsAdj (algebraMap k R)).homEquiv _ _ bR x) =
            (ModuleCat.extendRestrictScalarsAdj (algebraMap k S)).homEquiv _ _ bS x


open OrderedCechComparison (IntersectionAcyclic pullbackCover sheafCechFunctor)

/-- Connecting homomorphisms in derived cohomology computed using the
ordered cover and its Čech short exact sequence. -/
def cechConnecting {A : Type u} [CommRing A] (X : SchemeOverRing A)
    {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens)
    (hU : (⨆ i, U i) = ⊤) (S : ShortComplex X.left.Modules)
    (h₁ : IntersectionAcyclic U S.X₁) (h₃ : IntersectionAcyclic U S.X₃)
    (c : OrderedCechComparison.ComparisonFamily.{u})
    (hS : (S.map (sheafCechFunctor U)).ShortExact) (n : ℕ) :
    (cohomology X n).obj S.X₃ ⟶ (cohomology X (n + 1)).obj S.X₁ :=
  (c X U hU S.X₃ h₃ n).hom ≫ hS.δ n (n + 1) rfl ≫ (c X U hU S.X₁ h₁ (n + 1)).inv

/-- Naturality of the connecting maps for the actual cohomology maps when
the target cover is induced from the source cover. -/
def MatchedCechConnecting : Prop :=
  ∃ c : OrderedCechComparison.ComparisonFamily.{u},
    IsResolutionComparison c ∧
    ∀ {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A} {Y : SchemeOverRing B}
      (φ : A →+* B) (f : Y.left ⟶ X.left)
      (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
      {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens)
      (hU : (⨆ i, U i) = ⊤)
      (_ : ∀ (n : ℕ) (i : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen U i))
      (_ : ∀ (n : ℕ) (i : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen (pullbackCover f U) i))
      (S : ShortComplex X.left.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
      [S.X₃.IsQuasicoherent] (_ : S.ShortExact)
      (T : ShortComplex Y.left.Modules) [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent]
      [T.X₃.IsQuasicoherent] (_ : T.ShortExact)
      (α : S ⟶ T.map (Scheme.Modules.pushforward f)),
      let V := pullbackCover f U
      let hV := f.iSup_preimage_eq_top hU
      ∃ (h₁ : IntersectionAcyclic U S.X₁) (h₃ : IntersectionAcyclic U S.X₃)
        (g₁ : IntersectionAcyclic V T.X₁) (g₃ : IntersectionAcyclic V T.X₃)
        (s : (S.map (sheafCechFunctor U)).ShortExact)
        (t : (T.map (sheafCechFunctor V)).ShortExact),
        ∀ (n : ℕ) {m₁ m₃},
          IsCohomologyMap φ f w α.τ₁ (n + 1) m₁ →
          IsCohomologyMap φ f w α.τ₃ n m₃ →
          cechConnecting X U hU S h₁ h₃ c s n ≫ m₁ =
            m₃ ≫ (ModuleCat.restrictScalars.{u} φ).map (cechConnecting Y V hV T g₁ g₃ c t n)

/-- The connecting arrows between the actual right-derived global sections. -/
abbrev ConnectingMaps {A : Type u} [CommRing A] (X : SchemeOverRing A)
    (S : ShortComplex X.left.Modules) :=
  ∀ n : ℕ, (cohomology X n).obj S.X₃ ⟶ (cohomology X (n + 1)).obj S.X₁

/-- Exactness of the cohomology sequence using the ordinary derived maps
of the coefficient morphisms. -/
def IsLongExactSequence {A : Type u} [CommRing A] (X : SchemeOverRing A)
    (S : ShortComplex X.left.Modules) (d : ConnectingMaps X S) : Prop :=
  Function.Injective ((cohomology X 0).map S.f) ∧
  (∀ n, Function.Exact ((cohomology X n).map S.f) ((cohomology X n).map S.g)) ∧
  (∀ n, Function.Exact ((cohomology X n).map S.g) (d n)) ∧
  (∀ n, Function.Exact (d n) ((cohomology X (n + 1)).map S.f))

/-- The same connecting arrows are computed by every finite ordered affine
cover with affine intersections, using the injective-resolution comparison. -/
def ComputesConnectingUsingCech (c : OrderedCechComparison.ComparisonFamily.{u})
    {A : Type u} [CommRing A] (X : SchemeOverRing A)
    (S : ShortComplex X.left.Modules) (d : ConnectingMaps X S) : Prop :=
  ∀ {I : Type u} [LinearOrder I] [Fintype I] (U : I → X.left.Opens)
      (hU : (⨆ i, U i) = ⊤),
    (∀ (n : ℕ) (e : Fin (n + 1) ↪o I), IsAffineOpen (tupleOpen U e)) →
    ∃ (h₁ : IntersectionAcyclic U S.X₁) (h₃ : IntersectionAcyclic U S.X₃)
      (s : (S.map (sheafCechFunctor U)).ShortExact),
      ∀ n, d n = cechConnecting X U hU S h₁ h₃ c s n

/-- An affine pullback with a compatible map of coefficients commutes with
the connecting arrows. The two sequences may use different affine covers. -/
def ConnectingNaturality (c : OrderedCechComparison.ComparisonFamily.{u}) : Prop :=
  ∀ {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A} {Y : SchemeOverRing B}
    (φ : A →+* B) (f : Y.left ⟶ X.left) [IsAffineHom f]
    (w : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    (_ : HasFiniteAffineCover X)
    {S : ShortComplex X.left.Modules} {T : ShortComplex Y.left.Modules}
    (α : S ⟶ T.map (Scheme.Modules.pushforward f))
    {d : ConnectingMaps X S} {e : ConnectingMaps Y T},
    ComputesConnectingUsingCech c X S d → ComputesConnectingUsingCech c Y T e →
    ∀ (n : ℕ) {m₁ m₃},
      IsCohomologyMap φ f w α.τ₁ (n + 1) m₁ → IsCohomologyMap φ f w α.τ₃ n m₃ →
      d n ≫ m₁ = m₃ ≫ (ModuleCat.restrictScalars.{u} φ).map (e n)

/-- The scalar extension isomorphisms identify the connecting arrows by
extension of scalars along the structure map of the test algebra. -/
def BaseChangeConnecting (c : OrderedCechComparison.ComparisonFamily.{u}) : Prop :=
  ∀ {k : Type u} [Field k] (X : SchemeOver k) (_ : HasFiniteAffineCover X)
    (R : TestAlgebra k) (S : ShortComplex X.left.Modules),
    let Y := (extendScheme R).obj X
    let T := S.map (Scheme.Modules.pullback (extensionProjection R X))
    ∀ {d : ConnectingMaps X S} {e : ConnectingMaps Y T},
      ComputesConnectingUsingCech c X S d → ComputesConnectingUsingCech c Y T e →
      ∀ (n : ℕ) {b₁ b₃},
        IsBaseChange R X (F := S.X₁) (n + 1) b₁ → IsBaseChange R X (F := S.X₃) n b₃ →
        (extendToAlgebra (k := k) (K := R)).map (d n) ≫ b₁ = b₃ ≫ e n

section Linearized

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open EquivariantAffineModules (Linearization IsLinearizedMap Pull)

/-- Pullback on actual cohomology followed by the map of coefficient sheaves
for a morphism over the same field. -/
def IsOverCohomologyMap {k : Type u} [Field k] {X Y : SchemeOver k} (f : Y ⟶ X)
    {F : X.left.Modules} {G : Y.left.Modules} (α : Pull f F ⟶ G) (n : ℕ)
    (m : (cohomology X n).obj F ⟶ (cohomology Y n).obj G) : Prop :=
  IsCohomologyMap (RingHom.id k) f.left (by
    rw [show Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _ from Spec.map_id _,
      Category.comp_id]
    exact Over.w f)
    ((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv F G α) n
    (m ≫ (ModuleCat.restrictScalarsId'App (RingHom.id k) rfl ((cohomology Y n).obj G)).inv)

/-- The connecting square for every map induced by the two specified maps of
pulled-back coefficients. -/
def ConnectsForOverMap {k : Type u} [Field k] {X Y : SchemeOver k} (f : Y ⟶ X)
    {S : ShortComplex X.left.Modules} {T : ShortComplex Y.left.Modules}
    (α₁ : Pull f S.X₁ ⟶ T.X₁) (α₃ : Pull f S.X₃ ⟶ T.X₃)
    (d : ConnectingMaps X S) (e : ConnectingMaps Y T) : Prop :=
  (∀ n : ℕ, (∃ m₁, IsOverCohomologyMap f α₁ (n + 1) m₁) ∧
    (∃ m₃, IsOverCohomologyMap f α₃ n m₃)) ∧
  ∀ (n : ℕ) {m₁ m₃}, IsOverCohomologyMap f α₁ (n + 1) m₁ →
    IsOverCohomologyMap f α₃ n m₃ → d n ≫ m₁ = m₃ ≫ e n

/-- A short exact sequence of linearized coefficients uses one target
connecting map for the action and the projection with transport. -/
def LinearizedConnecting (c : OrderedCechComparison.ComparisonFamily.{u}) : Prop :=
  ∀ {k : Type u} [Field k] (H : GroupScheme k) [IsAffine H.X.left]
    (X : SchemeOver k), HasFiniteAffineCover X →
    ∀ (a : ModObj H.X X) (S : ShortComplex X.left.Modules) [S.X₁.IsQuasicoherent]
      [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent], S.ShortExact →
      ∀ (l₁ : Linearization a S.X₁) (l₂ : Linearization a S.X₂) (l₃ : Linearization a S.X₃),
        IsLinearizedMap l₁ l₂ S.f → IsLinearizedMap l₂ l₃ S.g →
        let Y := H.X ⊗ X
        let T := S.map (Scheme.Modules.pullback a.smul.left)
        ∃ (d : ConnectingMaps X S) (e : ConnectingMaps Y T),
          IsLongExactSequence X S d ∧ IsLongExactSequence Y T e ∧
          ComputesConnectingUsingCech c X S d ∧ ComputesConnectingUsingCech c Y T e ∧
          ConnectsForOverMap (snd H.X X) l₁.iso.hom l₃.iso.hom d e ∧
          ConnectsForOverMap a.smul (𝟙 _) (𝟙 _) d e

end Linearized

/-- Coherent cohomology has cover-independent connecting maps, compatible
with actual cohomology pullbacks and with the scalar extension comparison. -/
def CohomologyConnecting : Prop :=
  ∃ c : OrderedCechComparison.ComparisonFamily.{u}, IsResolutionComparison c ∧
    (∀ {A : Type u} [CommRing A] (X : SchemeOverRing A), HasFiniteAffineCover X →
      ∀ (S : ShortComplex X.left.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
        [S.X₃.IsQuasicoherent], S.ShortExact →
        ∃ d : ConnectingMaps X S,
          IsLongExactSequence X S d ∧ ComputesConnectingUsingCech c X S d) ∧
    ConnectingNaturality c ∧ BaseChangeConnecting c ∧ LinearizedConnecting c

end LinearAlgebraicGroups.Specs.CoherentCohomologyAlgebraBaseChange
