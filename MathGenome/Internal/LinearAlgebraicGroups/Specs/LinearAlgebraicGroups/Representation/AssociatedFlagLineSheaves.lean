import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagLineBundle
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RelativeFrobenius
import Mathlib.AlgebraicGeometry.Modules.Sheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonObj Polynomial

universe u

namespace LinearAlgebraicGroups.Specs.AssociatedFlagLineSheaves

open FlagLineBundle QuotientEmbedding

noncomputable section

variable {k : Type u} [Field k]

/-- The section associated with a map to the affine line, evaluated at the
polynomial coordinate. -/
def lineCoordinate {T : SchemeOver k} (f : T ⟶ affineLine k) : Γ(T.left, ⊤) :=
  f.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X)

/-- A section of the E04 total space over the given open. -/
def geometricSections {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    (L : AssociatedBundle Q a p χ) (U : Q.scheme.left.Opens) :=
  {s : U.toScheme ⟶ L.total.left // s ≫ L.projection.left = U.ι}

/-- The given open of a scheme over the ground field as a scheme over that field. -/
abbrev openOver (Y : SchemeOver k) (U : Y.left.Opens) : SchemeOver k :=
  Over.mk (U.ι ≫ Y.hom)

/-- A lift of an open chart to the original quotient torsor. -/
structure TorsorLift {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (U : Q.scheme.left.Opens) where
  lift : openOver Q.scheme U ⟶ G.val.X
  lifts : lift.left ≫ Q.projection.left = U.ι

/-- The pushforward of the structure module, with scalars through the given morphism. -/
abbrev functionsOver {X Y : Scheme.{u}} (q : X ⟶ Y) : Y.Modules :=
  (Scheme.Modules.pushforward q).obj (SheafOfModules.unit X.ringCatSheaf)

/-- Restrict a regular function on an open along a map whose image lies there. -/
def evalOn {X T : Scheme.{u}} (f : T ⟶ X) (U : X.Opens)
    (h : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U) (r : Γ(X, U)) : Γ(T, ⊤) :=
  f.appLE U ⊤ h r

/-- The value of the multiplicative character at a scheme-valued point as
an everywhere invertible regular function on the test scheme. -/
def characterFunction {H : GroupScheme k} (ψ : CharacterDescent.Character H)
    {T : SchemeOver k} (b : T ⟶ H.X) : Γ(T.left, ⊤) :=
  let A := DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters
  (b ≫ ψ.hom.hom).left.appTop
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv
      (MonoidAlgebra.of k _ DiagonalizableGroups.integerGenerator))

/-- The regular functions with inverse-character covariance on a quotient open.
The two sides are compared on the restriction of the torsor relation
`(g,b) ↦ (g,gb)`. -/
def IsCovariantOn {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (p : BorelProjection P)
    (χ : CharacterDescent.Character P.torus.group) (U : Q.scheme.left.Opens)
    (f : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)) : Prop :=
  ∀ (T : SchemeOver k) (g : T ⟶ G.val.X) (b : T ⟶ P.negative.group.X)
    (h : (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U))
    (h' : (⊤ : T.left.Opens) ≤
      (g * (b ≫ P.negative.inclusion.hom.hom)).left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U)),
    evalOn (g * (b ≫ P.negative.inclusion.hom.hom)).left _ h' f =
      characterFunction (p.projection ≫ χ) b⁻¹ * evalOn g.left _ h f

/-- A realization of the actual associated sheaf inside the pushforward of
regular functions. The geometric-section comparison keeps the given E04
trivialization, so evaluation is fixed on every open. -/
structure SectionRealization {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    (L : AssociatedBundle Q a p χ) where
  sheaf : Q.scheme.left.Modules
  functions : sheaf ⟶ functionsOver Q.projection.left
  functions_injective : ∀ U, Function.Injective (functions.app U)
  functions_range : ∀ U (f : Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U)),
    f ∈ Set.range (functions.app U) ↔ IsCovariantOn Q p χ U f
  sections : ∀ U, Γ(sheaf, U) ≃ geometricSections L U
  evaluation : ∀ (U : Q.scheme.left.Opens) (x : Γ(sheaf, U))
    (T : SchemeOver k) (g : T ⟶ G.val.X) (i : T.left ⟶ U.toScheme)
    (_hi : i ≫ U.ι = g.left ≫ Q.projection.left)
    (h : (⊤ : T.left.Opens) ≤ g.left ⁻¹ᵁ (Q.projection.left ⁻¹ᵁ U)),
    ∃ z : T ⟶ affineLine k, lineCoordinate z = evalOn g.left _ h (functions.app U x) ∧
      i ≫ (sections U x).val = (prod.lift g z ≫ L.trivialization).left

/-- The underlying regular function of a section. -/
abbrev SectionRealization.functionVal
    {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    {L : AssociatedBundle Q a p χ} (M : SectionRealization L)
    (U : Q.scheme.left.Opens) (x : Γ(M.sheaf, U)) :
    Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ U) :=
  M.functions.app U x

/-- All weights on the split opposite-Borel flag give actual module sheaves. -/
def AssociatedSectionSheaf : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    (L : AssociatedBundle Q a p χ), Nonempty (SectionRealization L)

/-- Restriction in the module sheaf agrees with restricting sections of
the given total space to a smaller open. -/
def GeometricSectionRestrictions : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    {L : AssociatedBundle Q a p χ} (M : SectionRealization L)
    (U V : Q.scheme.left.Opens) (h : V ≤ U) (x : Γ(M.sheaf, U)),
    (M.sections V (M.sheaf.presheaf.map (homOfLE h).op x)).val =
      Q.scheme.left.homOfLE h ≫ (M.sections U x).val

/-- Scalar functions from the ground field on a scheme over that field. -/
abbrev groundScalars (T : SchemeOver k) : CommRingCat.of k ⟶ Γ(T.left, ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ T.hom.appTop

section Charts

variable {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    {L : AssociatedBundle Q a p χ}

/-- The local coordinate on sections is obtained by evaluation along the
chosen lift of the open to the group. -/
def chartValue (M : SectionRealization L) {U : Q.scheme.left.Opens}
    (s : TorsorLift Q U) (x : Γ(M.sheaf, U)) : Γ(Q.scheme.left, U) :=
  U.topIso.hom (evalOn s.lift.left _ (by
    change (⊤ : U.toScheme.Opens) ≤ (s.lift.left ≫ Q.projection.left) ⁻¹ᵁ U
    rw [s.lifts]
    simp) (M.functions.app U x))

/-- Change of frame relates the two chart coordinates by the inverse
character at the right torsor difference. -/
def ChartTransition : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    {L : AssociatedBundle Q a p χ} (M : SectionRealization L)
    (U : Q.scheme.left.Opens) (s t : TorsorLift Q U),
    ∃ b : openOver Q.scheme U ⟶ P.negative.group.X,
      t.lift = s.lift * (b ≫ P.negative.inclusion.hom.hom) ∧
      ∀ x, chartValue M t x =
        U.topIso.hom (characterFunction (p.projection ≫ χ) b⁻¹) * chartValue M s x

/-- For every splitting open, the local sections identify linearly with
regular functions by evaluation in the given frame. -/
def ChartCoordinates : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    {L : AssociatedBundle Q a p χ} (M : SectionRealization L)
    (U : Q.scheme.left.Opens) (s : TorsorLift Q U),
    ∃ e : Γ(M.sheaf, U) ≃ₗ[Γ(Q.scheme.left, U)] Γ(Q.scheme.left, U),
      ∀ x, e x = chartValue M s x

/-- Torsor lifts exist on opens covering the whole flag. -/
def ChartCover : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    (Q : Presentation P.negative) (y : Q.scheme.left),
      ∃ U : Q.scheme.left.Opens, y ∈ U ∧ Nonempty (TorsorLift Q U)

/-- Invertibility witnessed by the actual restriction to each torsor chart. -/
def InvertibleSectionSheaf : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    {L : AssociatedBundle Q a p χ} (M : SectionRealization L)
    (y : Q.scheme.left),
    ∃ U : Q.scheme.left.Opens, y ∈ U ∧ Nonempty (TorsorLift Q U) ∧
      Nonempty (M.sheaf.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

end Charts

/-- Global sections agree with the E04 Hopf-coordinate covariants through
the bundle trivialization, for every choice of compatible affine coordinates. -/
def GlobalCovariantSections : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ : CharacterDescent.Character P.torus.group}
    {L : AssociatedBundle Q a p χ} (M : SectionRealization L)
    {A D : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group)
    (q : A ⟶ D)
    (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ D),
    specGroupMap q ≫ e.hom = d.hom ≫ P.negative.inclusion →
    specGroupMap φ = d.hom ≫ p.projection ≫ χ →
    ∀ (c : GroupLike k D), (c : D) = characterCoordinate φ →
      letI : Module k Γ(M.sheaf, ⊤) := Module.compHom _ (groundScalars Q.scheme).hom
      ∃ E : Γ(M.sheaf, ⊤) ≃ₗ[k] covariantFunctions q c,
        ∀ x : Γ(M.sheaf, ⊤),
          Q.projection.left ≫ Q.scheme.left.topIso.inv ≫ (M.sections ⊤ x).val =
            (prod.lift (𝟙 G.val.X)
              (e.inv.hom.hom ≫ linePoint (CommAlgCat.of k A) (E x : A)) ≫
                L.trivialization).left

section Tensor

variable {X : Scheme.{u}}

/-- An O-linear pairing of module sheaves, expressed by its natural
bilinear maps on sections. -/
structure SectionPairing (M N K : X.Modules) where
  app : ∀ U : X.Opens, Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(K, U)
  naturality : ∀ {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) (y : Γ(N, U)),
    K.presheaf.map i.op (app U x y) =
      app V (M.presheaf.map i.op x) (N.presheaf.map i.op y)

def IsTensorProduct {M N K : X.Modules} (m : SectionPairing M N K) : Prop :=
  ∀ (D : X.Modules) (b : SectionPairing M N D),
    ∃! f : K ⟶ D, ∀ (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)),
      f.app U (m.app U x y) = b.app U x y

open scoped TensorProduct

/-- Product of line coordinates, with the tensor identification computed
on any common quotient torsor chart. -/
def CharacterMultiplication : Prop :=
  ∀ {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {P : OppositeBorelPair G}
    {Q : Presentation P.negative} {a : ModObj G.val.X Q.scheme}
    {p : BorelProjection P} {χ χ₂ : CharacterDescent.Character P.torus.group}
    {L : AssociatedBundle Q a p χ} {N : AssociatedBundle Q a p χ₂}
    {K : AssociatedBundle Q a p (χ * χ₂)}
    (M : SectionRealization L) (M' : SectionRealization N) (M'' : SectionRealization K),
    ∃ m : SectionPairing M.sheaf M'.sheaf M''.sheaf,
      (∀ U x y, M''.functions.app U (m.app U x y) =
        M.functionVal U x * M'.functionVal U y) ∧
      (∀ (U : Q.scheme.left.Opens) (s : TorsorLift Q U),
        (∀ x y, chartValue M'' s (m.app U x y) =
          chartValue M s x * chartValue M' s y) ∧
        ∃ e : (Γ(M.sheaf, U) ⊗[Γ(Q.scheme.left, U)] Γ(M'.sheaf, U)) ≃ₗ[Γ(Q.scheme.left, U)]
            Γ(M''.sheaf, U),
          ∀ x y, e (x ⊗ₜ y) = m.app U x y) ∧
      IsTensorProduct m

end Tensor

section Pullback

variable {G G' : AffineAlgebraicGroup k} {P : OppositeBorelPair G} {P' : OppositeBorelPair G'}

/-- A map of the two opposite-Borel quotient presentations. No smoothness,
separability, or surjectivity of the group homomorphism is imposed. -/
structure QuotientMap (Q : Presentation P.negative) (Q' : Presentation P'.negative) where
  group : G.val ⟶ G'.val
  borel : P.negative.group ⟶ P'.negative.group
  flag : Q.scheme ⟶ Q'.scheme
  commutesBorel : P.negative.inclusion ≫ group = borel ≫ P'.negative.inclusion
  commutesFlag : Q.projection ≫ flag = group.hom.hom ≫ Q'.projection

variable {Q : Presentation P.negative} {Q' : Presentation P'.negative}

/-- Pulling back a regular function from the group over an open of the target flag. -/
def pullFunction (f : QuotientMap Q Q') (U : Q'.scheme.left.Opens)
    (r : Γ(G'.val.X.left, Q'.projection.left ⁻¹ᵁ U)) :
    Γ(G.val.X.left, Q.projection.left ⁻¹ᵁ (f.flag.left ⁻¹ᵁ U)) :=
  f.group.hom.hom.left.appLE _ _ (by
    change (Q.projection ≫ f.flag).left ⁻¹ᵁ U ≤
      (f.group.hom.hom ≫ Q'.projection).left ⁻¹ᵁ U
    rw [f.commutesFlag]) r

/-- The source character is the pullback of the target Borel character. -/
def CompatibleCharacters (f : QuotientMap Q Q') (p : BorelProjection P) (p' : BorelProjection P')
    (χ : CharacterDescent.Character P.torus.group) (χ' : CharacterDescent.Character P'.torus.group) :
    Prop :=
  p.projection ≫ χ = f.borel ≫ p'.projection ≫ χ'

/-- Pullback of covariant sections agrees with composition on the group. -/
def CovariantPullbackMap : Prop :=
  ∀ {k : Type u} [Field k] {G G' : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} {P' : OppositeBorelPair G'}
    {Q : Presentation P.negative} {Q' : Presentation P'.negative}
    {a : ModObj G.val.X Q.scheme} {a' : ModObj G'.val.X Q'.scheme}
    {p : BorelProjection P} {p' : BorelProjection P'}
    {χ : CharacterDescent.Character P.torus.group} {χ' : CharacterDescent.Character P'.torus.group}
    {L : AssociatedBundle Q a p χ} {L' : AssociatedBundle Q' a' p' χ'}
    (M : SectionRealization L) (M' : SectionRealization L')
    (f : QuotientMap Q Q'), CompatibleCharacters f p p' χ χ' →
    ∃ h : M'.sheaf ⟶ (Scheme.Modules.pushforward f.flag.left).obj M.sheaf,
      ∀ U x, M.functionVal (f.flag.left ⁻¹ᵁ U) (h.app U x) =
        pullFunction f U (M'.functionVal U x)

/-- If a target section is the unit in a torsor frame, its pullback is
a unit in every source frame on an open mapping into that chart. -/
def PullbackChartUnits : Prop :=
  ∀ {k : Type u} [Field k] {G G' : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} {P' : OppositeBorelPair G'}
    {Q : Presentation P.negative} {Q' : Presentation P'.negative}
    {a : ModObj G.val.X Q.scheme} {a' : ModObj G'.val.X Q'.scheme}
    {p : BorelProjection P} {p' : BorelProjection P'}
    {χ : CharacterDescent.Character P.torus.group} {χ' : CharacterDescent.Character P'.torus.group}
    {L : AssociatedBundle Q a p χ} {L' : AssociatedBundle Q' a' p' χ'}
    (M : SectionRealization L) (M' : SectionRealization L')
    (f : QuotientMap Q Q'), CompatibleCharacters f p p' χ χ' →
    ∀ (h : M'.sheaf ⟶ (Scheme.Modules.pushforward f.flag.left).obj M.sheaf),
      (∀ U x, M.functionVal (f.flag.left ⁻¹ᵁ U) (h.app U x) =
        pullFunction f U (M'.functionVal U x)) →
      ∀ (U : Q'.scheme.left.Opens) (s' : TorsorLift Q' U)
        (W : Q.scheme.left.Opens) (s : TorsorLift Q W)
        (hW : W ≤ f.flag.left ⁻¹ᵁ U) (x : Γ(M'.sheaf, U)),
        chartValue M' s' x = 1 →
        IsUnit (chartValue M s (M.sheaf.presheaf.map (homOfLE hW).op (h.app U x)))

/-- Compatibility with the actual inverse-image functor, with the adjoint
specified by pullback of covariant functions on the groups. -/
def HasCanonicalPullback
    {a : ModObj G.val.X Q.scheme} {a' : ModObj G'.val.X Q'.scheme}
    {p : BorelProjection P} {p' : BorelProjection P'}
    {χ : CharacterDescent.Character P.torus.group} {χ' : CharacterDescent.Character P'.torus.group}
    {L : AssociatedBundle Q a p χ} {L' : AssociatedBundle Q' a' p' χ'}
    (M : SectionRealization L) (M' : SectionRealization L')
    (f : QuotientMap Q Q') : Prop :=
    ∃ e : (Scheme.Modules.pullback f.flag.left).obj M'.sheaf ≅ M.sheaf,
      ∀ U x, M.functionVal (f.flag.left ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f.flag.left).homEquiv
          M'.sheaf M.sheaf e.hom).app U x) = pullFunction f U (M'.functionVal U x)

/-- The adjoint of the canonical pullback of covariants is an isomorphism
of module sheaves for the actual inverse-image functor. -/
def AssociatedSheafPullback : Prop :=
  ∀ {k : Type u} [Field k] {G G' : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} {P' : OppositeBorelPair G'}
    {Q : Presentation P.negative} {Q' : Presentation P'.negative}
    {a : ModObj G.val.X Q.scheme} {a' : ModObj G'.val.X Q'.scheme}
    {p : BorelProjection P} {p' : BorelProjection P'}
    {χ : CharacterDescent.Character P.torus.group} {χ' : CharacterDescent.Character P'.torus.group}
    {L : AssociatedBundle Q a p χ} {L' : AssociatedBundle Q' a' p' χ'}
    (M : SectionRealization L) (M' : SectionRealization L')
    (f : QuotientMap Q Q'), CompatibleCharacters f p p' χ χ' → HasCanonicalPullback M M' f

/-- The morphism of flags and the pullback comparison are constructed from
the group and Borel morphisms. -/
def InducedAssociatedSheafPullback : Prop :=
  ∀ {k : Type u} [Field k] {G G' : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} {P' : OppositeBorelPair G'}
    {Q : Presentation P.negative} {Q' : Presentation P'.negative}
    {a : ModObj G.val.X Q.scheme} {a' : ModObj G'.val.X Q'.scheme}
    {p : BorelProjection P} {p' : BorelProjection P'}
    {χ : CharacterDescent.Character P.torus.group} {χ' : CharacterDescent.Character P'.torus.group}
    {L : AssociatedBundle Q a p χ} {L' : AssociatedBundle Q' a' p' χ'}
    (M : SectionRealization L) (M' : SectionRealization L')
    (g : G.val ⟶ G'.val) (b : P.negative.group ⟶ P'.negative.group),
    P.negative.inclusion ≫ g = b ≫ P'.negative.inclusion →
    p.projection ≫ χ = b ≫ p'.projection ≫ χ' →
    ∃ f : QuotientMap Q Q', f.group = g ∧ f.borel = b ∧ HasCanonicalPullback M M' f

open RelativeFrobenius (extendAlong scalarTensor)

/-- The Hopf-coordinate formula for the iterated relative Frobenius. -/
def IteratedFrobeniusFormula (ℓ r : ℕ) [Fact ℓ.Prime] [CharP k ℓ] {A : HopfAlgebraCategory k}
    (F : extendAlong (iterateFrobenius k ℓ r) A ⟶ A) : Prop :=
  ∀ (c : k) (z : A), F.hom (scalarTensor (iterateFrobenius k ℓ r) A c z) = c • z ^ (ℓ ^ r)

/-- Pullback to the weight multiplied by `ℓ ^ r`. The source and target group
and Borel coordinates identify the group-level relative Frobenius maps.
The target character is transported to the scalar twist by `c ↦ 1 ⊗ c` on
its Borel coordinate. The map of flags is induced from the group map. -/
def FrobeniusAssociatedSheafPullback : Prop :=
  ∀ {k : Type u} [Field k] (ℓ r : ℕ) [Fact ℓ.Prime] [CharP k ℓ] {G G' : AffineAlgebraicGroup k}
    {P : OppositeBorelPair G} {P' : OppositeBorelPair G'}
    {Q : Presentation P.negative} {Q' : Presentation P'.negative}
    {a : ModObj G.val.X Q.scheme} {a' : ModObj G'.val.X Q'.scheme}
    {p : BorelProjection P} {p' : BorelProjection P'}
    {χ : CharacterDescent.Character P.torus.group} {χ' : CharacterDescent.Character P'.torus.group}
    {L : AssociatedBundle Q a p (χ ^ (ℓ ^ r))} {L' : AssociatedBundle Q' a' p' χ'}
    (M : SectionRealization L) (M' : SectionRealization L') {A D : HopfAlgebraCategory k}
    (e : specGroup A ≅ G.val) (d : specGroup D ≅ P.negative.group),
    let σ := iterateFrobenius k ℓ r
    ∀ (e' : specGroup (extendAlong σ A) ≅ G'.val)
      (d' : specGroup (extendAlong σ D) ≅ P'.negative.group)
      (F : extendAlong σ A ⟶ A) (F_B : extendAlong σ D ⟶ D)
      (φ : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶ D)
      (φ' : DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters ⟶
        extendAlong σ D),
    let g := e.inv ≫ specGroupMap F ≫ e'.hom
    let b := d.inv ≫ specGroupMap F_B ≫ d'.hom
    IteratedFrobeniusFormula ℓ r F → IteratedFrobeniusFormula ℓ r F_B →
    P.negative.inclusion ≫ g = b ≫ P'.negative.inclusion →
    specGroupMap φ = d.hom ≫ p.projection ≫ χ →
    specGroupMap φ' = d'.hom ≫ p'.projection ≫ χ' →
    characterCoordinate φ' = scalarTensor σ D 1 (characterCoordinate φ) →
    ∃ f : QuotientMap Q Q', f.group = g ∧ f.borel = b ∧ HasCanonicalPullback M M' f

end Pullback

end

end LinearAlgebraicGroups.Specs.AssociatedFlagLineSheaves
