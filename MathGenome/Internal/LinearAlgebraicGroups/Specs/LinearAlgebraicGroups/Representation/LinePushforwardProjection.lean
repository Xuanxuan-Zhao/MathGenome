import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u v

noncomputable section

namespace LinearAlgebraicGroups.Specs.LinePushforwardProjection

/-- The structure sheaf as a module over itself. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- An invertible module is a module trivial on an open neighborhood of each point. -/
def IsLine {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (M.restrict U.ι ≅ structureModule U.toScheme)

/-- The criterion of isomorphism on an open basis, applied to actual module maps. -/
def IsIsoOnBasis : Prop :=
  ∀ {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N) {ι : Type v}
    (U : ι → X.Opens), Opens.IsBasis (Set.range U) →
    (∀ i, IsIso (a.app (U i))) → IsIso a

/-- The affine comparison uses the canonical map from the tilde of the module of
global sections, which sends a global section to its restriction on each open. -/
def AffinePushforward : Prop :=
  ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec S).Modules),
    IsIso M.fromTildeΓ →
    IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj M).fromTildeΓ

/-- The affine pushforward comparison applies to every line module,
including those which are only locally trivial on the source affine. -/
def AffineLinePushforward : Prop :=
  ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec S).Modules),
    IsLine M → IsIso ((Scheme.Modules.pushforward (Spec.map φ)).obj M).fromTildeΓ

/-- Restriction of sections from the whole scheme to an open chart, with the
module of sections on the chart expressed over its own structure sheaf. -/
def chartSections {A X : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) : Γ(M, ⊤) ⟶ Γ(M.restrict j, ⊤) :=
  M.presheaf.map (j ''ᵁ (⊤ : A.Opens)).leTop.op ≫ (M.restrictAppIso j ⊤).inv

/-- The canonical pullback map on sections is the unit of the pullback-pushforward
adjunction on the top open. -/
def pullbackSections {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    Γ(M, ⊤) ⟶ Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤

/-- Restricting a direct image to an open chart commutes with the pushforward
on the cartesian source chart, with its canonical map on sections. -/
def RestrictPushforward : Prop :=
  ∀ {X Y A B : Scheme.{u}} {f : X ⟶ Y} {g : A ⟶ B}
    (i : A ⟶ X) (j : B ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (_h : IsPullback g i j f) (M : X.Modules),
    ∃ e : ((Scheme.Modules.pushforward f).obj M).restrict j ≅
        (Scheme.Modules.pushforward g).obj (M.restrict i),
      chartSections j ((Scheme.Modules.pushforward f).obj M) ≫ e.hom.app ⊤ =
        chartSections i M

/-- A morphism of modules which is an isomorphism on each member of an
open cover is an isomorphism. -/
def IsIsoOnCover : Prop :=
  ∀ {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N) {ι : Type v}
    (U : ι → X.Opens), IsOpenCover U →
    (∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map a)) → IsIso a

/-- For quasi-coherent modules on an affine scheme, the map on sections
detects an isomorphism. -/
def IsIsoOfAffineSections : Prop :=
  ∀ {R : CommRingCat.{u}} {M N : (Spec R).Modules} (a : M ⟶ N),
    M.IsQuasicoherent → N.IsQuasicoherent → IsIso (moduleSpecΓFunctor.map a) → IsIso a

/-- Global sections of the direct image on affine schemes are those of the
original module, with scalar multiplication through the coordinate ring map. -/
def AffinePushforwardSections : Prop :=
  ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec S).Modules),
    ∃ e : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ≅
        (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj M),
      ∀ s, e.hom s = s

/-- For each affine target chart of a finite morphism, identify the actual
restricted direct image with the tilde of the section module on the inverse
image chart, with scalars restricted along the chart ring map. -/
def FinitePushforwardOnChart : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {R : CommRingCat.{u}}
    (j : Spec R ⟶ Y) [IsOpenImmersion j] (M : X.Modules), IsLine M →
    let S := Γ(pullback f j, ⊤)
    let P := (Scheme.Modules.pushforward f).obj M
    ∃ (i : Spec S ⟶ X) (φ : R ⟶ S) (hi : IsOpenImmersion i),
      letI := hi
      IsPullback (Spec.map φ) i j f ∧
        let B := (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj (M.restrict i))
        ∃ e : P.restrict j ≅ tilde B,
          ∀ s : Γ(M, ⊤), (tilde.isoTop B).inv (e.hom.app ⊤ (chartSections j P s)) =
            chartSections i M s

/-- On an affine chart trivializing the source module, the actual direct image
is the tilde of the source coordinate algebra with its given finite free basis. -/
def FreeAffinePushforward : Prop :=
  ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec S).Modules)
    (t : M ≅ structureModule (Spec S)) (n : ℕ),
    let B := (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S)
    ∀ (b : Module.Basis (Fin n) R B),
      ∃ e : (Scheme.Modules.pushforward (Spec.map φ)).obj M ≅
        tilde (ModuleCat.of R (Fin n → R)),
        ∀ s : moduleSpecΓFunctor.obj M,
          (tilde.isoTop (ModuleCat.of R (Fin n → R))).inv
            (e.hom.app ⊤ s) =
          b.equivFun ((Scheme.ΓSpecIso S).hom (t.hom.app ⊤ s) : S)

section AffineFiber

variable (R S K : Type u) [CommRing R] [CommRing S] [CommRing K]
  [Algebra R S] [Algebra R K]

/-- The scheme-theoretic base change to a point, or more generally to an affine base. -/
abbrev affineFiber : Scheme.{u} :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))

/-- The map from the base change to the original source. -/
abbrev fiberSource : affineFiber R S K ⟶ Spec (CommRingCat.of S) :=
  pullback.fst _ _

/-- The structure map of the base change. -/
abbrev fiberBase : affineFiber R S K ⟶ Spec (CommRingCat.of K) :=
  pullback.snd _ _

/-- Sections of the actual pulled-back module, with the base-point scalars. -/
abbrev fiberSections (M : (Spec (CommRingCat.of S)).Modules) : ModuleCat.{u} K :=
  moduleSpecΓFunctor.obj
    ((Scheme.Modules.pushforward (fiberBase R S K)).obj
      ((Scheme.Modules.pullback (fiberSource R S K)).obj M))

end AffineFiber

/-- Base change for a trivialized line, with the specialization of sections.
Taking the residue field gives the closed-point assertion. The map is induced
by the unit of the actual sheaf pullback adjunction. -/
def AffineFiberComparison : Prop :=
  ∀ (R S K : Type u) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] (M : (Spec (CommRingCat.of S)).Modules)
    (t : M ≅ structureModule (Spec (CommRingCat.of S))),
    ∃ e : fiberSections R S K M ≅ ModuleCat.of K (K ⊗[R] S),
      ∀ s : moduleSpecΓFunctor.obj M,
        e.hom (pullbackSections (fiberSource R S K) M s) =
          (1 : K) ⊗ₜ[R] ((Scheme.ΓSpecIso (CommRingCat.of S)).hom (t.hom.app ⊤ s) : S)

/-- Taking the scalar fiber of the pushforward on an affine chart agrees
with taking sections of the pulled-back line on the scheme-theoretic fiber. -/
def AffineFiberBaseChange : Prop :=
  ∀ (R S K : Type u) [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] (M : (Spec (CommRingCat.of S)).Modules)
    (_t : M ≅ structureModule (Spec (CommRingCat.of S))),
    let P := moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj M)
    ∃ e : ModuleCat.of K (K ⊗[R] P) ≅ fiberSections R S K M,
      ∀ s : moduleSpecΓFunctor.obj M,
        e.hom ((1 : K) ⊗ₜ[R] (s : P)) =
          pullbackSections (fiberSource R S K) M s

/-- On an affine chart with a trivialized source line, sections of the actual
pullback of the direct image agree with sections on the Cartesian source.
The comparison sends the pullback of a source section to its pullback
along the other side of the square. -/
def AffineBaseChangeSections : Prop :=
  ∀ {R S K : CommRingCat.{u}} (φ : R ⟶ S) (g : Spec K ⟶ Spec R)
    {T : Scheme.{u}} (q : T ⟶ Spec K) (i : T ⟶ Spec S),
    IsPullback q i g (Spec.map φ) →
    ∀ (M : (Spec S).Modules), (M ≅ structureModule (Spec S)) →
      let P := (Scheme.Modules.pushforward (Spec.map φ)).obj M
      ∃ e : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback g).obj P) ≅
          moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj
            ((Scheme.Modules.pullback i).obj M)),
        ∀ s : moduleSpecΓFunctor.obj M,
          e.hom (pullbackSections g P s) = pullbackSections i M s

/-- The affine base change for a residue field represents the actual scheme
fiber and respects its maps to the source and to the residue field. -/
def AffineResidueFiber : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R),
    let f := Spec.map (CommRingCat.ofHom (algebraMap R S))
    ∃ e : affineFiber R S p.asIdeal.ResidueField ≅ f.fiber p,
      e.hom ≫ f.fiberι p = fiberSource R S p.asIdeal.ResidueField ∧
      e.hom ≫ f.fiberToSpecResidueField p ≫
        Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).inv =
          fiberBase R S p.asIdeal.ResidueField

/-- The fiber of the actual direct image, at any point of an affine target
chart, consists of sections of the pulled-back line over the scheme fiber.
This comparison preserves specialization of global sections. -/
def AffineResidueSections : Prop :=
  ∀ {R S : CommRingCat.{u}} (φ : R ⟶ S) (p : Spec R)
    (M : (Spec S).Modules), (M ≅ structureModule (Spec S)) →
      let f := Spec.map φ
      let g := (Spec R).fromSpecResidueField p
      let P := (Scheme.Modules.pushforward f).obj M
      ∃ e : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback g).obj P) ≅
          moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (f.fiberToSpecResidueField p)).obj
            ((Scheme.Modules.pullback (f.fiberι p)).obj M)),
        ∀ s : moduleSpecΓFunctor.obj M,
          e.hom (pullbackSections g P s) = pullbackSections (f.fiberι p) M s

/-- In an open chart of the target, taking the scheme-theoretic fiber
commutes with passing to its cartesian source chart. -/
def ChartFiberComparison : Prop :=
  ∀ {A B X Y : Scheme.{u}} {g : A ⟶ B} {f : X ⟶ Y}
    (i : A ⟶ X) (j : B ⟶ Y) [IsOpenImmersion j]
    (_h : IsPullback g i j f) (y : B),
    ∃ e : g.fiber y ≅ f.fiber (j y),
      e.hom ≫ f.fiberι (j y) = g.fiberι y ≫ i ∧
      e.hom ≫ f.fiberToSpecResidueField (j y) =
        g.fiberToSpecResidueField y ≫ Spec.map (j.residueFieldMap y)

section Projection

open MonoidalCategory

variable {X Y : Scheme.{u}}

/-- The presheaf tensor product, formed over the structure ring on each open. -/
abbrev tensorPresheaf (M N : X.Modules) :
    PresheafOfModulesOfCommRing X.presheaf := M.val ⊗ N.val

/-- The tensor product of sheaves of modules is the sheafification of the
presheaf tensor product. -/
def tensorModule (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (tensorPresheaf M N)

/-- The canonical map from section tensors to sections of the tensor sheaf. -/
def tensorToSheaf (M N : X.Modules) :
    tensorPresheaf M N ⟶ (tensorModule M N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _ (𝟙 _)

/-- The image of a simple tensor of sections. -/
def tensorSection (M N : X.Modules) (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    Γ(tensorModule M N, U) :=
  (tensorToSheaf M N).app (.op U) (s ⊗ₜ[Γ(X, U)] t)

/-- Characterizes the projection map by its action on local simple tensors.
The second section is sent by the unit of the actual pullback adjunction. -/
def IsProjectionMap (f : X ⟶ Y) (M : X.Modules) (N : Y.Modules)
    (p : tensorModule ((Scheme.Modules.pushforward f).obj M) N ⟶
      (Scheme.Modules.pushforward f).obj
        (tensorModule M ((Scheme.Modules.pullback f).obj N))) : Prop :=
  ∀ (U : Y.Opens) (s : Γ(M, f ⁻¹ᵁ U)) (t : Γ(N, U)),
    p.app U (tensorSection ((Scheme.Modules.pushforward f).obj M) N U s t) =
      tensorSection M ((Scheme.Modules.pullback f).obj N) (f ⁻¹ᵁ U) s
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U t)

/-- The underived canonical projection formula with a line on the target.
The assertion holds for arbitrary morphisms and arbitrary source modules. -/
def ProjectionFormula : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) (N : Y.Modules),
    IsLine N →
    ∃ e : tensorModule ((Scheme.Modules.pushforward f).obj M) N ≅
        (Scheme.Modules.pushforward f).obj
          (tensorModule M ((Scheme.Modules.pullback f).obj N)),
      IsProjectionMap f M N e.hom

end Projection

end LinearAlgebraicGroups.Specs.LinePushforwardProjection
