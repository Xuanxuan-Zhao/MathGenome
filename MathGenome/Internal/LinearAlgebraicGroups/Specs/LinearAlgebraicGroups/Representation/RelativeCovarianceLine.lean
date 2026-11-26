import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ArithmeticProjectiveFiniteness
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ArithmeticCohomologyBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RelativeCovarianceLine

noncomputable section

open FlagCohomology

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Right multiplication by the given subgroup. -/
def rightMultiply {G H : Grp (SchemeOverRing A)} (i : H ⟶ G) :
    G.X ⨯ H.X ⟶ G.X :=
  prod.fst * (prod.snd ≫ i.hom.hom)

/-- A quotient torsor with Zariski-local sections and a unit character of its
right subgroup. The kernel pair is given by the right multiplication map. -/
structure Torsor (A : Type u) [CommRing A] where
  group : Grp (SchemeOverRing A)
  subgroup : Grp (SchemeOverRing A)
  inclusion : subgroup ⟶ group
  closedSubgroup : IsClosedImmersion inclusion.hom.hom.left
  smoothGroup : Smooth group.X.hom
  smoothSubgroup : Smooth subgroup.X.hom
  affineGroup : IsAffine group.X.left
  affineSubgroup : IsAffine subgroup.X.left
  quotient : SchemeOverRing A
  smoothQuotient : Smooth quotient.hom
  separatedQuotient : IsSeparated quotient.hom
  projection : group.X ⟶ quotient
  smoothProjection : Smooth projection.left
  surjectiveProjection : Surjective projection.left
  kernelPair : IsPullback prod.fst (rightMultiply inclusion) projection projection
  localSections : ∀ y : quotient.left, ∃ U : quotient.left.Opens, y ∈ U ∧
    ∃ s : U.toScheme ⟶ group.X.left, s ≫ projection.left = U.ι
  character : Γ(subgroup.X.left, ⊤)ˣ
  character_mul :
    μ[subgroup.X].left.appTop (character : Γ(subgroup.X.left, ⊤)) =
      (fst subgroup.X subgroup.X).left.appTop (character : Γ(subgroup.X.left, ⊤)) *
        (snd subgroup.X subgroup.X).left.appTop (character : Γ(subgroup.X.left, ⊤))

/-- The sheaf is the actual kernel of the two regular-function restrictions,
using the inverse unit of the right subgroup on the overlap. -/
def Torsor.lineData (T : Torsor A) : CovarianceData T.quotient where
  torsor := T.group.X
  overlap := T.group.X ⨯ T.subgroup.X
  projection := T.projection
  overlapProjection := prod.fst ≫ T.projection
  first := prod.fst
  second := rightMultiply T.inclusion
  fst_w := rfl
  snd_w := T.kernelPair.w.symm
  multiplier := (prod.snd : T.group.X ⨯ T.subgroup.X ⟶ T.subgroup.X).left.appTop
    (T.character⁻¹ : Γ(T.subgroup.X.left, ⊤)ˣ)

abbrev Torsor.line (T : Torsor A) := T.lineData.sheaf

/-- A Cartesian change of the torsor and its double overlap with the actual
face maps and multiplier. This allows changes of the ground ring. -/
structure CartesianChange {X : SchemeOverRing A} {Y : SchemeOverRing B}
    (D : CovarianceData X) (E : CovarianceData Y) (f : Y.left ⟶ X.left) where
  torsorMap : E.torsor.left ⟶ D.torsor.left
  overlapMap : E.overlap.left ⟶ D.overlap.left
  torsorSquare : IsPullback torsorMap E.projection.left D.projection.left f
  overlapSquare : IsPullback overlapMap E.overlapProjection.left D.overlapProjection.left f
  first_eq : overlapMap ≫ D.first.left = E.first.left ≫ torsorMap
  second_eq : overlapMap ≫ D.second.left = E.second.left ≫ torsorMap
  multiplier_eq : overlapMap.appTop D.multiplier = E.multiplier

/-- The actual pullback sheaf is identified with the covariance kernel
through the adjunction for pullback and pushforward. -/
def CartesianChange.HasComparison {X : SchemeOverRing A} {Y : SchemeOverRing B}
    {D : CovarianceData X} {E : CovarianceData Y} {f : Y.left ⟶ X.left}
    (C : CartesianChange D E f) : Prop :=
  ∃ e : (Scheme.Modules.pullback f).obj D.sheaf ≅ E.sheaf,
    D.IsPullbackMap E f C.torsorMap C.torsorSquare.w
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ e.hom)

def IsLineBundle : Prop :=
  ∀ (A : Type u) [CommRing A] (T : Torsor A),
    ArithmeticProjectiveFiniteness.IsLineBundleOn A T.quotient T.line

def CartesianComparison : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] (T : Torsor A)
    {Y : SchemeOverRing B} (E : CovarianceData Y) (f : Y.left ⟶ T.quotient.left)
    (C : CartesianChange T.lineData E f),
    C.HasComparison ∧ ArithmeticProjectiveFiniteness.IsLineBundleOn B Y E.sheaf

/-- Compatible isomorphisms of quotients, torsors, and overlaps identify the
actual covariance lines by the adjoint of pullback on functions. -/
def IsoComparison : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] (T : Torsor A)
    {Y : SchemeOverRing B} (E : CovarianceData Y) (f : Y.left ≅ T.quotient.left)
    (g : E.torsor.left ≅ T.lineData.torsor.left)
    (j : E.overlap.left ≅ T.lineData.overlap.left)
    (h : g.hom ≫ T.projection.left = E.projection.left ≫ f.hom),
    j.hom ≫ T.lineData.overlapProjection.left = E.overlapProjection.left ≫ f.hom →
    j.hom ≫ T.lineData.first.left = E.first.left ≫ g.hom →
    j.hom ≫ T.lineData.second.left = E.second.left ≫ g.hom →
    j.hom.appTop T.lineData.multiplier = E.multiplier →
    ∃ e : (Scheme.Modules.pullback f.hom).obj T.line ≅ E.sheaf,
      T.lineData.IsPullbackMap E f.hom g.hom h
        ((Scheme.Modules.pullbackPushforwardAdjunction f.hom).homEquiv _ _ e.hom)

section BaseChange

open ArithmeticCohomologyBaseChange (changeBase fibreProjection)

abbrev ringChangeMap (φ : A →+* B) {X Y : SchemeOverRing A} (f : X ⟶ Y) :=
  (changeBase φ).map f

/-- In a change of coefficient rings the multiplier is pulled back from the
original double overlap, without a flatness hypothesis on the ring map. -/
def ringChange {X : SchemeOverRing A} (D : CovarianceData X) (φ : A →+* B) :
    CovarianceData ((changeBase φ).obj X) where
  torsor := (changeBase φ).obj D.torsor
  overlap := (changeBase φ).obj D.overlap
  projection := ringChangeMap φ D.projection
  overlapProjection := ringChangeMap φ D.overlapProjection
  first := ringChangeMap φ D.first
  second := ringChangeMap φ D.second
  fst_w := by rw [← Functor.map_comp, D.fst_w]
  snd_w := by rw [← Functor.map_comp, D.snd_w]
  multiplier := (fibreProjection φ D.overlap).appTop D.multiplier

def RingComparison : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] (T : Torsor A) (φ : A →+* B),
    ∃ C : CartesianChange T.lineData (ringChange T.lineData φ) (fibreProjection φ T.quotient),
      C.torsorMap = fibreProjection φ T.lineData.torsor ∧
        C.overlapMap = fibreProjection φ T.lineData.overlap ∧ C.HasComparison

end BaseChange

/-- Add an independent parameter to the base, torsor and double overlap. -/
def productData (W : SchemeOverRing A) {X : SchemeOverRing A} (D : CovarianceData X) :
    CovarianceData (W ⊗ X) where
  torsor := W ⊗ D.torsor
  overlap := W ⊗ D.overlap
  projection := W ◁ D.projection
  overlapProjection := W ◁ D.overlapProjection
  first := W ◁ D.first
  second := W ◁ D.second
  fst_w := by rw [← whiskerLeft_comp, D.fst_w]
  snd_w := by rw [← whiskerLeft_comp, D.snd_w]
  multiplier := (snd W D.overlap).left.appTop D.multiplier

variable (T : Torsor A)

/-- Data on the product of the acting group with the quotient, with the same
right character on the overlap. -/
def Torsor.actionLineData : CovarianceData (T.group.X ⊗ T.quotient) :=
  productData T.group.X T.lineData

/-- The action map with domain the categorical product of group and quotient. -/
def Torsor.leftAction (a : ModObj T.group.X T.quotient) :
    T.group.X ⊗ T.quotient ⟶ T.quotient := a.smul

/-- The group unit together with the unchanged point of the acted-on scheme. -/
def insertUnit (G : Grp (SchemeOverRing A)) (K : SchemeOverRing A) : K ⟶ G.X ⊗ K :=
  lift (toUnit K ≫ η[G.X]) (𝟙 K)

/-- Multiply the two group coordinates and retain the last coordinate. -/
def combineGroup (G : Grp (SchemeOverRing A)) (K : SchemeOverRing A) :
    G.X ⊗ (G.X ⊗ K) ⟶ G.X ⊗ K :=
  lift (fst G.X (G.X ⊗ K) * (snd G.X (G.X ⊗ K) ≫ fst G.X K))
    (snd G.X (G.X ⊗ K) ≫ snd G.X K)

/-- Reindex an identification of two pullbacks along a further scheme map. -/
def pullbackComparison {X Y Z : Scheme.{u}} (L : X.Modules) (j : Z ⟶ Y)
    (f g : Y ⟶ X) (e : (Scheme.Modules.pullback f).obj L ⟶
      (Scheme.Modules.pullback g).obj L) :
    (Scheme.Modules.pullback (j ≫ f)).obj L ⟶
      (Scheme.Modules.pullback (j ≫ g)).obj L :=
  (Scheme.Modules.pullbackComp j f).inv.app L ≫
    (Scheme.Modules.pullback j).map e ≫ (Scheme.Modules.pullbackComp j g).hom.app L

/-- The comparison for a product agrees with the successive comparisons,
under the three identifications of the pullback maps on the double product. -/
def SuccessiveComparison {X Y Z : Scheme.{u}} (L : X.Modules)
    (a p : Y ⟶ X) (v u t : Z ⟶ Y)
    (e : (Scheme.Modules.pullback a).obj L ⟶ (Scheme.Modules.pullback p).obj L)
    (ha : v ≫ a = u ≫ a) (hm : u ≫ p = t ≫ a) (hp : t ≫ p = v ≫ p) : Prop :=
  pullbackComparison L v a p e =
    (Scheme.Modules.pullbackCongr ha).hom.app L ≫
      pullbackComparison L u a p e ≫
      (Scheme.Modules.pullbackCongr hm).hom.app L ≫
      pullbackComparison L t a p e ≫
      (Scheme.Modules.pullbackCongr hp).hom.app L

/-- The action on the line is the identity over the group unit, and the
identification for a product equals the two successive identifications. -/
def Torsor.HasLineCocycle (a : ModObj T.group.X T.quotient)
    (e : (Scheme.Modules.pullback (T.leftAction a).left).obj T.line ⟶
      (Scheme.Modules.pullback (snd T.group.X T.quotient).left).obj T.line) : Prop :=
  let G := T.group.X
  let Y := T.quotient
  let p := (snd G Y).left
  let j := insertUnit T.group Y
  let u : G ⊗ (G ⊗ Y) ⟶ G ⊗ Y := G ◁ T.leftAction a
  let v := combineGroup T.group Y
  let t : G ⊗ (G ⊗ Y) ⟶ G ⊗ Y := snd G (G ⊗ Y)
  ∃ (hj : j.left ≫ (T.leftAction a).left = j.left ≫ p)
    (ha : v.left ≫ (T.leftAction a).left = u.left ≫ (T.leftAction a).left)
    (hm : u.left ≫ p = t.left ≫ (T.leftAction a).left)
    (hp : t.left ≫ p = v.left ≫ p),
    pullbackComparison T.line j.left (T.leftAction a).left p e =
      (Scheme.Modules.pullbackCongr hj).hom.app T.line ∧
    SuccessiveComparison T.line (T.leftAction a).left p v.left u.left t.left e ha hm hp

def Torsor.HasEquivariantLine (a : ModObj T.group.X T.quotient) : Prop :=
  let D := T.lineData
  let E := T.actionLineData
  let p := (snd T.group.X T.quotient).left
  let m := (μ[T.group.X]).left
  let s := (snd T.group.X T.group.X).left
  ∃ (ha : m ≫ D.projection.left = E.projection.left ≫ (T.leftAction a).left)
    (hp : s ≫ D.projection.left = E.projection.left ≫ p)
    (ea : (Scheme.Modules.pullback (T.leftAction a).left).obj D.sheaf ≅ E.sheaf)
    (ep : (Scheme.Modules.pullback p).obj D.sheaf ≅ E.sheaf),
    D.IsPullbackMap E (T.leftAction a).left m ha
      ((Scheme.Modules.pullbackPushforwardAdjunction (T.leftAction a).left).homEquiv _ _ ea.hom) ∧
    D.IsPullbackMap E p s hp
      ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _ ep.hom) ∧
    T.HasLineCocycle a (ea.hom ≫ ep.inv)

def EquivariantLine : Prop :=
  ∀ (A : Type u) [CommRing A] (T : Torsor A) (a : ModObj T.group.X T.quotient),
    μ[T.group.X] ≫ T.projection = (𝟙 T.group.X ⊗ₘ T.projection) ≫ T.leftAction a →
    T.HasEquivariantLine a

end

end LinearAlgebraicGroups.Specs.RelativeCovarianceLine
