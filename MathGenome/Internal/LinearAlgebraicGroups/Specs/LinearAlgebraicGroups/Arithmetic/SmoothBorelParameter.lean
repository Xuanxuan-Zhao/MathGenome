import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRealization
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.SmoothBorelParameter

open GeometricBorelConjugacy (IsBorel IsKBorel)
open GeometricRadicals (IsReductive)
open IntegralSemisimpleModel (Base Integers Model integerAlgebra)

noncomputable section

variable {S T U : Scheme.{u}}

/-- Scalar extension for group objects over schemes. -/
abbrev changeBase (a : T ⟶ S) : Grp (Over S) ⥤ Grp (Over T) :=
  (Over.pullback a).mapGrp

/-- The ambient group after pulling back along two maps, identified with the
group pulled back along their composite. -/
def changeBaseComp (a : U ⟶ T) (b : T ⟶ S) :
    changeBase (a ≫ b) ≅ changeBase b ⋙ changeBase a :=
  Functor.mapGrpNatIso (Over.pullbackComp a b) ≪≫ Functor.mapGrpCompIso

/-- Equal base maps induce the same extension of scalars. -/
def changeBaseCongr {a b : T ⟶ S} (h : a = b) (G : Grp (Over S)) :
    (changeBase a).obj G ≅ (changeBase b).obj G :=
  eqToIso (congrArg (fun f ↦ (changeBase f).obj G) h)

/-- Cancellation of scalar extension along the identity. -/
def changeBaseId (S : Scheme.{u}) : changeBase (𝟙 S) ≅ 𝟭 (Grp (Over S)) :=
  Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso

/-- A smooth closed subgroup of the actual group over the test scheme. -/
structure Family (G : Grp (Over S)) (T : Over S) where
  group : Grp (Over T.left)
  inclusion : group ⟶ (changeBase T.hom).obj G
  closed : IsClosedImmersion inclusion.hom.hom.left
  smooth : Smooth group.X.hom

/-- Families are identified by group isomorphisms commuting with their inclusions. -/
def SameFamily {G : Grp (Over S)} {T : Over S} (B B' : Family G T) : Prop :=
  ∃ e : B.group ≅ B'.group, e.hom ≫ B'.inclusion = B.inclusion

/-- Extension of scalars of a morphism is a cartesian square of schemes. -/
theorem pullbackMapSquare (a : T ⟶ S) {X Y : Over S} (q : X ⟶ Y) :
    IsPullback ((Over.pullback a).map q).left (pullback.fst X.hom a)
      (pullback.fst Y.hom a) q.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd Y.hom a) (h₂₂ := Y.hom) (v₁₃ := a)
  · simpa only [Over.pullback_map_left, pullback.lift_snd, Over.w q]
      using (IsPullback.of_hasPullback X.hom a).flip
  · simp only [Over.pullback_map_left, pullback.lift_fst]
  · exact (IsPullback.of_hasPullback Y.hom a).flip

/-- Pull back the subgroup and identify the ambient group via composition of pullbacks. -/
def Family.pullback {G : Grp (Over S)} {T U : Over S} (B : Family G T) (a : U ⟶ T) :
    Family G U where
  group := (changeBase a.left).obj B.group
  inclusion := (changeBase a.left).map B.inclusion ≫
    (changeBaseComp a.left T.hom).inv.app G ≫
    (changeBaseCongr (Over.w a) G).hom
  closed := by
    have : IsClosedImmersion B.inclusion.hom.hom.left := B.closed
    change IsClosedImmersion
      (((changeBase a.left).map B.inclusion).hom.hom.left ≫
        (((changeBaseComp a.left T.hom).inv.app G).hom.hom.left ≫
          (changeBaseCongr (Over.w a) G).hom.hom.hom.left))
    have h₁ : IsClosedImmersion (((changeBase a.left).map B.inclusion).hom.hom.left) := by
      exact MorphismProperty.of_isPullback (pullbackMapSquare a.left B.inclusion.hom.hom).flip
        ‹IsClosedImmersion B.inclusion.hom.hom.left›
    have h₂ : IsIso ((changeBaseComp a.left T.hom).inv.app G).hom.hom.left :=
      (Grp.forget (Over U.left) ⋙ Over.forget U.left).map_isIso
        ((changeBaseComp a.left T.hom).inv.app G)
    have h₃ : IsIso (changeBaseCongr (Over.w a) G).hom.hom.hom.left :=
      (Grp.forget (Over U.left) ⋙ Over.forget U.left).map_isIso
        (changeBaseCongr (Over.w a) G).hom
    exact IsClosedImmersion.comp _ _
  smooth := by
    change Smooth (pullback.snd B.group.X.hom a.left)
    have := B.smooth
    infer_instance

/-- The geometric fibres of a Borel family are Borel subgroups. -/
def IsBorelFamily {G : Grp (Over S)} {T : Over S} (B : Family G T) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (a : Spec (CommRingCat.of K) ⟶ T.left),
      ∃ h : IsClosedImmersion ((changeBase a).map B.inclusion).hom.hom.left,
        IsBorel (G := (changeBase a).obj ((changeBase T.hom).obj G))
          ⟨(changeBase a).obj B.group, (changeBase a).map B.inclusion, h⟩

/-- The same inclusion as a subgroup of the field fibre of the original group. -/
def Family.fieldSubgroup {G : Grp (Over S)} {k : Type u} [Field k]
    {a : Spec (CommRingCat.of k) ⟶ S} (B : Family G (Over.mk a)) :
    ClosedSubgroup ((changeBase a).obj G) :=
  ⟨B.group, B.inclusion, B.closed⟩

/-- The scheme and its universal Borel family represent Borel subgroups of
the model on test schemes. -/
structure Presentation (G : Grp (Over S)) where
  scheme : Over S
  smooth : Smooth scheme.hom
  universal : Family G scheme
  universalBorel : IsBorelFamily universal
  pullbackBorel : ∀ (T : Over S) (x : T ⟶ scheme), IsBorelFamily (universal.pullback x)
  represents : ∀ (T : Over S) (B : Family G T), IsBorelFamily B →
    ∃! x : T ⟶ scheme, SameFamily (universal.pullback x) B
  fieldClassifies : ∀ (k : Type u) [Field k] (a : Spec (CommRingCat.of k) ⟶ S)
    (B : ClosedSubgroup ((changeBase a).obj G)), IsKBorel B →
    ∃ x : Over.mk a ⟶ scheme,
      ∃ e : (universal.pullback x).group ≅ B.group,
        e.hom ≫ B.inclusion = (universal.pullback x).inclusion

abbrev ringSpec (R : Type u) [CommRing R] := Spec (CommRingCat.of R)

abbrev algebraSpecMap (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    ringSpec A ⟶ ringSpec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

/-- The scalar extension of the integral model to a ring. -/
abbrev integralSpecMap (R : Type u) [CommRing R] : ringSpec R ⟶ Base.{u} :=
  letI := integerAlgebra R
  algebraSpecMap Integers R

/-- Field fibres are affine algebraic groups with the original pulled back group law. -/
def affineFibre {G : Grp (Over S)} {k : Type u} [Field k] (a : ringSpec k ⟶ S)
    [IsAffineHom G.X.hom] [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] :
    AffineAlgebraicGroup k :=
  ⟨(changeBase a).obj G, by
    change IsAffine (pullback G.X.hom a) ∧ LocallyOfFiniteType (pullback.snd G.X.hom a) ∧
      QuasiCompact (pullback.snd G.X.hom a)
    exact ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The given model is identified with a split integral semisimple model after
a finite faithfully flat étale extension of the base ring. -/
def HasSplitModel {R : Type u} [CommRing R] (G : Grp (Over (ringSpec R))) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A)
    (_ : Module.Finite R A) (_ : Module.FaithfullyFlat R A) (_ : Algebra.Etale R A)
    (D : Pinning.BasedRootDatum.{u}) (_ : RootData.rationalRootAnnihilator D.datum = ⊥)
    (M : Model D),
    Nonempty
      ((changeBase (algebraSpecMap R A)).obj G ≅
        (changeBase (integralSpecMap A)).obj M.group)

/-- The geometric-fibre criterion gives a Borel in the field fibre of the
original model. -/
def FieldBorel : Prop :=
  ∀ {S : Scheme.{u}} {G : Grp (Over S)} {k : Type u} [Field k]
    {a : ringSpec k ⟶ S} (B : Family G (Over.mk a)),
    IsBorelFamily B → IsKBorel B.fieldSubgroup

/-- Smoothness of rational Borels, expressed using the original field group. -/
def FieldBorelSmooth : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} (B : ClosedSubgroup G),
    IsKBorel B → Smooth B.group.X.hom

/-- On an actual field fibre, pulling back the universal subgroup gives a
rational Borel. Each rational Borel gives a unique point whose pulled-back
family is isomorphic to it over the ambient group. -/
def FieldComparison : Prop :=
  ∀ {S : Scheme.{u}} {G : Grp (Over S)} (P : Presentation G)
    (k : Type u) [Field k] (a : ringSpec k ⟶ S),
    (∀ x : Over.mk a ⟶ P.scheme, IsKBorel (P.universal.pullback x).fieldSubgroup) ∧
    ∀ (B : ClosedSubgroup ((changeBase a).obj G)), IsKBorel B →
      ∃! x : Over.mk a ⟶ P.scheme,
        ∃ e : (P.universal.pullback x).group ≅ B.group,
          e.hom ≫ B.inclusion = (P.universal.pullback x).inclusion

/-- The canonical map defining the special fibre. -/
abbrev residueSpecMap (R : Type u) [CommRing R] [IsLocalRing R] :
    ringSpec (IsLocalRing.ResidueField R) ⟶ ringSpec R :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- Over the complete discrete valuation ring the Borel scheme is smooth and
represents the Borel families. Its field comparisons apply to the residue and
fraction-field fibres of the given model. -/
def Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Finite (IsLocalRing.ResidueField R)]
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
    (G : Grp (Over (ringSpec R))) [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom],
    Smooth G.X.hom →
    IsReductive (affineFibre (G := G) (residueSpecMap R)) →
    IsReductive (affineFibre (G := G) (algebraSpecMap R F)) →
    HasSplitModel G →
    Nonempty (Presentation G)

end

end LinearAlgebraicGroups.Specs.SmoothBorelParameter
