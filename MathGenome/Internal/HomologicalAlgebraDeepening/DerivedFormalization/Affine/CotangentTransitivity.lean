import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentTransitivity
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentDiagramComparison
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Pretriangulated

universe u v

namespace DerivedFormalization.Affine.CotangentTransitivity

open Specs.DerivedFormalization.Affine.CotangentTransitivity
open Specs.DerivedFormalization.Affine.CotangentDiagramComparison
open Specs.DerivedFormalization.Affine.ResolvedCotangentSequence
open Specs.DerivedFormalization.Affine.CotangentComplex (oneObject)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor)
open Specs.DerivedFormalization.DG
open Derived (HomotopyCategoryLaws quotient)
open DerivedKProjective (derivedCategoryInstance)
open LocalizedBimoduleExactness (classOfMap)
open DerivedBimoduleAdjunction (ConeLocalization)


set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option allowUnsafeReducibility true
attribute [local reducible] Derived.derivedCategory

noncomputable section

/-- Refine any pair of successive resolutions by its differential sequence and models. -/
theorem resolvedChainsExist : ResolvedChainsExist.{u,v} := by
  intro k _ _ T forms cmp coproducts X R
  obtain ⟨prod, hprod, _⟩ := coproducts
  obtain ⟨F, hF⟩ := ResolvedCotangentSequence.exactDifferentialSequence T forms R.P.base R.Q.base
    R.P.differentials R.absolute R.Q.differentials R.P.semifree R.Q.semifree
  let A := prod (underlying R.Q.base) (underlying R.P.augmentation)
  have hA : A.Formulas := hprod _ _
  obtain ⟨S⟩ := ResolvedCotangentSequence.pushoutResolves T forms cmp R.Q.base R.P.augmentation X.second
    R.Q.augmentation A hA R.Q.triangle R.Q.semifree R.P.quasiIso R.Q.surjective R.Q.quasiIso
  let W := Kahler.model (underlying (pushoutInr A hA))
  obtain ⟨hp, hf, ⟨I⟩, _, hL, hM, hN⟩ :=
    ResolvedCotangentSequence.resolvedTerms T forms cmp R.P R.Q R.absolute F A hA S W
  let Z : ResolvedChain T X :=
    ⟨R, F, fun _ e => Classical.choice (hF e),
      ResolvedCotangentSequence.concatenation _ _ R.P.semifree R.Q.semifree, A, hA, S, W, I, hp, hf, hL, hM, hN⟩
  exact ⟨Z, rfl⟩

section Naturality

variable {k : Type u} [Field k] [CharZero k] {T : ModuleTensor.{u,v} k}
variable {E : NonpositiveCDGA.{u,v} k} {h : HomotopyCategoryLaws (oneObject E)}
variable (K : ConeLocalization (oneObject E) h)
variable {X Y : Chain.{u,v} k} {R : ResolvedChain T X} {S : ResolvedChain T Y}
variable {e : X.C ⟶ E} {d : Y.C ⟶ E}

private theorem sequenceTriangle_unique (U V : SequenceTriangle K R.sequence e) : U = V := by
  letI := Derived.homotopyCategory (oneObject E) h
  letI := derivedCategoryInstance (oneObject E) h
  cases U with
  | mk q hq I hI hU =>
    cases V with
    | mk q' hq' I' hI' hV =>
      have eq : q = q' := by
        apply RightDGModule.strict_ext
        rintro ⟨⟩ n x
        exact (hq.1 n x).trans (hq'.1 n x).symm
      subst q'
      have eqI : I = I' := Iso.ext (hI.trans hI'.symm)
      subst I'
      rfl

open Specs.DerivedFormalization.Affine.Tensor (dgCat)
open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit)
open ShiftCone (cone coneProjection coneInclusion shift shiftMap)
open DerivedTriangles (coneTriangle)
open private conjugate_eqToHom localizedSequence_boundary strictNeg_comp comp_strictNeg
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentDiagramComparison
open private strictNeg from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeRotation

private theorem shiftNatural
    {M N : E.Module} (f : M ⟶ N) :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    let Q := quotient (oneObject E) h
    Q.map (classOfMap h (shiftMap 1 f)) ≫ (K.onShift N 1).hom =
      (K.onShift M 1).hom ≫ (shiftFunctor _ (1 : ℤ)).map (Q.map (classOfMap h f)) := by
  letI := Derived.homotopyCategory (oneObject E) h
  letI := derivedCategoryInstance (oneObject E) h
  letI := K.shiftK
  letI := K.shiftD
  let D := Derived.derivedCategory (oneObject E) h
  let Q : HomComplex.homotopyCategory (oneObject E) ⥤ D := quotient (oneObject E) h
  letI : Q.CommShift ℤ := K.quotientShift
  let η := (Q.commShiftIso (1 : ℤ)).hom
  let m := classOfMap h f
  let a := eqToHom (K.shiftObj M 1).symm
  let b := eqToHom (K.shiftObj N 1).symm
  have hK : classOfMap h (shiftMap 1 f) ≫ b = a ≫ (shiftFunctor _ (1 : ℤ)).map m :=
    conjugate_eqToHom _ _ (K.shiftMap f 1).symm
  have hD (P : E.Module) : (K.onShift P 1).hom =
      Q.map (eqToHom (K.shiftObj P 1).symm) ≫ η.app P := by
    change eqToHom (congrArg Q.obj (K.shiftObj P 1).symm) ≫ η.app P = _
    rw [eqToHom_map]
  have hη := η.naturality m
  change Q.map ((shiftFunctor _ (1 : ℤ)).map m) ≫ η.app N =
    η.app M ≫ (shiftFunctor _ (1 : ℤ)).map (Q.map m) at hη
  rw [hD M, hD N]
  calc
    _ = Q.map (classOfMap h (shiftMap 1 f) ≫ b) ≫ η.app N := by
      rw [Q.map_comp, Category.assoc]
    _ = _ := by rw [hK, Q.map_comp, Category.assoc, hη, Category.assoc]

private theorem localizedComparison
    {L M N L' M' N' : E.Module} {i : L ⟶ M} {p : M ⟶ N} {i' : L' ⟶ M'} {p' : M' ⟶ N'}
    (A : GradedSplit i p) (B : GradedSplit i' p') :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    letI := K.addD
    letI := K.zeroD
    letI := K.addShiftD
    letI := K.trianglesD
    let Q := quotient (oneObject E) h
    ∃ (q : cone i ⟶ N) (q' : cone i' ⟶ N')
      (a : Q.obj (cone i) ≅ Q.obj N) (b : Q.obj (cone i') ≅ Q.obj N'),
      IsConeQuotient p q ∧ IsConeQuotient p' q' ∧
      a.hom = Q.map (classOfMap h q) ∧ b.hom = Q.map (classOfMap h q') ∧
      let U := localizedSequenceTriangle h K i p a
      let V := localizedSequenceTriangle h K i' p' b
      U ∈ distTriang (Derived.derivedCategory (oneObject E) h) ∧
      V ∈ distTriang (Derived.derivedCategory (oneObject E) h) ∧
      ∃ m : SequenceMap i p i' p' → (U ⟶ V),
        (∀ f, (m f).hom₁ = Q.map (classOfMap h f.left) ∧ (m f).hom₂ = Q.map (classOfMap h f.middle) ∧
          (m f).hom₃ = Q.map (classOfMap h f.right)) ∧
        ∀ f g, SequenceHomotopy f g → m f = m g := by
  letI := Derived.homotopyCategory (oneObject E) h
  letI := derivedCategoryInstance (oneObject E) h
  letI := K.shiftK
  letI := K.shiftD
  letI := K.addD
  letI := K.zeroD
  letI := K.addShiftD
  letI := K.trianglesD
  let D := Derived.derivedCategory (oneObject E) h
  let Q : HomComplex.homotopyCategory (oneObject E) ⥤ D := quotient (oneObject E) h
  letI : Q.CommShift ℤ := K.quotientShift
  let J : E.Module ⥤ D := RightDGModule.toHomotopyCategory (oneObject E) ⋙ Q
  obtain ⟨q, q', co, hq, hq', hc, _⟩ := CotangentDiagramComparison.coneComparisons A B
  letI : IsIso (J.map q) := (Derived.quasiIsomorphisms (oneObject E)).Q_inverts _ ⟨q, rfl, hq.2⟩
  letI : IsIso (J.map q') := (Derived.quasiIsomorphisms (oneObject E)).Q_inverts _ ⟨q', rfl, hq'.2⟩
  let a := asIso (J.map q)
  let b := asIso (J.map q')
  let U := localizedSequenceTriangle h K i p a
  let V := localizedSequenceTriangle h K i' p' b
  have distinguished {L M N : E.Module} {i : L ⟶ M} {p : M ⟶ N} {q : cone i ⟶ N}
      (hq : IsConeQuotient p q) (e : J.obj (cone i) ≅ J.obj N) (he : e.hom = J.map q) :
      localizedSequenceTriangle h K i p e ∈ distTriang (Derived.derivedCategory (oneObject E) h) := by
    let W := Q.mapTriangle.obj (coneTriangle h K.shiftK (K.shiftObj L 1) i)
    have hqp : coneInclusion i ≫ q = p := by
      apply RightDGModule.strict_ext
      rintro ⟨⟩ n x
      exact hq.1 n (x, 0)
    let z : W ≅ localizedSequenceTriangle h K i p e :=
      Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
        (by
          change J.map i ≫ 𝟙 _ = 𝟙 _ ≫ J.map i
          rw [Category.comp_id, Category.id_comp])
        (by
          change J.map (coneInclusion i) ≫ e.hom = 𝟙 _ ≫ J.map p
          rw [he, ← J.map_comp, hqp, Category.id_comp])
        (by
          change W.mor₃ ≫ (shiftFunctor D (1 : ℤ)).map (𝟙 W.obj₁) = e.hom ≫ e.inv ≫ W.mor₃
          rw [(shiftFunctor D (1 : ℤ)).map_id, Category.comp_id, Iso.hom_inv_id_assoc])
    exact isomorphic_distinguished _ (K.localizedConeTriangles.1 i) _ z.symm
  let m (f : SequenceMap i p i' p') : U ⟶ V :=
    Triangle.homMk _ _ (J.map f.left) (J.map f.middle) (J.map f.right)
      (by
        change J.map i ≫ J.map f.middle = J.map f.left ≫ J.map i'
        rw [← J.map_comp, ← J.map_comp, f.incl_comm])
      (by
        change J.map p ≫ J.map f.right = J.map f.middle ≫ J.map p'
        rw [← J.map_comp, ← J.map_comp, f.proj_comm])
      (by
        have hs : co f ≫ strictNeg (coneProjection i') =
            strictNeg (coneProjection i) ≫ shiftMap 1 f.left := by
          rw [comp_strictNeg, strictNeg_comp, (hc f).2.2.1]
        have hq₀ : a.inv ≫ J.map (co f) = J.map f.right ≫ b.inv := by
          apply (cancel_mono b.hom).mp
          change (a.inv ≫ J.map (co f)) ≫ J.map q' = (J.map f.right ≫ b.inv) ≫ b.hom
          rw [Category.assoc, Category.assoc, b.inv_hom_id, Category.comp_id, ← J.map_comp,
            (hc f).2.2.2, J.map_comp]
          exact a.inv_hom_id_assoc _
        have hu := localizedSequence_boundary h K i p a
        have hv := localizedSequence_boundary h K i' p' b
        change U.mor₃ ≫ (shiftFunctor D (1 : ℤ)).map (J.map f.left) = J.map f.right ≫ V.mor₃
        change U.mor₃ = a.inv ≫ J.map (strictNeg (coneProjection i)) ≫ (K.onShift L 1).hom at hu
        change V.mor₃ = b.inv ≫ J.map (strictNeg (coneProjection i')) ≫ (K.onShift L' 1).hom at hv
        rw [hu, hv]
        simp only [Category.assoc]
        have hsh : J.map (shiftMap 1 f.left) ≫ (K.onShift L' 1).hom =
            (K.onShift L 1).hom ≫ (shiftFunctor D (1 : ℤ)).map (J.map f.left) :=
          shiftNatural K f.left
        rw [← hsh, ← Category.assoc (J.map (strictNeg (coneProjection i))),
          ← J.map_comp, ← hs, J.map_comp]
        simpa only [Category.assoc] using congrArg
          (fun m => m ≫ J.map (strictNeg (coneProjection i')) ≫ (K.onShift L' 1).hom) hq₀)
  refine ⟨q, q', a, b, hq, hq', rfl, rfl, distinguished hq a rfl, distinguished hq' b rfl,
    m, fun f => ⟨rfl, rfl, rfl⟩, ?_⟩
  intro f g H
  apply Triangle.hom_ext
  · exact congrArg Q.map ((RightDGModule.homotopyCriterion _ _).2 ⟨H.left, H.left_eq⟩)
  · exact congrArg Q.map ((RightDGModule.homotopyCriterion _ _).2 ⟨H.middle, H.middle_eq⟩)
  · exact congrArg Q.map ((RightDGModule.homotopyCriterion _ _).2 ⟨H.right, H.right_eq⟩)

private theorem sequenceTriangles_compare (R : ResolvedChain T X) (S : ResolvedChain T Y)
    (e : X.C ⟶ E) (d : Y.C ⟶ E) :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    let Q := quotient (oneObject E) h
    ∃ (U : SequenceTriangle K R.sequence e) (V : SequenceTriangle K S.sequence d)
      (m : MapAt R.sequence S.sequence e d → (U.triangle ⟶ V.triangle)),
      (∀ f, (m f).hom₁ = Q.map (classOfMap h f.left) ∧
        (m f).hom₂ = Q.map (classOfMap h f.middle) ∧ (m f).hom₃ = Q.map (classOfMap h f.right)) ∧
      ∀ f g, SequenceHomotopy f g → m f = m g := by
  letI := Derived.homotopyCategory (oneObject E) h
  letI := derivedCategoryInstance (oneObject E) h
  letI := K.shiftD
  obtain ⟨q, q', I, I', hq, hq', he, he', hU, hV, m, hm, hh⟩ :=
    localizedComparison K (R.split _ (underlying (R.resolution.Q.augmentation ≫ e)))
      (S.split _ (underlying (S.resolution.Q.augmentation ≫ d)))
  exact ⟨⟨q, hq, I, he, hU⟩, ⟨q', hq', I', he', hV⟩, m, hm, hh⟩

private theorem compare_chosen_triangles
    (U : SequenceTriangle K R.sequence e) (V : SequenceTriangle K S.sequence d) :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := derivedCategoryInstance (oneObject E) h
    letI := K.shiftD
    let Q := quotient (oneObject E) h
    ∃ m : MapAt R.sequence S.sequence e d → (U.triangle ⟶ V.triangle),
      (∀ f, (m f).hom₁ = Q.map (classOfMap h f.left) ∧
        (m f).hom₂ = Q.map (classOfMap h f.middle) ∧ (m f).hom₃ = Q.map (classOfMap h f.right)) ∧
      ∀ f g, SequenceHomotopy f g → m f = m g := by
  letI := Derived.homotopyCategory (oneObject E) h
  letI := derivedCategoryInstance (oneObject E) h
  letI := K.shiftD
  obtain ⟨U', V', m, hm, hh⟩ := sequenceTriangles_compare K R S e d
  cases sequenceTriangle_unique K U U'
  cases sequenceTriangle_unique K V V'
  exact ⟨m, hm, hh⟩

private theorem chain_id_comp_id (X : Chain.{u,v} k) :
    (ChainMap.id X).comp (ChainMap.id X) = ChainMap.id X := by
  simp [ChainMap.comp, ChainMap.id]

/-- At fixed final coefficients, the canonical comparison is functorial on chain maps. -/
theorem naturalSequenceTriangles : NaturalSequenceTriangles.{u,v} := by
  intro k _ _ T forms cmp E h K
  classical
  letI := Derived.homotopyCategory (oneObject E) h
  letI := derivedCategoryInstance (oneObject E) h
  letI := K.shiftD
  let Q := quotient (oneObject E) h
  let J := RightDGModule.toHomotopyCategory (oneObject E) ⋙ Q
  obtain ⟨s⟩ := CotangentDiagramComparison.strictSequenceComparisons T forms cmp E
  let tri (X : Chain.{u,v} k) (R : ResolvedChain T X) (e : X.C ⟶ E) :=
    Classical.choose (sequenceTriangles_compare K R R e e)
  let compare {X Y : Chain.{u,v} k} (R : ResolvedChain T X) (S : ResolvedChain T Y)
      (e : X.C ⟶ E) (d : Y.C ⟶ E) :=
    Classical.choose (compare_chosen_triangles K (tri X R e) (tri Y S d))
  have compareSpec {X Y : Chain.{u,v} k} (R : ResolvedChain T X) (S : ResolvedChain T Y)
      (e : X.C ⟶ E) (d : Y.C ⟶ E) :=
    Classical.choose_spec (compare_chosen_triangles K (tri X R e) (tri Y S d))
  let lift {X Y : Chain.{u,v} k} (f : ChainMap X Y) (R : ResolvedChain T X) (S : ResolvedChain T Y) :=
    Classical.choice (CotangentDiagramComparison.liftsExist f R.resolution S.resolution)
  let map {X Y : Chain.{u,v} k} (f : ChainMap X Y) (R : ResolvedChain T X) (S : ResolvedChain T Y)
      (e : X.C ⟶ E) (d : Y.C ⟶ E) (he : e = f.c ≫ d) :=
    compare R S e d (s.map (lift f R S) R.sequence S.sequence e d he)
  have components {X Y : Chain.{u,v} k} {f : ChainMap X Y}
      (R : ResolvedChain T X) (S : ResolvedChain T Y) (e : X.C ⟶ E) (d : Y.C ⟶ E)
      (he : e = f.c ≫ d) (l : Lift f R.resolution S.resolution) :
      let m := s.map l R.sequence S.sequence e d he
      let n := map f R S e d he
      n.hom₁ = J.map m.left ∧ n.hom₂ = J.map m.middle ∧ n.hom₃ = J.map m.right := by
    obtain ⟨H⟩ := CotangentDiagramComparison.sequenceComparisons T forms cmp E s l (lift f R S)
      R.sequence S.sequence e d he
    have eq := (compareSpec R S e d).2 _ _ H
    have hm := (compareSpec R S e d).1 (s.map l R.sequence S.sequence e d he)
    rw [← eq] at hm
    exact hm
  have identity (X : Chain.{u,v} k) (R : ResolvedChain T X) (e : X.C ⟶ E) :
      map (ChainMap.id X) R R e e (Category.id_comp e).symm = 𝟙 _ := by
    obtain ⟨a, b, c⟩ := components R R e e (Category.id_comp e).symm (Lift.id R.resolution)
    rw [s.identity] at a b c
    exact Triangle.hom_ext _ _
      (a.trans (J.map_id _)) (b.trans (J.map_id _)) (c.trans (J.map_id _))
  have composition {X Y Z : Chain.{u,v} k} (f : ChainMap X Y) (g : ChainMap Y Z)
      (R : ResolvedChain T X) (S : ResolvedChain T Y) (V : ResolvedChain T Z)
      (e : X.C ⟶ E) (d : Y.C ⟶ E) (c : Z.C ⟶ E) (hf : e = f.c ≫ d) (hg : d = g.c ≫ c) :
      map (f.comp g) R V e c (by rw [hf, hg]; exact (Category.assoc _ _ _).symm) =
        map f R S e d hf ≫ map g S V d c hg := by
    let l := lift f R S
    let m := lift g S V
    obtain ⟨a, b, c'⟩ := components R V e c
      (by rw [hf, hg]; exact (Category.assoc _ _ _).symm) (l.comp m)
    rw [s.composition l m R.sequence S.sequence V.sequence e d c hf hg] at a b c'
    obtain ⟨a₁, b₁, c₁⟩ := components R S e d hf l
    obtain ⟨a₂, b₂, c₂⟩ := components S V d c hg m
    apply TriangleMorphism.ext
    · exact a.trans ((J.map_comp _ _).trans (congrArg₂ (· ≫ ·) a₁.symm a₂.symm))
    · exact b.trans ((J.map_comp _ _).trans (congrArg₂ (· ≫ ·) b₁.symm b₂.symm))
    · exact c'.trans ((J.map_comp _ _).trans (congrArg₂ (· ≫ ·) c₁.symm c₂.symm))
  refine ⟨⟨s, tri, @map, @components, identity, @composition, ?_⟩⟩
  intro X R S e
  let f := ChainMap.id X
  have he : e = f.c ≫ e := (Category.id_comp e).symm
  refine ⟨⟨map f S R e e he, ?_, ?_⟩⟩
  · rw [← composition f f R S R e e e he he]
    simpa only [f, chain_id_comp_id] using identity X R e
  · rw [← composition f f S R S e e e he he]
    simpa only [f, chain_id_comp_id] using identity X S e

end Naturality

section Identifications

open Specs.DerivedFormalization.Affine.CotangentComplex (localizedModel moduleClass)

private def triangleTransport {D : Type*} [Category D] [HasShift D ℤ]
    (U : Triangle D) {L M N : D} (a : U.obj₁ ≅ L) (b : U.obj₂ ≅ M) (c : U.obj₃ ≅ N)
    (i : L ⟶ M) (p : M ⟶ N)
    (hi : U.mor₁ ≫ b.hom = a.hom ≫ i) (hp : U.mor₂ ≫ c.hom = b.hom ≫ p) :
    U ≅ Triangle.mk i p (c.inv ≫ U.mor₃ ≫ (shiftFunctor D (1 : ℤ)).map a.hom) :=
  Triangle.isoMk _ _ a b c hi hp (by
    change _ = c.hom ≫ c.inv ≫ _
    rw [Iso.hom_inv_id_assoc])

private theorem changeAugmentation {k : Type u} [Field k] [CharZero k]
    {T : ModuleTensor.{u,v} k} {P E : NonpositiveCDGA.{u,v} k}
    {f g : P ⟶ E} (e : f = g) {U V : P.Module} (a : U ⟶ V)
    {D : Type*} [Category D] (J : E.Module ⥤ D) :
    J.map ((extend T f).map a) ≫ eqToHom (congrArg J.obj (congrArg (fun t => (extend T t).obj V) e)) =
    eqToHom (congrArg J.obj (congrArg (fun t => (extend T t).obj U) e)) ≫ J.map ((extend T g).map a) := by
  subst g
  simp

/-- The differential sequence gives the triangle with the designated cotangent arrows. -/
theorem identifiedTriangles : IdentifiedTriangles.{u,v} := by
  intro k _ _ T X hB hC K E R U
  letI := Derived.homotopyCategory (oneObject X.C) hC
  letI := derivedCategoryInstance (oneObject X.B) hB
  letI := derivedCategoryInstance (oneObject X.C) hC
  letI := K.shiftD
  letI := K.addD
  letI := K.zeroD
  letI := K.addShiftD
  letI := K.trianglesD
  let Q := quotient (oneObject X.C) hC
  let J := RightDGModule.toHomotopyCategory (oneObject X.C) ⋙ Q
  let F := R.sequence
  let I := R.identifications
  let a := E.onProjective (R.resolution.P.module T) R.baseProjective
  obtain ⟨l, m, r, hl, hm, hr, hi, hp⟩ :=
    ResolvedCotangentSequence.localizedTerms R.resolution.absolute R.absoluteSemifree
      I F hB hC E R.baseProjective
  let z := R.resolution.Q.augmentation
  let e (M : R.resolution.Q.algebra.Module) :
      J.obj ((extend T (z ≫ 𝟙 _)).obj M) ≅ J.obj ((extend T z).obj M) :=
    eqToIso (congrArg J.obj (congrArg (fun t => (extend T t).obj M) (Category.comp_id z)))
  let l' := e (resolutionLeft T R.resolution) ≪≫ l.symm
  let m' := e R.resolution.absolute.module ≪≫ m
  let r' := e R.resolution.Q.differentials.module ≪≫ r
  let i := a.hom ≫ J.map (I.inclusion F)
  let p := J.map (I.projection F)
  have hin : U.triangle.mor₁ ≫ m'.hom = l'.hom ≫ i := by
    change J.map ((extend T (z ≫ 𝟙 _)).map F.incl) ≫
      ((e R.resolution.absolute.module).hom ≫ m.hom) =
      ((e (resolutionLeft T R.resolution)).hom ≫ l.inv) ≫ i
    have hx : J.map ((extend T (z ≫ 𝟙 _)).map F.incl) ≫ (e R.resolution.absolute.module).hom =
        (e (resolutionLeft T R.resolution)).hom ≫ J.map ((extend T z).map F.incl) :=
      changeAugmentation (T := T) (Category.comp_id z) F.incl J
    have hy : J.map ((extend T z).map F.incl) ≫ m.hom = l.inv ≫ i :=
      (l.inv_comp_eq.mpr hi.symm).symm
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ m.hom) hx).trans ((Category.assoc _ _ _).trans
        ((congrArg ((e (resolutionLeft T R.resolution)).hom ≫ ·) hy).trans (Category.assoc _ _ _).symm)))
  have hpr : U.triangle.mor₂ ≫ r'.hom = m'.hom ≫ p := by
    change J.map ((extend T (z ≫ 𝟙 _)).map F.proj) ≫
      ((e R.resolution.Q.differentials.module).hom ≫ r.hom) =
      ((e R.resolution.absolute.module).hom ≫ m.hom) ≫ p
    have hx : J.map ((extend T (z ≫ 𝟙 _)).map F.proj) ≫ (e R.resolution.Q.differentials.module).hom =
        (e R.resolution.absolute.module).hom ≫ J.map ((extend T z).map F.proj) :=
      changeAugmentation (T := T) (Category.comp_id z) F.proj J
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ r.hom) hx).trans ((Category.assoc _ _ _).trans
        ((congrArg ((e R.resolution.absolute.module).hom ≫ ·) hp).trans (Category.assoc _ _ _).symm)))
  let j := triangleTransport U.triangle l' m' r' i p hin hpr
  refine ⟨_, isomorphic_distinguished _ U.distinguished _ j.symm, j, ?_, ?_, ?_⟩
  · change l.hom ≫ (e (resolutionLeft T R.resolution)).inv = _
    rw [hl, Category.assoc]
    rfl
  · change m.inv ≫ (e R.resolution.absolute.module).inv = _
    have hmi : m.inv = 𝟙 _ := by
      have he := m.hom_inv_id
      rw [hm, Category.id_comp] at he
      exact he
    rw [hmi, Category.id_comp]
    rfl
  · change (e R.resolution.Q.differentials.module).hom ≫ r.hom = _
    rw [hr]
    rfl

end Identifications

section Extension
open ShiftCone (cone)
open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit)

open Specs.DerivedFormalization.Affine.Tensor (regular)
open Specs.DerivedFormalization.Affine.DerivedTensor (ScalarExtension)
open BimoduleAdjunction (ordinaryTensor)
open private extensionAssociator_exists extendGradedSplit
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentDiagramComparison

private theorem coneQuotientIso_unique
    {k : Type u} [Field k] [CharZero k] {D : NonpositiveCDGA.{u,v} k}
    (h : HomotopyCategoryLaws (oneObject D))
    {L M N : D.Module} {i : L ⟶ M} {p : M ⟶ N} {q q' : cone i ⟶ N}
    (hq : IsConeQuotient p q) (hq' : IsConeQuotient p q') :
    letI := Derived.homotopyCategory (oneObject D) h
    letI := derivedCategoryInstance (oneObject D) h
    let Q := quotient (oneObject D) h
    ∀ (a b : Q.obj (cone i) ≅ Q.obj N),
      a.hom = Q.map (classOfMap h q) → b.hom = Q.map (classOfMap h q') → a = b := by
  letI := Derived.homotopyCategory (oneObject D) h
  letI := derivedCategoryInstance (oneObject D) h
  dsimp only
  intro a b ha hb
  have hq₀ : q = q' := by
    apply RightDGModule.strict_ext
    rintro ⟨⟩ n x
    exact (hq.1 n x).trans (hq'.1 n x).symm
  subst q'
  exact Iso.ext (ha.trans hb.symm)

/-- Derived scalar extension of the constructed sequence triangle, with all its arrows. -/
theorem extendedTriangles : ExtendedTriangles.{u,v} := by
  intro k _ _ T forms cmp X D w hC hD E R
  letI := Derived.homotopyCategory (oneObject X.C) hC
  letI := Derived.homotopyCategory (oneObject D) hD
  letI := derivedCategoryInstance (oneObject X.C) hC
  letI := derivedCategoryInstance (oneObject D) hD
  let Q := quotient (oneObject D) hD
  let J := RightDGModule.toHomotopyCategory (oneObject D) ⋙ Q
  let G := ordinaryTensor E.models.tensor
  let F := R.sequence
  let i := inclusionAt F (𝟙 X.C)
  let p := projectionAt F (𝟙 X.C)
  let A := R.split _ (underlying (R.resolution.Q.augmentation ≫ 𝟙 X.C))
  obtain ⟨q, _, _, hq, _, _, _⟩ :=
    CotangentDiagramComparison.coneComparisons A A
  obtain ⟨KC, KD, s, q', e, e', hq', he, he', j, hj₁, hj₂, hj₃⟩ :=
    CotangentDiagramComparison.derivedTriangleExtension forms hC hD E q A hq
      (projectiveAtIdentity R).1 (projectiveAtIdentity R).2.1 (projectiveAtIdentity R).2.2
  letI := KC.shiftD
  letI := KD.shiftD
  letI : E.functor.CommShift ℤ := s
  letI := KD.addD
  letI := KD.zeroD
  letI := KD.addShiftD
  letI := KD.trianglesD
  refine ⟨KC, KD, s, ?_⟩
  intro NC ND
  let U := NC.triangle X R (𝟙 X.C)
  let V := ND.triangle X R w
  have hU : e = U.quotientIso :=
    coneQuotientIso_unique hC hq U.quotientFormula e U.quotientIso he U.quotientIso_hom
  obtain ⟨a⟩ := extensionAssociator_exists T forms cmp R.resolution.Q.augmentation (𝟙 X.C) w
  let b := extendedSequenceIso w E a
  have B : GradedSplit (G.map i) (G.map p) := by
    have hG : G = extend T w := E.strict
    have hB := extendGradedSplit T (underlying w) (forms (underlying w) (regular D.toCommDGAlgebra)) A
    rw [hG]
    exact hB
  let B' := R.split _ (underlying (R.resolution.Q.augmentation ≫ w))
  obtain ⟨q₁, q₂, e₁, e₂, h₁, h₂, he₁, he₂, _, _, m, hm, _⟩ :=
    localizedComparison KD B B'
  have h₁' : e₁ = e' := coneQuotientIso_unique hD h₁ hq' e₁ e' he₁ he'
  have h₂' : e₂ = V.quotientIso :=
    coneQuotientIso_unique hD h₂ V.quotientFormula e₂ V.quotientIso he₂ V.quotientIso_hom
  subst e
  subst e₁
  subst e₂
  let z : SequenceMap (G.map i) (G.map p) (inclusionAt F w) (projectionAt F w) :=
    ⟨b.hom.app (resolutionLeft T R.resolution), b.hom.app R.resolution.absolute.module,
      b.hom.app R.resolution.Q.differentials.module, b.hom.naturality F.incl, b.hom.naturality F.proj⟩
  obtain ⟨hc₁, hc₂, hc₃⟩ := hm z
  letI : IsIso (m z).hom₁ := hc₁.symm ▸
    (inferInstance : IsIso (J.map ((b.app (resolutionLeft T R.resolution)).hom)))
  letI : IsIso (m z).hom₂ := hc₂.symm ▸
    (inferInstance : IsIso (J.map ((b.app R.resolution.absolute.module).hom)))
  letI : IsIso (m z).hom₃ := hc₃.symm ▸
    (inferInstance : IsIso (J.map ((b.app R.resolution.Q.differentials.module).hom)))
  letI : IsIso (m z) := Triangle.isIso_of_isIsos _ inferInstance inferInstance inferInstance
  let j' := j ≪≫ asIso (m z)
  refine ⟨a, j', isomorphic_distinguished _ V.distinguished _ j', ?_, ?_, ?_, ?_⟩
  · exact congrArg₂ (· ≫ ·) hj₁ hc₁
  · exact congrArg₂ (· ≫ ·) hj₂ hc₂
  · exact congrArg₂ (· ≫ ·) hj₃ hc₃
  · intro Y f S d he l
    obtain ⟨h₁, h₂, h₃⟩ := ND.components R S w d he l
    have hn₁ := congrArg (j'.hom.hom₁ ≫ ·) h₁
    have hn₂ := congrArg (j'.hom.hom₂ ≫ ·) h₂
    have hn₃ := congrArg (j'.hom.hom₃ ≫ ·) h₃
    refine ⟨hn₁, hn₂, hn₃, ?_⟩
    intro U' V' a₁ a₂
    let n := j'.hom ≫ ND.map f R S w d he
    refine ⟨E.functor.mapTriangle.map a₁.inv ≫ n ≫ a₂.hom, ?_, ?_, ?_⟩
    · change E.functor.map a₁.inv.hom₁ ≫ n.hom₁ ≫ a₂.hom.hom₁ = _
      exact congrArg (fun m => E.functor.map a₁.inv.hom₁ ≫ m ≫ a₂.hom.hom₁) hn₁ |>.trans
        (congrArg (E.functor.map a₁.inv.hom₁ ≫ ·) (Category.assoc _ _ _))
    · change E.functor.map a₁.inv.hom₂ ≫ n.hom₂ ≫ a₂.hom.hom₂ = _
      exact congrArg (fun m => E.functor.map a₁.inv.hom₂ ≫ m ≫ a₂.hom.hom₂) hn₂ |>.trans
        (congrArg (E.functor.map a₁.inv.hom₂ ≫ ·) (Category.assoc _ _ _))
    · change E.functor.map a₁.inv.hom₃ ≫ n.hom₃ ≫ a₂.hom.hom₃ = _
      exact congrArg (fun m => E.functor.map a₁.inv.hom₃ ≫ m ≫ a₂.hom.hom₃) hn₃ |>.trans
        (congrArg (E.functor.map a₁.inv.hom₃ ≫ ·) (Category.assoc _ _ _))

end Extension

open private localizedSequence_boundary from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentDiagramComparison

/-- The normalized shift identifies the boundaries in any two realizations
of the cone localization on the same derived category. -/
theorem boundaryComparison : BoundaryComparison.{u,v} := by
  intro k _ _ T E h K K'
  letI := Derived.homotopyCategory (oneObject E) h
  letI := derivedCategoryInstance (oneObject E) h
  let D := Derived.derivedCategory (oneObject E) h
  let Q : HomComplex.homotopyCategory (oneObject E) ⥤ D := quotient (oneObject E) h
  let A := translation K
  let B := translation K'
  let σ : Q ⋙ A ≅ Q ⋙ B := NatIso.ofComponents
    (fun M => (K.onShift M 1).symm ≪≫ K'.onShift M 1) (by
      intro M N g
      obtain ⟨f, rfl⟩ := RightDGModule.homotopyClass_surjective g
      let a := K.onShift M 1
      let b := K.onShift N 1
      let a' := K'.onShift M 1
      let b' := K'.onShift N 1
      let m := Q.map (classOfMap h f)
      let n := Q.map (classOfMap h (ShiftCone.shiftMap 1 f))
      have hm : n ≫ b.hom = a.hom ≫ A.map m := shiftNatural K f
      have hn : n ≫ b'.hom = a'.hom ≫ B.map m := shiftNatural K' f
      change A.map m ≫ (b.inv ≫ b'.hom) = (a.inv ≫ a'.hom) ≫ B.map m
      rw [← cancel_epi a.hom, Category.assoc, ← Category.assoc (a.hom) (A.map m),
        ← hm, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
      exact hn)
  let W := Derived.quasiIsomorphisms (oneObject E)
  letI : Q.IsLocalization W := inferInstanceAs (W.Q.IsLocalization W)
  letI : Localization.Lifting Q W (Q ⋙ A) A := ⟨Iso.refl _⟩
  letI : Localization.Lifting Q W (Q ⋙ B) B := ⟨Iso.refl _⟩
  let s := Localization.liftNatIso Q W (Q ⋙ A) (Q ⋙ B) A B σ
  have ss (M : E.Module) :
      (K.onShift M 1).hom ≫ s.hom.app (Q.obj M) = (K'.onShift M 1).hom := by
    have hs : s.hom.app (Q.obj M) = (K.onShift M 1).inv ≫ (K'.onShift M 1).hom := by
      change (Localization.liftNatTrans Q W (Q ⋙ A) (Q ⋙ B) A B σ.hom).app (Q.obj M) = _
      rw [Localization.liftNatTrans_app]
      change 𝟙 _ ≫ ((K.onShift M 1).inv ≫ (K'.onShift M 1).hom) ≫ 𝟙 _ = _
      simp only [Category.id_comp, Category.comp_id]
    rw [hs, Iso.hom_inv_id_assoc]
  refine ⟨s, ss, ?_⟩
  intro X R e U V
  let L := leftAt T R.resolution e
  have he : U.quotientIso = V.quotientIso :=
    coneQuotientIso_unique h U.quotientFormula V.quotientFormula _ _
      U.quotientIso_hom V.quotientIso_hom
  have hl := localizedSequence_boundary h K (inclusionAt R.sequence e) (projectionAt R.sequence e) U.quotientIso
  have hr := localizedSequence_boundary h K' (inclusionAt R.sequence e) (projectionAt R.sequence e) V.quotientIso
  change U.boundary ≫ s.hom.app (Q.obj L) = V.boundary
  change U.boundary = U.quotientIso.inv ≫ _ ≫ (K.onShift L 1).hom at hl
  change V.boundary = V.quotientIso.inv ≫ _ ≫ (K'.onShift L 1).hom at hr
  rw [hl, hr, he, Category.assoc, Category.assoc, ss]

open private laws scalarExtensionModel from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedTensor
open private coneLocalization from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.LocalizedBimoduleExactness

/-- The cotangent transitivity triangle at the common coefficient bound. -/
theorem cotangentTransitivity : Transitivity.{u,v} := by
  intro k _ _
  classical
  let T := Tensor.moduleTensorModel.{u,v} k
  let h (A : NonpositiveCDGA.{u,v} k) := laws A.toCommDGAlgebra
  let K (A : NonpositiveCDGA.{u,v} k) :=
    adjunctionConeLocalization (coneLocalization.{u,v,0} (oneObject A) (h A))
  let E {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B) := scalarExtensionModel (underlying f)
  have forms : TensorFormulas T := Tensor.moduleTensor_formulas
  have cmp : T.Comparisons := Tensor.moduleTensor_comparisons
  have prod : T.AlgebraCoproducts := Tensor.algebra_tensor_construction
  let N (A : NonpositiveCDGA.{u,v} k) : Naturality (K A) T :=
    Classical.choice (naturalSequenceTriangles T forms cmp A (h A) (K A))
  refine ⟨T, h, K, @E, N, ?_, ?_⟩
  · intro A B f
    exact CotangentComplex.nativeComparison f T (h B) forms
  · intro X
    obtain ⟨P, Q, _, ⟨W⟩⟩ := ResolvedCotangentSequence.resolutionsExist X.first X.second
    obtain ⟨R, _⟩ := resolvedChainsExist T forms cmp prod (X := X) ⟨P, Q, W⟩
    exact ⟨R, identifiedTriangles (h X.B) (h X.C) (K X.C) (E X.second) R
      ((N X.C).triangle X R (𝟙 X.C))⟩

section Coefficients

universe t

open Specs.DerivedFormalization.Affine.CotangentComplex (Model cdgaLift localizedModel)
open Specs.DerivedFormalization.Affine.DerivedTensor (liftAlgebra liftAlgebraMap)
open Specs.DerivedFormalization.Affine.Tensor (dgCat)
open private ambientDescent from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedTensor

variable {k : Type u} [Field k] [CharZero k]

open Specs.DerivedFormalization.Affine.DerivedTensor (liftInput)
open Specs.DerivedFormalization.Affine.Tensor (regular term)
open private liftTensorIso liftTensorIso_pure from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.DerivedTensor
open private differentialScalarMap_ext differentialDoubleScalarMap_ext
  inclusionAt_symbol projectionAt_symbol from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentDiagramComparison


/-- Extend an identified lifted module along the lifted coefficient map. -/
private def liftExtend {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B)
    {M : A.Module} {N : ((cdgaLift.{u,v,max v t} k).obj A).Module}
    (a : (liftInput.{u,v,t} A.toCommDGAlgebra).obj M ≅ N) :
    (liftInput.{u,v,t} B.toCommDGAlgebra).obj ((extend (Tensor.moduleTensorModel.{u,v} k) f).obj M) ≅
      (extend (Tensor.moduleTensorModel.{u,max v t} k) ((cdgaLift.{u,v,max v t} k).map f)).obj N :=
  liftTensorIso.{u,v,t} (underlying f) M (regular B.toCommDGAlgebra) ≪≫
    (extend (Tensor.moduleTensorModel.{u,max v t} k) ((cdgaLift.{u,v,max v t} k).map f)).mapIso a

private theorem liftExtend_tmul {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B)
    {M : A.Module} {N : ((cdgaLift.{u,v,max v t} k).obj A).Module}
    (a : (liftInput.{u,v,t} A.toCommDGAlgebra).obj M ≅ N)
    (i j n : ℤ) (h : i + j = n) (x : term M i) (y : B.complex.X j) :
    ((liftExtend f a).hom.app ()).f n
        (ULift.up ((Tensor.moduleTensorModel.{u,v} k).tmul (underlying f) (N := regular B.toCommDGAlgebra) i j n h x y)) =
      (Tensor.moduleTensorModel.{u,max v t} k).tmul (underlying ((cdgaLift.{u,v,max v t} k).map f))
        (N := regular ((cdgaLift.{u,v,max v t} k).obj B).toCommDGAlgebra)
        i j n h ((a.hom.app ()).f i (ULift.up x)) (ULift.up y) := by
  change (((extend (Tensor.moduleTensorModel.{u,max v t} k) ((cdgaLift.{u,v,max v t} k).map f)).map a.hom).app ()).f n
    (((liftTensorIso.{u,v,t} (underlying f) M (regular B.toCommDGAlgebra)).hom.app ()).f n
      (ULift.up ((Tensor.moduleTensorModel.{u,v} k).tmul (underlying f) (N := regular B.toCommDGAlgebra) i j n h x y))) = _
  let B' := (cdgaLift.{u,v,max v t} k).obj B
  let f' := (cdgaLift.{u,v,max v t} k).map f
  let m := (extend (Tensor.moduleTensorModel.{u,max v t} k) f').map a.hom
  have hp := liftTensorIso_pure.{u,v,t} (underlying f) M (regular B.toCommDGAlgebra) i j n h x y
  change (m.app ()).f n
    (((liftTensorIso.{u,v,t} (underlying f) M (regular B.toCommDGAlgebra)).hom.app ()).f n
      (ULift.up (Specs.DerivedFormalization.Affine.Tensor.pure (underlying f) (M := M) (N := regular B.toCommDGAlgebra) i j n h x y))) = _
  rw [hp]
  exact (Tensor.moduleTensor_formulas (underlying f') (regular B'.toCommDGAlgebra)).first
    a.hom i j n h (ULift.up x) (ULift.up y)

private def liftExtendAlong {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B)
    {f' : (cdgaLift.{u,v,max v t} k).obj A ⟶ (cdgaLift.{u,v,max v t} k).obj B}
    (hf : (cdgaLift.{u,v,max v t} k).map f = f')
    {M : A.Module} {N : ((cdgaLift.{u,v,max v t} k).obj A).Module}
    (a : (liftInput.{u,v,t} A.toCommDGAlgebra).obj M ≅ N) :
    (liftInput.{u,v,t} B.toCommDGAlgebra).obj ((extend (Tensor.moduleTensorModel.{u,v} k) f).obj M) ≅
      (extend (Tensor.moduleTensorModel.{u,max v t} k) f').obj N :=
  hf ▸ liftExtend f a

private theorem liftExtendAlong_tmul {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B)
    {f' : (cdgaLift.{u,v,max v t} k).obj A ⟶ (cdgaLift.{u,v,max v t} k).obj B}
    (hf : (cdgaLift.{u,v,max v t} k).map f = f')
    {M : A.Module} {N : ((cdgaLift.{u,v,max v t} k).obj A).Module}
    (a : (liftInput.{u,v,t} A.toCommDGAlgebra).obj M ≅ N)
    (i j n : ℤ) (h : i + j = n) (x : term M i) (y : B.complex.X j) :
    ((liftExtendAlong f hf a).hom.app ()).f n
        (ULift.up ((Tensor.moduleTensorModel.{u,v} k).tmul (underlying f) (N := regular B.toCommDGAlgebra) i j n h x y)) =
      (Tensor.moduleTensorModel.{u,max v t} k).tmul (underlying f')
        (N := regular ((cdgaLift.{u,v,max v t} k).obj B).toCommDGAlgebra)
        i j n h ((a.hom.app ()).f i (ULift.up x)) (ULift.up y) := by
  subst f'
  exact liftExtend_tmul f a i j n h x y

private def rebaseIso {A B : NonpositiveCDGA.{u,v} k} {f g : A ⟶ B}
    (h : f = g) (O : Differentials f) : O.module ≅ (rebaseDifferentials h O).module := by
  subst g
  exact Iso.refl _

private theorem rebaseIso_symbol {A B : NonpositiveCDGA.{u,v} k} {f g : A ⟶ B}
    (h : f = g) (O : Differentials f) (n : ℤ) (x : B.complex.X n) :
    (((rebaseIso h O).hom.app ()).f n) (symbol O n x) = symbol (rebaseDifferentials h O) n x := by
  subst g
  rfl

private theorem liftSquare {E : NonpositiveCDGA.{u,v} k}
    {L M : E.Module} {L' M' : ((cdgaLift.{u,v,max v t} k).obj E).Module}
    (a : (liftInput.{u,v,t} E.toCommDGAlgebra).obj L ≅ L')
    (b : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ≅ M')
    (f : L ⟶ M) (g : L' ⟶ M')
    {I : ℤ → Type*} (s : ∀ n, I n → term L n) (s' : ∀ n, I n → term L' n)
    (ha : ∀ n x, (a.hom.app ()).f n (ULift.up (s n x)) = s' n x)
    (hext : ∀ (p q : L' ⟶ M'), (∀ n x, (p.app ()).f n (s' n x) = (q.app ()).f n (s' n x)) →
      p = q)
    (h : ∀ n x, (b.hom.app ()).f n (ULift.up ((f.app ()).f n (s n x))) =
      (g.app ()).f n (s' n x)) :
    (liftInput.{u,v,t} E.toCommDGAlgebra).map f ≫ b.hom = a.hom ≫ g := by
  rw [← cancel_epi a.inv, Iso.inv_hom_id_assoc]
  apply hext
  intro n x
  have hx : (a.inv.app ()).f n (s' n x) = ULift.up (s n x) := by
    rw [← ha n x]
    let P := (liftInput.{u,v,t} E.toCommDGAlgebra).obj L
    have h := congrArg (fun p : P ⟶ P => (p.app ()).f n) a.hom_inv_id
    exact CategoryTheory.congr_fun h (ULift.up (s n x))
  change (b.hom.app ()).f n (ULift.up ((f.app ()).f n
    (((a.inv.app ()).f n (s' n x)).down))) = _
  rw [hx]
  exact h n x

private theorem liftSquareOnSymbols {E : NonpositiveCDGA.{u,v} k}
    {L M : E.Module} {L' M' : ((cdgaLift.{u,v,max v t} k).obj E).Module}
    (a : (liftInput.{u,v,t} E.toCommDGAlgebra).obj L ≅ L')
    (b : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ≅ M')
    (f : L ⟶ M) (g : L' ⟶ M')
    {I J : ℤ → Type v} (x : ∀ n, I n → term L n) (x' : ∀ n, I n → term L' n)
    (y : ∀ n, J n → term M n) (y' : ∀ n, J n → term M' n)
    (ha : ∀ n z, (a.hom.app ()).f n (ULift.up (x n z)) = x' n z)
    (hb : ∀ n z, (b.hom.app ()).f n (ULift.up (y n z)) = y' n z)
    (ρ : ∀ n, I n → J n)
    (hf : ∀ n z, (f.app ()).f n (x n z) = y n (ρ n z))
    (hg : ∀ n z, (g.app ()).f n (x' n z) = y' n (ρ n z))
    (hext : ∀ (p q : L' ⟶ M'), (∀ n z, (p.app ()).f n (x' n z) = (q.app ()).f n (x' n z)) →
      p = q) :
    (liftInput.{u,v,t} E.toCommDGAlgebra).map f ≫ b.hom = a.hom ≫ g :=
  liftSquare.{u,v,t} a b f g x x' ha hext (by
    intro n z
    rw [hf n z, hb n (ρ n z), hg n z])

private theorem leftAt_ext {X : Chain.{u,v} k} {R : Resolution X}
    {E : NonpositiveCDGA.{u,v} k} (e : X.C ⟶ E) {M : E.Module}
    {f g : leftAt (Tensor.moduleTensorModel.{u,v} k) R e ⟶ M}
    (h : ∀ n x, (f.app ()).f n (leftSymbol (Tensor.moduleTensorModel.{u,v} k) R e n x) =
      (g.app ()).f n (leftSymbol (Tensor.moduleTensorModel.{u,v} k) R e n x)) : f = g :=
  differentialDoubleScalarMap_ext (Tensor.moduleTensorModel.{u,v} k) Tensor.moduleTensor_formulas _ _ _
    R.P.differentials h

private theorem extendedDiff_ext {A Q E : NonpositiveCDGA.{u,v} k} {p : A ⟶ Q}
    (O : Differentials p) (e : Q ⟶ E) {M : E.Module}
    {f g : (extend (Tensor.moduleTensorModel.{u,v} k) e).obj O.module ⟶ M}
    (h : ∀ n x, (f.app ()).f n (extendedSymbol (Tensor.moduleTensorModel.{u,v} k) O e n 0 n (add_zero n) x E.one) =
      (g.app ()).f n (extendedSymbol (Tensor.moduleTensorModel.{u,v} k) O e n 0 n (add_zero n) x E.one)) : f = g :=
  differentialScalarMap_ext (Tensor.moduleTensorModel.{u,v} k) Tensor.moduleTensor_formulas _ _ O h

private def liftedAbsoluteIso {X : Chain.{u,v} k} {R : ResolvedChain (Tensor.moduleTensorModel.{u,v} k) X}
    (U : LiftedResolution.{u,v,t} (Tensor.moduleTensorModel.{u,max v t} k) R) :
    (liftInput.{u,v,t} R.resolution.Q.algebra.toCommDGAlgebra).obj R.resolution.absolute.module ≅
      U.resolution.absolute.module :=
  U.absolute.differentialIso ≪≫ rebaseIso ((cdgaLift.{u,v,max v t} k).map_comp _ _) U.absolute.differentials

private theorem liftedAbsoluteIso_symbol {X : Chain.{u,v} k} {R : ResolvedChain (Tensor.moduleTensorModel.{u,v} k) X}
    (U : LiftedResolution.{u,v,t} (Tensor.moduleTensorModel.{u,max v t} k) R) (n : ℤ) (x : R.resolution.Q.algebra.complex.X n) :
    ((liftedAbsoluteIso U).hom.app ()).f n (ULift.up (symbol R.resolution.absolute n x)) =
      symbol U.resolution.absolute n (ULift.up x) := by
  change (((rebaseIso ((cdgaLift.{u,v,max v t} k).map_comp _ _) U.absolute.differentials).hom.app ()).f n)
    ((U.absolute.differentialIso.hom.app ()).f n (ULift.up (symbol R.resolution.absolute n x))) = _
  rw [show (U.absolute.differentialIso.hom.app ()).f n (ULift.up (symbol R.resolution.absolute n x)) =
    symbol U.absolute.differentials n (ULift.up x) from U.absolute.symbol n x]
  exact rebaseIso_symbol.{u,max v t}
    ((cdgaLift.{u,v,max v t} k).map_comp R.resolution.P.base R.resolution.Q.base)
    U.absolute.differentials n (ULift.up x)

/-- A strict module comparison and its action on the chosen homogeneous symbols. -/
private structure SymbolLift {E : NonpositiveCDGA.{u,v} k}
    {M : E.Module} {M' : ((cdgaLift.{u,v,max v t} k).obj E).Module} {I : ℤ → Type v}
    (x : ∀ n, I n → term M n) (x' : ∀ n, I n → term M' n) where
  iso : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ≅ M'
  onSymbol (n : ℤ) (z : I n) : (iso.hom.app ()).f n (ULift.up (x n z)) = x' n z

private abbrev unitTensorSymbol {A E : NonpositiveCDGA.{u,v} k}
    (T : ModuleTensor.{u,v} k) (f : A ⟶ E) {M : A.Module} {I : ℤ → Type*}
    (x : ∀ n, I n → term M n) (n : ℤ) (z : I n) :=
  T.tmul (underlying f) (N := regular E.toCommDGAlgebra) n 0 n (add_zero n) (x n z) E.one

private def SymbolLift.extendAlong {A E : NonpositiveCDGA.{u,v} k}
    (f : A ⟶ E) {f' : (cdgaLift.{u,v,max v t} k).obj A ⟶ (cdgaLift.{u,v,max v t} k).obj E}
    (hf : (cdgaLift.{u,v,max v t} k).map f = f')
    {M : A.Module} {M' : ((cdgaLift.{u,v,max v t} k).obj A).Module} {I : ℤ → Type v}
    {x : ∀ n, I n → term M n} {x' : ∀ n, I n → term M' n}
    (a : SymbolLift.{u,v,t} x x') :
    SymbolLift.{u,v,t} (unitTensorSymbol (Tensor.moduleTensorModel.{u,v} k) f x)
      (unitTensorSymbol (Tensor.moduleTensorModel.{u,max v t} k) f' x') := by
  refine ⟨liftExtendAlong.{u,v,t} f hf a.iso, ?_⟩
  intro n z
  have hp := liftExtendAlong_tmul.{u,v,t} f hf a.iso n 0 n (add_zero n) (x n z) E.one
  rw [a.onSymbol n z] at hp
  exact hp

section SequenceCoordinates

variable {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
variable (R : ResolvedChain (Tensor.moduleTensorModel.{u,v} k) X)
variable (U : LiftedResolution.{u,v,t} (Tensor.moduleTensorModel.{u,max v t} k) R) (e : X.C ⟶ E)

private def leftCoordinates :
    SymbolLift.{u,v,t} (leftSymbol (Tensor.moduleTensorModel.{u,v} k) R.resolution e)
      (fun n x => leftSymbol (Tensor.moduleTensorModel.{u,max v t} k) U.resolution
        ((cdgaLift.{u,v,max v t} k).map e) n (ULift.up x)) := by
  let F := cdgaLift.{u,v,max v t} k
  let z := R.resolution.Q.augmentation
  let a : SymbolLift.{u,v,t} (symbol R.resolution.P.differentials)
      (fun n x => symbol U.resolution.P.differentials n (ULift.up x)) :=
    ⟨U.base.differentialIso, U.base.symbol⟩
  exact (a.extendAlong R.resolution.Q.base rfl).extendAlong (z ≫ e) (F.map_comp z e)

private def middleCoordinates :
    SymbolLift.{u,v,t} (middleSymbol (Tensor.moduleTensorModel.{u,v} k) R.resolution e)
      (fun n x => middleSymbol (Tensor.moduleTensorModel.{u,max v t} k) U.resolution
        ((cdgaLift.{u,v,max v t} k).map e) n (ULift.up x)) := by
  let F := cdgaLift.{u,v,max v t} k
  let z := R.resolution.Q.augmentation
  let a : SymbolLift.{u,v,t} (symbol R.resolution.absolute)
      (fun n x => symbol U.resolution.absolute n (ULift.up x)) :=
    ⟨liftedAbsoluteIso.{u,v,t} U, liftedAbsoluteIso_symbol.{u,v,t} U⟩
  exact a.extendAlong (z ≫ e) (F.map_comp z e)

private def rightCoordinates :
    SymbolLift.{u,v,t} (rightSymbol (Tensor.moduleTensorModel.{u,v} k) R.resolution e)
      (fun n x => rightSymbol (Tensor.moduleTensorModel.{u,max v t} k) U.resolution
        ((cdgaLift.{u,v,max v t} k).map e) n (ULift.up x)) := by
  let F := cdgaLift.{u,v,max v t} k
  let z := R.resolution.Q.augmentation
  let a : SymbolLift.{u,v,t} (symbol R.resolution.Q.differentials)
      (fun n x => symbol U.resolution.Q.differentials n (ULift.up x)) :=
    ⟨U.step.differentialIso, U.step.symbol⟩
  exact a.extendAlong (z ≫ e) (F.map_comp z e)

end SequenceCoordinates

section StrictSquares

attribute [local irreducible] Tensor.moduleTensorModel leftCoordinates middleCoordinates rightCoordinates

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency true in
private def compareLiftedSequence {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
    (R : ResolvedChain (Tensor.moduleTensorModel.{u,v} k) X)
    (S : ResolvedChain (Tensor.moduleTensorModel.{u,max v t} k) (liftChain.{u,v,t} X))
    (U : LiftedResolution.{u,v,t} (Tensor.moduleTensorModel.{u,max v t} k) R)
    (hS : S.resolution = U.resolution) (e : X.C ⟶ E) :
    {a : LiftedSequence.{u,v,t} R S e // a.PreservesSymbols U} := by
  rcases S with ⟨V, G, hsplit, hfree, cop, hcop, rel, O, ids, hp, hf, hL, hM, hN⟩
  change V = U.resolution at hS
  subst V
  let T := Tensor.moduleTensorModel.{u,v} k
  let T' := Tensor.moduleTensorModel.{u,max v t} k
  let e' := (cdgaLift.{u,v,max v t} k).map e
  let aL := leftCoordinates.{u,v,t} R U e
  let aM := middleCoordinates.{u,v,t} R U e
  let aN := rightCoordinates.{u,v,t} R U e
  refine ⟨⟨aL.iso, aM.iso, aN.iso, ?_, ?_⟩, ?_⟩
  · change (liftInput.{u,v,t} E.toCommDGAlgebra).map (inclusionAt R.sequence e) ≫ aM.iso.hom =
      aL.iso.hom ≫ inclusionAt G e'
    refine liftSquareOnSymbols.{u,v,t} (E := E)
      (L := leftAt T R.resolution e) (M := middleAt T R.resolution e)
      (L' := leftAt T' U.resolution e') (M' := middleAt T' U.resolution e')
      aL.iso aM.iso (inclusionAt R.sequence e) (inclusionAt G e')
      (leftSymbol T R.resolution e) (fun n x => leftSymbol T' U.resolution e' n (ULift.up x))
      (middleSymbol T R.resolution e) (fun n x => middleSymbol T' U.resolution e' n (ULift.up x))
      aL.onSymbol aM.onSymbol (fun n x => R.resolution.Q.base.chainMap.f n x)
      (inclusionAt_symbol T Tensor.moduleTensor_formulas R.sequence e) ?_ ?_
    · intro n x
      exact inclusionAt_symbol.{u,max v t} T' Tensor.moduleTensor_formulas G e' n (ULift.up x)
    · intro f g h
      exact leftAt_ext.{u,max v t} (R := U.resolution) e' (fun n x => h n x.down)
  · change (liftInput.{u,v,t} E.toCommDGAlgebra).map (projectionAt R.sequence e) ≫ aN.iso.hom =
      aM.iso.hom ≫ projectionAt G e'
    refine liftSquareOnSymbols.{u,v,t} (E := E)
      (L := middleAt T R.resolution e) (M := rightAt T R.resolution e)
      (L' := middleAt T' U.resolution e') (M' := rightAt T' U.resolution e')
      aM.iso aN.iso (projectionAt R.sequence e) (projectionAt G e')
      (middleSymbol T R.resolution e) (fun n x => middleSymbol T' U.resolution e' n (ULift.up x))
      (rightSymbol T R.resolution e) (fun n x => rightSymbol T' U.resolution e' n (ULift.up x))
      aM.onSymbol aN.onSymbol (fun _ x => x)
      (projectionAt_symbol T Tensor.moduleTensor_formulas R.sequence e) ?_ ?_
    · intro n x
      exact projectionAt_symbol.{u,max v t} T' Tensor.moduleTensor_formulas G e' n (ULift.up x)
    · intro f g h
      exact extendedDiff_ext.{u,max v t} U.resolution.absolute (U.resolution.Q.augmentation ≫ e')
        (fun n x => h n x.down)
  · exact ⟨fun n x => heq_of_eq (aL.onSymbol n x),
      fun n x => heq_of_eq (aM.onSymbol n x), fun n x => heq_of_eq (aN.onSymbol n x)⟩

set_option maxHeartbeats 3600000 in
set_option backward.isDefEq.respectTransparency true in
private theorem sequenceCoordinates_natural
    {X Y : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
    {R : ResolvedChain (Tensor.moduleTensorModel.{u,v} k) X}
    {S : ResolvedChain (Tensor.moduleTensorModel.{u,v} k) Y}
    {R' : ResolvedChain (Tensor.moduleTensorModel.{u,max v t} k) (liftChain.{u,v,t} X)}
    {S' : ResolvedChain (Tensor.moduleTensorModel.{u,max v t} k) (liftChain.{u,v,t} Y)}
    {U : LiftedResolution.{u,v,t} (Tensor.moduleTensorModel.{u,max v t} k) R}
    {V : LiftedResolution.{u,v,t} (Tensor.moduleTensorModel.{u,max v t} k) S}
    {hR : R'.resolution = U.resolution} {hS : S'.resolution = V.resolution}
    {e : X.C ⟶ E} {d : Y.C ⟶ E}
    (a : LiftedSequence.{u,v,t} R R' e) (b : LiftedSequence.{u,v,t} S S' d)
    (ha : a.PreservesSymbols U) (hb : b.PreservesSymbols V)
    {f : ChainMap X Y} (l : Lift f R.resolution S.resolution)
    {m : MapAt R.sequence S.sequence e d}
    {m' : MapAt R'.sequence S'.sequence
      ((cdgaLift.{u,v,max v t} k).map e) ((cdgaLift.{u,v,max v t} k).map d)}
    (hm : Induces l m)
    (hm' : Induces (hR.symm ▸ hS.symm ▸ U.lift V l) m') :
    LiftedSequenceNaturality a b m m' := by
  rcases R' with ⟨P, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases S' with ⟨Q, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  change P = U.resolution at hR
  change Q = V.resolution at hS
  subst P
  subst Q
  let T := Tensor.moduleTensorModel.{u,v} k
  let T' := Tensor.moduleTensorModel.{u,max v t} k
  let F := cdgaLift.{u,v,max v t} k
  let e' := F.map e
  let d' := F.map d
  obtain ⟨haL, haM, haN⟩ := ha
  obtain ⟨hbL, hbM, hbN⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · change (liftInput.{u,v,t} E.toCommDGAlgebra).map m.left ≫ b.left.hom = a.left.hom ≫ m'.left
    refine liftSquareOnSymbols.{u,v,t} (E := E)
      (L := leftAt T R.resolution e) (M := leftAt T S.resolution d)
      (L' := leftAt T' U.resolution e') (M' := leftAt T' V.resolution d')
      a.left b.left m.left m'.left
      (leftSymbol T R.resolution e) (fun n x => leftSymbol T' U.resolution e' n (ULift.up x))
      (leftSymbol T S.resolution d) (fun n x => leftSymbol T' V.resolution d' n (ULift.up x))
      (fun n x => eq_of_heq (haL n x)) (fun n x => eq_of_heq (hbL n x)) (fun n x => l.p.chainMap.f n x)
      hm.1 ?_ ?_
    · intro n x
      exact hm'.1 n (ULift.up x)
    · intro p q h
      exact leftAt_ext.{u,max v t} (R := U.resolution) e' (fun n x => h n x.down)
  · change (liftInput.{u,v,t} E.toCommDGAlgebra).map m.middle ≫ b.middle.hom = a.middle.hom ≫ m'.middle
    refine liftSquareOnSymbols.{u,v,t} (E := E)
      (L := middleAt T R.resolution e) (M := middleAt T S.resolution d)
      (L' := middleAt T' U.resolution e') (M' := middleAt T' V.resolution d')
      a.middle b.middle m.middle m'.middle
      (middleSymbol T R.resolution e) (fun n x => middleSymbol T' U.resolution e' n (ULift.up x))
      (middleSymbol T S.resolution d) (fun n x => middleSymbol T' V.resolution d' n (ULift.up x))
      (fun n x => eq_of_heq (haM n x)) (fun n x => eq_of_heq (hbM n x)) (fun n x => l.q.chainMap.f n x)
      hm.2.1 ?_ ?_
    · intro n x
      exact hm'.2.1 n (ULift.up x)
    · intro p q h
      exact extendedDiff_ext.{u,max v t} U.resolution.absolute (U.resolution.Q.augmentation ≫ e')
        (fun n x => h n x.down)
  · change (liftInput.{u,v,t} E.toCommDGAlgebra).map m.right ≫ b.right.hom = a.right.hom ≫ m'.right
    refine liftSquareOnSymbols.{u,v,t} (E := E)
      (L := rightAt T R.resolution e) (M := rightAt T S.resolution d)
      (L' := rightAt T' U.resolution e') (M' := rightAt T' V.resolution d')
      a.right b.right m.right m'.right
      (rightSymbol T R.resolution e) (fun n x => rightSymbol T' U.resolution e' n (ULift.up x))
      (rightSymbol T S.resolution d) (fun n x => rightSymbol T' V.resolution d' n (ULift.up x))
      (fun n x => eq_of_heq (haN n x)) (fun n x => eq_of_heq (hbN n x)) (fun n x => l.q.chainMap.f n x)
      hm.2.2 ?_ ?_
    · intro n x
      exact hm'.2.2 n (ULift.up x)
    · intro p q h
      exact extendedDiff_ext.{u,max v t} U.resolution.Q.differentials (U.resolution.Q.augmentation ≫ e')
        (fun n x => h n x.down)

end StrictSquares

open Specs.DerivedFormalization.DG.DerivedCoefficientLift (Descent)
open ShiftCone (shift shiftMap cone coneProjection)
open private represented_naturality classMap_strict from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoefficientLift

private theorem commuteComp {D : Type*} [Category* D] {A B C A' B' C' : D}
    {f : A ⟶ A'} {g : B ⟶ B'} {h : C ⟶ C'}
    {a : A ⟶ B} {b : B ⟶ C} {a' : A' ⟶ B'} {b' : B' ⟶ C'}
    (e : f ≫ a' = a ≫ g) (e' : g ≫ b' = b ≫ h) :
    f ≫ (a' ≫ b') = (a ≫ b) ≫ h := by
  rw [← Category.assoc, e, Category.assoc, e', Category.assoc]

private theorem commuteInv {D : Type*} [Category* D] {A B A' B' : D}
    {f : A ⟶ A'} {g : B ⟶ B'} (a : A ≅ B) (b : A' ≅ B')
    (e : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  rw [← cancel_epi a.hom, Iso.hom_inv_id_assoc, ← Category.assoc, ← e, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

section LocalShift

variable {E : NonpositiveCDGA.{u,v} k}

variable {h : HomotopyCategoryLaws (oneObject E)}
variable {h' : HomotopyCategoryLaws (oneObject ((cdgaLift.{u,v,max v t} k).obj E))}
variable (K : ConeLocalization (oneObject E) h) (K' : ConeLocalization (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h')
variable (d : Descent h h' (liftInput.{u,v,t} E.toCommDGAlgebra))



private theorem representedMap {M N : E.Module} (f : M ⟶ N) :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := Derived.homotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    letI := derivedCategoryInstance (oneObject E) h
    letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    let Q := quotient (oneObject E) h
    let Q' := quotient (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    d.D.map (Q.map (classOfMap h f)) ≫ (d.representedIso N).hom =
      (d.representedIso M).hom ≫ Q'.map (classOfMap h' ((liftInput.{u,v,t} E.toCommDGAlgebra).map f)) := by
  letI := Derived.homotopyCategory (oneObject E) h
  letI := Derived.homotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  letI := derivedCategoryInstance (oneObject E) h
  letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  have hn := represented_naturality d (classOfMap h f)
  rw [classMap_strict d f] at hn
  exact hn

private def localizedLiftedShift : LiftedShift K K' d := by
  letI := Derived.homotopyCategory (oneObject E) h
  letI := Derived.homotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  letI := derivedCategoryInstance (oneObject E) h
  letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  letI := K.shiftD
  letI := K'.shiftD
  let Q := quotient (oneObject E) h
  let Q' := quotient (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  let J := RightDGModule.toHomotopyCategory (oneObject E) ⋙ Q
  let J' := RightDGModule.toHomotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) ⋙ Q'
  let A := translation K ⋙ d.D
  let B := d.D ⋙ translation K'
  let s (M : E.Module) := DG.CoefficientLift.shiftIso.{u,v,0,max v t} M 1
  let a (M : E.Module) := d.D.mapIso (K.onShift M 1)
  let b (M : E.Module) := (d.representedIso (shift M 1) ≪≫ J'.mapIso (s M)) ≪≫
    (K'.onShift ((liftInput.{u,v,t} E.toCommDGAlgebra).obj M) 1 ≪≫ ((translation K').mapIso (d.representedIso M)).symm)
  let c (M : E.Module) := (a M).symm ≪≫ b M
  have ha {M N : E.Module} (f : M ⟶ N) :
      d.D.map (J.map (shiftMap 1 f)) ≫ (a N).hom = (a M).hom ≫ A.map (J.map f) := by
    change d.D.map (J.map (shiftMap 1 f)) ≫ d.D.map (K.onShift N 1).hom =
      d.D.map (K.onShift M 1).hom ≫ d.D.map ((translation K).map (J.map f))
    rw [← d.D.map_comp, ← d.D.map_comp]
    exact congrArg d.D.map (shiftNatural K f)
  have hb {M N : E.Module} (f : M ⟶ N) :
      d.D.map (J.map (shiftMap 1 f)) ≫ (b N).hom = (b M).hom ≫ B.map (J.map f) := by
    have h₁ := representedMap d (shiftMap 1 f)
    have h₂ : (liftInput.{u,v,t} E.toCommDGAlgebra).map (shiftMap 1 f) ≫ (s N).hom =
        (s M).hom ≫ shiftMap 1 ((liftInput.{u,v,t} E.toCommDGAlgebra).map f) := by
      apply RightDGModuleModel.hom_ext
      intro o
      apply HomologicalComplex.hom_ext
      intro n
      rfl
    have h₂' : J'.map ((liftInput.{u,v,t} E.toCommDGAlgebra).map (shiftMap 1 f)) ≫ (J'.mapIso (s N)).hom =
        (J'.mapIso (s M)).hom ≫ J'.map (shiftMap 1 ((liftInput.{u,v,t} E.toCommDGAlgebra).map f)) := by
      simpa only [Functor.mapIso_hom, Functor.map_comp] using congrArg J'.map h₂
    have h₃ := shiftNatural K' ((liftInput.{u,v,t} E.toCommDGAlgebra).map f)
    have h₄ : B.map (J.map f) ≫ ((translation K').mapIso (d.representedIso N)).hom =
        ((translation K').mapIso (d.representedIso M)).hom ≫
          (translation K').map (J'.map ((liftInput.{u,v,t} E.toCommDGAlgebra).map f)) := by
      let S := translation K'
      change S.map (d.D.map (J.map f)) ≫ S.map (d.representedIso N).hom =
        S.map (d.representedIso M).hom ≫ S.map (J'.map ((liftInput.{u,v,t} E.toCommDGAlgebra).map f))
      rw [← S.map_comp, ← S.map_comp]
      exact congrArg S.map (representedMap d f)
    exact commuteComp (commuteComp h₁ h₂') (commuteComp h₃ (commuteInv _ _ h₄))
  let σ : Q ⋙ A ≅ Q ⋙ B := NatIso.ofComponents c (by
    intro M N g
    obtain ⟨f, rfl⟩ := RightDGModule.homotopyClass_surjective g
    exact commuteComp (commuteInv _ _ (ha f)) (hb f))
  let W := Derived.quasiIsomorphisms (oneObject E)
  letI : Q.IsLocalization W := inferInstanceAs (W.Q.IsLocalization W)
  letI : Localization.Lifting Q W (Q ⋙ A) A := ⟨Iso.refl _⟩
  letI : Localization.Lifting Q W (Q ⋙ B) B := ⟨Iso.refl _⟩
  let α := Localization.liftNatIso Q W (Q ⋙ A) (Q ⋙ B) A B σ
  refine ⟨s, fun _ _ _ => rfl, α, ?_⟩
  intro M
  have hα : α.hom.app (Q.obj M) = (c M).hom := by
    change (Localization.liftNatTrans Q W (Q ⋙ A) (Q ⋙ B) A B σ.hom).app (Q.obj M) = _
    rw [Localization.liftNatTrans_app]
    change 𝟙 _ ≫ (c M).hom ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  change (a M).hom ≫ α.hom.app (Q.obj M) ≫
    ((translation K').mapIso (d.representedIso M)).hom = _
  rw [hα]
  simp only [c, b, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [Iso.inv_hom_id, Category.comp_id]
  rfl

end LocalShift

section ConeLift

variable {E : NonpositiveCDGA.{u,v} k}


variable {h : HomotopyCategoryLaws (oneObject E)}
variable {h' : HomotopyCategoryLaws (oneObject ((cdgaLift.{u,v,max v t} k).obj E))}
variable {K : ConeLocalization (oneObject E) h} {K' : ConeLocalization (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'}
variable {d : Descent h h' (liftInput.{u,v,t} E.toCommDGAlgebra)}

private theorem localizedSquare
    {L M : E.Module} {L' M' : ((cdgaLift.{u,v,max v t} k).obj E).Module}
    (a : (liftInput.{u,v,t} E.toCommDGAlgebra).obj L ⟶ L') (b : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ⟶ M') (f : L ⟶ M) (g : L' ⟶ M')
    (e : (liftInput.{u,v,t} E.toCommDGAlgebra).map f ≫ b = a ≫ g) :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := Derived.homotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    letI := derivedCategoryInstance (oneObject E) h
    letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    let J := RightDGModule.toHomotopyCategory (oneObject E) ⋙ quotient (oneObject E) h
    let J' := RightDGModule.toHomotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) ⋙ quotient (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    d.D.map (J.map f) ≫ ((d.representedIso M).hom ≫ J'.map b) =
      ((d.representedIso L).hom ≫ J'.map a) ≫ J'.map g := by
  letI := Derived.homotopyCategory (oneObject E) h
  letI := Derived.homotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  letI := derivedCategoryInstance (oneObject E) h
  letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  let J := RightDGModule.toHomotopyCategory (oneObject E) ⋙ quotient (oneObject E) h
  let J' := RightDGModule.toHomotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) ⋙ quotient (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  have hf : d.D.map (J.map f) ≫ (d.representedIso M).hom =
      (d.representedIso L).hom ≫ J'.map ((liftInput.{u,v,t} E.toCommDGAlgebra).map f) :=
    representedMap d f
  refine commuteComp hf ?_
  rw [← J'.map_comp, ← J'.map_comp, e]

open ShiftCone (coneTerm)
open CoefficientLiftComparison (coneMap)
open private strictNeg from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeRotation

private def liftConeMap {L M : E.Module} {L' M' : ((cdgaLift.{u,v,max v t} k).obj E).Module} {i : L ⟶ M} {i' : L' ⟶ M'}
    {a : (liftInput.{u,v,t} E.toCommDGAlgebra).obj L ⟶ L'} {b : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ⟶ M'}
    (e : (liftInput.{u,v,t} E.toCommDGAlgebra).map i ≫ b = a ≫ i') : (liftInput.{u,v,t} E.toCommDGAlgebra).obj (cone i) ⟶ cone i' :=
  (DG.CoefficientLift.coneIso.{u,v,0,max v t} i).hom ≫ coneMap a b e

private theorem liftConeMap_quotient {L M N : E.Module} {L' M' N' : ((cdgaLift.{u,v,max v t} k).obj E).Module}
    {i : L ⟶ M} {i' : L' ⟶ M'} {p : M ⟶ N} {p' : M' ⟶ N'}
    {q : cone i ⟶ N} {q' : cone i' ⟶ N'}
    (hq : IsConeQuotient p q) (hq' : IsConeQuotient p' q')
    {a : (liftInput.{u,v,t} E.toCommDGAlgebra).obj L ⟶ L'} {b : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ⟶ M'} {c : (liftInput.{u,v,t} E.toCommDGAlgebra).obj N ⟶ N'}
    (e : (liftInput.{u,v,t} E.toCommDGAlgebra).map i ≫ b = a ≫ i') (e' : (liftInput.{u,v,t} E.toCommDGAlgebra).map p ≫ c = b ≫ p') :
    (liftInput.{u,v,t} E.toCommDGAlgebra).map q ≫ c = liftConeMap e ≫ q' := by
  apply RightDGModule.strict_ext
  rintro ⟨⟩ n x
  change (c.app ()).f n (ULift.up ((q.app ()).f n x.down)) =
    (q'.app ()).f n ((b.app ()).f n (ULift.up x.down.1), (a.app ()).f (n+1) (ULift.up x.down.2))
  rw [hq.1, hq'.1]
  exact CategoryTheory.congr_fun
    (congrArg (fun f : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ⟶ N' => (f.app ()).f n) e') (ULift.up x.down.1)

private theorem liftConeMap_projection {L M : E.Module} {L' M' : ((cdgaLift.{u,v,max v t} k).obj E).Module}
    {i : L ⟶ M} {i' : L' ⟶ M'} {a : (liftInput.{u,v,t} E.toCommDGAlgebra).obj L ⟶ L'} {b : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ⟶ M'}
    (e : (liftInput.{u,v,t} E.toCommDGAlgebra).map i ≫ b = a ≫ i') (s : LiftedShift K K' d) :
    (liftInput.{u,v,t} E.toCommDGAlgebra).map (strictNeg (coneProjection i)) ≫ (s.strict L).hom ≫ shiftMap 1 a =
      liftConeMap e ≫ strictNeg (coneProjection i') := by
  apply RightDGModule.strict_ext
  rintro ⟨⟩ n x
  change (a.app ()).f (n+1) (((s.strict L).hom.app ()).f n (ULift.up (-x.down.2))) =
    -((a.app ()).f (n+1) (ULift.up x.down.2))
  have hp := ULift.ext (s.coordinates L n (ULift.up (-x.down.2)))
  rw [hp]
  exact map_neg ((a.app ()).f (n+1)).hom (ULift.up x.down.2)

end ConeLift

section TriangleLift
open private strictNeg from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeRotation

variable {E : NonpositiveCDGA.{u,v} k}


variable {h : HomotopyCategoryLaws (oneObject E)}
variable {h' : HomotopyCategoryLaws (oneObject ((cdgaLift.{u,v,max v t} k).obj E))}
variable {K : ConeLocalization (oneObject E) h} {K' : ConeLocalization (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'}
variable {d : Descent h h' (liftInput.{u,v,t} E.toCommDGAlgebra)}

private theorem liftedBoundary
    (s : LiftedShift K K' d)
    {L M N : E.Module} {L' M' N' : ((cdgaLift.{u,v,max v t} k).obj E).Module}
    {i : L ⟶ M} {i' : L' ⟶ M'} {p : M ⟶ N} {p' : M' ⟶ N'}
    {q : cone i ⟶ N} {q' : cone i' ⟶ N'}
    (hq : IsConeQuotient p q) (hq' : IsConeQuotient p' q')
    (a : (liftInput.{u,v,t} E.toCommDGAlgebra).obj L ≅ L') (b : (liftInput.{u,v,t} E.toCommDGAlgebra).obj M ≅ M') (c : (liftInput.{u,v,t} E.toCommDGAlgebra).obj N ≅ N')
    (hi : (liftInput.{u,v,t} E.toCommDGAlgebra).map i ≫ b.hom = a.hom ≫ i') (hp : (liftInput.{u,v,t} E.toCommDGAlgebra).map p ≫ c.hom = b.hom ≫ p') :
    letI := Derived.homotopyCategory (oneObject E) h
    letI := Derived.homotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    letI := derivedCategoryInstance (oneObject E) h
    letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    letI := K.shiftD
    letI := K'.shiftD
    let J := RightDGModule.toHomotopyCategory (oneObject E) ⋙ quotient (oneObject E) h
    let J' := RightDGModule.toHomotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) ⋙ quotient (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
    ∀ (e : J.obj (cone i) ≅ J.obj N) (e' : J'.obj (cone i') ≅ J'.obj N'),
      e.hom = J.map q → e'.hom = J'.map q' →
      let U := localizedSequenceTriangle h K i p e
      let V := localizedSequenceTriangle h' K' i' p' e'
      let l := d.representedIso L ≪≫ J'.mapIso a
      let r := d.representedIso N ≪≫ J'.mapIso c
      (s.triangles.obj U).mor₃ ≫ (translation K').map l.hom = r.hom ≫ V.mor₃ := by
  letI := Derived.homotopyCategory (oneObject E) h
  letI := Derived.homotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  letI := derivedCategoryInstance (oneObject E) h
  letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  letI := K.shiftD
  letI := K'.shiftD
  let Q := quotient (oneObject E) h
  let Q' := quotient (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) h'
  let J := RightDGModule.toHomotopyCategory (oneObject E) ⋙ Q
  let J' := RightDGModule.toHomotopyCategory (oneObject ((cdgaLift.{u,v,max v t} k).obj E)) ⋙ Q'
  dsimp only
  intro e e' he he'
  let F := d.D
  let S := translation K'
  let l := d.representedIso L ≪≫ J'.mapIso a
  let r := d.representedIso N ≪≫ J'.mapIso c
  let m := liftConeMap hi
  let j := (d.representedIso (cone i)).hom ≫ J'.map m
  let pr := strictNeg (coneProjection i)
  let pr' := strictNeg (coneProjection i')
  let u := (K.onShift L 1).hom
  let u' := (K'.onShift L' 1).hom
  have hq₀ : (F.mapIso e).hom ≫ r.hom = j ≫ e'.hom := by
    change F.map e.hom ≫ r.hom = j ≫ e'.hom
    rw [he, he']
    exact localizedSquare m c.hom q q' (liftConeMap_quotient hq hq' hi hp)
  have hq₁ : F.map e.inv ≫ j = r.hom ≫ e'.inv :=
    (commuteInv (F.mapIso e) e' hq₀.symm).symm
  have hs : S.map l.hom = S.map (d.representedIso L).hom ≫ S.map (J'.map a.hom) :=
    S.map_comp _ _
  have hn : F.map u ≫ s.iso.hom.app (J.obj L) ≫ S.map (d.representedIso L).hom =
      (d.representedIso (shift L 1)).hom ≫ J'.map (s.strict L).hom ≫
        (K'.onShift ((liftInput.{u,v,t} E.toCommDGAlgebra).obj L) 1).hom :=
    s.normalized L
  have hs' := shiftNatural K' a.hom
  have hpr : F.map (J.map pr) ≫ ((d.representedIso (shift L 1)).hom ≫
      J'.map ((s.strict L).hom ≫ shiftMap 1 a.hom)) = j ≫ J'.map pr' :=
    localizedSquare m ((s.strict L).hom ≫ shiftMap 1 a.hom) pr pr'
      (liftConeMap_projection hi s)
  have hbd : F.map (J.map pr ≫ u) ≫ s.iso.hom.app (J.obj L) ≫ S.map l.hom =
      j ≫ J'.map pr' ≫ u' := by
    rw [F.map_comp, hs]
    calc
      _ = F.map (J.map pr) ≫
            (F.map u ≫ s.iso.hom.app (J.obj L) ≫ S.map (d.representedIso L).hom) ≫
            S.map (J'.map a.hom) := by simp only [Category.assoc]
      _ = F.map (J.map pr) ≫
            ((d.representedIso (shift L 1)).hom ≫ J'.map (s.strict L).hom ≫
              J'.map (shiftMap 1 a.hom)) ≫ u' := by
        rw [hn]
        simp only [Category.assoc]
        exact congrArg (F.map (J.map pr) ≫ (d.representedIso (shift L 1)).hom ≫
          J'.map (s.strict L).hom ≫ ·) hs'.symm
      _ = j ≫ J'.map pr' ≫ u' := by
        have hh := congrArg (· ≫ u') hpr
        rw [J'.map_comp] at hh
        simpa only [Category.assoc] using hh
  have hU := localizedSequence_boundary h K i p e
  have hV := localizedSequence_boundary h' K' i' p' e'
  change (localizedSequenceTriangle h K i p e).mor₃ = e.inv ≫ J.map pr ≫ u at hU
  change (localizedSequenceTriangle h' K' i' p' e').mor₃ = e'.inv ≫ J'.map pr' ≫ u' at hV
  change (F.map (localizedSequenceTriangle h K i p e).mor₃ ≫
      s.iso.hom.app (J.obj L)) ≫ S.map l.hom = r.hom ≫ (localizedSequenceTriangle h' K' i' p' e').mor₃
  rw [Category.assoc, hU, hV, F.map_comp]
  calc
    _ = F.map e.inv ≫ j ≫ J'.map pr' ≫ u' := by
      rw [Category.assoc, hbd]
    _ = _ := by rw [← Category.assoc (F.map e.inv), hq₁, Category.assoc]

private def compareLiftedTriangle
    {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {X : Chain.{u,v} k} {R : ResolvedChain T X} {R' : ResolvedChain T' (liftChain.{u,v,t} X)}
    {e : X.C ⟶ E} (a : LiftedSequence.{u,v,t} R R' e)
    (s : LiftedShift K K' d) (U : SequenceTriangle K R.sequence e)
    (V : SequenceTriangle K' R'.sequence ((cdgaLift.{u,v,max v t} k).map e)) :
    LiftedTriangle a s U V := by
  let E' := (cdgaLift.{u,v,max v t} k).obj E
  letI := Derived.homotopyCategory (oneObject E) h
  letI := Derived.homotopyCategory (oneObject E') h'
  letI := derivedCategoryInstance (oneObject E) h
  letI := derivedCategoryInstance (oneObject E') h'
  letI := K.shiftD
  letI := K'.shiftD
  let J' := RightDGModule.toHomotopyCategory (oneObject E') ⋙ quotient (oneObject E') h'
  let l := d.representedIso (leftAt T R.resolution e) ≪≫ J'.mapIso a.left
  let m := d.representedIso (middleAt T R.resolution e) ≪≫ J'.mapIso a.middle
  let r := d.representedIso (rightAt T R.resolution e) ≪≫ J'.mapIso a.right
  let j := Triangle.isoMk (s.triangles.obj U.triangle) V.triangle l m r
    (localizedSquare a.left.hom a.middle.hom _ _ a.incl_comm)
    (localizedSquare a.middle.hom a.right.hom _ _ a.proj_comm)
    (liftedBoundary s U.quotientFormula V.quotientFormula a.left a.middle a.right
      a.incl_comm a.proj_comm U.quotientIso V.quotientIso U.quotientIso_hom V.quotientIso_hom)
  exact ⟨j, rfl, rfl, rfl⟩

private theorem liftedTriangles_natural
    {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {X Y : Chain.{u,v} k}
    {R : ResolvedChain T X} {R' : ResolvedChain T' (liftChain.{u,v,t} X)}
    {S : ResolvedChain T Y} {S' : ResolvedChain T' (liftChain.{u,v,t} Y)}
    {e : X.C ⟶ E} {c : Y.C ⟶ E}
    (a : LiftedSequence.{u,v,t} R R' e) (b : LiftedSequence.{u,v,t} S S' c)
    (s : LiftedShift K K' d)
    (A : Naturality K T) (B : Naturality K' T')
    {f : ChainMap X Y} (he : e = f.c ≫ c)
    (l : Lift f R.resolution S.resolution)
    (l' : Lift (liftChainMap.{u,v,t} f) R'.resolution S'.resolution)
    (hs : LiftedSequenceNaturality a b (A.strict.map l R.sequence S.sequence e c he)
      (B.strict.map l' R'.sequence S'.sequence
        ((cdgaLift.{u,v,max v t} k).map e) ((cdgaLift.{u,v,max v t} k).map c) (liftFinalMap f he)))
    (j₁ : LiftedTriangle a s (A.triangle X R e)
      (B.triangle _ R' ((cdgaLift.{u,v,max v t} k).map e)))
    (j₂ : LiftedTriangle b s (A.triangle Y S c)
      (B.triangle _ S' ((cdgaLift.{u,v,max v t} k).map c))) :
    let E' := (cdgaLift.{u,v,max v t} k).obj E
    letI := derivedCategoryInstance (oneObject E) h
    letI := derivedCategoryInstance (oneObject E') h'
    letI := K.shiftD
    letI := K'.shiftD
    s.triangles.map (A.map f R S e c he) ≫ j₂.iso.hom =
      j₁.iso.hom ≫ B.map (liftChainMap.{u,v,t} f) R' S'
        ((cdgaLift.{u,v,max v t} k).map e) ((cdgaLift.{u,v,max v t} k).map c) (liftFinalMap f he) := by
  let E' := (cdgaLift.{u,v,max v t} k).obj E
  letI := Derived.homotopyCategory (oneObject E) h
  letI := Derived.homotopyCategory (oneObject E') h'
  letI := derivedCategoryInstance (oneObject E) h
  letI := derivedCategoryInstance (oneObject E') h'
  letI := K.shiftD
  letI := K'.shiftD
  let e' := (cdgaLift.{u,v,max v t} k).map e
  let c' := (cdgaLift.{u,v,max v t} k).map c
  let he' := liftFinalMap f he
  let n := A.map f R S e c he
  let n' := B.map (liftChainMap.{u,v,t} f) R' S' e' c' he'
  obtain ⟨x₁, x₂, x₃⟩ := A.components R S e c he l
  obtain ⟨y₁, y₂, y₃⟩ := B.components R' S' e' c' he' l'
  obtain ⟨a₁, a₂, a₃⟩ := j₁.components
  obtain ⟨b₁, b₂, b₃⟩ := j₂.components
  apply Triangle.hom_ext
  · change d.D.map n.hom₁ ≫ j₂.iso.hom.hom₁ = j₁.iso.hom.hom₁ ≫ n'.hom₁
    rw [x₁, y₁, a₁, b₁]
    exact localizedSquare a.left.hom b.left.hom _ _ hs.1
  · change d.D.map n.hom₂ ≫ j₂.iso.hom.hom₂ = j₁.iso.hom.hom₂ ≫ n'.hom₂
    rw [x₂, y₂, a₂, b₂]
    exact localizedSquare a.middle.hom b.middle.hom _ _ hs.2.1
  · change d.D.map n.hom₃ ≫ j₂.iso.hom.hom₃ = j₁.iso.hom.hom₃ ≫ n'.hom₃
    rw [x₃, y₃, a₃, b₃]
    exact localizedSquare a.right.hom b.right.hom _ _ hs.2.2

end TriangleLift

private theorem compareBoundModel
    {A B : NonpositiveCDGA.{u,v} k} (f : A ⟶ B)
    {g : (cdgaLift.{u,v,max v t} k).obj A ⟶ (cdgaLift.{u,v,max v t} k).obj B}
    (hg : (cdgaLift.{u,v,max v t} k).map f = g) (R : Model f) (S : Model g) :
    let h := laws B.toCommDGAlgebra
    let h' := laws (liftAlgebra.{u,v,t} B.toCommDGAlgebra)
    letI := derivedCategoryInstance (oneObject B) h
    letI := derivedCategoryInstance (oneObject ((cdgaLift.{u,v,max v t} k).obj B)) h'
    Nonempty ((ambientDescent.{u,v,t} B.toCommDGAlgebra).D.obj
      (localizedModel h R (Tensor.moduleTensorModel k)) ≅
      localizedModel h' S (Tensor.moduleTensorModel k)) := by
  subst g
  let h := laws B.toCommDGAlgebra
  let B' := (cdgaLift.{u,v,max v t} k).obj B
  let h' := laws B'.toCommDGAlgebra
  letI := Derived.homotopyCategory (oneObject B) h
  letI := Derived.homotopyCategory (oneObject B') h'
  letI := derivedCategoryInstance (oneObject B) h
  letI := derivedCategoryInstance (oneObject B') h'
  let T := Tensor.moduleTensorModel.{u,v} k
  let T' := Tensor.moduleTensorModel.{u,max v t} k
  obtain ⟨U⟩ := CotangentComplex.modelEnlargement.{u,v,max v t} R T T'
    Tensor.moduleTensor_formulas Tensor.moduleTensor_formulas
  obtain ⟨C⟩ := CotangentComplex.nativeComparison ((cdgaLift.{u,v,max v t} k).map f) T' h'
    Tensor.moduleTensor_formulas
  let Q := quotient (oneObject B') h'
  let J := RightDGModule.toHomotopyCategory (oneObject B') ⋙ Q
  let V := ambientDescent.{u,v,t} B.toCommDGAlgebra
  exact ⟨V.representedIso (R.module T) ≪≫ J.mapIso U.cotangentIso ≪≫ C.derivedIso U.model S⟩

set_option maxHeartbeats 2600000 in
private def commonComparisons
    {h : ∀ A : CommDGAlgebra.{u,v} k, HomotopyCategoryLaws (dgCat A)}
    {h' : ∀ A : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat A)}
    (d : ∀ A : CommDGAlgebra.{u,v} k,
      Descent (h A) (h' (liftAlgebra.{u,v,t} A)) (liftInput.{u,v,t} A))
    (K₀ : ∀ E : NonpositiveCDGA.{u,v} k, ConeLocalization (oneObject E) (h E.toCommDGAlgebra))
    (K : ∀ E : NonpositiveCDGA.{u,max v t} k, ConeLocalization (oneObject E) (h' E.toCommDGAlgebra))
    (N₀ : ∀ E, Naturality (K₀ E) (Tensor.moduleTensorModel.{u,v} k))
    (N : ∀ E, Naturality (K E) (Tensor.moduleTensorModel.{u,max v t} k))
    (U : ∀ {X : Chain.{u,v} k} (R : ResolvedChain (Tensor.moduleTensorModel.{u,v} k) X),
      LiftedResolution.{u,v,t} (Tensor.moduleTensorModel.{u,max v t} k) R)
    (S : ∀ {X : Chain.{u,v} k}, ResolvedChain (Tensor.moduleTensorModel.{u,v} k) X →
      ResolvedChain (Tensor.moduleTensorModel.{u,max v t} k) (liftChain.{u,v,t} X))
    (hS : ∀ {X : Chain.{u,v} k} (R : ResolvedChain (Tensor.moduleTensorModel.{u,v} k) X),
      (S R).resolution = (U R).resolution) :
    CommonBoundComparisons.{u,v,t} d K₀ K N₀ N := by
  let T := Tensor.moduleTensorModel.{u,v} k
  let sh (E : NonpositiveCDGA.{u,v} k) := localizedLiftedShift (K₀ E)
    (K ((cdgaLift.{u,v,max v t} k).obj E)) (d E.toCommDGAlgebra)
  let a {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
      (R : ResolvedChain T X) (e : X.C ⟶ E) :=
    (compareLiftedSequence.{u,v,t} R (S R) (U R) (hS R) e).1
  have hSymbols {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
      (R : ResolvedChain T X) (e : X.C ⟶ E) : (a R e).PreservesSymbols (U R) :=
    (compareLiftedSequence.{u,v,t} R (S R) (U R) (hS R) e).2
  let j {X : Chain.{u,v} k} {E : NonpositiveCDGA.{u,v} k}
      (R : ResolvedChain T X) (e : X.C ⟶ E) :=
    compareLiftedTriangle.{u,v,t} (a R e) (sh E) ((N₀ E).triangle X R e)
      ((N ((cdgaLift.{u,v,max v t} k).obj E)).triangle _ (S R) ((cdgaLift.{u,v,max v t} k).map e))
  refine ⟨sh, @U, @S, @hS, @a, @hSymbols, @j, ?_⟩
  intro X Y E f R V e c he l
  let E' := (cdgaLift.{u,v,max v t} k).obj E
  let e' := (cdgaLift.{u,v,max v t} k).map e
  let c' := (cdgaLift.{u,v,max v t} k).map c
  let he' := liftFinalMap.{u,v,t} f he
  let l' : Lift (liftChainMap.{u,v,t} f) (S R).resolution (S V).resolution :=
    (hS R).symm ▸ (hS V).symm ▸ (U R).lift (U V) l
  let m := (N₀ E).strict.map l R.sequence V.sequence e c he
  let m' := (N E').strict.map l' (S R).sequence (S V).sequence e' c' he'
  have hs : LiftedSequenceNaturality (a R e) (a V c) m m' :=
    sequenceCoordinates_natural.{u,v,t} (hR := hS R) (hS := hS V)
      (a R e) (a V c) (hSymbols R e) (hSymbols V c) l (m := m) (m' := m')
      ((N₀ E).strict.induced l R.sequence V.sequence e c he)
      ((N E').strict.induced l' (S R).sequence (S V).sequence e' c' he')
  constructor
  · exact hs
  · exact liftedTriangles_natural.{u,v,t} (a R e) (a V c) (sh E) (N₀ E) (N E') he
      l l' hs (j R e) (j V c)

private theorem identifyLiftedTriangles
    {T : ModuleTensor.{u,v} k} {T' : ModuleTensor.{u,max v t} k}
    {h : ∀ A : CommDGAlgebra.{u,v} k, HomotopyCategoryLaws (dgCat A)}
    {h' : ∀ A : CommDGAlgebra.{u,max v t} k, HomotopyCategoryLaws (dgCat A)}
    {d : ∀ A : CommDGAlgebra.{u,v} k,
      Descent (h A) (h' (liftAlgebra.{u,v,t} A)) (liftInput.{u,v,t} A)}
    {K : ∀ E : NonpositiveCDGA.{u,v} k, ConeLocalization (oneObject E) (h E.toCommDGAlgebra)}
    {K' : ∀ E : NonpositiveCDGA.{u,max v t} k, ConeLocalization (oneObject E) (h' E.toCommDGAlgebra)}
    {N : ∀ E, Naturality (K E) T} {N' : ∀ E, Naturality (K' E) T'}
    (b : CommonBoundComparisons d K K' N N') {X : Chain.{u,v} k} (R : ResolvedChain T X) :
    b.identified R := by
  let F := cdgaLift.{u,v,max v t} k
  let C' := F.obj X.C
  letI := derivedCategoryInstance (oneObject X.C) (h X.C.toCommDGAlgebra)
  letI := derivedCategoryInstance (oneObject C') (h' C'.toCommDGAlgebra)
  letI := (K X.C).shiftD
  letI := (K' C').shiftD
  dsimp only [CommonBoundComparisons.identified]
  intro U V i i'
  let r (e : C' ⟶ C') := ((N' C').triangle _ (b.resolved R) e).triangle
  let a : r (F.map (𝟙 X.C)) ≅ r (𝟙 C') := eqToIso (congrArg r (F.map_id X.C))
  exact ⟨(b.shiftComparison X.C).triangles.mapIso i.symm ≪≫
    ((b.triangle R (𝟙 X.C)).iso ≪≫ (a ≪≫ i')), rfl⟩

attribute [local irreducible] CommonBoundComparisons.identified commonComparisons

set_option maxHeartbeats 2000000 in
/-- The triangle and its maps can be computed at any common coefficient bound,
using the compatible extension and cotangent models at that bound. -/
theorem commonBoundTransitivity : CommonBoundTransitivity.{u,v,t} := by
  intro k _ _
  classical
  let T := Tensor.moduleTensorModel.{u,v} k
  let T' := Tensor.moduleTensorModel.{u,max v t} k
  let h (A : CommDGAlgebra.{u,v} k) := laws A
  let h' (A : CommDGAlgebra.{u,max v t} k) := laws A
  let F {A B : CommDGAlgebra.{u,v} k} (f : A ⟶ B) := scalarExtensionModel f
  let F' {A B : CommDGAlgebra.{u,max v t} k} (f : A ⟶ B) := scalarExtensionModel f
  let d (A : CommDGAlgebra.{u,v} k) := ambientDescent.{u,v,t} A
  let K (A : NonpositiveCDGA.{u,max v t} k) :=
    adjunctionConeLocalization (coneLocalization.{u,max v t,0} (oneObject A) (h' A.toCommDGAlgebra))
  have forms : TensorFormulas T' := Tensor.moduleTensor_formulas
  have cmp : T'.Comparisons := Tensor.moduleTensor_comparisons
  have prod : T'.AlgebraCoproducts := Tensor.algebra_tensor_construction
  let N (A : NonpositiveCDGA.{u,max v t} k) : Naturality (K A) T' :=
    Classical.choice (naturalSequenceTriangles T' forms cmp A (h' A.toCommDGAlgebra) (K A))
  let K₀ (A : NonpositiveCDGA.{u,v} k) :=
    adjunctionConeLocalization (coneLocalization.{u,v,0} (oneObject A) (h A.toCommDGAlgebra))
  have forms₀ : TensorFormulas T := Tensor.moduleTensor_formulas
  let N₀ (A : NonpositiveCDGA.{u,v} k) : Naturality (K₀ A) T :=
    Classical.choice (naturalSequenceTriangles T forms₀ Tensor.moduleTensor_comparisons
      A (h A.toCommDGAlgebra) (K₀ A))
  let U {X : Chain.{u,v} k} (R : ResolvedChain T X) : LiftedResolution.{u,v,t} T' R :=
    ⟨Classical.choice (CotangentComplex.modelEnlargement.{u,v,max v t} R.resolution.P T T' forms₀ forms),
      Classical.choice (CotangentComplex.modelEnlargement.{u,v,max v t} R.resolution.Q T T' forms₀ forms),
      Classical.choice (CotangentComplex.modelEnlargement.{u,v,max v t} R.absoluteModel T T' forms₀ forms)⟩
  let ex {X : Chain.{u,v} k} (R : ResolvedChain T X) :=
    resolvedChainsExist T' forms cmp prod (X := liftChain.{u,v,t} X) (U R).resolution
  let S {X : Chain.{u,v} k} (R : ResolvedChain T X) := Classical.choose (ex R)
  have hS {X : Chain.{u,v} k} (R : ResolvedChain T X) :
      (S R).resolution = (U R).resolution := Classical.choose_spec (ex R)
  let b : CommonBoundComparisons.{u,v,t} (T := T) (T' := T') (h := h) (h' := h') d K₀ K N₀ N :=
    commonComparisons.{u,v,t} (h := h) (h' := h') d K₀ K N₀ N @U @S @hS
  have bIdent (X : Chain.{u,v} k) (R : ResolvedChain T X) : b.identified R :=
    identifyLiftedTriangles.{u,v,t} (T := T) (T' := T') (h := h) (h' := h')
      (d := d) (K := K₀) (K' := K) (N := N₀) (N' := N) (X := X) b R
  refine ⟨T, T', h, h', @F, @F', d, K₀, N₀, K, N, b, ?_, ?_⟩
  · intro A B f
    exact ⟨DerivedTensor.extensionCoefficientComparison.{u,v,t} f⟩
  · intro X
    let Y := liftChain.{u,v,t} X
    constructor
    · obtain ⟨P, Q, _, ⟨W⟩⟩ := ResolvedCotangentSequence.resolutionsExist X.first X.second
      obtain ⟨R, _⟩ := resolvedChainsExist T forms₀ Tensor.moduleTensor_comparisons
        Tensor.algebra_tensor_construction (X := X) ⟨P, Q, W⟩
      exact ⟨R⟩
    intro R₀
    let Z := b.resolved R₀
    refine ⟨identifiedTriangles (h X.B.toCommDGAlgebra) (h X.C.toCommDGAlgebra)
      (K₀ X.C) (F (underlying X.second)) R₀ ((N₀ X.C).triangle X R₀ (𝟙 X.C)),
      identifiedTriangles (h' Y.B.toCommDGAlgebra) (h' Y.C.toCommDGAlgebra)
        (K Y.C) (F' (underlying Y.second)) Z ((N Y.C).triangle Y Z (𝟙 Y.C)), ?_, ?_⟩
    · exact bIdent X R₀
    · intro R
      letI := derivedCategoryInstance (oneObject X.B) (h X.B.toCommDGAlgebra)
      letI := derivedCategoryInstance (oneObject X.C) (h X.C.toCommDGAlgebra)
      letI := derivedCategoryInstance (oneObject Y.B) (h' Y.B.toCommDGAlgebra)
      letI := derivedCategoryInstance (oneObject Y.C) (h' Y.C.toCommDGAlgebra)
      let G := F' (underlying Y.second)
      have g : (cdgaLift.{u,v,max v t} k).map (X.first ≫ X.second) = Y.first ≫ Y.second :=
        (cdgaLift.{u,v,max v t} k).map_comp X.first X.second
      obtain ⟨a⟩ := compareBoundModel.{u,v,t} X.first rfl R.resolution.P Z.resolution.P
      obtain ⟨b⟩ := compareBoundModel.{u,v,t} (X.first ≫ X.second) g R.absoluteModel Z.absoluteModel
      obtain ⟨c⟩ := compareBoundModel.{u,v,t} X.second rfl R.relativeModel Z.relativeModel
      let e := DerivedTensor.extensionCoefficientComparison.{u,v,t} (underlying X.second)
      exact ⟨⟨e.app (localizedModel (h X.B.toCommDGAlgebra) R.resolution.P T) ≪≫ G.functor.mapIso a⟩,
        ⟨b⟩, ⟨c⟩⟩

end Coefficients

end
end DerivedFormalization.Affine.CotangentTransitivity
