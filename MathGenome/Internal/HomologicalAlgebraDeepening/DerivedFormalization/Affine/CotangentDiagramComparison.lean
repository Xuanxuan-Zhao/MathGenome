import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.CotangentDiagramComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeResolution
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeRotation
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyShift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleTensorComparisons
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.ResolvedCotangentSequence
open CategoryTheory

set_option linter.style.haveILetI false

noncomputable section

universe u v

namespace DerivedFormalization.Affine.CotangentDiagramComparison

open Specs.DerivedFormalization.Affine.CotangentDiagramComparison
open Specs.DerivedFormalization.Affine.ResolvedCotangentSequence

theorem liftsExist_conditional
    (_ : Concatenation.{u,v}) (_ : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (_ : PushoutResolves.{u,v})
    (_ : ResolutionsExist.{u,v}) (_ : ResolvedTerms.{u,v}) : LiftsExist.{u,v} := by
  intro k _ _ X Y f R S
  obtain ⟨p, hp, ha⟩ := Semifree.exists_lift_of_surjective_quasiIso
    R.P.base (f.a ≫ S.P.base) (f.a ≫ Y.first) (R.P.augmentation ≫ f.b) S.P.augmentation
    R.P.semifree (by rw [← Category.assoc, R.P.triangle, f.first_comm])
    (by rw [Category.assoc, S.P.triangle]) S.P.surjective S.P.quasiIso
  obtain ⟨q, hq, hb⟩ := Semifree.exists_lift_of_surjective_quasiIso
    R.Q.base (p ≫ S.Q.base) (R.P.augmentation ≫ f.b ≫ Y.second)
    (R.Q.augmentation ≫ f.c) S.Q.augmentation R.Q.semifree
    (by rw [← Category.assoc, R.Q.triangle, Category.assoc, f.second_comm])
    (by rw [Category.assoc, S.Q.triangle, ← Category.assoc, ha, Category.assoc])
    S.Q.surjective S.Q.quasiIso
  exact ⟨⟨p, q, hp, ha, hq, hb⟩⟩

section Paths

open PolynomialPath
open Specs.DerivedFormalization.Affine.PolynomialPath
  (RelativePathModel mapCoefficients)

variable {k : Type u} [Field k] [CharZero k]

private theorem pathAlgebraMap_comp {A B C : CommDGAlgebra.{u,v} k}
    (f : A ⟶ B) (g : B ⟶ C) :
    pathAlgebraMap f ≫ pathAlgebraMap g = pathAlgebraMap (f ≫ g) := by
  apply CommDGAlgebra.Hom.ext_chainMap
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change mapDegree g.chainMap n (mapDegree f.chainMap n x) =
    mapDegree (f.chainMap ≫ g.chainMap) n x
  rcases x with ⟨x,y⟩
  rw [mapDegree_coordinates, mapDegree_coordinates, mapDegree_coordinates]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, mapCoefficients_comp_apply]

private theorem factorsThroughTruncation {A : NonpositiveCDGA.{u,v} k}
    {B : CommDGAlgebra.{u,v} k} (f : A.toCommDGAlgebra ⟶ B) (i : ℤ) (x : A.complex.X i) :
    f.chainMap.f i x ∈ truncationDegree B i := by
  apply (mem_truncationDegree _ _ _).2
  constructor
  · intro hi
    rw [(A.nonpositive i hi).elim x 0, map_zero]
  · rintro rfl
    exact (CategoryTheory.congr_fun (f.chainMap.comm 0 1) x).trans
      (by rw [ModuleCat.comp_apply, NonpositiveCDGA.d_zero_apply, map_zero])

private theorem relative_path_change {P B Q C : NonpositiveCDGA.{u,v} k}
    (p : P ⟶ B) (q : Q ⟶ C) (f : P ⟶ Q) (g : B ⟶ C) (h : f ≫ q = p ≫ g) :
    ∃ J : relativePath p ⟶ relativePath q,
      (show (relativePath p).toCommDGAlgebra ⟶ (relativePath q).toCommDGAlgebra from J) ≫
          relativePathInclusion q ≫ relativeInclusion q =
        relativePathInclusion p ≫ relativeInclusion p ≫ pathAlgebraMap (underlying f) ∧
      ∀ c, J ≫ evaluation q c = evaluation p c ≫ f := by
  let F := pathAlgebraMap (underlying f)
  let t := relativePathInclusion p ≫ relativeInclusion p
  have e : underlying f ≫ underlying q = underlying p ≫ underlying g := h
  have hs : (t ≫ F) ≫ pathAlgebraMap (underlying q) =
      (relativePathInclusion p ≫ relativeAugmentation p ≫ underlying g) ≫
        constantAlgebra C.toCommDGAlgebra := by
    dsimp only [t, F]
    rw [Category.assoc, pathAlgebraMap_comp, e,
      ← pathAlgebraMap_comp (underlying p) (underlying g),
      Category.assoc, ← Category.assoc (relativeInclusion p), relative_square p,
      Category.assoc, constantAlgebra_natural]
    simp only [Category.assoc]
  obtain ⟨G, ⟨hG, _⟩, _⟩ := relative_pullback q _ _ _ hs
  let J : relativePath p ⟶ relativePath q :=
    (truncationTerms (relativeAlgebra q)).factor G (factorsThroughTruncation G)
  have hJ : underlying J ≫ relativePathInclusion q = G :=
    (truncationTerms _).factor_inclusion _ _
  have hJ' : underlying J ≫ relativePathInclusion q ≫ relativeInclusion q = t ≫ F := by
    rwa [← Category.assoc, hJ]
  refine ⟨J, hJ', fun c => ?_⟩
  change underlying J ≫ relativePathInclusion q ≫ relativeInclusion q ≫
      endpointAlgebra _ c = (t ≫ endpointAlgebra _ c) ≫ underlying f
  rw [← Category.assoc _ (relativeInclusion q), ← Category.assoc, hJ', Category.assoc,
    endpointAlgebra_natural, ← Category.assoc]

private theorem pathsInNativeModels {X Y : Chain.{u,v} k}
    {f : ChainMap X Y} {R : Resolution X} {S : Resolution Y} (l₀ l₁ : Lift f R S) :
    Nonempty (Paths l₀ l₁ (relativePathModel S.P.augmentation)
      (relativePathModel S.Q.augmentation)) := by
  let P := relativePathModel S.P.augmentation
  let Q := relativePathModel S.Q.augmentation
  obtain ⟨J, hJ, hJend⟩ := relative_path_change S.P.augmentation S.Q.augmentation
    S.Q.base Y.second S.Q.triangle
  obtain ⟨Hp, hp, h₀, h₁, _⟩ := RelativePathComparison.relativePathLifting
    R.P.base (f.a ≫ S.P.base) (R.P.augmentation ≫ f.b) S.P.augmentation
    P l₀.p l₁.p R.P.semifree S.P.surjective S.P.quasiIso
    l₀.p_base l₁.p_base l₀.p_aug l₁.p_aug
  obtain ⟨ends, ⟨e₀, e₁⟩, _⟩ := Q.target_pullback R.Q.algebra l₀.q l₁.q (l₀.q_aug.trans l₁.q_aug.symm)
  have hl (l : Lift f R S) : R.Q.base ≫ l.q = l.p ≫ S.Q.base := l.q_base
  have he₀ : (J ≫ Q.endpoints ≫ Q.first) = P.endpoints ≫ P.first ≫ S.Q.base := by
    change J ≫ endpoints _ ≫ firstEndpoint _ = endpoints _ ≫ firstEndpoint _ ≫ S.Q.base
    rw [endpoints_first, ← Category.assoc, endpoints_first, hJend]
  have he₁ : (J ≫ Q.endpoints ≫ Q.second) = P.endpoints ≫ P.second ≫ S.Q.base := by
    change J ≫ endpoints _ ≫ secondEndpoint _ = endpoints _ ≫ secondEndpoint _ ≫ S.Q.base
    rw [endpoints_second, ← Category.assoc, endpoints_second, hJend]
  obtain ⟨base, _, uniq⟩ := Q.target_pullback R.P.algebra (R.Q.base ≫ l₀.q)
    (R.Q.base ≫ l₁.q) (by simp only [Category.assoc, l₀.q_aug, l₁.q_aug])
  have hb₀ : R.Q.base ≫ ends = base := uniq _ (by simp only [Category.assoc, e₀, e₁, and_self])
  let j : P.truncated ⟶ Q.truncated := J
  have hje₀ : j ≫ Q.endpoints ≫ Q.first = P.endpoints ≫ P.first ≫ S.Q.base := he₀
  have hje₁ : j ≫ Q.endpoints ≫ Q.second = P.endpoints ≫ P.second ≫ S.Q.base := he₁
  have hb₁ : (Hp ≫ j) ≫ Q.endpoints = base := uniq _ ⟨by
    rw [Category.assoc, Category.assoc, hje₀]
    calc
      _ = (Hp ≫ P.endpoints ≫ P.first) ≫ S.Q.base := by simp only [Category.assoc]
      _ = _ := by rw [h₀, ← hl l₀], by
    rw [Category.assoc, Category.assoc, hje₁]
    calc
      _ = (Hp ≫ P.endpoints ≫ P.second) ≫ S.Q.base := by simp only [Category.assoc]
      _ = _ := by rw [h₁, ← hl l₁]⟩
  have hLift : ∃ Hq : R.Q.algebra ⟶ Q.truncated,
      R.Q.base ≫ Hq = Hp ≫ j ∧ Hq ≫ Q.endpoints = ends :=
    Semifree.exists_lift_of_surjective_quasiIso R.Q.base
      (Hp ≫ j) base ends Q.endpoints R.Q.semifree hb₀ hb₁
      (Q.trivial_fibration S.Q.surjective S.Q.quasiIso).1
      (Q.trivial_fibration S.Q.surjective S.Q.quasiIso).2
  obtain ⟨Hq, hq, hend⟩ := hLift
  refine ⟨⟨j, ?_, Hp, Hq, ?_, hq, h₀, h₁, ?_, ?_⟩⟩
  · intro n x
    have eq := CategoryTheory.congr_fun (congrArg (fun a => a.chainMap.f n) hJ) x
    let z := (relativePathInclusion S.P.augmentation ≫ relativeInclusion S.P.augmentation).chainMap.f n x
    exact eq.trans (mapDegree_coordinates S.Q.base.chainMap n z.1 z.2)
  · simpa only [Category.assoc] using hp
  · rw [← Category.assoc, hend, e₀]
  · rw [← Category.assoc, hend, e₁]

theorem pathsExist_conditional
    (_ : Concatenation.{u,v}) (_ : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (_ : PushoutResolves.{u,v})
    (_ : ResolutionsExist.{u,v}) (_ : ResolvedTerms.{u,v}) : PathsExist.{u,v} := by
  intro k _ _ X Y f R S l₀ l₁
  exact ⟨_, _, _, _, _, _, pathsInNativeModels l₀ l₁⟩

end Paths

theorem sequencesExist_conditional
    (_ : Concatenation.{u,v}) (exactSequence : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (pushoutResolution : PushoutResolves.{u,v})
    (resolutions : ResolutionsExist.{u,v}) (terms : ResolvedTerms.{u,v}) :
    SequencesExist.{u,v} := by
  intro k _ _ T forms comparisons coproducts X
  obtain ⟨coproduct, hcoproduct, _⟩ := coproducts
  obtain ⟨P, Q, _, ⟨U⟩⟩ := resolutions X.first X.second
  let R : Resolution X := ⟨P, Q, U⟩
  obtain ⟨F, split⟩ := exactSequence T forms P.base Q.base
    P.differentials U Q.differentials P.semifree Q.semifree
  let W := coproduct (underlying Q.base) (underlying P.augmentation)
  have hW : W.Formulas := hcoproduct _ _
  obtain ⟨D⟩ := pushoutResolution T forms comparisons Q.base P.augmentation X.second
    Q.augmentation W hW Q.triangle Q.semifree P.quasiIso Q.surjective Q.quasiIso
  obtain ⟨_, _, _, _, hL, hM, hN⟩ := terms T forms comparisons P Q U F W hW D
    (Kahler.model (underlying (pushoutInr W hW)))
  exact ⟨R, F, split, hL, hM, hN⟩

section Cones

open Specs.DerivedFormalization.Affine.Tensor (term act)
open Tensor (homOfDegrees)
open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component HomotopyEquation)
open Specs.DerivedFormalization.DG.ShiftCone
  (cone coneInclusion coneProjection coneTerm coneDiff coneDiff_succ shiftMap)
open private quasiIso_of_surjective_of_kernel_acyclic from
  MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.SemifreeResolution
open private strictConeMap strictConeMap_apply homotopy_at_succ from
  MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeMaps

variable {k : Type u} [Field k] [CharZero k] {E : CommDGAlgebra.{u,v} k}
variable {L M N L' M' N' : E.Module} {i : L ⟶ M} {p : M ⟶ N} {i' : L' ⟶ M'} {p' : M' ⟶ N'}

private theorem gradedSplit_zero_apply (S : GradedSplit i p) (n : ℤ) (x : term L n) :
    (p.app ()).f n ((i.app ()).f n x) = 0 :=
  congrArg (fun f : L ⟶ N => (f.app ()).f n x) S.zero

private def coneQuotient (S : GradedSplit i p) : cone i ⟶ N :=
  homOfDegrees (fun n => ((p.app ()).f n).hom.comp (LinearMap.fst _ _ _))
    (by
      intro n x
      change _ = (p.app ()).f (n+1) (coneDiff i () n (n+1) x).1
      rw [coneDiff_succ]
      simp only [map_add, gradedSplit_zero_apply S, add_zero]
      exact RightDGModule.strict_d p () n x.1)
    (by
      intro a b n e x z
      exact p.comm_act a b n e x.1 z)

private theorem coneQuotient_quasiIso (S : GradedSplit i p) : IsConeQuotient p (coneQuotient S) := by
  refine ⟨fun _ _ => rfl, ?_⟩
  rintro ⟨⟩
  apply quasiIso_of_surjective_of_kernel_acyclic
  · intro n z
    refine ⟨(component S.sectionMap () n n (add_zero n) z, 0), S.section_id n z⟩
  · intro j z hz hd
    change (p.app ()).f (j+1) z.1 = 0 at hz
    change coneDiff i () (j+1) (j+1+1) z = 0 at hd
    rw [coneDiff_succ] at hd
    have hx : (i.app ()).f (j+1) (component S.retraction () (j+1) (j+1) (add_zero _) z.1) = z.1 := by
      simpa only [hz, map_zero, add_zero] using S.decompose (j+1) z.1
    let x := component S.retraction () (j+1) (j+1) (add_zero _) z.1
    refine ⟨(0, x), ?_, ?_⟩
    · exact (map_zero ((p.app ()).f j).hom : _)
    change coneDiff i () j (j+1) (0, x) = z
    rw [coneDiff_succ, map_zero, zero_add]
    apply Prod.ext hx
    have hd₁ : (M.complex ()).d (j+1) (j+1+1) z.1 + (i.app ()).f (j+1+1) z.2 = 0 :=
      congrArg Prod.fst hd
    rw [← hx, RightDGModule.strict_d i, ← map_add] at hd₁
    have inj : Function.Injective ((i.app ()).f (j+1+1)) := fun a b h =>
      (S.retract _ a).symm.trans ((congrArg (component S.retraction () _ _ (add_zero _)) h).trans
        (S.retract _ b))
    have de := inj (hd₁.trans (map_zero _).symm)
    exact neg_eq_of_add_eq_zero_right (by simpa only [add_comm] using de)

private def sequenceConeMap (f : SequenceMap i p i' p') : cone i ⟶ cone i' :=
  strictConeMap i i' f.left f.middle f.incl_comm

private theorem sequenceConeMap_apply (f : SequenceMap i p i' p') (n : ℤ) (x : coneTerm L M () n) :
    ((sequenceConeMap f).app ()).f n x = ((f.middle.app ()).f n x.1, (f.left.app ()).f (n+1) x.2) :=
  strictConeMap_apply _ _ _ _ _ _ _ _

private def sequenceConeHomotopy {f g : SequenceMap i p i' p'} (H : SequenceHomotopy f g) :
    gradedHom (cone i) (cone i') (-1) :=
  RightDGModule.homotopyOfComponents
    (fun _ n => ((component H.middle () (n+1) n (by omega)).hom.comp (LinearMap.fst _ _ _)).prod
      (-((component H.left () (n+1+1) (n+1) (by omega)).hom.comp (LinearMap.snd _ _ _))))
    (by
      rintro ⟨⟩ ⟨⟩ a b n e x z
      apply Prod.ext
      · exact H.middle.property (a := ()) (b := ()) (a+1) b (n+1) a n
          (by omega) (by omega) (by omega) x.1 z
      · change -component H.left () (n+1+1) (n+1) (by omega)
          (act L (a+1+1) b (n+1+1) (by omega) x.2 z) =
          act L' (a+1) b (n+1) (by omega) (-component H.left () (a+1+1) (a+1) (by omega) x.2) z
        rw [H.left.property (a := ()) (b := ()), map_neg, LinearMap.neg_apply])

private theorem sequenceConeHomotopy_apply {f g : SequenceMap i p i' p'} (H : SequenceHomotopy f g)
    (n : ℤ) (x : coneTerm L M () (n+1)) :
    component (sequenceConeHomotopy H) () (n+1) n (by omega) x =
      (component H.middle () (n+1) n (by omega) x.1,
        -component H.left () (n+1+1) (n+1) (by omega) x.2) := rfl

private theorem sequenceConeHomotopy_eq {f g : SequenceMap i p i' p'} (H : SequenceHomotopy f g) :
    HomotopyEquation (sequenceConeMap f) (sequenceConeMap g) (sequenceConeHomotopy H) := by
  apply RightDGModule.homotopyEquationOfSucc
  rintro ⟨⟩ n x
  change _ = coneDiff i' () n (n+1)
      (component (sequenceConeHomotopy H) () (n+1) n (by omega) x) +
    component (sequenceConeHomotopy H) () (n+1+1) (n+1) (by omega) (coneDiff i () (n+1) (n+1+1) x)
  rw [sequenceConeMap_apply, sequenceConeMap_apply, coneDiff_succ, sequenceConeHomotopy_apply,
    sequenceConeHomotopy_apply, coneDiff_succ]
  apply Prod.ext
  · change (f.middle.app ()).f (n+1) x.1 - (g.middle.app ()).f (n+1) x.1 =
      ((M'.complex ()).d n (n+1) (component H.middle () (n+1) n (by omega) x.1) +
        (i'.app ()).f (n+1) (-component H.left () (n+1+1) (n+1) (by omega) x.2)) +
        component H.middle () (n+1+1) (n+1) (by omega)
          ((M.complex ()).d (n+1) (n+1+1) x.1 + (i.app ()).f (n+1+1) x.2)
    have hm := homotopy_at_succ H.middle_eq () n x.1
    rw [hm]
    simp only [map_add, map_neg, H.incl_comm]
    abel
  · change (f.left.app ()).f (n+1+1) x.2 - (g.left.app ()).f (n+1+1) x.2 =
      -(L'.complex ()).d (n+1) (n+1+1) (-component H.left () (n+1+1) (n+1) (by omega) x.2) +
        -component H.left () (n+1+1+1) (n+1+1) (by omega)
          (-(L.complex ()).d (n+1+1) (n+1+1+1) x.2)
    simp only [map_neg, neg_neg]
    exact homotopy_at_succ H.left_eq () (n+1) x.2

theorem coneComparisons_conditional
    (_ : Concatenation.{u,v}) (_ : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (_ : PushoutResolves.{u,v})
    (_ : ResolutionsExist.{u,v}) (_ : ResolvedTerms.{u,v}) : ConeComparisons.{u,v} := by
  intro k _ _ E L M N L' M' N' i p i' p' S S'
  refine ⟨coneQuotient S, coneQuotient S', sequenceConeMap,
    coneQuotient_quasiIso S, coneQuotient_quasiIso S', ?_, ?_⟩
  · intro f
    refine ⟨sequenceConeMap_apply f, ?_, ?_, ?_⟩
    · apply RightDGModule.strict_ext
      rintro ⟨⟩ n x
      change ((sequenceConeMap f).app ()).f n (x,0) =
        ((f.middle.app ()).f n x, 0)
      rw [sequenceConeMap_apply, map_zero]
    · apply RightDGModule.strict_ext
      rintro ⟨⟩ n x
      change (((sequenceConeMap f).app ()).f n x).2 = (f.left.app ()).f (n+1) x.2
      rw [sequenceConeMap_apply]
    · apply RightDGModule.strict_ext
      rintro ⟨⟩ n x
      change (p'.app ()).f n (((sequenceConeMap f).app ()).f n x).1 =
        (f.right.app ()).f n ((p.app ()).f n x.1)
      rw [sequenceConeMap_apply]
      exact (congrArg (fun t : M ⟶ N' => (t.app ()).f n x.1) f.proj_comm).symm
  · exact fun _ _ H => ⟨sequenceConeHomotopy H, sequenceConeHomotopy_eq H⟩

end Cones


section Localization

open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.DG.Derived (quotient)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance kProjectiveObjects)
open Specs.DerivedFormalization.DG.HomComplex (homotopyClass homotopyCategory)
open Specs.DerivedFormalization.Affine.Tensor (dgCat ModuleTensor)

private theorem conjugate_eqToHom {C : Type*} [Category* C] {W X Y Z : C}
    (e : W = X) (e' : Y = Z) {f : W ⟶ Y} {g : X ⟶ Z} (h : HEq f g) :
    f ≫ eqToHom e' = eqToHom e ≫ g := by
  cases e
  cases e'
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using eq_of_heq h

set_option maxHeartbeats 1200000 in
theorem derivedExtensionComparison_conditional
    (_ : Concatenation.{u,v}) (_ : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (_ : PushoutResolves.{u,v})
    (_ : ResolutionsExist.{u,v}) (_ : ResolvedTerms.{u,v}) :
    DerivedExtensionComparison.{u,v} := by
  intro k _ _ T A B f hA hB F
  letI := Derived.homotopyCategory (dgCat A) hA
  letI := Derived.homotopyCategory (dgCat B) hB
  letI := derivedCategoryInstance (dgCat A) hA
  letI := derivedCategoryInstance (dgCat B) hB
  dsimp only
  intro M N m hM hN
  let QA : homotopyCategory (dgCat A) ⥤ Derived.derivedCategory (dgCat A) hA :=
    quotient (dgCat A) hA
  let QB : homotopyCategory (dgCat B) ⥤ Derived.derivedCategory (dgCat B) hB :=
    quotient (dgCat B) hB
  let PM : (kProjectiveObjects (dgCat A)).FullSubcategory := ⟨M, hM⟩
  let PN : (kProjectiveObjects (dgCat A)).FullSubcategory := ⟨N, hN⟩
  let a : PM ⟶ PN := ObjectProperty.homMk (homotopyClass m)
  have hs := F.data.tensorSquare.hom.naturality a
  change F.functor.map (QA.map (homotopyClass m)) ≫ F.data.tensorSquare.hom.app PN =
    F.data.tensorSquare.hom.app PM ≫ QB.map (F.data.tensorH.map (homotopyClass m)) at hs
  let G := Specs.DerivedFormalization.DG.BimoduleAdjunction.ordinaryTensor F.models.tensor
  let first (P : (kProjectiveObjects (dgCat A)).FullSubcategory) :
      F.functor.obj (QA.obj P.obj) ⟶ QB.obj (F.data.tensorH.obj P.obj) :=
    F.data.tensorSquare.hom.app P
  let second (P : A.Module) : QB.obj (F.data.tensorH.obj P) ⟶ QB.obj (G.obj P) :=
    eqToHom (congrArg QB.obj (F.data.tensorObj P))
  let third (P : A.Module) : QB.obj (G.obj P) ⟶ QB.obj ((T.baseChange f).obj P) :=
    eqToHom (congrArg (fun J : A.Module ⥤ B.Module => QB.obj (J.obj P)) F.strict)
  change F.functor.map (QA.map (homotopyClass m)) ≫ first PN = first PM ≫ _ at hs
  have ht := conjugate_eqToHom (C := homotopyCategory (dgCat B))
    (F.data.tensorObj M) (F.data.tensorObj N) (F.realizes.2.1 m)
  have hmap : QB.map (F.data.tensorH.map (homotopyClass m)) ≫
        eqToHom (congrArg QB.obj (F.data.tensorObj N)) =
      eqToHom (congrArg QB.obj (F.data.tensorObj M)) ≫ QB.map (homotopyClass (G.map m)) := by
    let r := F.data.tensorH.map (homotopyClass m)
    let s : @Quiver.Hom (homotopyCategory (dgCat B))
        (Derived.homotopyCategory (dgCat B) hB).toQuiver (G.obj M) (G.obj N) :=
      homotopyClass (G.map m)
    calc
      _ = QB.map (r ≫ eqToHom (F.data.tensorObj N)) := by
        rw [QB.map_comp, eqToHom_map]
      _ = QB.map (eqToHom (F.data.tensorObj M) ≫ s) := congrArg QB.map ht
      _ = _ := by
        have e := QB.map_comp (eqToHom (F.data.tensorObj M)) s
        rw [eqToHom_map] at e
        exact e
  change QB.map (F.data.tensorH.map (homotopyClass m)) ≫ second N =
    second M ≫ QB.map (homotopyClass (G.map m)) at hmap
  have hc : QB.map (homotopyClass (G.map m)) ≫
        eqToHom (congrArg (fun J : A.Module ⥤ B.Module => QB.obj (J.obj N)) F.strict) =
      eqToHom (congrArg (fun J : A.Module ⥤ B.Module => QB.obj (J.obj M)) F.strict) ≫
        QB.map (homotopyClass ((T.baseChange f).map m)) := by
    have eq : G = T.baseChange f := F.strict
    change _ ≫ eqToHom (congrArg (fun J : A.Module ⥤ B.Module => QB.obj (J.obj N)) eq) =
      eqToHom (congrArg (fun J : A.Module ⥤ B.Module => QB.obj (J.obj M)) eq) ≫ _
    generalize T.baseChange f = J at eq ⊢
    cases eq
    simp
  change QB.map (homotopyClass (G.map m)) ≫ third N =
    third M ≫ QB.map (homotopyClass ((T.baseChange f).map m)) at hc
  change F.functor.map (QA.map (homotopyClass m)) ≫ ((first PN ≫ second N) ≫ third N) =
    ((first PM ≫ second M) ≫ third M) ≫ QB.map (homotopyClass ((T.baseChange f).map m))
  calc
    _ = (F.functor.map (QA.map (homotopyClass m)) ≫ first PN) ≫ second N ≫ third N := by
      simp only [Category.assoc]
    _ = first PM ≫ (QB.map (F.data.tensorH.map (homotopyClass m)) ≫ second N) ≫ third N := by
      rw [hs]
      simp only [Category.assoc]
    _ = _ := by
      rw [hmap]
      simp only [Category.assoc, hc]

end Localization


section DifferentialPaths

open CochainComplex.HomComplex (Cochain)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor regular restrict term act)
open Specs.DerivedFormalization.Affine.PolynomialPath
  (RelativePathModel AlgebraPathModel ModulePathModel mapCoefficients)
open Specs.DerivedFormalization.Affine.RelativePathComparison (baseChangedSymbol)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component HomotopyEquation)
open Kahler (DifferentialModel IsDerivation)
open private includedPath includedPath_endpoint pathDerivative pathDerivative_coordinates
  pathDerivative_leibniz representStrict scalarExtend scalarExtend_pure
  act_baseChangedSymbol precomposeHomotopy precomposeHomotopy_equation
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {k : Type u} [Field k] [CharZero k]
variable {A P A' Q E : NonpositiveCDGA.{u,v} k}
variable {a : A ⟶ P} {a' : A' ⟶ Q} {p : P ⟶ E} {q : Q ⟶ E}
variable {U : AlgebraPathModel Q.toCommDGAlgebra} {V : AlgebraPathModel E.toCommDGAlgebra}

private theorem derivative_path_killing_base
    (J : RelativePathModel q U V) (H : P ⟶ J.truncated)
    (hAug : H ≫ J.endpoints ≫ J.first ≫ q = p)
    (T : ModuleTensor.{u,v} k) (forms : TensorFormulas T)
    (O : Differentials a) (O' : Differentials a')
    (W : ModulePathModel ((extend T q).obj O'.module))
    (hBase : ∀ n (x : A.complex.X n),
      let z := U.coordinates n ((includedPath q J H).chainMap.f n (a.chainMap.f n x))
      (mapCoefficients (baseChangedSymbol T (underlying q) O' n) z.1,
        mapCoefficients (baseChangedSymbol T (underlying q) O' (n-1)) z.2) = 0) :
    ∃ F : (extend T p).obj O.module ⟶ W.obj,
      (∀ n (x : P.complex.X n),
        let z := U.coordinates n ((includedPath q J H).chainMap.f n x)
        W.coordinates n ((F.app ()).f n (baseChangedSymbol T (underlying p) O n x)) =
          (mapCoefficients (baseChangedSymbol T (underlying q) O' n) z.1,
            mapCoefficients (baseChangedSymbol T (underlying q) O' (n-1)) z.2)) ∧
      (∀ (f : P ⟶ Q) (c : k),
        (f = H ≫ J.endpoints ≫ J.first ∧ c = 0 ∨
          f = H ≫ J.endpoints ≫ J.second ∧ c = 1) →
        ∀ n (x : P.complex.X n),
          ((F ≫ W.evaluation c).app ()).f n (baseChangedSymbol T (underlying p) O n x) =
            baseChangedSymbol T (underlying q) O' n (f.chainMap.f n x)) ∧
      ∃ h : gradedHom ((extend T p).obj O.module) ((extend T q).obj O'.module) (-1),
        HomotopyEquation (F ≫ W.evaluation 1) (F ≫ W.evaluation 0) h ∧
        ∀ n m e (x : term ((extend T p).obj O.module) n),
          component h () n m e x = component W.homotopy () n m e ((F.app ()).f n x) := by
  let fp := forms (underlying p) (regular E.toCommDGAlgebra)
  let fq := forms (underlying q) (regular E.toCommDGAlgebra)
  let D := pathDerivative q J H T O' fq W
  have hD : IsDerivation (underlying a) (M := restrict (underlying p) W.obj) (Cochain.ofHom D) := by
    constructor
    · intro i j e x
      have hj : i = j := by omega
      cases hj
      rw [Cochain.ofHom_v]
      apply (W.coordinates i).injective
      rw [pathDerivative_coordinates, map_zero]
      exact hBase i x
    · intro i j n ir jr nr e ei ej en x y
      have hi : i = ir := by omega
      have hj : j = jr := by omega
      have hn : n = nr := by omega
      cases hi
      cases hj
      cases hn
      simp only [Cochain.ofHom_v]
      exact pathDerivative_leibniz p q J H T O' fq W hAug i j n e x y
  obtain ⟨L, hL⟩ := representStrict O (restrict (underlying p) W.obj) D hD
  let F := scalarExtend T fp L
  refine ⟨F, ?_, ?_, ⟨precomposeHomotopy F W.homotopy,
    precomposeHomotopy_equation F _ _ _ W.endpoints_homotopic, fun _ _ _ _ => rfl⟩⟩
  · intro i x
    change W.coordinates i ((F.app ()).f i
      (extendedSymbol T O p i 0 i (add_zero i) x E.one)) = _
    rw [scalarExtend_pure, W.obj.act_id, hL]
    exact pathDerivative_coordinates q J H T O' fq W i x
  · intro f c hf i x
    change ((W.evaluation c).app ()).f i ((F.app ()).f i
      (extendedSymbol T O p i 0 i (add_zero i) x E.one)) = _
    rw [scalarExtend_pure, W.obj.act_id, hL, W.evaluation_coordinates,
      pathDerivative_coordinates]
    change Specs.DerivedFormalization.Affine.PolynomialPath.evaluate c
      (mapCoefficients (baseChangedSymbol T (underlying q) O' i)
        (U.coordinates i ((includedPath q J H).chainMap.f i x)).1) = _
    rw [PolynomialPath.evaluate_mapCoefficients, includedPath_endpoint q J H i x f c hf]

end DifferentialPaths


section PathNaturality

open Specs.DerivedFormalization.Affine.Tensor (term act)
open Specs.DerivedFormalization.Affine.PolynomialPath
  (ModulePathModel mapCoefficients endpoint contraction)
open Specs.DerivedFormalization.DG.HomComplex (component)
open private asPathCoordinates fromPathCoordinates from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
open PolynomialPath

variable {k : Type u} [Field k] [CharZero k] {E : CommDGAlgebra.{u,v} k}
variable {M N : E.Module}

private theorem mapDegree_apply (f : M.complex () ⟶ N.complex ()) (n : ℤ)
    (z : Specs.DerivedFormalization.Affine.PolynomialPath.term (M.complex ()) n) :
    mapDegree f n z =
      (mapCoefficients (f.f n).hom z.1, mapCoefficients (f.f (n-1)).hom z.2) :=
  mapDegree_coordinates f n z.1 z.2

private def modulePathMap (W : ModulePathModel M) (V : ModulePathModel N) (f : M ⟶ N) :
    W.obj ⟶ V.obj where
  app _ :=
    asPathCoordinates W.coordinates (fun i => W.d_coordinates i (i+1) rfl) ≫
      pathMap (f.app ()) ≫
      fromPathCoordinates V.coordinates (fun i => V.d_coordinates i (i+1) rfl)
  comm_act := by
    rintro ⟨⟩ ⟨⟩ i j n e x z
    apply (V.coordinates n).injective
    change V.coordinates n ((V.coordinates n).symm
      (mapDegree (f.app ()) n (W.coordinates n (act W.obj i j n e x z)))) =
      V.coordinates n (act V.obj i j n e ((V.coordinates i).symm
        (mapDegree (f.app ()) i (W.coordinates i x))) z)
    rw [LinearEquiv.apply_symm_apply, W.action_coordinates, V.action_coordinates,
      LinearEquiv.apply_symm_apply, mapDegree_apply, mapDegree_apply]
    simp only [Units.smul_def, map_zsmul, mapCoefficients_comp_apply]
    have cmp (a b : ℤ) (h : a+j=b) :
        ((f.app ()).f b).hom.comp ((act M a j b h).flip z) =
          ((act N a j b h).flip z).comp ((f.app ()).f a).hom := by
      apply LinearMap.ext
      intro y
      exact f.comm_act a j b h y z
    rw [cmp i n e, cmp (i-1) (n-1) (by omega)]

private theorem modulePathMap_coordinates (W : ModulePathModel M) (V : ModulePathModel N)
    (f : M ⟶ N) (n : ℤ) (x : term W.obj n) :
    V.coordinates n (((modulePathMap W V f).app ()).f n x) =
      mapDegree (f.app ()) n (W.coordinates n x) := (V.coordinates n).apply_symm_apply _

private theorem modulePathMap_evaluation (W : ModulePathModel M) (V : ModulePathModel N)
    (f : M ⟶ N) (c : k) :
    modulePathMap W V f ≫ V.evaluation c = W.evaluation c ≫ f := by
  apply RightDGModule.strict_ext
  rintro ⟨⟩ n x
  change ((V.evaluation c).app ()).f n (((modulePathMap W V f).app ()).f n x) =
    (f.app ()).f n (((W.evaluation c).app ()).f n x)
  rw [V.evaluation_coordinates, W.evaluation_coordinates, modulePathMap_coordinates, mapDegree_apply]
  exact evaluate_mapCoefficients _ _ _

private theorem modulePathMap_integral (W : ModulePathModel M) (V : ModulePathModel N)
    (f : M ⟶ N) (n m : ℤ) (e : n+(-1)=m) (x : term W.obj n) :
    component V.homotopy () n m e (((modulePathMap W V f).app ()).f n x) =
      (f.app ()).f m (component W.homotopy () n m e x) := by
  have h : n-1=m := by omega
  rw [V.integral_coordinates n m h, W.integral_coordinates n m h, modulePathMap_coordinates]
  let z := W.coordinates n x
  change endpoint (N.complex ()) 1 m (contraction (N.complex ()) n m h (mapDegree (f.app ()) n z)) =
    (f.app ()).f m (endpoint (M.complex ()) 1 m (contraction (M.complex ()) n m h z))
  rw [← contraction_natural (f.app ()) n m h z, mapDegree_apply]
  exact evaluate_mapCoefficients _ _ _

end PathNaturality


section Symbols

open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor term act regular restrict restrictFunctor)
open Specs.DerivedFormalization.Affine.RelativePathComparison (baseChangedSymbol)
open private tensor_ext unit_tensor_action from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison
open private unitTensor unitTensor_apply differentialMap_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.CotangentComplex

variable {k : Type u} [Field k] [CharZero k]
variable {A B E : CommDGAlgebra.{u,v} k}
variable (T : ModuleTensor.{u,v} k) (forms : TensorFormulas T)

include forms

private theorem scalarMap_ext (p : A ⟶ B) {M : A.Module} {N : B.Module}
    {F G : (T.baseChange p).obj M ⟶ N}
    (h : ∀ n (x : term M n),
      (F.app ()).f n (T.tmul p (N := regular B) n 0 n (add_zero n) x B.one) =
      (G.app ()).f n (T.tmul p (N := regular B) n 0 n (add_zero n) x B.one)) : F = G := by
  apply RightDGModule.strict_ext
  rintro ⟨⟩ n
  apply LinearMap.congr_fun
  apply tensor_ext T
  intro i j e x y
  change (F.app ()).f n (T.tmul p (N := regular B) i j n e x y) =
    (G.app ()).f n (T.tmul p (N := regular B) i j n e x y)
  rw [← unit_tensor_action T (forms p (regular B)), F.comm_act, G.comm_act, h]

private theorem differentialScalarMap_ext (a : A ⟶ B) (p : B ⟶ E)
    (O : Kahler.DifferentialModel a) {N : E.Module}
    {F G : (T.baseChange p).obj O.module ⟶ N}
    (h : ∀ n (x : B.complex.X n),
      (F.app ()).f n (baseChangedSymbol T p O n x) =
      (G.app ()).f n (baseChangedSymbol T p O n x)) : F = G := by
  let U := unitTensor p O.module (forms p (regular E))
  have hU : U ≫ (restrictFunctor p).map F = U ≫ (restrictFunctor p).map G := by
    apply differentialMap_ext O
    exact h
  apply scalarMap_ext T forms p
  intro n x
  exact congrArg (fun t : O.module ⟶ restrict p N => (t.app ()).f n x) hU

private theorem differentialDoubleScalarMap_ext {D : CommDGAlgebra.{u,v} k}
    (a : A ⟶ B) (p : B ⟶ E) (q : E ⟶ D)
    (O : Kahler.DifferentialModel a) {N : D.Module}
    {F G : (T.baseChange q).obj ((T.baseChange p).obj O.module) ⟶ N}
    (h : ∀ n (x : B.complex.X n),
      (F.app ()).f n (T.tmul q (N := regular D) n 0 n (add_zero n)
        (baseChangedSymbol T p O n x) D.one) =
      (G.app ()).f n (T.tmul q (N := regular D) n 0 n (add_zero n)
        (baseChangedSymbol T p O n x) D.one)) : F = G := by
  let U := unitTensor q ((T.baseChange p).obj O.module) (forms q (regular D))
  have hU : U ≫ (restrictFunctor q).map F = U ≫ (restrictFunctor q).map G := by
    apply differentialScalarMap_ext T forms a p O
    exact h
  apply scalarMap_ext T forms q
  intro n x
  exact congrArg (fun t : (T.baseChange p).obj O.module ⟶ restrict q N => (t.app ()).f n x) hU

variable {X Y Z : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y} {V : Resolution Z}
variable {D : NonpositiveCDGA.{u,v} k}

private theorem inclusionAt_symbol (F : Sequence T R) (e : X.C ⟶ D)
    (n : ℤ) (x : R.P.algebra.complex.X n) :
    ((inclusionAt F e).app ()).f n (leftSymbol T R e n x) =
      middleSymbol T R e n (R.Q.base.chainMap.f n x) := by
  change (((extend T (R.Q.augmentation ≫ e)).map F.incl).app ()).f n
    (T.tmul (underlying (R.Q.augmentation ≫ e)) (N := regular D.toCommDGAlgebra)
      n 0 n (add_zero n)
      (extendedSymbol T R.P.differentials R.Q.base n 0 n (add_zero n) x R.Q.algebra.one) D.one) = _
  rw [(forms _ _).first, F.incl_symbol, R.absolute.module.act_id]

private theorem projectionAt_symbol (F : Sequence T R) (e : X.C ⟶ D)
    (n : ℤ) (x : R.Q.algebra.complex.X n) :
    ((projectionAt F e).app ()).f n (middleSymbol T R e n x) = rightSymbol T R e n x := by
  change (((extend T (R.Q.augmentation ≫ e)).map F.proj).app ()).f n
    (T.tmul (underlying (R.Q.augmentation ≫ e)) (N := regular D.toCommDGAlgebra)
      n 0 n (add_zero n) (symbol R.absolute n x) D.one) = _
  rw [(forms _ _).first, F.proj_symbol]

private theorem inducedMap_unique {f : ChainMap X Y} {l : Lift f R S}
    {F : Sequence T R} {G : Sequence T S} {e : X.C ⟶ D} {d : Y.C ⟶ D}
    {c c' : MapAt F G e d} (hc : Induces l c) (hc' : Induces l c') : c = c' := by
  have hl : c.left = c'.left := by
    apply differentialDoubleScalarMap_ext T forms _ _ _ R.P.differentials
    exact fun n x => (hc.1 n x).trans (hc'.1 n x).symm
  have hm : c.middle = c'.middle := by
    apply differentialScalarMap_ext T forms _ _ R.absolute
    exact fun n x => (hc.2.1 n x).trans (hc'.2.1 n x).symm
  have hr : c.right = c'.right := by
    apply differentialScalarMap_ext T forms _ _ R.Q.differentials
    exact fun n x => (hc.2.2 n x).trans (hc'.2.2 n x).symm
  cases c
  cases c'
  cases hl
  cases hm
  cases hr
  rfl

omit forms in
private theorem inducedMap_id (F : Sequence T R) (e : X.C ⟶ D) :
    Induces (Lift.id R) (SequenceMap.id : MapAt F F e e) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

omit forms in
private theorem inducedMap_comp {f : ChainMap X Y} {g : ChainMap Y Z}
    {l : Lift f R S} {m : Lift g S V}
    {F : Sequence T R} {G : Sequence T S} {H : Sequence T V}
    {e : X.C ⟶ D} {d : Y.C ⟶ D} {c : Z.C ⟶ D}
    {a : MapAt F G e d} {b : MapAt G H d c} (ha : Induces l a) (hb : Induces m b) :
    Induces (l.comp m) (a.comp b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n x
    change (b.left.app ()).f n ((a.left.app ()).f n _) = _
    rw [ha.1, hb.1]
    rfl
  · intro n x
    change (b.middle.app ()).f n ((a.middle.app ()).f n _) = _
    rw [ha.2.1, hb.2.1]
    rfl
  · intro n x
    change (b.right.app ()).f n ((a.right.app ()).f n _) = _
    rw [ha.2.2, hb.2.2]
    rfl

end Symbols


section TensorOfSequence

open CochainComplex.HomComplex (Cochain)
open Specs.DerivedFormalization.DG.BalancedTensor (RightModule tmul)
open Specs.DerivedFormalization.DG.BimoduleAdjunction (TensorModel ordinaryTensor)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor term act regular signedBimodule dgCat pure)
open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit)
open Specs.DerivedFormalization.DG.HomComplex (gradedHom component)
open Specs.DerivedFormalization.DG.ShiftCone (cone coneInclusion coneProjection shift)
open private tensor_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {k : Type u} [Field k] [CharZero k]
variable {A B : CommDGAlgebra.{u,v} k} (T : ModuleTensor.{u,v} k) (f : A ⟶ B)
variable (hf : T.Formulas f (regular B))

private abbrev asMixed (B : CommDGAlgebra.{u,v} k) :
    B.Module ⥤ RightModule.{u,v,0,v} (dgCat B) where
  obj M := ⟨M.complex, M.act, M.act_id, M.act_assoc, M.leibniz⟩
  map g := ⟨g.app, g.comm_act⟩
  map_id _ := rfl
  map_comp _ _ := rfl

private abbrev scalarTensorModel : TensorModel (signedBimodule f (regular B)) where
  functor := T.baseChange f ⋙ asMixed B
  degree M _ n := T.degree f M (regular B) n
  d_tmul M _ _ := hf.differential M
  act_tmul M _ := fun _ _ _ _ _ => hf.action M _ _ _ _ _
  map_tmul g _ _ := hf.first g

variable {L M N : A.Module}

private def tensorGradedDegree {r : ℤ} (g : gradedHom L M r) (n q : ℤ) (e : n+r=q) :
    term ((T.baseChange f).obj L) n →ₗ[k] term ((T.baseChange f).obj M) q :=
  (T.degree f M (regular B) q).toLinearMap.comp
    (((component (Tensor.mapFirstGraded f (regular B) g) () n q e).hom).comp
      (T.degree f L (regular B) n).symm.toLinearMap)

private theorem tensorGradedDegree_pure {r : ℤ} (g : gradedHom L M r)
    (i j n ir q : ℤ) (h : i+j=n) (hi : i+r=ir) (e : n+r=q) (x : term L i) (y : B.complex.X j) :
    tensorGradedDegree T f g n q e (T.tmul f (N := regular B) i j n h x y) =
      T.tmul f (N := regular B) ir j q (by omega) (component g () i ir hi x) y := by
  simp only [tensorGradedDegree, ModuleTensor.tmul, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Tensor.map_first_graded_pure f (regular B) g i j n ir q h hi e x y]

include hf in
private def tensorGraded {r : ℤ} (g : gradedHom L M r) :
    gradedHom ((T.baseChange f).obj L) ((T.baseChange f).obj M) r :=
  ⟨fun _ => Cochain.mk fun n q e => ModuleCat.ofHom (tensorGradedDegree T f g n q e), by
    rintro ⟨⟩ ⟨⟩ n l p nr pr h e ep x z
    have eq : (tensorGradedDegree T f g p pr ep).comp ((act ((T.baseChange f).obj L) n l p h).flip z) =
        ((act ((T.baseChange f).obj M) nr l pr (by omega)).flip z).comp (tensorGradedDegree T f g n nr e) := by
      apply tensor_ext T
      intro i j hij y b
      simp only [LinearMap.comp_apply, LinearMap.flip_apply]
      rw [hf.action, tensorGradedDegree_pure T f g i (j+l) p (i+r) pr _ rfl ep,
        tensorGradedDegree_pure T f g i j n (i+r) nr hij rfl e, hf.action]
    exact LinearMap.congr_fun eq x⟩

private theorem tensorGraded_pure {r : ℤ} (g : gradedHom L M r)
    (i j n ir q : ℤ) (h : i+j=n) (hi : i+r=ir) (e : n+r=q) (x : term L i) (y : B.complex.X j) :
    component (tensorGraded T f hf g) () n q e (T.tmul f (N := regular B) i j n h x y) =
      T.tmul f (N := regular B) ir j q (by omega) (component g () i ir hi x) y :=
  tensorGradedDegree_pure T f g i j n ir q h hi e x y

private def extendGradedSplit {i : L ⟶ M} {p : M ⟶ N} (S : GradedSplit i p) :
    GradedSplit ((T.baseChange f).map i) ((T.baseChange f).map p) where
  zero := by
    apply RightDGModule.strict_ext
    rintro ⟨⟩ n
    apply LinearMap.congr_fun
    apply tensor_ext T
    intro a b h x y
    change ((((T.baseChange f).map p).app ()).f n)
      ((((T.baseChange f).map i).app ()).f n (T.tmul f (N := regular B) a b n h x y)) = 0
    rw [hf.first, hf.first, gradedSplit_zero_apply S]
    simp only [ModuleTensor.tmul, ← Tensor.pair_apply, map_zero, LinearMap.zero_apply]
  retraction := tensorGraded T f hf S.retraction
  sectionMap := tensorGraded T f hf S.sectionMap
  retract n x := by
    refine LinearMap.congr_fun (f := (component (tensorGraded T f hf S.retraction) () n n (add_zero n)).hom.comp
      (((T.baseChange f).map i).app () |>.f n).hom) (g := LinearMap.id) ?_ x
    apply tensor_ext T
    intro a b e y z
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [hf.first, tensorGraded_pure T f hf S.retraction a b n a n e (add_zero a) (add_zero n), S.retract]
  section_id n x := by
    refine LinearMap.congr_fun
      (f := (((T.baseChange f).map p).app () |>.f n).hom.comp
        (component (tensorGraded T f hf S.sectionMap) () n n (add_zero n)).hom)
      (g := LinearMap.id) ?_ x
    apply tensor_ext T
    intro a b e y z
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [tensorGraded_pure T f hf S.sectionMap a b n a n e (add_zero a) (add_zero n), hf.first, S.section_id]
  decompose n x := by
    refine LinearMap.congr_fun
      (f := (((T.baseChange f).map i).app () |>.f n).hom.comp
          (component (tensorGraded T f hf S.retraction) () n n (add_zero n)).hom +
        (component (tensorGraded T f hf S.sectionMap) () n n (add_zero n)).hom.comp
          (((T.baseChange f).map p).app () |>.f n).hom)
      (g := LinearMap.id) ?_ x
    apply tensor_ext T
    intro a b e y z
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [tensorGraded_pure T f hf S.retraction a b n a n e (add_zero a) (add_zero n), hf.first,
      hf.first, tensorGraded_pure T f hf S.sectionMap a b n a n e (add_zero a) (add_zero n)]
    change T.degree f M _ n _ + T.degree f M _ n _ = _
    rw [← map_add, ← Tensor.pure_add_left, S.decompose]

set_option maxHeartbeats 600000 in
theorem strictExtension_conditional
    (_ : Concatenation.{u,v}) (_ : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (_ : PushoutResolves.{u,v})
    (_ : ResolutionsExist.{u,v}) (_ : ResolvedTerms.{u,v}) : StrictExtension.{u,v} := by
  intro k _ _ T forms A B f L M N i p q S hq
  let hf := forms f (regular B)
  let D := scalarTensorModel T f hf
  obtain ⟨shiftIso, coneIso, _, hIncl, hProj, _, hPure⟩ :=
    DGBimodule.tensorComparisons.{u,v,0,0} (dgCat A) (dgCat B) (signedBimodule f (regular B)) D
  let F := T.baseChange f
  let S' := extendGradedSplit T f hf S
  let e : F.obj (cone i) ≅ cone (F.map i) := coneIso i
  let t : F.obj (shift L 1) ≅ shift (F.obj L) 1 := shiftIso L 1
  have hI : F.map (coneInclusion i) ≫ e.hom = coneInclusion (F.map i) := hIncl i
  have hP : F.map (coneProjection i) ≫ t.hom = e.hom ≫ coneProjection (F.map i) := hProj i
  refine ⟨e.symm, t, ⟨S'⟩, ?_, ?_, ?_⟩
  · have eq : F.map q = e.hom ≫ coneQuotient S' := by
      apply RightDGModule.strict_ext
      rintro ⟨⟩ n
      apply LinearMap.congr_fun
      apply tensor_ext T
      intro a b he x y
      change ((F.map q).app ()).f n (T.tmul f (N := regular B) a b n he x y) =
        ((F.map p).app ()).f n (((e.hom.app ()).f n (T.tmul f (N := regular B) a b n he x y))).1
      have hpure := hPure i () () a b n he x y
      change (e.hom.app ()).f n (T.tmul f (N := regular B) a b n he x y) =
        (T.tmul f (N := regular B) a b n he x.1 y,
          T.tmul f (N := regular B) (a+1) b (n+1) (by omega) x.2 y) at hpure
      rw [hpure, hf.first, hf.first, hq.1]
    change IsConeQuotient (F.map p) (e.inv ≫ F.map q)
    rw [eq, e.inv_hom_id_assoc]
    exact coneQuotient_quasiIso S'
  · change _ ≫ e.inv = _
    rw [← hI, Category.assoc, e.hom_inv_id, Category.comp_id]
  · change e.inv ≫ F.map (coneProjection i) ≫ t.hom = _
    rw [hP, e.inv_hom_id_assoc]

end TensorOfSequence


section Integration

open Specs.DerivedFormalization.Affine.PolynomialPath (ModulePathModel)
open Specs.DerivedFormalization.DG.HomComplex (component)
open Specs.DerivedFormalization.Affine.Tensor (term)
open private precomposeHomotopy precomposeHomotopy_equation
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {k : Type u} [Field k] [CharZero k] {E : CommDGAlgebra.{u,v} k}
variable {L M N L' M' N' : E.Module} {i : L ⟶ M} {p : M ⟶ N} {i' : L' ⟶ M'} {p' : M' ⟶ N'}
variable (WL : ModulePathModel L') (WM : ModulePathModel M') (WN : ModulePathModel N')
variable (l : L ⟶ WL.obj) (m : M ⟶ WM.obj) (r : N ⟶ WN.obj)

private def sequencePathEndpoint (hi : i ≫ m = l ≫ modulePathMap WL WM i')
    (hp : p ≫ r = m ≫ modulePathMap WM WN p') (c : k) : SequenceMap i p i' p' where
  left := l ≫ WL.evaluation c
  middle := m ≫ WM.evaluation c
  right := r ≫ WN.evaluation c
  incl_comm := by
    rw [← Category.assoc, hi, Category.assoc, modulePathMap_evaluation, Category.assoc]
  proj_comm := by
    rw [← Category.assoc, hp, Category.assoc, modulePathMap_evaluation, Category.assoc]

private def integrateSequencePath (hi : i ≫ m = l ≫ modulePathMap WL WM i')
    (hp : p ≫ r = m ≫ modulePathMap WM WN p') :
    SequenceHomotopy (sequencePathEndpoint WL WM WN l m r hi hp 1)
      (sequencePathEndpoint WL WM WN l m r hi hp 0) where
  left := precomposeHomotopy l WL.homotopy
  middle := precomposeHomotopy m WM.homotopy
  right := precomposeHomotopy r WN.homotopy
  left_eq := precomposeHomotopy_equation l _ _ _ WL.endpoints_homotopic
  middle_eq := precomposeHomotopy_equation m _ _ _ WM.endpoints_homotopic
  right_eq := precomposeHomotopy_equation r _ _ _ WN.endpoints_homotopic
  incl_comm := by
    intro n q e x
    have hh := congrArg (fun a : L ⟶ WM.obj => (a.app ()).f n x) hi
    change (m.app ()).f n ((i.app ()).f n x) =
      ((modulePathMap WL WM i').app ()).f n ((l.app ()).f n x) at hh
    change component WM.homotopy () n q e ((m.app ()).f n ((i.app ()).f n x)) =
      (i'.app ()).f q (component WL.homotopy () n q e ((l.app ()).f n x))
    rw [hh, modulePathMap_integral]
  proj_comm := by
    intro n q e x
    have hh := congrArg (fun a : M ⟶ WN.obj => (a.app ()).f n x) hp
    change (r.app ()).f n ((p.app ()).f n x) =
      ((modulePathMap WM WN p').app ()).f n ((m.app ()).f n x) at hh
    change component WN.homotopy () n q e ((r.app ()).f n ((p.app ()).f n x)) =
      (p'.app ()).f q (component WM.homotopy () n q e ((m.app ()).f n x))
    rw [hh, modulePathMap_integral]

end Integration


section Coefficients

open PolynomialPath
open Specs.DerivedFormalization.Affine.PolynomialPath (mapCoefficients RelativePathModel)
open private includedPath includedPath_relative from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {k : Type u} [Field k] [CharZero k]
variable {P B C : NonpositiveCDGA.{u,v} k}

/-- Extending the augmentation leaves the polynomial in the resolution unchanged. -/
private theorem relativePath_over_composite (p : P ⟶ B) (g : B ⟶ C) :
    ∃ j : (relativePathModel p).truncated ⟶ (relativePathModel (p ≫ g)).truncated,
      (∀ (i : ℤ) (x : (relativePathModel p).truncated.complex.X i),
        (relativePathInclusion (p ≫ g) ≫ relativeInclusion (p ≫ g)).chainMap.f i (j.chainMap.f i x) =
        (relativePathInclusion p ≫ relativeInclusion p).chainMap.f i x) ∧
      ∀ c, j ≫ evaluation (p ≫ g) c = evaluation p c := by
  obtain ⟨j,hj,he⟩ := relative_path_change p (p ≫ g) (𝟙 P) g (Category.id_comp _)
  refine ⟨j, ?_, fun c => (he c).trans (Category.comp_id _)⟩
  intro i x
  let z : Specs.DerivedFormalization.Affine.PolynomialPath.term P.complex i :=
    (relativePathInclusion p ≫ relativeInclusion p).chainMap.f i x
  have h := CategoryTheory.congr_fun (congrArg (fun m => m.chainMap.f i) hj) x
  change (relativePathInclusion (p ≫ g) ≫ relativeInclusion (p ≫ g)).chainMap.f i
    (j.chainMap.f i x) = mapDegree (𝟙 P.complex) i z at h
  refine h.trans ?_
  change mapDegree (𝟙 P.complex) i z = z
  exact (mapDegree_coordinates (𝟙 P.complex) i z.1 z.2).trans (by
    simp only [HomologicalComplex.id_f, ModuleCat.hom_id, mapCoefficients_id_apply, Prod.mk.eta])

private theorem extendPath_coordinates (p : P ⟶ B) (g : B ⟶ C)
    (j : (relativePathModel p).truncated ⟶ (relativePathModel (p ≫ g)).truncated)
    (hj : ∀ (i : ℤ) (x : (relativePathModel p).truncated.complex.X i),
      (relativePathInclusion (p ≫ g) ≫ relativeInclusion (p ≫ g)).chainMap.f i (j.chainMap.f i x) =
      (relativePathInclusion p ≫ relativeInclusion p).chainMap.f i x)
    {D : NonpositiveCDGA.{u,v} k} (H : D ⟶ (relativePathModel p).truncated)
    (i : ℤ) (x : D.complex.X i) :
    (algebraPathModel P.toCommDGAlgebra).coordinates i
        ((includedPath (p ≫ g) (relativePathModel (p ≫ g)) (H ≫ j)).chainMap.f i x) =
      (algebraPathModel P.toCommDGAlgebra).coordinates i
        ((includedPath p (relativePathModel p) H).chainMap.f i x) :=
  hj i (H.chainMap.f i x)

variable {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}
variable {f : ChainMap X Y} {l₀ l₁ : Lift f R S}

/-- The common-coefficient path on Q restricts to the chosen polynomial on P. -/
private theorem compatiblePath_coefficients
    (H : Paths l₀ l₁ (relativePathModel S.P.augmentation) (relativePathModel S.Q.augmentation))
    (i : ℤ) (x : R.P.algebra.complex.X i) :
    let z := (algebraPathModel S.P.algebra.toCommDGAlgebra).coordinates i
      ((includedPath S.P.augmentation (relativePathModel S.P.augmentation) H.p).chainMap.f i x)
    (algebraPathModel S.Q.algebra.toCommDGAlgebra).coordinates i
      ((includedPath S.Q.augmentation (relativePathModel S.Q.augmentation) H.q).chainMap.f i
        (R.Q.base.chainMap.f i x)) =
      (mapCoefficients (S.Q.base.chainMap.f i).hom z.1,
        mapCoefficients (S.Q.base.chainMap.f (i-1)).hom z.2) := by
  have eq := CategoryTheory.congr_fun (congrArg (fun g : R.P.algebra ⟶
    (relativePathModel S.Q.augmentation).truncated => g.chainMap.f i) H.q_base) x
  change H.q.chainMap.f i (R.Q.base.chainMap.f i x) = H.changePath.chainMap.f i (H.p.chainMap.f i x) at eq
  exact (congrArg (fun y => (algebraPathModel S.Q.algebra.toCommDGAlgebra).coordinates i
    (((relativePathModel S.Q.augmentation).includeTruncation ≫
      (relativePathModel S.Q.augmentation).includeRelative).chainMap.f i y)) eq).trans
    (H.change_coordinates i (H.p.chainMap.f i x))

end Coefficients


section StrictComparisons

open CochainComplex.HomComplex (Cochain)
open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor act term regular restrict)
open Specs.DerivedFormalization.Affine.RelativePathComparison (baseChangedSymbol)
open Kahler (DifferentialModel IsDerivation value)
open private baseChangedSymbol_d baseChangedSymbol_mul representStrict scalarExtend scalarExtend_pure
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {k : Type u} [Field k] [CharZero k]
variable {A P A' Q E : CommDGAlgebra.{u,v} k}

private theorem symbol_of_base {a : A ⟶ P} (O : DifferentialModel a)
    (T : ModuleTensor.{u,v} k) (p : P ⟶ E) (n : ℤ) (x : A.complex.X n) :
    baseChangedSymbol T p O n (a.chainMap.f n x) = 0 := by
  change T.tmul p (N := regular E) n 0 n (add_zero n)
    (value O.symbol n n (add_zero n) (a.chainMap.f n x)) E.one = _
  rw [O.symbol.property.relative]
  simp only [ModuleTensor.tmul, ← Tensor.pair_apply, map_zero, LinearMap.zero_apply]

private theorem scalarDifferentialMap
    (T : ModuleTensor.{u,v} k) (forms : TensorFormulas T)
    {a : A ⟶ P} {a' : A' ⟶ Q} (O : DifferentialModel a) (O' : DifferentialModel a')
    (p : P ⟶ E) (q : Q ⟶ E) (f : P ⟶ Q) (g : A ⟶ A')
    (hbase : a ≫ f = g ≫ a') (hAug : f ≫ q = p) :
    ∃ m : (T.baseChange p).obj O.module ⟶ (T.baseChange q).obj O'.module,
      ∀ n x, (m.app ()).f n (baseChangedSymbol T p O n x) =
        baseChangedSymbol T q O' n (f.chainMap.f n x) := by
  let N := (T.baseChange q).obj O'.module
  let D : Q.complex ⟶ N.complex () :=
    CochainComplex.ofHom (fun n => ModuleCat.ofHom (baseChangedSymbol T q O' n))
      (fun n => ModuleCat.hom_ext (LinearMap.ext
        (baseChangedSymbol_d T O' (forms q (regular E)) n)))
  have hfD : IsDerivation a (M := restrict p N) (Cochain.ofHom (f.chainMap ≫ D)) := by
    constructor
    · intro i j e x
      have h : i = j := by omega
      cases h
      rw [Cochain.ofHom_v]
      change baseChangedSymbol T q O' i (f.chainMap.f i (a.chainMap.f i x)) = 0
      have he := CategoryTheory.congr_fun (congrArg (fun l : A ⟶ Q => l.chainMap.f i) hbase) x
      change f.chainMap.f i (a.chainMap.f i x) = a'.chainMap.f i (g.chainMap.f i x) at he
      rw [he, symbol_of_base]
    · intro i j n ir jr nr e hi hj hn x y
      have ei : i = ir := by omega
      have ej : j = jr := by omega
      have en : n = nr := by omega
      cases ei
      cases ej
      cases en
      simp only [Cochain.ofHom_v]
      change baseChangedSymbol T q O' n (f.chainMap.f n (P.mul i j n e x y)) =
        act N i j n e (baseChangedSymbol T q O' i (f.chainMap.f i x)) (p.chainMap.f j y) +
        (i*j).negOnePow •
          act N j i n (by omega) (baseChangedSymbol T q O' j (f.chainMap.f j y)) (p.chainMap.f i x)
      have aug (d : ℤ) (z : P.complex.X d) :
          q.chainMap.f d (f.chainMap.f d z) = p.chainMap.f d z :=
        CategoryTheory.congr_fun (congrArg (fun l : P ⟶ E => l.chainMap.f d) hAug) z
      rw [f.map_mul, baseChangedSymbol_mul T O' (forms q (regular E)), aug, aug]
  obtain ⟨m, hm⟩ := representStrict O (restrict p N) (f.chainMap ≫ D) hfD
  let m' := scalarExtend T (forms p (regular E)) m
  refine ⟨m', fun n x => ?_⟩
  change (m'.app ()).f n (T.tmul p (N := regular E) n 0 n (add_zero n)
    (value O.symbol n n (add_zero n) x) E.one) = _
  rw [scalarExtend_pure, N.act_id, hm]
  rfl

variable {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}
variable {D : NonpositiveCDGA.{u,v} k}

private abbrev leftAug (R : Resolution X) (e : X.C ⟶ D) : R.P.algebra ⟶ D :=
  R.Q.base ≫ R.Q.augmentation ≫ e

private theorem leftAt_assoc (T : ModuleTensor.{u,v} k) (cmp : T.Comparisons)
    (R : Resolution X) (e : X.C ⟶ D) :
    ∃ a : (extend T (R.Q.augmentation ≫ e)).obj ((extend T R.Q.base).obj R.P.differentials.module)
        ≅ (extend T (leftAug R e)).obj R.P.differentials.module,
      ∀ n x, (a.hom.app ()).f n (leftSymbol T R e n x) =
        baseChangedSymbol T (underlying (leftAug R e)) R.P.differentials n x := by
  obtain ⟨a, ha⟩ := cmp.compose (underlying R.Q.base) (underlying (R.Q.augmentation ≫ e))
    R.P.differentials.module
  refine ⟨a, fun n x => ?_⟩
  have h := ha n 0 0 n n (add_zero n) (add_zero n) (symbol R.P.differentials n x)
    R.Q.algebra.one D.one
  change (a.hom.app ()).f n (leftSymbol T R e n x) =
    T.tmul (underlying (leftAug R e)) (N := regular D.toCommDGAlgebra) n 0 n (add_zero n)
      (symbol R.P.differentials n x)
      (D.mul 0 0 0 rfl ((R.Q.augmentation ≫ e).chainMap.f 0 R.Q.algebra.one) D.one) at h
  rw [(R.Q.augmentation ≫ e).map_one, D.toDGAlgebra.id_comp] at h
  exact h

private theorem leftAt_assoc_inv
    (T : ModuleTensor.{u,v} k) (R : Resolution X) (e : X.C ⟶ D)
    (a : (extend T (R.Q.augmentation ≫ e)).obj ((extend T R.Q.base).obj R.P.differentials.module)
        ≅ (extend T (leftAug R e)).obj R.P.differentials.module)
    (ha : ∀ n x, (a.hom.app ()).f n (leftSymbol T R e n x) =
        baseChangedSymbol T (underlying (leftAug R e)) R.P.differentials n x)
    (n : ℤ) (x : R.P.algebra.complex.X n) :
    (a.inv.app ()).f n (baseChangedSymbol T (underlying (leftAug R e)) R.P.differentials n x) =
      leftSymbol T R e n x := by
  rw [← ha]
  exact congrArg (fun t => (t.app ()).f n (leftSymbol T R e n x)) a.hom_inv_id

set_option maxHeartbeats 650000 in
private theorem strictInducedMap (T : ModuleTensor.{u,v} k) (forms : TensorFormulas T) (cmp : T.Comparisons)
    {f : ChainMap X Y} (l : Lift f R S) (F : Sequence T R) (G : Sequence T S)
    (e : X.C ⟶ D) (d : Y.C ⟶ D) (h : e = f.c ≫ d) : ∃ m : MapAt F G e d, Induces l m := by
  have hq : l.q ≫ S.Q.augmentation ≫ d = R.Q.augmentation ≫ e := by
    rw [← Category.assoc, l.q_aug, Category.assoc, ← h]
  have hp : l.p ≫ leftAug S d = leftAug R e := by
    rw [leftAug, leftAug, ← Category.assoc, ← l.q_base, Category.assoc, hq]
  have hbase : (R.P.base ≫ R.Q.base) ≫ l.q = f.a ≫ (S.P.base ≫ S.Q.base) := by
    rw [Category.assoc, l.q_base, ← Category.assoc, l.p_base, Category.assoc]
  obtain ⟨a, ha⟩ := leftAt_assoc T cmp R e
  obtain ⟨a', ha'⟩ := leftAt_assoc T cmp S d
  obtain ⟨b, hb⟩ := scalarDifferentialMap T forms R.P.differentials S.P.differentials
    (underlying (leftAug R e)) (underlying (leftAug S d)) (underlying l.p) (underlying f.a) l.p_base hp
  let left := a.hom ≫ b ≫ a'.inv
  have hL (n : ℤ) (x : R.P.algebra.complex.X n) :
      (left.app ()).f n (leftSymbol T R e n x) = leftSymbol T S d n (l.p.chainMap.f n x) := by
    change (a'.inv.app ()).f n ((b.app ()).f n ((a.hom.app ()).f n (leftSymbol T R e n x))) = _
    rw [ha, hb, leftAt_assoc_inv T S d a' ha']
  obtain ⟨m, hM⟩ := scalarDifferentialMap T forms R.absolute S.absolute
    (underlying (R.Q.augmentation ≫ e)) (underlying (S.Q.augmentation ≫ d))
    (underlying l.q) (underlying f.a) hbase hq
  obtain ⟨r, hR⟩ := scalarDifferentialMap T forms R.Q.differentials S.Q.differentials
    (underlying (R.Q.augmentation ≫ e)) (underlying (S.Q.augmentation ≫ d))
    (underlying l.q) (underlying l.p) l.q_base hq
  have hm (n : ℤ) (x : R.Q.algebra.complex.X n) :
    (m.app ()).f n (middleSymbol T R e n x) = middleSymbol T S d n (l.q.chainMap.f n x) := hM n x
  have hr (n : ℤ) (x : R.Q.algebra.complex.X n) :
    (r.app ()).f n (rightSymbol T R e n x) = rightSymbol T S d n (l.q.chainMap.f n x) := hR n x
  refine ⟨⟨left, m, r, ?_, ?_⟩, hL, hm, hr⟩
  · apply differentialDoubleScalarMap_ext T forms _ _ _ R.P.differentials
    intro n x
    change (m.app ()).f n (((inclusionAt F e).app ()).f n (leftSymbol T R e n x)) =
      ((inclusionAt G d).app ()).f n ((left.app ()).f n (leftSymbol T R e n x))
    rw [inclusionAt_symbol T forms, hm, hL, inclusionAt_symbol T forms]
    exact congrArg (middleSymbol T S d n) (CategoryTheory.congr_fun
      (congrArg (fun j : R.P.algebra ⟶ S.Q.algebra => j.chainMap.f n) l.q_base) x)
  · apply differentialScalarMap_ext T forms _ _ R.absolute
    intro n x
    change (r.app ()).f n (((projectionAt F e).app ()).f n (middleSymbol T R e n x)) =
      ((projectionAt G d).app ()).f n ((m.app ()).f n (middleSymbol T R e n x))
    rw [projectionAt_symbol T forms, hr, hm, projectionAt_symbol T forms]

theorem strictSequenceComparisons_conditional
    (_ : Concatenation.{u,v}) (_ : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (_ : PushoutResolves.{u,v})
    (_ : ResolutionsExist.{u,v}) (_ : ResolvedTerms.{u,v}) : StrictSequenceComparisons.{u,v} := by
  classical
  intro k _ _ T forms cmp E
  let map := fun {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}
    {f : ChainMap X Y} (l : Lift f R S) (F : Sequence T R) (G : Sequence T S)
    (e : X.C ⟶ E) (d : Y.C ⟶ E) (h : e = f.c ≫ d) =>
      Classical.choose (strictInducedMap T forms cmp l F G e d h)
  have hi {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}
    {f : ChainMap X Y} (l : Lift f R S) (F : Sequence T R) (G : Sequence T S)
    (e : X.C ⟶ E) (d : Y.C ⟶ E) (h : e = f.c ≫ d) : Induces l (map l F G e d h) :=
      Classical.choose_spec (strictInducedMap T forms cmp l F G e d h)
  refine ⟨⟨map, hi, ?_, ?_⟩⟩
  · intro X R F e
    exact inducedMap_unique T forms (hi _ _ _ _ _ (Category.id_comp e).symm) (inducedMap_id T F e)
  · intro X Y Z R S V f g l r F G H e d c hf hg
    have hfg : e = (f.comp g).c ≫ c := by
      rw [hf, hg]
      exact (Category.assoc _ _ _).symm
    exact inducedMap_unique T forms (hi _ _ _ _ _ hfg)
      (inducedMap_comp T (hi _ _ _ _ _ hf) (hi _ _ _ _ _ hg))

end StrictComparisons

section ComparisonHomotopies

open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor regular)
open Specs.DerivedFormalization.Affine.RelativePathComparison (baseChangedSymbol)
open Specs.DerivedFormalization.Affine.PolynomialPath (mapCoefficients)
open PolynomialPath
open private includedPath includedPath_relative from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {k : Type u} [Field k] [CharZero k]
variable {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}
variable {f : ChainMap X Y} {l₀ l₁ : Lift f R S} {E : NonpositiveCDGA.{u,v} k}

private theorem pathCoefficients_of_single
    {A P E : NonpositiveCDGA.{u,v} k} {a : A ⟶ P} (p : P ⟶ E)
    (T : ModuleTensor.{u,v} k) (O : Differentials a) (i : ℤ) (x : A.complex.X i) :
    (mapCoefficients (baseChangedSymbol T (underlying p) O i)
        (Finsupp.single 0 (a.chainMap.f i x)),
      mapCoefficients (baseChangedSymbol T (underlying p) O (i-1)) 0) = 0 := by
  rw [mapCoefficients_single, symbol_of_base, Finsupp.single_zero, map_zero]
  rfl

private theorem pathCoefficients_of_base
    {A P E : NonpositiveCDGA.{u,v} k} {a : A ⟶ P} (p : P ⟶ E)
    (T : ModuleTensor.{u,v} k) (O : Differentials a) (i : ℤ)
    (z : Specs.DerivedFormalization.Affine.PolynomialPath.term A.complex i) :
    (mapCoefficients (baseChangedSymbol T (underlying p) O i)
        (mapCoefficients (a.chainMap.f i).hom z.1),
      mapCoefficients (baseChangedSymbol T (underlying p) O (i-1))
        (mapCoefficients (a.chainMap.f (i-1)).hom z.2)) = 0 := by
  have h (j : ℤ) :
      (baseChangedSymbol T (underlying p) O j).comp (a.chainMap.f j).hom = 0 :=
    LinearMap.ext (symbol_of_base O T (underlying p) j)
  rw [mapCoefficients_comp_apply, mapCoefficients_comp_apply, h, h,
    mapCoefficients_zero_apply, mapCoefficients_zero_apply]
  rfl

set_option maxHeartbeats 1800000 in
private theorem compatibleCotangentHomotopy (T : ModuleTensor.{u,v} k)
    (forms : TensorFormulas T) (cmp : T.Comparisons)
    (F : Sequence T R) (G : Sequence T S) (e : X.C ⟶ E) (d : Y.C ⟶ E)
    (h : e = f.c ≫ d) (H : Paths l₀ l₁ (relativePathModel S.P.augmentation)
      (relativePathModel S.Q.augmentation)) :
    ∃ (m₀ m₁ : MapAt F G e d), Induces l₀ m₀ ∧ Induces l₁ m₁ ∧ Nonempty (SequenceHomotopy m₁ m₀) := by
  let q₀ := R.Q.augmentation ≫ e
  let q₁ := S.Q.augmentation ≫ d
  let p₀ := R.P.augmentation ≫ X.second ≫ e
  let p₁ := S.P.augmentation ≫ Y.second ≫ d
  have p₀eq : p₀ = leftAug R e :=
    (Category.assoc R.P.augmentation X.second e).symm.trans
      ((congrArg (fun j : R.P.algebra ⟶ X.C => j ≫ e) R.Q.triangle.symm).trans
        (Category.assoc R.Q.base R.Q.augmentation e))
  have p₁eq : p₁ = leftAug S d :=
    (Category.assoc S.P.augmentation Y.second d).symm.trans
      ((congrArg (fun j : S.P.algebra ⟶ Y.C => j ≫ d) S.Q.triangle.symm).trans
        (Category.assoc S.Q.base S.Q.augmentation d))
  let Jp := relativePathModel p₁
  let Jq := relativePathModel q₁
  obtain ⟨jp, hjp, hjpe⟩ := relativePath_over_composite S.P.augmentation (Y.second ≫ d)
  obtain ⟨jq, hjq, hjqe⟩ := relativePath_over_composite S.Q.augmentation d
  let Hp : R.P.algebra ⟶ Jp.truncated := H.p ≫ jp
  let Hq : R.Q.algebra ⟶ Jq.truncated := H.q ≫ jq
  have Hp_end (i : Bool) :
      Hp ≫ Jp.endpoints ≫ (if i then Jp.second else Jp.first) = (if i then l₁.p else l₀.p) := by
    cases i
    · calc
        _ = Hp ≫ PolynomialPath.evaluation p₁ 0 :=
          congrArg (fun t => Hp ≫ t) (endpoints_first p₁)
        _ = H.p ≫ PolynomialPath.evaluation S.P.augmentation 0 :=
          (Category.assoc H.p jp (PolynomialPath.evaluation p₁ 0)).trans
            (congrArg (fun t => H.p ≫ t) (hjpe 0))
        _ = _ := (congrArg (fun t => H.p ≫ t)
          (endpoints_first S.P.augmentation).symm).trans H.p_zero
    · calc
        _ = Hp ≫ PolynomialPath.evaluation p₁ 1 :=
          congrArg (fun t => Hp ≫ t) (endpoints_second p₁)
        _ = H.p ≫ PolynomialPath.evaluation S.P.augmentation 1 :=
          (Category.assoc H.p jp (PolynomialPath.evaluation p₁ 1)).trans
            (congrArg (fun t => H.p ≫ t) (hjpe 1))
        _ = _ := (congrArg (fun t => H.p ≫ t)
          (endpoints_second S.P.augmentation).symm).trans H.p_one
  have Hq_end (i : Bool) :
      Hq ≫ Jq.endpoints ≫ (if i then Jq.second else Jq.first) = (if i then l₁.q else l₀.q) := by
    cases i
    · calc
        _ = Hq ≫ PolynomialPath.evaluation q₁ 0 :=
          congrArg (fun t => Hq ≫ t) (endpoints_first q₁)
        _ = H.q ≫ PolynomialPath.evaluation S.Q.augmentation 0 :=
          (Category.assoc H.q jq (PolynomialPath.evaluation q₁ 0)).trans
            (congrArg (fun t => H.q ≫ t) (hjqe 0))
        _ = _ := (congrArg (fun t => H.q ≫ t)
          (endpoints_first S.Q.augmentation).symm).trans H.q_zero
    · calc
        _ = Hq ≫ PolynomialPath.evaluation q₁ 1 :=
          congrArg (fun t => Hq ≫ t) (endpoints_second q₁)
        _ = H.q ≫ PolynomialPath.evaluation S.Q.augmentation 1 :=
          (Category.assoc H.q jq (PolynomialPath.evaluation q₁ 1)).trans
            (congrArg (fun t => H.q ≫ t) (hjqe 1))
        _ = _ := (congrArg (fun t => H.q ≫ t)
          (endpoints_second S.Q.augmentation).symm).trans H.q_one
  have pAug : Hp ≫ Jp.endpoints ≫ Jp.first ≫ p₁ = p₀ := by
    have ep := Hp_end false
    change Hp ≫ Jp.endpoints ≫ Jp.first = l₀.p at ep
    rw [← Category.assoc _ _ p₁, ← Category.assoc _ _ p₁, ep]
    change l₀.p ≫ S.P.augmentation ≫ Y.second ≫ d = R.P.augmentation ≫ X.second ≫ e
    rw [← Category.assoc, l₀.p_aug, Category.assoc, ← Category.assoc _ _ d, ← f.second_comm,
      Category.assoc, ← h]
  have qAug : Hq ≫ Jq.endpoints ≫ Jq.first ≫ q₁ = q₀ := by
    have eq := Hq_end false
    change Hq ≫ Jq.endpoints ≫ Jq.first = l₀.q at eq
    rw [← Category.assoc _ _ q₁, ← Category.assoc _ _ q₁, eq]
    change l₀.q ≫ S.Q.augmentation ≫ d = R.Q.augmentation ≫ e
    rw [← Category.assoc, l₀.q_aug, Category.assoc, ← h]
  let zp (i : ℤ) (x : R.P.algebra.complex.X i) :=
    (algebraPathModel S.P.algebra.toCommDGAlgebra).coordinates i
      ((includedPath p₁ Jp Hp).chainMap.f i x)
  let zq (i : ℤ) (x : R.Q.algebra.complex.X i) :=
    (algebraPathModel S.Q.algebra.toCommDGAlgebra).coordinates i
      ((includedPath q₁ Jq Hq).chainMap.f i x)
  have pBase (i : ℤ) (x : X.A.complex.X i) :
    zp i (R.P.base.chainMap.f i x) =
      (Finsupp.single 0 (S.P.base.chainMap.f i (f.a.chainMap.f i x)), 0) :=
    (extendPath_coordinates S.P.augmentation (Y.second ≫ d) jp hjp H.p i _).trans
      (includedPath_relative f.a R.P.base S.P.base S.P.augmentation _ H.p H.p_base i x)
  have pqBase (i : ℤ) (x : R.P.algebra.complex.X i) :
    zq i (R.Q.base.chainMap.f i x) =
      (mapCoefficients (S.Q.base.chainMap.f i).hom (zp i x).1,
        mapCoefficients (S.Q.base.chainMap.f (i-1)).hom (zp i x).2) := by
    have eqp := extendPath_coordinates S.P.augmentation (Y.second ≫ d) jp hjp H.p i x
    have eqq := extendPath_coordinates S.Q.augmentation d jq hjq H.q i (R.Q.base.chainMap.f i x)
    change zp i x = _ at eqp
    change zq i (R.Q.base.chainMap.f i x) = _ at eqq
    rw [eqp, eqq]
    exact compatiblePath_coefficients H i x
  have qBase (i : ℤ) (x : X.A.complex.X i) :
    zq i ((R.P.base ≫ R.Q.base).chainMap.f i x) =
      (Finsupp.single 0 ((S.P.base ≫ S.Q.base).chainMap.f i (f.a.chainMap.f i x)), 0) := by
    change zq i (R.Q.base.chainMap.f i (R.P.base.chainMap.f i x)) = _
    rw [pqBase, pBase, mapCoefficients_single, map_zero]
    rfl
  obtain ⟨a, ha⟩ := leftAt_assoc T cmp R e
  obtain ⟨a', ha'⟩ := leftAt_assoc T cmp S d
  -- Use the direct extension model for differentiating the P-path.
  let a₀ := a ≪≫ eqToIso (congrArg (fun p : R.P.algebra ⟶ E =>
    (extend T p).obj R.P.differentials.module) p₀eq.symm)
  let a₁ := a' ≪≫ eqToIso (congrArg (fun p : S.P.algebra ⟶ E =>
    (extend T p).obj S.P.differentials.module) p₁eq.symm)
  have ha₀ (i : ℤ) (x : R.P.algebra.complex.X i) :
      (a₀.hom.app ()).f i (leftSymbol T R e i x) =
        baseChangedSymbol T (underlying p₀) R.P.differentials i x := by
    dsimp only [a₀, Iso.trans_hom]
    generalize p₀ = p at p₀eq ⊢
    cases p₀eq
    exact ha i x
  have ha₁ (i : ℤ) (x : S.P.algebra.complex.X i) :
      (a₁.hom.app ()).f i (leftSymbol T S d i x) =
        baseChangedSymbol T (underlying p₁) S.P.differentials i x := by
    dsimp only [a₁, Iso.trans_hom]
    generalize p₁ = p at p₁eq ⊢
    cases p₁eq
    exact ha' i x
  let Wp := modulePathModel ((extend T p₁).obj S.P.differentials.module)
  let Wm := modulePathModel ((extend T q₁).obj S.absolute.module)
  let Wr := modulePathModel ((extend T q₁).obj S.Q.differentials.module)
  let Wl := modulePathModel ((extend T q₁).obj ((extend T S.Q.base).obj S.P.differentials.module))
  obtain ⟨lp, hlp, ep, _⟩ := derivative_path_killing_base Jp Hp pAug T forms
    R.P.differentials S.P.differentials Wp (by
      intro i x
      change (mapCoefficients _ (zp i (R.P.base.chainMap.f i x)).1,
        mapCoefficients _ (zp i (R.P.base.chainMap.f i x)).2) = 0
      rw [pBase]
      exact pathCoefficients_of_single p₁ T S.P.differentials i (f.a.chainMap.f i x))
  obtain ⟨m, hm, em, _⟩ := derivative_path_killing_base Jq Hq qAug T forms
    R.absolute S.absolute Wm (by
      intro i x
      change (mapCoefficients _ (zq i ((R.P.base ≫ R.Q.base).chainMap.f i x)).1,
        mapCoefficients _ (zq i ((R.P.base ≫ R.Q.base).chainMap.f i x)).2) = 0
      rw [qBase]
      exact pathCoefficients_of_single q₁ T S.absolute i (f.a.chainMap.f i x))
  obtain ⟨r, hr, er, _⟩ := derivative_path_killing_base Jq Hq qAug T forms
    R.Q.differentials S.Q.differentials Wr (by
      intro i x
      change (mapCoefficients _ (zq i (R.Q.base.chainMap.f i x)).1,
        mapCoefficients _ (zq i (R.Q.base.chainMap.f i x)).2) = 0
      rw [pqBase]
      exact pathCoefficients_of_base q₁ T S.Q.differentials i (zp i x))
  let l := a₀.hom ≫ lp ≫ modulePathMap Wp Wl a₁.inv
  have left_inv (i : ℤ) (x : S.P.algebra.complex.X i) :
      (a₁.inv.app ()).f i (baseChangedSymbol T (underlying p₁) S.P.differentials i x) =
        leftSymbol T S d i x := by
    rw [← ha₁]
    exact congrArg (fun t => (t.app ()).f i (leftSymbol T S d i x)) a₁.hom_inv_id
  have hi : inclusionAt F e ≫ m = l ≫ modulePathMap Wl Wm (inclusionAt G d) := by
    apply differentialDoubleScalarMap_ext T forms _ _ _ R.P.differentials
    intro i x
    apply (Wm.coordinates i).injective
    change Wm.coordinates i ((m.app ()).f i (((inclusionAt F e).app ()).f i (leftSymbol T R e i x))) =
      Wm.coordinates i (((modulePathMap Wl Wm (inclusionAt G d)).app ()).f i
        (((modulePathMap Wp Wl a₁.inv).app ()).f i ((lp.app ()).f i
          ((a₀.hom.app ()).f i (leftSymbol T R e i x)))))
    rw [inclusionAt_symbol T forms, modulePathMap_coordinates, modulePathMap_coordinates, ha₀]
    change Wm.coordinates i ((m.app ()).f i (baseChangedSymbol T (underlying q₀)
      R.absolute i (R.Q.base.chainMap.f i x))) = _
    rw [hm, hlp]
    change (mapCoefficients _ (zq i (R.Q.base.chainMap.f i x)).1,
      mapCoefficients _ (zq i (R.Q.base.chainMap.f i x)).2) = _
    rw [pqBase, mapDegree_apply, mapDegree_apply]
    simp only [mapCoefficients_comp_apply]
    have eq (j : ℤ) :
        ((baseChangedSymbol T (underlying q₁) S.absolute j).comp (S.Q.base.chainMap.f j).hom) =
        (((inclusionAt G d).app ()).f j).hom.comp
          (((a₁.inv.app ()).f j).hom.comp (baseChangedSymbol T (underlying p₁) S.P.differentials j)) := by
      apply LinearMap.ext
      intro y
      simp only [LinearMap.comp_apply]
      rw [left_inv, inclusionAt_symbol T forms]
      rfl
    rw [eq, eq]
  have hj : projectionAt F e ≫ r = m ≫ modulePathMap Wm Wr (projectionAt G d) := by
    apply differentialScalarMap_ext T forms _ _ R.absolute
    intro i x
    apply (Wr.coordinates i).injective
    change Wr.coordinates i ((r.app ()).f i (((projectionAt F e).app ()).f i (middleSymbol T R e i x))) =
      Wr.coordinates i (((modulePathMap Wm Wr (projectionAt G d)).app ()).f i
        ((m.app ()).f i (middleSymbol T R e i x)))
    rw [projectionAt_symbol T forms, modulePathMap_coordinates]
    change Wr.coordinates i ((r.app ()).f i (baseChangedSymbol T (underlying q₀) R.Q.differentials i x)) =
      mapDegree _ i (Wm.coordinates i ((m.app ()).f i (baseChangedSymbol T (underlying q₀) R.absolute i x)))
    rw [hr, hm, mapDegree_apply]
    simp only [mapCoefficients_comp_apply]
    have eq (j : ℤ) :
        baseChangedSymbol T (underlying q₁) S.Q.differentials j =
        (((projectionAt G d).app ()).f j).hom.comp
          (baseChangedSymbol T (underlying q₁) S.absolute j) :=
      LinearMap.ext (fun y => (projectionAt_symbol T forms G d j y).symm)
    rw [← eq, ← eq]
  let comparisonAt := sequencePathEndpoint Wl Wm Wr l m r hi hj
  have liftAt (b : Bool) (c : k) (hc : c = if b then 1 else 0) :
      Induces (if b then l₁ else l₀) (comparisonAt c) := by
    have p_end : (((if b then l₁ else l₀) : Lift f R S).p =
          Hp ≫ Jp.endpoints ≫ Jp.first ∧ c = 0) ∨
        (((if b then l₁ else l₀) : Lift f R S).p =
          Hp ≫ Jp.endpoints ≫ Jp.second ∧ c = 1) := by
      cases b
      · exact Or.inl ⟨(Hp_end false).symm, hc⟩
      · exact Or.inr ⟨(Hp_end true).symm, hc⟩
    have q_end : (((if b then l₁ else l₀) : Lift f R S).q =
          Hq ≫ Jq.endpoints ≫ Jq.first ∧ c = 0) ∨
        (((if b then l₁ else l₀) : Lift f R S).q =
          Hq ≫ Jq.endpoints ≫ Jq.second ∧ c = 1) := by
      cases b
      · exact Or.inl ⟨(Hq_end false).symm, hc⟩
      · exact Or.inr ⟨(Hq_end true).symm, hc⟩
    refine ⟨?_, em _ _ q_end, er _ _ q_end⟩
    intro i x
    have eeval : (comparisonAt c).left = a₀.hom ≫ (lp ≫ Wp.evaluation c) ≫ a₁.inv := by
      change (a₀.hom ≫ lp ≫ modulePathMap Wp Wl a₁.inv) ≫ Wl.evaluation c = _
      simp only [Category.assoc, modulePathMap_evaluation]
    rw [eeval]
    change (a₁.inv.app ()).f i ((((lp ≫ Wp.evaluation c).app ()).f i)
        ((a₀.hom.app ()).f i (leftSymbol T R e i x))) = _
    rw [ha₀, ep _ _ p_end, left_inv]
  exact ⟨comparisonAt 0, comparisonAt 1, liftAt false 0 rfl, liftAt true 1 rfl,
    ⟨integrateSequencePath Wl Wm Wr l m r hi hj⟩⟩

theorem sequenceComparisons_conditional
    (_ : Concatenation.{u,v}) (_ : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (_ : PushoutResolves.{u,v})
    (_ : ResolutionsExist.{u,v}) (_ : ResolvedTerms.{u,v}) : SequenceComparisons.{u,v} := by
  intro k _ _ T forms cmp E m X Y R S f l₀ l₁ F G e d h
  obtain ⟨H⟩ := pathsInNativeModels l₀ l₁
  obtain ⟨m₀, m₁, e₀, e₁, hh⟩ := compatibleCotangentHomotopy T forms cmp F G e d h H
  have h₀ := inducedMap_unique T forms e₀ (m.induced l₀ F G e d h)
  have h₁ := inducedMap_unique T forms e₁ (m.induced l₁ F G e d h)
  exact h₁ ▸ h₀ ▸ hh

end ComparisonHomotopies


section ScalarCoherence

open Specs.DerivedFormalization.Affine.Tensor (ModuleTensor regular term)
open private tensor_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.RelativePathComparison

variable {k : Type u} [Field k] [CharZero k]
variable (T : ModuleTensor.{u,v} k) (forms : TensorFormulas T) (cmp : T.Comparisons)
variable {P C E D : NonpositiveCDGA.{u,v} k}

include forms cmp in
private theorem extensionAssociator_exists (p : P ⟶ C) (e : C ⟶ E) (w : E ⟶ D) :
    Nonempty (ExtensionAssociator T p e w) := by
  classical
  let f := underlying (p ≫ e)
  let g := underlying w
  have hex (M : P.Module) := cmp.compose f g M
  let a (M : P.Module) := Classical.choose (hex M)
  have ha (M : P.Module) := Classical.choose_spec (hex M)
  let b : T.baseChange (f ≫ g) ≅ extend T (p ≫ e ≫ w) :=
    eqToIso (congrArg (fun z : P ⟶ D => extend T z) (Category.assoc p e w))
  have hb (M : P.Module) (i j n : ℤ) (h : i+j=n) (x : term M i) (y : D.complex.X j) :
      ((b.hom.app M).app ()).f n (T.tmul (f ≫ g) (N := regular D.toCommDGAlgebra) i j n h x y) =
        T.tmul (underlying (p ≫ e ≫ w)) (N := regular D.toCommDGAlgebra) i j n h x y := by
    have hpc : (p ≫ e) ≫ w = p ≫ e ≫ w := Category.assoc p e w
    change (((eqToIso (congrArg (fun z : P ⟶ D => extend T z) hpc)).hom.app M).app ()).f n
      (T.tmul (underlying ((p ≫ e) ≫ w)) (N := regular D.toCommDGAlgebra) i j n h x y) = _
    generalize (p ≫ e) ≫ w = q at hpc ⊢
    cases hpc
    rfl
  have hn {M N : P.Module} (h : M ⟶ N) :
      (extend T w).map ((extend T (p ≫ e)).map h) ≫ (a N).hom =
      (a M).hom ≫ (T.baseChange (f ≫ g)).map h := by
    apply RightDGModule.strict_ext
    rintro ⟨⟩ n
    apply LinearMap.congr_fun
    apply tensor_ext T
    intro m l hn z c
    let F := (extend T w).map ((extend T (p ≫ e)).map h) ≫ (a N).hom
    let G := (a M).hom ≫ (T.baseChange (f ≫ g)).map h
    change (F.app ()).f n (T.tmul g (N := regular D.toCommDGAlgebra) m l n hn z c) =
      (G.app ()).f n (T.tmul g (N := regular D.toCommDGAlgebra) m l n hn z c)
    let v := ((Tensor.pair g (N := regular D.toCommDGAlgebra) (M := (extend T (p ≫ e)).obj M)
      m l n hn).flip c)
    have eq :
      (((F.app ()).f n).hom.comp (T.degree g _ _ n).toLinearMap).comp v =
      (((G.app ()).f n).hom.comp (T.degree g _ _ n).toLinearMap).comp v := by
      apply tensor_ext T
      intro i j hm x y
      change ((a N).hom.app ()).f n (((T.baseChange g).map ((T.baseChange f).map h)).app () |>.f n
        (T.tmul g (N := regular D.toCommDGAlgebra) m l n hn
          (T.tmul f (N := regular E.toCommDGAlgebra) i j m hm x y) c)) =
        (((T.baseChange (f ≫ g)).map h).app ()).f n
          (((a M).hom.app ()).f n (T.tmul g (N := regular D.toCommDGAlgebra) m l n hn
            (T.tmul f (N := regular E.toCommDGAlgebra) i j m hm x y) c))
      rw [(forms g _).first, (forms f _).first, ha N, ha M, (forms (f ≫ g) _).first]
    exact LinearMap.congr_fun eq z
  let aNat : extend T (p ≫ e) ⋙ extend T w ≅ T.baseChange (f ≫ g) :=
    NatIso.ofComponents a hn
  let ab := aNat ≪≫ b
  refine ⟨⟨ab, ?_⟩⟩
  intro M i j l m n hm hn x y z
  change ((b.hom.app M).app ()).f n (((a M).hom.app ()).f n
      (T.tmul g (N := regular D.toCommDGAlgebra) m l n hn
        (T.tmul f (N := regular E.toCommDGAlgebra) i j m hm x y) z)) = _
  rw [ha M, hb]

variable {T} in
private theorem extensionAssociator_units {p : P ⟶ C} {e : C ⟶ E} {w : E ⟶ D}
    (a : ExtensionAssociator T p e w) (M : P.Module) (n : ℤ) (x : term M n) :
    ((a.iso.hom.app M).app ()).f n
      (T.tmul (underlying w) (N := regular D.toCommDGAlgebra) n 0 n (add_zero n)
        (T.tmul (underlying (p ≫ e)) (N := regular E.toCommDGAlgebra) n 0 n (add_zero n) x E.one) D.one) =
      T.tmul (underlying (p ≫ e ≫ w)) (N := regular D.toCommDGAlgebra) n 0 n (add_zero n) x D.one := by
  rw [a.pure, w.map_one]
  change T.tmul (underlying (p ≫ e ≫ w)) (N := regular D.toCommDGAlgebra) n 0 n (add_zero n) x
    (D.mul 0 0 0 rfl D.one D.one) = _
  rw [D.toDGAlgebra.id_comp]

variable {X Y : Chain.{u,v} k} {R : Resolution X} {S : Resolution Y}

include forms in
set_option maxHeartbeats 800000 in
private theorem transportedInduces
    {f : ChainMap X Y} (l : Lift f R S) (F : Sequence T R) (G : Sequence T S)
    (e : X.C ⟶ E) (d : Y.C ⟶ E) (w : E ⟶ D) (m : MapAt F G e d)
    (a : ExtensionAssociator T R.Q.augmentation e w)
    (b : ExtensionAssociator T S.Q.augmentation d w) (hm : Induces l m) :
    ∃ m' : MapAt F G (e ≫ w) (d ≫ w), Induces l m' ∧
      (extend T w).map m.left ≫ b.iso.hom.app (resolutionLeft T S) =
        a.iso.hom.app (resolutionLeft T R) ≫ m'.left ∧
      (extend T w).map m.middle ≫ b.iso.hom.app S.absolute.module =
        a.iso.hom.app R.absolute.module ≫ m'.middle ∧
      (extend T w).map m.right ≫ b.iso.hom.app S.Q.differentials.module =
        a.iso.hom.app R.Q.differentials.module ≫ m'.right := by
  let U := extend T w
  let n : MapAt F G (e ≫ w) (d ≫ w) :=
    { left := a.iso.inv.app (resolutionLeft T R) ≫ U.map m.left ≫ b.iso.hom.app (resolutionLeft T S)
      middle := a.iso.inv.app R.absolute.module ≫ U.map m.middle ≫ b.iso.hom.app S.absolute.module
      right := a.iso.inv.app R.Q.differentials.module ≫ U.map m.right ≫ b.iso.hom.app S.Q.differentials.module
      incl_comm := by
        have ha := a.iso.inv.naturality F.incl
        have hb := b.iso.hom.naturality G.incl
        change inclusionAt F (e ≫ w) ≫ a.iso.inv.app R.absolute.module =
          a.iso.inv.app (resolutionLeft T R) ≫ U.map (inclusionAt F e) at ha
        change U.map (inclusionAt G d) ≫ b.iso.hom.app S.absolute.module =
          b.iso.hom.app (resolutionLeft T S) ≫ inclusionAt G (d ≫ w) at hb
        have hs : U.map (inclusionAt F e) ≫ U.map m.middle =
            U.map m.left ≫ U.map (inclusionAt G d) := by
          rw [← U.map_comp, m.incl_comm, U.map_comp]
        simp only [← Category.assoc, ha]
        simp only [Category.assoc, reassoc_of% hs, hb]
      proj_comm := by
        have ha := a.iso.inv.naturality F.proj
        have hb := b.iso.hom.naturality G.proj
        change projectionAt F (e ≫ w) ≫ a.iso.inv.app R.Q.differentials.module =
          a.iso.inv.app R.absolute.module ≫ U.map (projectionAt F e) at ha
        change U.map (projectionAt G d) ≫ b.iso.hom.app S.Q.differentials.module =
          b.iso.hom.app S.absolute.module ≫ projectionAt G (d ≫ w) at hb
        have hs : U.map (projectionAt F e) ≫ U.map m.right =
            U.map m.middle ≫ U.map (projectionAt G d) := by
          rw [← U.map_comp, m.proj_comm, U.map_comp]
        simp only [← Category.assoc, ha]
        simp only [Category.assoc, reassoc_of% hs, hb] }
  have inv (M : R.Q.algebra.Module) (i : ℤ) (x : term M i) :
    ((a.iso.inv.app M).app ()).f i
      (T.tmul (underlying (R.Q.augmentation ≫ e ≫ w)) (N := regular D.toCommDGAlgebra)
        i 0 i (add_zero i) x D.one) =
    T.tmul (underlying w) (N := regular D.toCommDGAlgebra) i 0 i (add_zero i)
      (T.tmul (underlying (R.Q.augmentation ≫ e)) (N := regular E.toCommDGAlgebra)
        i 0 i (add_zero i) x E.one) D.one := by
    rw [← extensionAssociator_units a M i x]
    let z := T.tmul (underlying w) (N := regular D.toCommDGAlgebra) i 0 i (add_zero i)
      (T.tmul (underlying (R.Q.augmentation ≫ e)) (N := regular E.toCommDGAlgebra)
        i 0 i (add_zero i) x E.one) D.one
    exact congrArg (fun g : U.obj ((extend T (R.Q.augmentation ≫ e)).obj M) ⟶ _ =>
      (g.app ()).f i z) (a.iso.hom_inv_id_app M)
  have transfer {M : R.Q.algebra.Module} {N : S.Q.algebra.Module}
      (g : (extend T (R.Q.augmentation ≫ e)).obj M ⟶ (extend T (S.Q.augmentation ≫ d)).obj N)
      (i : ℤ) (x : term M i) (y : term N i)
      (hg : (g.app ()).f i
          (T.tmul (underlying (R.Q.augmentation ≫ e)) (N := regular E.toCommDGAlgebra)
            i 0 i (add_zero i) x E.one) =
          T.tmul (underlying (S.Q.augmentation ≫ d)) (N := regular E.toCommDGAlgebra)
            i 0 i (add_zero i) y E.one) :
      ((b.iso.hom.app N).app ()).f i
        (((U.map g).app ()).f i (((a.iso.inv.app M).app ()).f i
          (T.tmul (underlying (R.Q.augmentation ≫ e ≫ w)) (N := regular D.toCommDGAlgebra)
            i 0 i (add_zero i) x D.one))) =
        T.tmul (underlying (S.Q.augmentation ≫ d ≫ w)) (N := regular D.toCommDGAlgebra)
          i 0 i (add_zero i) y D.one := by
    rw [inv, (forms (underlying w) _).first, hg, extensionAssociator_units]
  refine ⟨n, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact fun i x => transfer m.left i _ _ (hm.1 i x)
  · exact fun i x => transfer m.middle i _ _ (hm.2.1 i x)
  · exact fun i x => transfer m.right i _ _ (hm.2.2 i x)
  all_goals
    dsimp only [n]
    rw [Iso.hom_inv_id_app_assoc]

theorem scalarCoherence_conditional
    (_ : Concatenation.{u,v}) (_ : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (_ : PushoutResolves.{u,v})
    (_ : ResolutionsExist.{u,v}) (_ : ResolvedTerms.{u,v}) : ScalarCoherence.{u,v} := by
  intro k _ _ T forms cmp X Y R S E D f l F G e d w m m' hm hm'
  obtain ⟨a⟩ := extensionAssociator_exists T forms cmp R.Q.augmentation e w
  obtain ⟨b⟩ := extensionAssociator_exists T forms cmp S.Q.augmentation d w
  obtain ⟨n, hn, hl, hc, hr⟩ := transportedInduces T forms l F G e d w m a b hm
  have eq := inducedMap_unique T forms hn hm'
  exact ⟨a, b, eq ▸ hl, eq ▸ hc, eq ▸ hr⟩

end ScalarCoherence


section LocalizedTriangles

open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.Affine.Tensor (dgCat)
open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws quotient)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance)
open Specs.DerivedFormalization.DG.DerivedTriangles (coneTriangle)
open Specs.DerivedFormalization.DG.LocalizedBimoduleExactness (ConeLocalization classOfMap)
open Specs.DerivedFormalization.DG.HomComplex (homotopyCategory)
open Specs.DerivedFormalization.DG.ShiftCone (cone coneInclusion coneProjection shift shiftMap)
open CategoryTheory.Pretriangulated

variable {k : Type u} [Field k] [CharZero k] {E : CommDGAlgebra.{u,v} k}
variable (h : HomotopyCategoryLaws (dgCat E)) (K : ConeLocalization (dgCat E) h)
variable {L M N L' M' N' : E.Module} {i : L ⟶ M} {p : M ⟶ N} {i' : L' ⟶ M'} {p' : M' ⟶ N'}

set_option maxHeartbeats 1000000 in
private def homotopyConeComparison (f : SequenceMap i p i' p')
    (g : cone i ⟶ cone i') (hi : coneInclusion i ≫ g = f.middle ≫ coneInclusion i')
    (hp : g ≫ coneProjection i' = coneProjection i ≫ shiftMap 1 f.left) :
    letI := Derived.homotopyCategory (dgCat E) h
    letI := K.shiftK
    coneTriangle h K.shiftK (K.shiftObj L 1) i ⟶ coneTriangle h K.shiftK (K.shiftObj L' 1) i' := by
  letI := Derived.homotopyCategory (dgCat E) h
  letI := K.shiftK
  letI := K.addK
  let C := homotopyCategory (dgCat E)
  let F : E.Module ⥤ C := RightDGModule.toHomotopyCategory (dgCat E)
  let V := shiftFunctor C (1 : ℤ)
  refine ⟨F.map f.left, F.map f.middle, F.map g, ?_, ?_, ?_⟩
  · change F.map i ≫ F.map f.middle = F.map f.left ≫ F.map i'
    rw [← F.map_comp, ← F.map_comp, f.incl_comm]
  · change F.map (coneInclusion i) ≫ F.map g = F.map f.middle ≫ F.map (coneInclusion i')
    rw [← F.map_comp, ← F.map_comp, hi]
  · let a : F.obj (shift L 1) ⟶ V.obj (F.obj L) := eqToHom (K.shiftObj L 1).symm
    let b : F.obj (shift L' 1) ⟶ V.obj (F.obj L') := eqToHom (K.shiftObj L' 1).symm
    have hs : F.map (shiftMap 1 f.left) ≫ b = a ≫ V.map (F.map f.left) :=
      conjugate_eqToHom (K.shiftObj L 1).symm (K.shiftObj L' 1).symm (K.shiftMap f.left 1).symm
    have hw : F.map (coneProjection i) ≫ F.map (shiftMap 1 f.left) =
        F.map g ≫ F.map (coneProjection i') := by
      rw [← F.map_comp, ← F.map_comp, hp]
    have hm : (F.map (coneProjection i) ≫ a) ≫ V.map (F.map f.left) =
        F.map g ≫ (F.map (coneProjection i') ≫ b) := by
      calc
        _ = F.map (coneProjection i) ≫ (a ≫ V.map (F.map f.left)) := Category.assoc _ _ _
        _ = F.map (coneProjection i) ≫ (F.map (shiftMap 1 f.left) ≫ b) :=
          congrArg (fun t => F.map (coneProjection i) ≫ t) hs.symm
        _ = (F.map (coneProjection i) ≫ F.map (shiftMap 1 f.left)) ≫ b := (Category.assoc _ _ _).symm
        _ = (F.map g ≫ F.map (coneProjection i')) ≫ b := congrArg (fun t => t ≫ b) hw
        _ = _ := Category.assoc _ _ _
    let n {X Y : C} (z : X ⟶ Y) : X ⟶ Y := by
      letI : AddCommGroup (X ⟶ Y) := K.addK.homGroup X Y
      exact -z
    have sign {X Y : C} (z : X ⟶ Y) :
        (show X ⟶ Y from -(show Basic.h0Hom (HomComplex.homComplex X Y) from z)) = n z := by
      have he : K.addK.homGroup X Y =
          inferInstanceAs (AddCommGroup (Basic.h0Hom (HomComplex.homComplex X Y))) :=
        eq_of_heq (K.homGroup X Y)
      exact congrArg (fun G : AddCommGroup (X ⟶ Y) => by
        letI := G
        exact (show X ⟶ Y from -z)) he.symm
    let u := F.map (coneProjection i) ≫ a
    let v := F.map (coneProjection i') ≫ b
    have su : (coneTriangle h K.shiftK (K.shiftObj L 1) i).mor₃ = n u := sign u
    have sv : (coneTriangle h K.shiftK (K.shiftObj L' 1) i').mor₃ = n v := sign v
    have hsigned : n u ≫ V.map (F.map f.left) = F.map g ≫ n v :=
      (Preadditive.neg_comp _ _).trans
        ((congrArg (fun t => n t) hm).trans (Preadditive.comp_neg _ _).symm)
    exact (congrArg (fun t => t ≫ V.map (F.map f.left)) su).trans
      (hsigned.trans (congrArg (fun t => F.map g ≫ t) sv.symm))

set_option maxHeartbeats 1000000 in
private def coneToSequenceIso
    (q : cone i ⟶ N) (hq : IsConeQuotient p q)
    (e : letI := Derived.homotopyCategory (dgCat E) h
         letI := derivedCategoryInstance (dgCat E) h
         let Q : homotopyCategory (dgCat E) ⥤ Derived.derivedCategory (dgCat E) h :=
           quotient (dgCat E) h
         Q.obj (cone i) ≅ Q.obj N)
    (he : letI := Derived.homotopyCategory (dgCat E) h
          letI := derivedCategoryInstance (dgCat E) h
          let Q : homotopyCategory (dgCat E) ⥤ Derived.derivedCategory (dgCat E) h :=
            quotient (dgCat E) h
          e.hom = Q.map (classOfMap h q)) :
    letI := Derived.homotopyCategory (dgCat E) h
    letI := derivedCategoryInstance (dgCat E) h
    letI := K.shiftK
    letI := K.shiftD
    let Q : homotopyCategory (dgCat E) ⥤ Derived.derivedCategory (dgCat E) h :=
      quotient (dgCat E) h
    letI : Q.CommShift ℤ := K.quotientShift
    Q.mapTriangle.obj (coneTriangle h K.shiftK (K.shiftObj L 1) i) ≅
      localizedSequenceTriangle h (adjunctionConeLocalization K) i p e := by
  letI := Derived.homotopyCategory (dgCat E) h
  letI := derivedCategoryInstance (dgCat E) h
  letI := K.shiftK
  letI := K.shiftD
  let Q : homotopyCategory (dgCat E) ⥤ Derived.derivedCategory (dgCat E) h :=
    quotient (dgCat E) h
  letI : Q.CommShift ℤ := K.quotientShift
  let D := Derived.derivedCategory (dgCat E) h
  let U := Q.mapTriangle.obj (coneTriangle h K.shiftK (K.shiftObj L 1) i)
  let V := localizedSequenceTriangle h (adjunctionConeLocalization K) i p e
  let F : E.Module ⥤ homotopyCategory (dgCat E) := RightDGModule.toHomotopyCategory (dgCat E)
  have hp : coneInclusion i ≫ q = p := by
    apply RightDGModule.strict_ext
    rintro ⟨⟩ n x
    exact hq.1 n (x, 0)
  refine Triangle.isoMk U V (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change Q.map (F.map (coneInclusion i)) ≫ e.hom = 𝟙 _ ≫ Q.map (F.map p)
    have he' : e.hom = Q.map (F.map q) := he
    have hh : F.map (coneInclusion i) ≫ F.map q = F.map p :=
      (F.map_comp _ _).symm.trans (congrArg F.map hp)
    exact (congrArg (fun t => Q.map (F.map (coneInclusion i)) ≫ t) he').trans
      ((Q.map_comp _ _).symm.trans ((congrArg Q.map hh).trans (Category.id_comp _).symm))
  · change U.mor₃ ≫ (shiftFunctor D 1).map (𝟙 _) = e.hom ≫ e.inv ≫ U.mor₃
    calc
      _ = U.mor₃ ≫ 𝟙 _ :=
        congrArg (fun t => U.mor₃ ≫ t) ((shiftFunctor D (1 : ℤ)).map_id U.obj₁)
      _ = U.mor₃ := Category.comp_id _
      _ = _ := (e.hom_inv_id_assoc _).symm

set_option maxHeartbeats 1700000 in
theorem localizedSequenceComparisons_conditional
    (c₁ : Concatenation.{u,v}) (c₂ : ExactDifferentialSequence.{u,v})
    (c₃ : LocalizedTerms.{u,v}) (c₄ : PushoutResolves.{u,v})
    (c₅ : ResolutionsExist.{u,v}) (c₆ : ResolvedTerms.{u,v}) :
    LocalizedSequenceComparisons.{u,v} := by
  intro k _ _ E h K L M N L' M' N' i p i' p' S S'
  letI := Derived.homotopyCategory (dgCat E) h
  letI := derivedCategoryInstance (dgCat E) h
  letI := K.shiftK
  letI := K.shiftD
  letI := K.addD
  letI := K.zeroD
  letI := K.addShiftD
  letI := K.trianglesD
  let Q : homotopyCategory (dgCat E) ⥤ Derived.derivedCategory (dgCat E) h :=
    quotient (dgCat E) h
  letI : Q.CommShift ℤ := K.quotientShift
  dsimp only
  obtain ⟨q, q', co, hq, hq', hco, _⟩ := coneComparisons_conditional c₁ c₂ c₃ c₄ c₅ c₆ S S'
  let F : E.Module ⥤ homotopyCategory (dgCat E) := RightDGModule.toHomotopyCategory (dgCat E)
  let J := F ⋙ Q
  have hiq {U V : E.Module} (g : U ⟶ V) (hg : Module.quasiIsomorphism g) :
      IsIso (J.map g) := by
    exact (Derived.quasiIsomorphisms (dgCat E)).Q_inverts (F.map g) ⟨g, rfl, hg⟩
  letI := hiq q hq.2
  letI := hiq q' hq'.2
  let e := asIso (J.map q)
  let e' := asIso (J.map q')
  let W := coneToSequenceIso h K q hq e rfl
  let W' := coneToSequenceIso h K q' hq' e' rfl
  refine ⟨q, q', e, e', hq, hq', rfl, rfl, ?_, ?_, ?_⟩
  · exact isomorphic_distinguished _ (K.localizedConeTriangles.1 i) _ W.symm
  · exact isomorphic_distinguished _ (K.localizedConeTriangles.1 i') _ W'.symm
  let m (f : SequenceMap i p i' p') :=
    W.inv ≫ Q.mapTriangle.map (homotopyConeComparison h K f (co f) (hco f).2.1 (hco f).2.2.1) ≫ W'.hom
  have hm (f : SequenceMap i p i' p') :
      (m f).hom₁ = J.map f.left ∧ (m f).hom₂ = J.map f.middle ∧ (m f).hom₃ = J.map f.right := by
    refine ⟨?_, ?_, ?_⟩
    · change 𝟙 _ ≫ J.map f.left ≫ 𝟙 _ = _
      rw [Category.id_comp, Category.comp_id]
    · change 𝟙 _ ≫ J.map f.middle ≫ 𝟙 _ = _
      rw [Category.id_comp, Category.comp_id]
    · change e.inv ≫ J.map (co f) ≫ e'.hom = J.map f.right
      have hc : J.map (co f) ≫ e'.hom = e.hom ≫ J.map f.right := by
        change J.map (co f) ≫ J.map q' = J.map q ≫ J.map f.right
        rw [← J.map_comp, ← J.map_comp, (hco f).2.2.2]
      rw [hc, Iso.inv_hom_id_assoc]
  refine ⟨m, hm, ?_⟩
  intro f g H
  apply TriangleMorphism.ext
  · exact (hm f).1.trans ((congrArg Q.map ((RightDGModule.homotopyCriterion _ _).2
      ⟨H.left, H.left_eq⟩)).trans (hm g).1.symm)
  · exact (hm f).2.1.trans ((congrArg Q.map ((RightDGModule.homotopyCriterion _ _).2
      ⟨H.middle, H.middle_eq⟩)).trans (hm g).2.1.symm)
  · exact (hm f).2.2.trans ((congrArg Q.map ((RightDGModule.homotopyCriterion _ _).2
      ⟨H.right, H.right_eq⟩)).trans (hm g).2.2.symm)

end LocalizedTriangles


section DerivedTriangleExtension

open Specs.DerivedFormalization.DG
open Specs.DerivedFormalization.Affine.Tensor (dgCat ModuleTensor regular signedBimodule)
open Specs.DerivedFormalization.Affine.FlatFiltration (GradedSplit)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws quotient)
open Specs.DerivedFormalization.DG.DerivedKProjective (derivedCategoryInstance kProjectiveObjects)
open Specs.DerivedFormalization.DG.DerivedTriangles (coneTriangle)
open Specs.DerivedFormalization.DG.KProjective (isKProjective)
open Specs.DerivedFormalization.DG.HomComplex (homotopyCategory)
open Specs.DerivedFormalization.DG.DerivedBimoduleAdjunction
  (ConeLocalization ShiftConeComparisons TensorComparisonLaws)
open Specs.DerivedFormalization.DG.LocalizedBimoduleExactness (classOfMap)
open private strictNeg homotopyClass_neg from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ConeRotation
open Specs.DerivedFormalization.DG.ShiftCone (cone coneProjection shift)
open Specs.DerivedFormalization.DG.BalancedTensor (tmul)
open Specs.DerivedFormalization.DG.BimoduleAdjunction (ordinaryTensor)
open private tensorHom_ext from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.BimoduleTensorComparisons

variable {k : Type u} [Field k] [CharZero k]
variable {T : ModuleTensor.{u,v} k} {A B : CommDGAlgebra.{u,v} k} {f : A ⟶ B}
variable {hA : HomotopyCategoryLaws (dgCat A)} {hB : HomotopyCategoryLaws (dgCat B)}
variable (E : Specs.DerivedFormalization.Affine.DerivedTensor.ScalarExtension T f hA hB)

set_option maxHeartbeats 1000000 in
private theorem projectiveTensor_natural {P R : A.Module} (m : P ⟶ R)
    (hP : isKProjective P) (hR : isKProjective R) :
    letI := Derived.homotopyCategory (dgCat A) hA
    letI := Derived.homotopyCategory (dgCat B) hB
    letI := derivedCategoryInstance (dgCat A) hA
    letI := derivedCategoryInstance (dgCat B) hB
    let QA : homotopyCategory (dgCat A) ⥤ Derived.derivedCategory (dgCat A) hA :=
      quotient (dgCat A) hA
    let QB : homotopyCategory (dgCat B) ⥤ Derived.derivedCategory (dgCat B) hB :=
      quotient (dgCat B) hB
    E.functor.map (QA.map (classOfMap hA m)) ≫ (E.data.onProjective R hR).hom =
      (E.data.onProjective P hP).hom ≫ QB.map (classOfMap hB ((ordinaryTensor.{u,v,0,0} E.models.tensor).map m)) := by
  letI := Derived.homotopyCategory (dgCat A) hA
  letI := Derived.homotopyCategory (dgCat B) hB
  letI := derivedCategoryInstance (dgCat A) hA
  letI := derivedCategoryInstance (dgCat B) hB
  dsimp only
  let QA : homotopyCategory (dgCat A) ⥤ Derived.derivedCategory (dgCat A) hA :=
    quotient (dgCat A) hA
  let QB : homotopyCategory (dgCat B) ⥤ Derived.derivedCategory (dgCat B) hB :=
    quotient (dgCat B) hB
  let PP : (kProjectiveObjects (dgCat A)).FullSubcategory := ⟨P, hP⟩
  let PR : (kProjectiveObjects (dgCat A)).FullSubcategory := ⟨R, hR⟩
  let a : PP ⟶ PR := ObjectProperty.homMk (classOfMap hA m)
  let first (J : (kProjectiveObjects (dgCat A)).FullSubcategory) :
      E.functor.obj (QA.obj J.obj) ⟶ QB.obj (E.data.tensorH.obj J.obj) :=
    E.data.tensorSquare.hom.app J
  let second (J : A.Module) : QB.obj (E.data.tensorH.obj J) ⟶ QB.obj ((ordinaryTensor.{u,v,0,0} E.models.tensor).obj J) :=
    eqToHom (congrArg QB.obj (E.data.tensorObj J))
  let z := E.data.tensorH.map (classOfMap hA m)
  have hsq : E.functor.map (QA.map (classOfMap hA m)) ≫ first PR =
      first PP ≫ QB.map z := E.data.tensorSquare.hom.naturality a
  have ht := conjugate_eqToHom (E.data.tensorObj P) (E.data.tensorObj R) (E.realizes.2.1 m)
  have htens : QB.map z ≫ second R = second P ≫ QB.map (classOfMap hB ((ordinaryTensor.{u,v,0,0} E.models.tensor).map m)) := by
    change QB.map z ≫ eqToHom (congrArg QB.obj (E.data.tensorObj R)) =
      eqToHom (congrArg QB.obj (E.data.tensorObj P)) ≫ QB.map (classOfMap hB ((ordinaryTensor.{u,v,0,0} E.models.tensor).map m))
    calc
      _ = QB.map (z ≫ eqToHom (E.data.tensorObj R)) := by
        rw [QB.map_comp, eqToHom_map]
      _ = QB.map (eqToHom (E.data.tensorObj P) ≫ classOfMap hB ((ordinaryTensor.{u,v,0,0} E.models.tensor).map m)) := congrArg QB.map ht
      _ = _ := by
        have he := QB.map_comp (eqToHom (E.data.tensorObj P)) (classOfMap hB ((ordinaryTensor.{u,v,0,0} E.models.tensor).map m))
        rw [eqToHom_map] at he
        exact he
  change E.functor.map (QA.map (classOfMap hA m)) ≫ (first PR ≫ second R) =
    (first PP ≫ second P) ≫ QB.map (classOfMap hB ((ordinaryTensor.{u,v,0,0} E.models.tensor).map m))
  calc
    _ = (E.functor.map (QA.map (classOfMap hA m)) ≫ first PR) ≫ second R :=
      (Category.assoc _ _ _).symm
    _ = _ := by rw [hsq, Category.assoc, htens, Category.assoc]

variable {L M N : A.Module} {i : L ⟶ M} {p : M ⟶ N}

set_option maxHeartbeats 860000 in
private theorem quotientAfterExtension (forms : TensorFormulas T) (S : GradedSplit i p)
    (Z : ShiftConeComparisons (ordinaryTensor.{u,v,0,0} E.models.tensor)) (hZ : TensorComparisonLaws.{u,v,0,0} Z)
    (q : cone i ⟶ N) (hq : IsConeQuotient p q) :
    IsConeQuotient ((ordinaryTensor.{u,v,0,0} E.models.tensor).map p) ((Z.coneIso i).inv ≫ (ordinaryTensor.{u,v,0,0} E.models.tensor).map q) := by
  let split := Eq.mpr (congrArg (fun H : A.Module ⥤ B.Module => GradedSplit (H.map i) (H.map p)) E.strict)
    (extendGradedSplit T f (forms f (regular B)) S)
  have he : (ordinaryTensor.{u,v,0,0} E.models.tensor).map q = (Z.coneIso i).hom ≫ coneQuotient split := by
    apply tensorHom_ext E.models.tensor
    rintro ⟨⟩ n ⟨⟩ a b hab x y
    have hp := E.models.tensor.map_tmul p () () a b n hab x.1 y
    have hq' := E.models.tensor.map_tmul q () () a b n hab x y
    have hz := hZ.2 i () () a b n hab x y
    let z := E.models.tensor.degree (cone i) () n (tmul (signedBimodule f (regular B)) (cone i) () () a b n hab x y)
    change (((ordinaryTensor.{u,v,0,0} E.models.tensor).map q).app ()).f n z =
      (((ordinaryTensor.{u,v,0,0} E.models.tensor).map p).app ()).f n (((Z.coneIso i).hom.app ()).f n z).1
    change (((ordinaryTensor.{u,v,0,0} E.models.tensor).map q).app ()).f n z = _ at hq'
    change (((ordinaryTensor.{u,v,0,0} E.models.tensor).map p).app ()).f n _ = _ at hp
    change (((Z.coneIso i).hom.app ()).f n z) = _ at hz
    rw [hq', hz, hp, hq.1]
  rw [he, Iso.inv_hom_id_assoc]
  exact coneQuotient_quasiIso split


private theorem tensorMap_neg {P R : A.Module} (m : P ⟶ R) :
    (ordinaryTensor.{u,v,0,0} E.models.tensor).map (strictNeg m) =
      strictNeg ((ordinaryTensor.{u,v,0,0} E.models.tensor).map m) := by
  apply tensorHom_ext E.models.tensor
  rintro ⟨⟩ n ⟨⟩ i j h x y
  let D := E.models.tensor
  let z := D.degree P () n (tmul (signedBimodule f (regular B)) P () () i j n h x y)
  have e₁ := D.map_tmul (strictNeg m) () () i j n h x y
  have e₂ := D.map_tmul m () () i j n h x y
  change (((ordinaryTensor.{u,v,0,0} D).map (strictNeg m)).app ()).f n z = _ at e₁
  change (((ordinaryTensor.{u,v,0,0} D).map m).app ()).f n z = _ at e₂
  change (((ordinaryTensor.{u,v,0,0} D).map (strictNeg m)).app ()).f n z =
    -(((ordinaryTensor.{u,v,0,0} D).map m).app ()).f n z
  rw [e₁, e₂]
  change D.degree R () n (tmul (signedBimodule f (regular B)) R () () i j n h (-(m.app ()).f i x) y) =
    -D.degree R () n (tmul (signedBimodule f (regular B)) R () () i j n h ((m.app ()).f i x) y)
  simp only [← DGBimodule.tensorPair_apply, map_neg, LinearMap.neg_apply]

private theorem strictNeg_comp {P R S : B.Module} (m : P ⟶ R) (n : R ⟶ S) :
    strictNeg m ≫ n = strictNeg (m ≫ n) := by
  apply RightDGModule.strict_ext
  rintro ⟨⟩ t x
  exact map_neg ((n.app ()).f t).hom ((m.app ()).f t x)

private theorem comp_strictNeg {P R S : B.Module} (m : P ⟶ R) (n : R ⟶ S) :
    m ≫ strictNeg n = strictNeg (m ≫ n) := by
  apply RightDGModule.strict_ext
  rintro ⟨⟩ t x
  rfl

set_option maxHeartbeats 1000000 in
private theorem localizedSequence_boundary {A : CommDGAlgebra.{u,v} k}
    (h : HomotopyCategoryLaws (dgCat A)) (K : ConeLocalization (dgCat A) h)
    {L M N : A.Module} (i : L ⟶ M) (p : M ⟶ N)
    (q : letI := Derived.homotopyCategory (dgCat A) h
         letI := derivedCategoryInstance (dgCat A) h
         let Q : homotopyCategory (dgCat A) ⥤ Derived.derivedCategory (dgCat A) h :=
           quotient (dgCat A) h
         Q.obj (cone i) ≅ Q.obj N) :
    letI := Derived.homotopyCategory (dgCat A) h
    letI := derivedCategoryInstance (dgCat A) h
    letI := K.shiftD
    let Q : homotopyCategory (dgCat A) ⥤ Derived.derivedCategory (dgCat A) h :=
      quotient (dgCat A) h
    (localizedSequenceTriangle h K i p q).mor₃ =
      q.inv ≫ Q.map (classOfMap h (strictNeg (coneProjection i))) ≫ (K.onShift L 1).hom := by
  letI := Derived.homotopyCategory (dgCat A) h
  letI := derivedCategoryInstance (dgCat A) h
  letI := K.shiftK
  letI := K.shiftD
  let C := homotopyCategory (dgCat A)
  letI : Preadditive C := RightDGModule.homotopyPreadditive
  let Q : homotopyCategory (dgCat A) ⥤ Derived.derivedCategory (dgCat A) h :=
    quotient (dgCat A) h
  letI : Q.CommShift ℤ := K.quotientShift
  let F : A.Module ⥤ C := RightDGModule.toHomotopyCategory (dgCat A)
  let D := Derived.derivedCategory (dgCat A) h
  let a : F.obj (shift L 1) ⟶ (shiftFunctor C (1 : ℤ)).obj (F.obj L) :=
    eqToHom (K.shiftObj L 1).symm
  let pr := F.map (coneProjection i)
  let c : Q.obj ((shiftFunctor C (1 : ℤ)).obj (F.obj L)) ⟶ (shiftFunctor D (1 : ℤ)).obj (Q.obj (F.obj L)) :=
    (Q.commShiftIso (1 : ℤ)).hom.app L
  have hx : F.map (strictNeg (coneProjection i)) = -pr := homotopyClass_neg _
  have hs : (coneTriangle h K.shiftK (K.shiftObj L 1) i).mor₃ =
      F.map (strictNeg (coneProjection i)) ≫ a :=
    (Preadditive.neg_comp pr a).symm.trans (congrArg (fun m => m ≫ a) hx.symm)
  have hShift : (K.onShift L 1).hom = Q.map a ≫ c := by
    change eqToHom (congrArg Q.obj (K.shiftObj L 1).symm) ≫ c = _
    exact congrArg (fun t => t ≫ c) (eqToHom_map Q (K.shiftObj L 1).symm).symm
  let r := F.map (strictNeg (coneProjection i))
  let v : Q.obj N ⟶ Q.obj (F.obj (cone i)) := q.inv
  have hv : Q.map (coneTriangle h K.shiftK (K.shiftObj L 1) i).mor₃ = Q.map r ≫ Q.map a :=
    (congrArg Q.map hs).trans (Q.map_comp r a)
  change v ≫ Q.map (coneTriangle h K.shiftK (K.shiftObj L 1) i).mor₃ ≫ c =
    v ≫ Q.map r ≫ (K.onShift L 1).hom
  calc
    _ = v ≫ (Q.map r ≫ Q.map a) ≫ c := congrArg (fun t => v ≫ t ≫ c) hv
    _ = v ≫ Q.map r ≫ (Q.map a ≫ c) :=
      congrArg (fun t => v ≫ t) (Category.assoc _ _ _)
    _ = _ := congrArg (fun t => v ≫ Q.map r ≫ t) hShift.symm


open CategoryTheory.Pretriangulated

set_option maxHeartbeats 2400000 in
theorem derivedTriangleExtension_conditional
    (_ : Concatenation.{u,v}) (_ : ExactDifferentialSequence.{u,v})
    (_ : LocalizedTerms.{u,v}) (_ : PushoutResolves.{u,v})
    (_ : ResolutionsExist.{u,v}) (_ : ResolvedTerms.{u,v}) : DerivedTriangleExtension.{u,v} := by
  intro k _ _ T forms A B f hA hB E L M N i p q S hq hL hM hN
  letI := Derived.homotopyCategory (dgCat A) hA
  letI := Derived.homotopyCategory (dgCat B) hB
  letI := derivedCategoryInstance (dgCat A) hA
  letI := derivedCategoryInstance (dgCat B) hB
  let DA := Derived.derivedCategory (dgCat A) hA
  let DB := Derived.derivedCategory (dgCat B) hB
  let QA : homotopyCategory (dgCat A) ⥤ DA := quotient (dgCat A) hA
  let QB : homotopyCategory (dgCat B) ⥤ DB := quotient (dgCat B) hB
  let JA : A.Module ⥤ DA := RightDGModule.toHomotopyCategory (dgCat A) ⋙ QA
  let JB : B.Module ⥤ DB := RightDGModule.toHomotopyCategory (dgCat B) ⋙ QB
  let H : DA ⥤ DB := E.functor
  obtain ⟨KA, KB, Z, _, hZ, _, ss, _, hExact, _, _, _, hShift⟩ := E.exactness
  letI := KA.shiftD
  letI := KA.addD
  letI := KA.zeroD
  letI := KA.addShiftD
  letI := KA.trianglesD
  letI := KB.shiftD
  letI := KB.addD
  letI := KB.zeroD
  letI := KB.addShiftD
  letI := KB.trianglesD
  letI : H.CommShift ℤ := ss
  letI : H.IsTriangulated := hExact
  have hC : isKProjective (cone i) := RightDGModule.IsKProjective.cone i hL hM
  have hS : isKProjective (shift L 1) := RightDGModule.IsKProjective.shift 1 hL
  let G : A.Module ⥤ B.Module := ordinaryTensor E.models.tensor
  let q' : cone (G.map i) ⟶ G.obj N := (Z.coneIso i).inv ≫ G.map q
  have hq' : IsConeQuotient (G.map p) q' := quotientAfterExtension E forms S Z hZ q hq
  letI : IsIso (JA.map q) := (Derived.quasiIsomorphisms (dgCat A)).Q_inverts _ ⟨q,rfl,hq.2⟩
  letI : IsIso (JB.map q') := (Derived.quasiIsomorphisms (dgCat B)).Q_inverts _ ⟨q',rfl,hq'.2⟩
  let e := asIso (JA.map q)
  let e' := asIso (JB.map q')
  let U := localizedSequenceTriangle hA KA i p e
  let V := localizedSequenceTriangle hB KB (G.map i) (G.map p) e'
  let aL : H.obj (JA.obj L) ≅ JB.obj (G.obj L) := E.data.onProjective L hL
  let aM : H.obj (JA.obj M) ≅ JB.obj (G.obj M) := E.data.onProjective M hM
  let aN : H.obj (JA.obj N) ≅ JB.obj (G.obj N) := E.data.onProjective N hN
  let aC : H.obj (JA.obj (cone i)) ≅ JB.obj (G.obj (cone i)) := E.data.onProjective (cone i) hC
  let aS : H.obj (JA.obj (shift L 1)) ≅ JB.obj (G.obj (shift L 1)) := E.data.onProjective (shift L 1) hS
  let SC := JB.map (Z.coneIso i).hom
  let SS := JB.map (Z.shiftIso L 1).hom
  let VA := shiftFunctor DA (1 : ℤ)
  let VB := shiftFunctor DB (1 : ℤ)
  let src : JA.obj (shift L 1) ⟶ VA.obj (JA.obj L) := (KA.onShift L 1).hom
  let dst : JB.obj (shift (G.obj L) 1) ⟶ VB.obj (JB.obj (G.obj L)) := (KB.onShift (G.obj L) 1).hom
  let d := JA.map (strictNeg (coneProjection i))
  let dG := JB.map (G.map (strictNeg (coneProjection i)))
  let d' := JB.map (strictNeg (coneProjection (G.map i)))
  have hproj : dG ≫ SS = SC ≫ d' := by
    have hsign : G.map (strictNeg (coneProjection i)) ≫ (Z.shiftIso L 1).hom =
        (Z.coneIso i).hom ≫ strictNeg (coneProjection (G.map i)) := by
      have hn : G.map (strictNeg (coneProjection i)) = strictNeg (G.map (coneProjection i)) :=
        tensorMap_neg E _
      rw [hn, strictNeg_comp, comp_strictNeg, Z.projection]
    exact (JB.map_comp _ _).symm.trans ((congrArg JB.map hsign).trans (JB.map_comp _ _))
  have hqmap : JB.map (G.map q) = SC ≫ e'.hom := by
    have hq₀ : G.map q = (Z.coneIso i).hom ≫ q' := (Iso.hom_inv_id_assoc _ _).symm
    exact (congrArg JB.map hq₀).trans (JB.map_comp _ _)
  have hnq : H.map e.hom ≫ aN.hom = aC.hom ≫ SC ≫ e'.hom := by
    have hn : H.map e.hom ≫ aN.hom = aC.hom ≫ JB.map (G.map q) :=
      projectiveTensor_natural E q hC hN
    exact hn.trans (congrArg (fun x => aC.hom ≫ x) hqmap)
  have hqn : H.map e.inv ≫ aC.hom ≫ SC = aN.hom ≫ e'.inv := by
    apply (cancel_mono e'.hom).mp
    have he₀ : H.map e.inv ≫ H.map e.hom = 𝟙 _ :=
      (H.map_comp _ _).symm.trans ((congrArg H.map e.inv_hom_id).trans (H.map_id _))
    calc
      _ = H.map e.inv ≫ (aC.hom ≫ SC ≫ e'.hom) := by simp only [Category.assoc]
      _ = H.map e.inv ≫ (H.map e.hom ≫ aN.hom) :=
        congrArg (fun x => H.map e.inv ≫ x) hnq.symm
      _ = (H.map e.inv ≫ H.map e.hom) ≫ aN.hom := (Category.assoc _ _ _).symm
      _ = _ := by rw [he₀, Category.id_comp, Category.assoc, e'.inv_hom_id, Category.comp_id]
  have hd : H.map d ≫ aS.hom = aC.hom ≫ dG :=
    projectiveTensor_natural E (strictNeg (coneProjection i)) hC hS
  let θ : H.obj (VA.obj (JA.obj L)) ⟶ VB.obj (H.obj (JA.obj L)) :=
    (H.commShiftIso (1 : ℤ)).hom.app (JA.obj L)
  let ζ : VB.obj (H.obj (JA.obj L)) ⟶ VB.obj (JB.obj (G.obj L)) := VB.map aL.hom
  have hsh : H.map src ≫ θ ≫ ζ = aS.hom ≫ SS ≫ dst :=
    hShift L 1 hL hS
  have hU : U.mor₃ = e.inv ≫ d ≫ src := localizedSequence_boundary hA KA i p e
  have hV : V.mor₃ = e'.inv ≫ d' ≫ dst := localizedSequence_boundary hB KB (G.map i) (G.map p) e'
  let j : H.mapTriangle.obj U ≅ V := Triangle.isoMk _ _ aL aM aN
    (projectiveTensor_natural E i hL hM) (projectiveTensor_natural E p hM hN) (by
      change (H.map U.mor₃ ≫ θ) ≫ ζ = aN.hom ≫ V.mor₃
      have ho : H.map U.mor₃ = H.map e.inv ≫ H.map d ≫ H.map src :=
        (congrArg H.map hU).trans ((H.map_comp _ _).trans
          (congrArg (fun x => H.map e.inv ≫ x) (H.map_comp _ _)))
      calc
        _ = ((H.map e.inv ≫ H.map d ≫ H.map src) ≫ θ) ≫ ζ :=
          congrArg (fun g => (g ≫ θ) ≫ ζ) ho
        _ = H.map e.inv ≫ H.map d ≫ (H.map src ≫ θ ≫ ζ) := by simp only [Category.assoc]
        _ = H.map e.inv ≫ H.map d ≫ (aS.hom ≫ SS ≫ dst) :=
          congrArg (fun g => H.map e.inv ≫ H.map d ≫ g) hsh
        _ = H.map e.inv ≫ (H.map d ≫ aS.hom) ≫ SS ≫ dst := by simp only [Category.assoc]
        _ = H.map e.inv ≫ (aC.hom ≫ dG) ≫ SS ≫ dst :=
          congrArg (fun g => H.map e.inv ≫ g ≫ SS ≫ dst) hd
        _ = H.map e.inv ≫ aC.hom ≫ (dG ≫ SS) ≫ dst := by simp only [Category.assoc]
        _ = H.map e.inv ≫ aC.hom ≫ (SC ≫ d') ≫ dst :=
          congrArg (fun g => H.map e.inv ≫ aC.hom ≫ g ≫ dst) hproj
        _ = (H.map e.inv ≫ aC.hom ≫ SC) ≫ d' ≫ dst := by simp only [Category.assoc]
        _ = (aN.hom ≫ e'.inv) ≫ d' ≫ dst := congrArg (fun g => g ≫ d' ≫ dst) hqn
        _ = aN.hom ≫ (e'.inv ≫ d' ≫ dst) := Category.assoc _ _ _
        _ = _ := congrArg (fun g => aN.hom ≫ g) hV.symm)
  exact ⟨KA, KB, ss, q', e, e', hq', rfl, rfl, j, rfl, rfl, rfl⟩

end DerivedTriangleExtension

end DerivedFormalization.Affine.CotangentDiagramComparison

universe v8_closure_cabea4259d9a9815_u0 v8_closure_cabea4259d9a9815_u1
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«coneComparisons» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«ConeComparisons».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«coneComparisons_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«derivedExtensionComparison» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«DerivedExtensionComparison».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«derivedExtensionComparison_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«derivedTriangleExtension» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«DerivedTriangleExtension».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«derivedTriangleExtension_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«liftsExist» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«LiftsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«liftsExist_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«localizedSequenceComparisons» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«LocalizedSequenceComparisons».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«localizedSequenceComparisons_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«pathsExist» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«PathsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«pathsExist_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«scalarCoherence» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«ScalarCoherence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«scalarCoherence_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«sequenceComparisons» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«SequenceComparisons».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«sequenceComparisons_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«sequencesExist» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«SequencesExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«sequencesExist_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«strictExtension» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«StrictExtension».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«strictExtension_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
theorem _root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«strictSequenceComparisons» : _root_.«Specs».«DerivedFormalization».«Affine».«CotangentDiagramComparison».«StrictSequenceComparisons».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} :=
  @_root_.«DerivedFormalization».«Affine».«CotangentDiagramComparison».«strictSequenceComparisons_conditional».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1} (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«concatenation».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«exactDifferentialSequence».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«localizedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«pushoutResolves».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolutionsExist».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1}) (@_root_.«DerivedFormalization».«Affine».«ResolvedCotangentSequence».«resolvedTerms».{v8_closure_cabea4259d9a9815_u0, v8_closure_cabea4259d9a9815_u1})
