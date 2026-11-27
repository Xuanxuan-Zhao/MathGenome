import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.StrictInjectiveExtension
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.InjectiveTruncationTower
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveComplexReplacement

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open Specs.DerivedFormalization.InjectiveTruncationTower (stage projection)
open scoped ZeroObject

universe u v

noncomputable section

private lemma truncationProjection_isIso_above {R : Type u} [CommRing R]
    (X : Comp.{v} R) (a j : ℤ) (h : a < j) :
    IsIso ((CochainComplex.πTruncGE X a).f j) :=
  AdvancedHomologicalAlgebra.InjectiveComplexReplacement.isIso_truncation_component X a j h

section Truncations

variable {R : Type u} [CommRing R] (X : Comp.{v} R)

private lemma nextProjection_isIso (n : ℕ) (j : ℤ) (h : -(n : ℤ) ≤ j) :
    IsIso ((projection X (n + 1)).f j) :=
  truncationProjection_isIso_above X _ _ (by push_cast; omega)

private def truncationStepComponent (n : ℕ) (j : ℤ) :
    (stage X (n + 1)).X j ⟶ (stage X n).X j :=
  if h : -(n : ℤ) ≤ j then
    letI := nextProjection_isIso X n j h
    inv ((projection X (n + 1)).f j) ≫ (projection X n).f j
  else 0

private lemma truncationStepComponent_fac (n : ℕ) (j : ℤ) :
    (projection X (n + 1)).f j ≫ truncationStepComponent X n j =
      (projection X n).f j := by
  by_cases h : -(n : ℤ) ≤ j
  · let := nextProjection_isIso X n j h
    simp [truncationStepComponent, h]
  · exact ((stage X n).isZero_of_isStrictlyGE (-(n : ℤ)) j (by omega)).eq_of_tgt _ _

private def truncationStep (n : ℕ) : stage X (n + 1) ⟶ stage X n where
  f := truncationStepComponent X n
  comm' j k _ := by
    have : Epi ((projection X (n + 1)).f j) := by
      dsimp [projection, CochainComplex.πTruncGE]
      infer_instance
    apply (cancel_epi ((projection X (n + 1)).f j)).1
    rw [← Category.assoc, truncationStepComponent_fac, (projection X n).comm,
      (projection X (n + 1)).comm_assoc, truncationStepComponent_fac]

private lemma truncationStep_fac (n : ℕ) :
    projection X (n + 1) ≫ truncationStep X n = projection X n := by
  apply HomologicalComplex.hom_ext
  exact truncationStepComponent_fac X n

private lemma truncationStep_epi (n : ℕ) (j : ℤ) :
    Epi ((truncationStep X n).f j) := by
  have : Epi ((projection X n).f j) := by
    dsimp [projection, CochainComplex.πTruncGE]
    infer_instance
  exact epi_of_epi_fac (truncationStepComponent_fac X n j)

private def truncationCone :
    Cone (Functor.ofOpSequence (truncationStep X)) :=
  Cone.mk X (NatTrans.ofOpSequence (projection X) (fun n => by
    simp only [Functor.const_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
    change 𝟙 X ≫ projection X n = projection X (n + 1) ≫ truncationStep X n
    rw [Category.id_comp, truncationStep_fac]))

private def truncationConeIsLimit : IsLimit (truncationCone X) := by
  apply HomologicalComplex.isLimitOfEval
  intro j
  let s := (HomologicalComplex.eval (ModuleCat.{v} R) (.up ℤ) j).mapCone (truncationCone X)
  let n := (-j).toNat + 1
  have legIso (m : ℕ) (hm : n ≤ m) : IsIso (s.π.app ⟨m⟩) := by
    change IsIso ((projection X m).f j)
    apply truncationProjection_isIso_above
    dsimp [n] at hm
    omega
  have := legIso n le_rfl
  have h : (Functor.ofOpSequence (truncationStep X) ⋙
      HomologicalComplex.eval _ (.up ℤ) j).IsEventuallyConstantTo ⟨n⟩ := by
    intro m f
    have := legIso m.unop (leOfHom f.unop)
    exact IsIso.of_isIso_fac_left (s.w f)
  exact h.isLimitOfIsIso s

/-- The canonical projections exhibit the original complex as the limit of
its degreewise surjective good truncation tower. -/
theorem truncationTowerExists :
    Specs.DerivedFormalization.InjectiveTruncationTower.truncationTowerExistsType.{u, v} := by
  intro R _ X
  refine ⟨truncationStep X, truncationStep_fac X, ?_, (truncationCone X).π, fun _ => rfl,
    ⟨truncationConeIsLimit X⟩⟩
  intro n j
  exact (ModuleCat.epi_iff_surjective _).1 (truncationStep_epi X n j)

end Truncations

section InjectiveModels

variable {R : Type u} [CommRing R]

/-- A termwise monic quasi-isomorphism to injectives with a prescribed lower bound. -/
private structure InjectiveStage (T : Comp.{v} R) (a : ℤ) where
  model : Comp.{v} R
  ι : T ⟶ model
  mono_f : ∀ j : ℤ, Mono (ι.f j)
  quasiIso : QuasiIso ι
  injective : ∀ j : ℤ, Injective (model.X j)
  bound : model.IsStrictlyGE a

private def replaceStage (T : Comp.{v} R) (a : ℤ)
    [EnoughInjectives (ModuleCat.{v} R)] [T.IsStrictlyGE a] : InjectiveStage T a :=
  Classical.choice (by
    obtain ⟨I, f, hm, hq, hi, hb⟩ :=
      AdvancedHomologicalAlgebra.InjectiveComplexReplacement.replacement
        (ModuleCat.{v} R) T a inferInstance
    exact ⟨⟨I, f, hm, hq, hi, hb⟩⟩)

private def coconeIdTermIso (I : Comp.{v} R) (j : ℤ) :
    (mappingCocone (𝟙 I)).X j ≅ I.X j ⊞ I.X (j + -1) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 I) (j + -1) j (by simp)

private def coconeIdContractingHomotopy (I : Comp.{v} R) :
    Homotopy (𝟙 (mappingCocone (𝟙 I))) 0 :=
  (Homotopy.ofEq (by simp [mappingCocone])).trans
    (((mappingCone.homotopyToZeroOfId I).shift (-1)).trans
      (Homotopy.ofEq (by simp; rfl)))

private def biprodInlHomotopyEquiv (J C : Comp.{v} R) (h : Homotopy (𝟙 C) 0) :
    HomotopyEquiv J (J ⊞ C) where
  hom := biprod.inl
  inv := biprod.fst
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := by
    have hC := (h.compRight (biprod.inr : C ⟶ J ⊞ C)).compLeft
      (biprod.snd : J ⊞ C ⟶ C)
    have hsum := (Homotopy.refl (biprod.fst ≫ biprod.inl : J ⊞ C ⟶ J ⊞ C)).add hC
    exact (Homotopy.ofEq (by simp)).trans
      (hsum.symm.trans (Homotopy.ofEq (by simp [biprod.total])))

private structure InjectiveStageExtension {T T' : Comp.{v} R} {a : ℤ}
    (S : InjectiveStage T a) (t : T' ⟶ T) (b : ℤ) where
  next : InjectiveStage T' b
  transition : next.model ⟶ S.model
  comm : next.ι ≫ transition = t ≫ S.ι
  split : ∀ j : ℤ, ∃ s : S.model.X j ⟶ next.model.X j, s ≫ transition.f j = 𝟙 _

private def extendStage {T T' : Comp.{v} R} {a b : ℤ}
    (S : InjectiveStage T a) (P : InjectiveStage T' b) (t : T' ⟶ T) (hba : b ≤ a) :
    InjectiveStageExtension S t b := by
  have := S.bound
  have := S.injective
  let hK := CochainComplex.isKInjective_of_injective S.model a
  let extension := strictInjectiveExtension P.ι P.mono_f P.quasiIso hK S.injective (t ≫ S.ι)
  let g : P.model ⟶ S.model := extension.choose
  have hg : P.ι ≫ g = t ≫ S.ι := extension.choose_spec
  let C := mappingCocone (𝟙 S.model)
  let e (j : ℤ) := (HomologicalComplex.eval _ (.up ℤ) j).mapBiprod P.model C
  let p := mappingCocone.fst (𝟙 S.model)
  let i : P.model ⟶ P.model ⊞ C := biprod.inl
  have hi : QuasiIso i := (biprodInlHomotopyEquiv P.model C
    (coconeIdContractingHomotopy S.model)).quasiIso_hom
  have := P.quasiIso
  refine
    { next :=
        { model := P.model ⊞ C
          ι := P.ι ≫ i
          mono_f := ?_
          quasiIso := inferInstance
          injective := ?_
          bound := ?_ }
      transition := biprod.desc g p
      comm := ?_
      split := ?_ }
  · intro j
    have h : Mono (P.ι.f j) := P.mono_f j
    have hi' : Mono (i.f j) := by
      have hsplit : i.f j ≫ (biprod.fst : P.model ⊞ C ⟶ P.model).f j = 𝟙 _ := by
        rw [← HomologicalComplex.comp_f, biprod.inl_fst, HomologicalComplex.id_f]
      exact mono_of_mono_fac hsplit
    simpa only [HomologicalComplex.comp_f] using
      (show Mono (P.ι.f j ≫ i.f j) from inferInstance)
  · intro j
    have := P.injective j
    have : Injective (C.X j) := by
      have := S.injective j
      have := S.injective (j + -1)
      exact Injective.of_iso (coconeIdTermIso S.model j).symm inferInstance
    apply Injective.of_iso (e j).symm
    change Injective (P.model.X j ⊞ C.X j)
    infer_instance
  · rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    have := P.bound
    apply IsZero.of_iso _ (e j)
    rw [biprod_isZero_iff]
    refine ⟨P.model.isZero_of_isStrictlyGE b j hj, IsZero.of_iso ?_ (coconeIdTermIso S.model j)⟩
    rw [biprod_isZero_iff]
    exact ⟨S.model.isZero_of_isStrictlyGE a j (by omega),
      S.model.isZero_of_isStrictlyGE a (j + -1) (by omega)⟩
  · simpa only [Category.assoc, i, biprod.inl_desc] using hg
  · intro j
    refine ⟨(mappingCocone.inl (𝟙 S.model)).v j j (add_zero j) ≫
      (biprod.inr : C ⟶ P.model ⊞ C).f j, ?_⟩
    rw [Category.assoc, ← HomologicalComplex.comp_f, biprod.inr_desc]
    exact mappingCocone.inl_v_fst_f (𝟙 S.model) j

variable (X : Comp.{v} R) [EnoughInjectives (ModuleCat.{v} R)]
  (t : ∀ n : ℕ, stage X (n + 1) ⟶ stage X n)

private def extendTruncationStage (n : ℕ) (S : InjectiveStage (stage X n) (-(n : ℤ))) :
    InjectiveStageExtension S (t n) (-(↑(n + 1) : ℤ)) :=
  extendStage S (replaceStage (stage X (n + 1)) (-(↑(n + 1) : ℤ)))
    (t n) (by push_cast; omega)

private def injectiveStages : (n : ℕ) → InjectiveStage (stage X n) (-(n : ℤ))
  | 0 => replaceStage (stage X 0) (-(0 : ℤ))
  | n + 1 => (extendTruncationStage X t n (injectiveStages n)).next

private def injectiveTowerStep (n : ℕ) :
    (injectiveStages X t (n + 1)).model ⟶ (injectiveStages X t n).model :=
  (extendTruncationStage X t n (injectiveStages X t n)).transition

end InjectiveModels

/-- The truncation tower admits compatible bounded-below injective models
with degreewise split epimorphisms as transitions. -/
theorem injectiveTruncationTowerExists :
    Specs.DerivedFormalization.InjectiveTruncationTower.injectiveTruncationTowerExistsType.{u, v} := by
  intro R _ X t _
  have := ModuleCat.enoughInjectives R
  let I := Functor.ofOpSequence (X := fun n => (injectiveStages X t n).model)
    (injectiveTowerStep X t)
  let ι : Functor.ofOpSequence t ⟶ I :=
    NatTrans.ofOpSequence (fun n => (injectiveStages X t n).ι) (fun n => by
      simp only [I, Functor.ofOpSequence_map_homOfLE_succ]
      exact (extendTruncationStage X t n (injectiveStages X t n)).comm.symm)
  refine ⟨I, ι, fun n => ?_, fun n j => ?_⟩
  · let S := injectiveStages X t n
    exact ⟨S.bound, S.injective, S.mono_f, S.quasiIso⟩
  · simp only [I, Functor.ofOpSequence_map_homOfLE_succ]
    exact (extendTruncationStage X t n (injectiveStages X t n)).split j

end

end DerivedFormalization
