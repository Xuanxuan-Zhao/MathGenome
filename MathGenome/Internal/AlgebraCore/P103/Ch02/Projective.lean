import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.Projective
import MathGenome.Internal.AlgebraCore.P103.Ch01.FreeModules
import MathGenome.Internal.AlgebraCore.P103.Ch01.SplitSequences
import MathGenome.Internal.AlgebraCore.P103.Ch01.HomTensorExactness

noncomputable section

universe u v w x

namespace P103.Ch02.Projective

open P103.Specs.Ch02.Projective P103.Ch01 P103.HomTensorExactness

/-- The kernel of a surjection gives its short exact sequence. -/
private theorem kernel_injective {R M N : Type*} [Ring R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) :
    Function.Injective (LinearMap.ker f).subtype := Subtype.val_injective

theorem lifting : liftingType.{u,v,w,x} := by
  intro R _ P _ _ _ M N _ _ _ _ f g hf
  exact Module.projective_lifting_property f g hf

theorem projective_iff_lifting : projective_iff_liftingType.{u,v,w} := by
  intro R _ P _ _
  constructor
  · intro h
    let := h
    intro M N _ _ _ _ f g hf
    exact Module.projective_lifting_property f g hf
  · intro h
    let F := P →₀ R
    let eF : ULift.{w} F ≃ₗ[R] F := ULift.moduleEquiv
    let eP : ULift.{max u w} P ≃ₗ[R] P := ULift.moduleEquiv
    let q : F →ₗ[R] P := Finsupp.linearCombination R id
    let f := eP.symm.toLinearMap.comp (q.comp eF.toLinearMap)
    have hq : Function.Surjective q :=
      Finsupp.linearCombination_surjective _ Function.surjective_id
    obtain ⟨s, hs⟩ := h _ _ f eP.symm.toLinearMap
      (eP.symm.surjective.comp (hq.comp eF.surjective))
    apply Module.projective_def'.mpr
    refine ⟨eF.toLinearMap.comp s, ?_⟩
    ext p
    have hx := congrArg eP (LinearMap.congr_fun hs p)
    simpa [f, q] using hx

theorem free_projective : free_projectiveType.{u,v} := by
  intro R X _
  obtain ⟨b, _⟩ := P103.Ch01.FreeModules.standard_basis R X
  exact Module.Projective.of_basis b

theorem free_retract_projective : free_retract_projectiveType.{u,v,w} := by
  intro R _ P X _ _ i r h
  let := free_projective R X
  exact Module.Projective.of_split i r h

theorem projective_iff_splitting : projective_iff_splittingType.{u,v,w} := by
  intro R _ P _ _
  constructor
  · intro h
    let := h
    intro A B _ _ _ _ i p hi he hp
    exact Module.projective_lifting_property p LinearMap.id hp
  · intro h
    let F := P →₀ R
    let eF : ULift.{w} F ≃ₗ[R] F := ULift.moduleEquiv
    let q : F →ₗ[R] P := Finsupp.linearCombination R id
    let p := q.comp eF.toLinearMap
    have hq : Function.Surjective q :=
      Finsupp.linearCombination_surjective _ Function.surjective_id
    obtain ⟨s, hs⟩ := h (LinearMap.ker p) (ULift.{w} F)
      (LinearMap.ker p).subtype p (kernel_injective p)
      (LinearMap.exact_subtype_ker_map p) (hq.comp eF.surjective)
    apply Module.projective_def'.mpr
    exact ⟨eF.toLinearMap.comp s, hs⟩

theorem projective_iff_freeSummand : projective_iff_freeSummandType.{u,v,w} := by
  intro R _ P _ _
  constructor
  · intro h
    let := h
    let X := ULift.{max u w} P
    let e : FreeModule R X ≃ₗ[R] (P →₀ R) :=
      Finsupp.mapDomain.linearEquiv R R Equiv.ulift
    let q := (Finsupp.linearCombination R (id : P → P)).comp e.toLinearMap
    have hq : Function.Surjective q :=
      (Finsupp.linearCombination_surjective R Function.surjective_id).comp e.surjective
    obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
    let eSplit := P103.Ch01.SplitSequences.splitting R (LinearMap.ker q)
      (FreeModule R X) P (LinearMap.ker q).subtype q (kernel_injective q)
      (LinearMap.exact_subtype_ker_map q) s hs
    exact ⟨X, LinearMap.ker q, inferInstance, inferInstance,
      ⟨(LinearEquiv.prodComm R P (LinearMap.ker q)).trans eSplit⟩⟩
  · rintro ⟨X, Q, _, _, ⟨e⟩⟩
    apply free_retract_projective R P X
      (e.toLinearMap.comp (LinearMap.inl R P Q))
      ((LinearMap.fst R P Q).comp e.symm.toLinearMap)
    ext p
    simp

theorem projective_iff_homExact : projective_iff_homExactType.{u,v,w} := by
  intro R _ P _ _
  constructor
  · intro h
    let := h
    intro A B C _ _ _ _ _ _ i p hi he hp
    obtain ⟨hinj, hex⟩ := P103.HomTensorExactness.homCovariant R A B C P i p hi he
    refine ⟨hinj, hex, ?_⟩
    intro g
    exact Module.projective_lifting_property p g hp
  · intro h
    apply (projective_iff_lifting R P).mpr
    intro M N _ _ _ _ f g hf
    obtain ⟨_, _, hsurj⟩ := h (LinearMap.ker f) M N (LinearMap.ker f).subtype f
      (kernel_injective f) (LinearMap.exact_subtype_ker_map f) hf
    exact hsurj g

theorem right_characterizations : right_characterizationsType.{u,v,w} := by
  intro R _ P _ _
  exact ⟨projective_iff_lifting Rᵐᵒᵖ P, projective_iff_splitting Rᵐᵒᵖ P,
    projective_iff_freeSummand Rᵐᵒᵖ P, projective_iff_homExact Rᵐᵒᵖ P⟩

end P103.Ch02.Projective
