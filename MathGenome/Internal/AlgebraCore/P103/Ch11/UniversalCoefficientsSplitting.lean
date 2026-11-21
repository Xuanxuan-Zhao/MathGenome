import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.UniversalCoefficientsSplitting
import MathGenome.Internal.AlgebraCore.P103.Ch11.UniversalCoefficientsHomology
import MathGenome.Internal.AlgebraCore.P103.Ch11.UniversalCoefficientsCohomology
import MathGenome.Internal.AlgebraCore.P103.Ch11.ArbitraryRankPIDSubmodules

namespace P103.Ch11.UniversalCoefficientsSplitting
open CategoryTheory
open P103.BalancedTensor
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Specs.Ch11.UniversalCoefficientsSplitting
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
variable {R : Type u} [Ring R]

/-- Boundary projectivity supplies the sections without any rank condition. -/
theorem boundary_sections : boundary_sectionsType.{u,v} := by
  intro R _ C h
  have hp : ∀ n, Module.Projective R (Q.previousBoundary C n) := by
    intro n
    cases n with
    | zero => change Module.Projective R (⊥ : Submodule R (C.X 0)); infer_instance
    | succ n => exact h n
  have hs : ∀ n, ∃ s : Q.previousBoundary C n →ₗ[R] C.X n,
      (Q.boundaryProjection C n).comp s = LinearMap.id := by
    intro n
    letI := hp n
    exact Module.projective_lifting_property _ LinearMap.id
      (UniversalCoefficientsCohomology.boundaryProjection_surjective C n)
  choose s hs using hs
  exact ⟨⟨s, hs⟩⟩

/-- Coordinates from the first basic short exact sequence. -/
def termCoordinates (C : Q.Ordinary.{u,v} R) (S : BoundarySections C) (n : ℕ) :
    (cycles C n × Q.previousBoundary C n) ≃ₗ[R] C.X n :=
  P103.Ch01.SplitSequences.splitting R _ _ _ (cycles C n).subtype
    (Q.boundaryProjection C n) Subtype.val_injective
    (UniversalCoefficientsCohomology.cycles_boundary_exact C n) (S.s n) (S.right_inv n)

theorem termCoordinates_apply (C : Q.Ordinary.{u,v} R) (S : BoundarySections C)
    (n : ℕ) (z : cycles C n) (b : Q.previousBoundary C n) :
    termCoordinates C S n (z,b) = z.val + S.s n b := rfl

theorem coordinates : coordinatesType.{u,v} := by
  intro R _ C S
  refine ⟨termCoordinates C S, termCoordinates_apply C S, ?_⟩
  intro n z b
  apply (termCoordinates C S n).injective
  rw [LinearEquiv.apply_symm_apply, termCoordinates_apply, termCoordinates_apply,
    map_zero, add_zero, map_add]
  have hz : (C.d (n+1) n).hom z.val = 0 := by
    have hh := z.property
    change (C.d (n+1) ((ComplexShape.down ℕ).next (n+1))).hom z.val = 0 at hh
    rwa [ChainComplex.next_nat_succ] at hh
  have hs := congrArg Subtype.val (LinearMap.congr_fun (S.right_inv (n+1)) b)
  change (C.d (n+1) n).hom (S.s (n+1) b) = b.val at hs
  rw [hz, zero_add]
  exact hs

/-- Tensoring a boundary section lifts every element of ker(j ⊗ 1) to a cycle. -/
def liftedTensorCycle (C : H.Complex.{u,v} R) (S : BoundarySections C)
    (M : ModuleCat.{w} R) (n : ℕ) :
    LinearMap.ker (H.jTensor C M n) →ₗ[ℤ] cycles (tensorComplex C M) (n+1) :=
  ((tensorMap (S.s (n+1)) (LinearMap.id : M →ₗ[R] M)).comp
    (LinearMap.ker (H.jTensor C M n)).subtype).codRestrict _ (by
      intro t
      change ((tensorComplex C M).d (n+1)
        ((ComplexShape.down ℕ).next (n+1))).hom
          (tensorMap (S.s (n+1)) (LinearMap.id : M →ₗ[R] M) t.val) = 0
      rw [ChainComplex.next_nat_succ]
      have he : ((tensorComplex C M).d (n+1) n).hom.comp
          (tensorMap (S.s (n+1)) (LinearMap.id : M →ₗ[R] M)) =
          (tensorMap (cycles C n).subtype (LinearMap.id : M →ₗ[R] M)).comp
            (H.jTensor C M n) := by
        apply tensor_hom_ext
        intro b m
        change tmul R ((C.d (n+1) n).hom (S.s (n+1) b)) m = tmul R b.val m
        have hs := congrArg Subtype.val (LinearMap.congr_fun (S.right_inv (n+1)) b)
        exact congrArg (fun c => tmul R c m) hs
      change (((tensorComplex C M).d (n+1) n).hom.comp _) t.val = 0
      rw [he]
      change tensorMap (cycles C n).subtype LinearMap.id (H.jTensor C M n t.val) = 0
      rw [show H.jTensor C M n t.val = 0 from t.property, map_zero])

theorem homology_splitting : homology_splittingType.{u,v,w} := by
  intro R _ C _ S M n P U
  let σ := (homologyClass (tensorComplex C M) (n+1)).comp
    ((liftedTensorCycle C S M n).comp U.kernelIso.toLinearMap)
  refine ⟨σ, ?_, fun x => ⟨liftedTensorCycle C S M n (U.kernelIso x), rfl, rfl⟩⟩
  apply LinearMap.ext
  intro x
  change U.β (σ x) = x
  apply U.kernelIso.injective
  apply Subtype.ext
  have hβ := UniversalCoefficientsHomology.beta_class_formula U
    (liftedTensorCycle C S M n (U.kernelIso x))
  change (U.kernelIso (U.β (σ x))).val = _ at hβ
  apply hβ.trans
  have he : (tensorMap
      (P103.Specs.Ch11.UniversalCoefficientsHomology.boundaryProjectionTerm C (n+1))
      (LinearMap.id : M →ₗ[R] M)).comp (tensorMap (S.s (n+1)) LinearMap.id) =
      LinearMap.id := by
    apply tensor_hom_ext
    intro b m
    change tmul R (Q.boundaryProjection C (n+1) (S.s (n+1) b)) m = tmul R b m
    rw [show Q.boundaryProjection C (n+1) (S.s (n+1) b) = b from
      LinearMap.congr_fun (S.right_inv (n+1)) b]
  exact LinearMap.congr_fun he (U.kernelIso x).val

theorem homology_zero_splitting : homology_zero_splittingType.{u,v,w} := by
  intro R _ C M U P
  refine ⟨⟨(LinearEquiv.ofBijective U.α U.bijective_α).symm.toLinearMap, ?_⟩,
    ⟨0, ?_⟩⟩
  · apply LinearMap.ext
    intro x
    exact (LinearEquiv.ofBijective U.α U.bijective_α).symm_apply_apply x
  · letI := U.zero_tor P
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _

theorem homology_projective : homology_projectiveType.{u,v,w} := by
  intro R _ C hC hp
  obtain ⟨S⟩ := boundary_sections C hp
  refine ⟨S, ?_⟩
  intro M n P
  obtain ⟨U⟩ := UniversalCoefficientsHomology.positiveSequence_exists C hC M n P
  obtain ⟨σ,hσ,_⟩ := homology_splitting C hC S M n P U
  exact ⟨U,σ,hσ⟩

/-- The cycle component of the coordinates fixed by S. -/
def cycleRetraction (C : Q.Ordinary.{u,v} R) (S : BoundarySections C) (n : ℕ) :
    C.X n →ₗ[R] cycles C n :=
  (LinearMap.fst R (cycles C n) (Q.previousBoundary C n)).comp
    (termCoordinates C S n).symm.toLinearMap

theorem cycleRetraction_coordinates (C : Q.Ordinary.{u,v} R) (S : BoundarySections C)
    (n : ℕ) (a : cycles C n) (b : Q.previousBoundary C n) :
    cycleRetraction C S n (a.val + S.s n b) = a := by
  change ((termCoordinates C S n).symm (termCoordinates C S n (a,b))).1 = a
  rw [LinearEquiv.symm_apply_apply]

theorem cycleRetraction_cycle (C : Q.Ordinary.{u,v} R) (S : BoundarySections C)
    (n : ℕ) (a : cycles C n) : cycleRetraction C S n a.val = a := by
  simpa using cycleRetraction_coordinates C S n a 0

/-- Extend along the cycle retraction, giving zero on the boundary-section summand. -/
def extendedCocycle (C : Q.Ordinary.{u,v} R) (S : BoundarySections C)
    (M : ModuleCat.{w} R) (n : ℕ) :
    (Homology C n →ₗ[R] M) →ₗ[ℤ] cycles (homComplex C M) n :=
  (P103.HomTensorExactness.pre (Q := M)
    ((homologyClass C n).comp (cycleRetraction C S n))).toIntLinearMap.codRestrict _ (by
      intro h
      change ((homComplex C M).d n ((ComplexShape.up ℕ).next n)).hom
        (h.comp ((homologyClass C n).comp (cycleRetraction C S n))) = 0
      rw [CochainComplex.next]
      change (h.comp ((homologyClass C n).comp (cycleRetraction C S n))).comp
        (C.d (n+1) n).hom = 0
      ext y
      let b := P103.Specs.Ch11.UniversalCoefficientsCohomology.incomingProjection C n y
      change h (homologyClass C n (cycleRetraction C S n (Q.j C n b).val)) = 0
      rw [cycleRetraction_cycle,
        UniversalCoefficientsCohomology.homologyClass_boundary, map_zero])

theorem cohomology_splitting : cohomology_splittingType.{u,v,w} := by
  intro R _ C S M n β hβ
  let σ := (homologyClass (homComplex C M) n).comp (extendedCocycle C S M n)
  refine ⟨σ, ?_, ?_⟩
  · apply LinearMap.ext
    intro h
    apply (cycleBoundaries C n).quot_hom_ext
    intro a
    change β (homologyClass _ n (extendedCocycle C S M n h))
      (homologyClass C n a) = h (homologyClass C n a)
    rw [hβ]
    change h (homologyClass C n (cycleRetraction C S n a.val)) = _
    rw [cycleRetraction_cycle]
  · intro h
    refine ⟨extendedCocycle C S M n h, rfl, ?_⟩
    intro a b
    change h (homologyClass C n (cycleRetraction C S n (a.val + S.s n b))) = _
    rw [cycleRetraction_coordinates]

theorem cohomology_projective : cohomology_projectiveType.{u,v,w} := by
  intro R _ C hC S M n N hN
  obtain ⟨e,α,β,he,hseq,hi,hex,hs⟩ :=
    UniversalCoefficientsCohomology.universal_coefficients C hC M n N hN
  obtain ⟨σ,hσ,_⟩ := cohomology_splitting C S M (n+1) β hseq.2.1
  exact ⟨e,α,β,σ,he,hseq,hi,hex,hs,hσ⟩

theorem pid_free : pid_freeType.{u,v} := by
  intro R _ _ _ C hC n
  letI := hC n
  exact ⟨ArbitraryRankPIDSubmodules.free_submodule R (C.X n) (cycles C n),
    ArbitraryRankPIDSubmodules.free_submodule R (C.X n) (boundaries C n)⟩

theorem pid_homology : pid_homologyType.{u,v,w} := by
  intro R _ _ _ C hC
  letI : IsPrincipalIdealRing Rᵐᵒᵖ := IsPrincipalIdealRing.of_surjective
    (RingEquiv.toOpposite R).toRingHom (RingEquiv.toOpposite R).surjective
  have hf := pid_free C hC
  have hp : ∀ n, Module.Projective Rᵐᵒᵖ (boundaries C n) := by
    intro n
    letI := (hf n).2
    infer_instance
  have hflat : H.FlatTermsAndBoundaries.{u,v,w} C := by
    constructor
    · intro n
      letI := hC n
      exact (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R (C.X n)).mpr
        (P103.Ch02.FlatnessTests.projective_flat Rᵐᵒᵖ (C.X n) inferInstance)
    · intro n
      exact (P103.Ch02.FlatnessTests.rightFlat_iff_opposite R (boundaries C n)).mpr
        (P103.Ch02.FlatnessTests.projective_flat Rᵐᵒᵖ (boundaries C n) (hp n))
  obtain ⟨S,hS⟩ := homology_projective C hflat hp
  refine ⟨hflat, S, ?_⟩
  intro M
  exact ⟨UniversalCoefficientsHomology.zeroSequence_exists C hflat M, hS M⟩

theorem pid_cohomology : pid_cohomologyType.{u,v} := by
  intro R _ _ _ C hC
  have hf := pid_free C hC
  have hp : Q.ProjectiveTermsAndBoundaries C := by
    constructor
    · intro n
      letI := hC n
      infer_instance
    · intro n
      letI := (hf n).2
      infer_instance
  exact ⟨hp, boundary_sections C hp.2⟩

/-- Actions on the two tensor factors commute, directly on elementary tensors. -/
theorem tensorMap_comm {A A' B : Type*} [AddCommGroup A] [AddCommGroup A']
    [AddCommGroup B] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ A'] [Module R B]
    (f : A →ₗ[Rᵐᵒᵖ] A') (g : B →ₗ[R] B) :
    (tensorMap f (LinearMap.id : B →ₗ[R] B)).comp (tensorMap LinearMap.id g) =
      (tensorMap LinearMap.id g).comp (tensorMap f LinearMap.id) := by
  apply tensor_hom_ext
  intro a b
  rfl

theorem homology_scalar_splitting : homology_scalar_splittingType.{u,v,w} := by
  intro K _ U C hC S M
  have hsc := UniversalCoefficientsHomology.scalar_compatibility K U C hC M
  constructor
  · let A := U.zero C hC M
    let e := LinearEquiv.ofBijective A.α A.bijective_α
    refine ⟨e.symm.toLinearMap, ?_, ?_⟩
    · apply LinearMap.ext
      intro x
      exact e.symm_apply_apply x
    · intro r x
      apply e.injective
      change e (e.symm _) = A.α (tensorMap LinearMap.id (scalarMap M r).hom (e.symm x))
      rw [e.apply_symm_apply]
      have hh := LinearMap.congr_fun (hsc.1 r) (e.symm x)
      change homologyMap (tensorSecondMap C (scalarMap M r).hom) 0 (e (e.symm x)) =
        A.α (tensorMap LinearMap.id (scalarMap M r).hom (e.symm x)) at hh
      rwa [e.apply_symm_apply] at hh
  · intro n P T
    letI := torModule T P M
    let V := U.positive C hC M n P
    obtain ⟨σ,hσ,hrep⟩ := homology_splitting C hC S M n P V
    refine ⟨σ,hσ,?_⟩
    intro r x
    obtain ⟨z,hz,hclass⟩ := hrep x
    obtain ⟨zr,hzr,hclassr⟩ := hrep (r • x)
    let zg := cyclesMap (tensorSecondMap C (scalarMap M r).hom) (n+1) z
    have hsx : V.β (homologyClass _ (n+1) z) = x := by
      rw [← hclass]
      exact LinearMap.congr_fun hσ x
    have hzg : V.β (homologyClass _ (n+1) zg) = r • x := by
      change V.β (homologyMap (tensorSecondMap C (scalarMap M r).hom) (n+1)
        (homologyClass _ (n+1) z)) = r • x
      rw [(hsc.2 n P T).2 r, hsx]
    have hk := UniversalCoefficientsHomology.beta_class_formula V zg
    rw [hzg] at hk
    have hk0 := UniversalCoefficientsHomology.beta_class_formula V z
    rw [hsx] at hk0
    have hk' : (V.kernelIso (r • x)).val =
        tensorMap LinearMap.id (scalarMap M r).hom (V.kernelIso x).val := by
      calc
        _ = tensorMap
            (P103.Specs.Ch11.UniversalCoefficientsHomology.boundaryProjectionTerm C (n+1))
            LinearMap.id (tensorMap LinearMap.id (scalarMap M r).hom z.val) := hk
        _ = tensorMap LinearMap.id (scalarMap M r).hom
            (tensorMap
              (P103.Specs.Ch11.UniversalCoefficientsHomology.boundaryProjectionTerm C (n+1))
              LinearMap.id z.val) := LinearMap.congr_fun (tensorMap_comm _ _) z.val
        _ = _ := congrArg (tensorMap LinearMap.id (scalarMap M r).hom) hk0.symm
    rw [hclassr, hclass]
    change homologyClass _ (n+1) zr = homologyClass _ (n+1) zg
    apply congrArg (homologyClass _ (n+1))
    apply Subtype.ext
    change zr.val = tensorMap LinearMap.id (scalarMap M r).hom z.val
    rw [hzr, hk', hz]
    exact LinearMap.congr_fun (tensorMap_comm (S.s (n+1)) (scalarMap M r).hom)
      (V.kernelIso x).val

theorem cohomology_scalar_splitting : cohomology_scalar_splittingType.{u,v,w} := by
  intro K _ C S M n β hβ
  letI := P103.Specs.Ch11.UniversalCoefficientsCohomology.cohomologyModule C M n
  obtain ⟨σ,hσ,hrep⟩ := cohomology_splitting C S M n β hβ
  have hlin : ∀ (r : K) h, σ (r • h) = r • σ h := by
    intro r h
    obtain ⟨z,hclass,hformula⟩ := hrep h
    obtain ⟨zr,hclassr,hformular⟩ := hrep (r • h)
    rw [hclassr,hclass]
    change homologyClass _ n zr = homologyClass _ n
      (cyclesMap (homPostMap C (scalarMap M r).hom) n z)
    apply congrArg (homologyClass _ n)
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    obtain ⟨⟨a,b⟩,rfl⟩ := (termCoordinates C S n).surjective y
    change P103.Specs.Ch11.UniversalCoefficientsCohomology.homTerm C M n zr.val
        (a.val + S.s n b) =
      r • P103.Specs.Ch11.UniversalCoefficientsCohomology.homTerm C M n z.val
        (a.val + S.s n b)
    rw [hformular,hformula]
    rfl
  exact ⟨{ toFun := σ, map_add' := σ.map_add, map_smul' := hlin }, hσ⟩

theorem pid_cohomology_sequences : pid_cohomology_sequencesType.{u,v,w} := by
  intro R _ _ _ C hC
  obtain ⟨hp, ⟨S⟩⟩ := pid_cohomology C hC
  refine ⟨S, ?_, ?_⟩
  · intro M
    obtain ⟨e,he⟩ := UniversalCoefficientsCohomology.degree_zero C M
    obtain ⟨σ,hσ,_⟩ := cohomology_splitting C S M 0 e.toLinearMap he
    exact ⟨e,he,σ,hσ⟩
  · intro M n N hN
    exact cohomology_projective C hp S M n N hN

end
end P103.Ch11.UniversalCoefficientsSplitting
