import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedCongruencePointTopology

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj WithZero TensorProduct

set_option linter.style.haveILetI false

namespace LinearAlgebraicGroups.Arithmetic.RamifiedCongruencePointTopology

open _root_.LinearAlgebraicGroups.Specs
open IntegralSemisimpleModel ExceptionalIwahoriCongruence
open ExceptionalAffineBruhat ExceptionalAffineBuilding
open RamifiedCongruencePointTopology
open ValuativeRel

universe u v

noncomputable section

private theorem pointAlgebra_changeRing (B : IntegralAlgebra.{u}) {X : IntegralScheme.{u}}
    (iso : integralSpec.obj (op B) ≅ X) {R S : IntegralAlgebra.{u}}
    (f : R ⟶ S) (p : integralSpec.obj (op R) ⟶ X) :
    (pointAlgebraEquiv B iso S).symm (changeRing f p) =
      f.hom.comp ((pointAlgebraEquiv B iso R).symm p) := by
  obtain ⟨a, rfl⟩ := (pointAlgebraEquiv B iso R).surjective p
  rw [Equiv.symm_apply_apply]
  apply (pointAlgebraEquiv B iso S).injective
  rw [Equiv.apply_symm_apply]
  change integralSpec.map f.op ≫ integralSpec.map (CommAlgCat.ofHom a).op ≫ iso.hom =
    integralSpec.map (CommAlgCat.ofHom (f.hom.comp a)).op ≫ iso.hom
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  rfl

private theorem pointAlgebra_postcompose (B C : IntegralAlgebra.{u})
    {X Y : IntegralScheme.{u}}
    (b : integralSpec.obj (op B) ≅ X) (c : integralSpec.obj (op C) ≅ Y) (m : X ⟶ Y) :
    ∃ f : C →ₐ[Integers.{u}] B, ∀ (R : IntegralAlgebra.{u})
      (p : integralSpec.obj (op R) ⟶ X),
      (pointAlgebraEquiv C c R).symm (p ≫ m) =
        ((pointAlgebraEquiv B b R).symm p).comp f := by
  let S := algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})
  let f := S.preimage (b.hom ≫ m ≫ c.inv)
  have hf : integralSpec.map f = b.hom ≫ m ≫ c.inv := S.map_preimage _
  refine ⟨f.unop.hom, fun R p => ?_⟩
  obtain ⟨a, rfl⟩ := (pointAlgebraEquiv B b R).surjective p
  rw [Equiv.symm_apply_apply]
  apply (pointAlgebraEquiv C c R).injective
  rw [Equiv.apply_symm_apply]
  change (integralSpec.map (CommAlgCat.ofHom a).op ≫ b.hom) ≫ m =
    integralSpec.map (CommAlgCat.ofHom (a.comp f.unop.hom)).op ≫ c.hom
  rw [show (CommAlgCat.ofHom (a.comp f.unop.hom)).op = (CommAlgCat.ofHom a).op ≫ f by
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    rfl]
  simp [hf, Category.assoc]

private theorem continuous_markedPoints_iff {P : Type*} [TopologicalSpace P]
    {K : Type u} [Field K] [TopologicalSpace K] {X : IntegralScheme.{u}}
    (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (op B) ≅ X)
    (f : P → (integralSpec.obj (op (integralRing K)) ⟶ X)) :
    letI := markedPointTopology B iso K
    Continuous f ↔ ∀ a : B, Continuous fun z =>
      (pointAlgebraEquiv B iso (integralRing K)).symm (f z) a := by
  change @Continuous _ _ _ (TopologicalSpace.induced _ (TopologicalSpace.induced _ _)) f ↔ _
  rw [continuous_induced_rng, continuous_induced_rng, continuous_pi_iff]
  rfl

private theorem continuous_markedEvaluation
    {K : Type u} [Field K] [TopologicalSpace K] {X : IntegralScheme.{u}}
    (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (op B) ≅ X) (b : B) :
    letI := markedPointTopology B iso K
    Continuous (fun p : integralSpec.obj (op (integralRing K)) ⟶ X =>
      (pointAlgebraEquiv B iso (integralRing K)).symm p b) := by
  letI := markedPointTopology B iso K
  exact (continuous_markedPoints_iff (K := K) B iso
    (@id (integralSpec.obj (op (integralRing K)) ⟶ X))).mp continuous_id b

/-- A continuous field embedding gives a continuous scalar map in the
marked point topology. -/
private theorem continuous_markedChangeRing {K E : Type u} [Field K] [Field E]
    [TopologicalSpace K] [TopologicalSpace E]
    (f : K →+* E) (hf : Continuous f) {X : IntegralScheme.{u}}
    (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (op B) ≅ X) :
    letI := markedPointTopology B iso K
    letI := markedPointTopology B iso E
    Continuous (changeRing (integralRingMap f) (X := X)) := by
  letI := markedPointTopology B iso K
  letI := markedPointTopology B iso E
  apply (continuous_markedPoints_iff B iso _).mpr
  intro b
  letI : Algebra Integers.{u} E := (integralRing E).algebra
  have he (p : integralSpec.obj (op (integralRing K)) ⟶ X) :
      (pointAlgebraEquiv B iso (integralRing E)).symm (changeRing (integralRingMap f) p) b =
        f ((pointAlgebraEquiv B iso (integralRing K)).symm p b) :=
    congrArg (fun a : B →ₐ[Integers.{u}] E => a b)
      (pointAlgebra_changeRing B iso (integralRingMap f) p)
  simpa only [he, Function.comp_def] using hf.comp (continuous_markedEvaluation B iso b)

open ExceptionalLocalRootCoordinates (normalizedValuation)
open scoped Topology

private theorem continuous_of_valuation_power {K E : Type*} [Field K] [Field E]
    [ValuativeRel K] [ValuativeRel E] [TopologicalSpace K] [TopologicalSpace E]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
    (f : K →+* E) {d : ℕ} (hd : 0 < d)
    (hf : ∀ x, normalizedValuation E (f x) = normalizedValuation K x ^ d) :
    Continuous f := by
  apply continuous_of_continuousAt_zero f
  change Filter.Tendsto f (𝓝 (0 : K)) (𝓝 (f 0))
  rw [map_zero]
  apply ((IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero' E)).mpr
  intro radius hradius
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E
  let k := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let a := min 1 (e radius)
  have ha : a ≠ 0 := ne_of_gt
    (lt_min (by simp) (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hradius)))
  refine ⟨k.symm a, (map_ne_zero _).mpr ha, fun z hz => ?_⟩
  have hz' : normalizedValuation K z < a := by
    change valuation K z < k.symm a at hz
    have h := k.strictMono hz
    rwa [k.apply_symm_apply] at h
  change valuation E (f z) < radius
  apply e.strictMono.lt_iff_lt.mp
  change normalizedValuation E (f z) < e radius
  rw [hf]
  apply lt_of_le_of_lt _ (hz'.trans_le (min_le_right _ _))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [pow_succ']
  exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le (hz'.le.trans (min_le_left _ _)))

private theorem isClosed_valuationIdealPower {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : (valuation K).valuationSubring) (hπ : (valuation K).IsUniformizer (π : K))
    (n : ℕ) :
    IsClosed (Set.range fun z : ↥(IsLocalRing.maximalIdeal ((valuation K).valuationSubring) ^ n) =>
      ((z : (valuation K).valuationSubring) : K)) := by
  let O := (valuation K).valuationSubring
  letI : CompactSpace O := inferInstanceAs (CompactSpace (Valuation.integer (valuation K)))
  have hfactor (z : O) : z ∈ IsLocalRing.maximalIdeal O ^ n ↔ ∃ b, z = π ^ n * b := by
    rw [hπ.is_generator, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rfl
  have he : (Set.range fun z : ↥(IsLocalRing.maximalIdeal O ^ n) => ((z : O) : K)) =
      Set.range (fun b : O => (π : K) ^ n * (b : K)) := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := (hfactor (a : O)).mp a.2
      exact ⟨b, (congrArg (fun z : O => (z : K)) hb).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨π ^ n * b, (hfactor _).mpr ⟨b, rfl⟩⟩, rfl⟩
  rw [he]
  exact (isCompact_range (continuous_const.mul (continuous_subtype_val : Continuous fun b : O => (b : K)))).isClosed

private theorem isClosed_pointReductionKernel {P : Type*} [Group P] [TopologicalSpace P]
    {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : (valuation K).valuationSubring) (hπ : (valuation K).IsUniformizer (π : K))
    (G : IntegralGroup.{u}) (B : IntegralAlgebra.{u}) (iso : integralSpec.obj (op B) ≅ G.X)
    (p : P →* IntegralPoints G (localIntegers K))
    (hcont : letI := markedPointTopology B iso K
      Continuous (fun g => changeRingHom G (localIntegersInclusion K) (p g))) (n : ℕ) :
    IsClosed (((changeRingHom G (congruenceHom (localIntegers K) n)).comp p).ker : Set P) := by
  let O := localIntegers K
  letI : Algebra Integers.{u} K := (integralRing K).algebra
  let I := IsLocalRing.maximalIdeal O ^ n
  let f := congruenceHom O n
  let j := localIntegersInclusion K
  let i := pointAlgebraEquiv B iso (integralRing K)
  let q (a : B) (g : P) := i.symm (changeRingHom G j (p g)) a
  let Z : Set K := Set.range fun z : I => ((z : O) : K)
  have hZ : IsClosed Z := isClosed_valuationIdealPower π hπ n
  have hl (b : O) : (b : K) ∈ Z ↔ b ∈ I := by
    constructor
    · rintro ⟨a, ha⟩
      obtain rfl : (a : O) = b := Subtype.ext ha
      exact a.2
    · intro hb
      exact ⟨⟨b, hb⟩, rfl⟩
  have hq (a : B) (g : P) : q a g = ((pointAlgebraEquiv B iso O).symm (p g) a : K) :=
    congrArg (fun f : B →ₐ[Integers.{u}] K => f a)
      (pointAlgebra_changeRing B iso j (p g))
  have hR : (((changeRingHom G f).comp p).ker : Set P) =
      ⋂ a : B, (fun g => q a g - q a 1) ⁻¹' Z := by
    ext g
    change changeRingHom G f (p g) = 1 ↔ _
    have hone : changeRingHom G f (p 1) = 1 := by
      exact (congrArg (changeRingHom G f) (p.map_one)).trans ((changeRingHom G f).map_one)
    rw [← hone]
    rw [← (pointAlgebraEquiv B iso (congruenceRing O n)).symm.injective.eq_iff]
    change (pointAlgebraEquiv B iso _).symm (changeRing f (p g)) =
      (pointAlgebraEquiv B iso _).symm (changeRing f (p 1)) ↔ _
    rw [pointAlgebra_changeRing, pointAlgebra_changeRing, AlgHom.ext_iff, Set.mem_iInter]
    simp only [Set.mem_preimage, AlgHom.comp_apply, hq]
    apply forall_congr'
    intro a
    let x := (pointAlgebraEquiv B iso O).symm (p g) a
    let y := (pointAlgebraEquiv B iso O).symm (p 1) a
    change Ideal.Quotient.mk I x = Ideal.Quotient.mk I y ↔ (((x - y : O) : K) ∈ Z)
    exact Ideal.Quotient.eq.trans (hl (x - y)).symm
  rw [hR]
  refine isClosed_iInter fun a => hZ.preimage ?_
  letI := markedPointTopology B iso K
  exact ((continuous_markedEvaluation B iso a).comp hcont).sub continuous_const

theorem presentationIndependent : PresentationIndependent.{u} := by
  intro X B B' e e' K _ _
  suffices step : ∀ (A A' : IntegralAlgebra.{u})
      (a : integralSpec.obj (op A) ≅ X) (a' : integralSpec.obj (op A') ≅ X),
      markedPointTopology A a K ≤ markedPointTopology A' a' K by
    exact le_antisymm (step B B' e e') (step B' B e' e)
  intro A A' a a'
  apply continuous_id_iff_le.mp
  letI := markedPointTopology A a K
  apply (continuous_markedPoints_iff A' a' id).mpr
  obtain ⟨f, hf⟩ := pointAlgebra_postcompose A A' a a' (𝟙 X)
  simp only [Category.comp_id] at hf
  intro b
  simp only [id_eq, hf, AlgHom.comp_apply]
  exact continuous_markedEvaluation A a (f b)

theorem finiteTypePresentation : FiniteTypePresentation.{u} := by
  intro D M
  obtain ⟨B, ⟨e⟩⟩ := essImage_algSpec.mpr M.affine
  refine ⟨B.unop, ?_, ⟨e⟩⟩
  haveI := M.locallyOfFinitePresentation
  haveI : IsIso e.hom.left := by
    change IsIso ((Over.forget _).map e.hom)
    infer_instance
  have h : LocallyOfFiniteType ((integralSpec.obj B).hom) := by
    rw [← Over.w e.hom]
    infer_instance
  let f := CommRingCat.ofHom (algebraMap Integers.{u} B.unop)
  have h' : LocallyOfFiniteType (Spec.map f) := h
  exact RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h')

private theorem continuous_convolutionEvaluation
    {P R A K : Type*} [TopologicalSpace P] [CommRing R] [CommRing A]
    [Bialgebra R A] [CommRing K] [Algebra R K] [TopologicalSpace K] [IsTopologicalRing K]
    (f g : P → WithConv (A →ₐ[R] K))
    (hf : ∀ a, Continuous fun z => f z a) (hg : ∀ a, Continuous fun z => g z a)
    (a : A) : Continuous fun z => (f z * g z) a := by
  let r := Coalgebra.Repr.arbitrary R a
  have he (z : P) : (f z * g z) a =
      ∑ i ∈ r.index, f z (r.left i) * g z (r.right i) := by
    change (toConv (f z).ofConv.toLinearMap * toConv (g z).ofConv.toLinearMap :
      WithConv (A →ₗ[R] K)) a = _
    exact r.convMul_apply _ _
  simp only [he]
  exact continuous_finsetSum _ fun i _ => (hf (r.left i)).mul (hg (r.right i))

set_option maxHeartbeats 800000 in
open scoped RingTheory.LinearMap in
theorem markedPointGroup : MarkedPointGroup.{u} := by
  intro K _ _ _ H B e
  have hAffine : IsAffine H.X.left :=
    (essImage_algSpec (R := CommRingCat.of Integers.{u}) (G := H.X)).mp ⟨op B, ⟨e⟩⟩
  obtain ⟨A, ⟨i⟩⟩ := (essImage_hopfSpec (R := CommRingCat.of Integers.{u}) (G := H)).mpr hAffine
  let R := integralRing K
  letI : Algebra Integers.{u} R := R.algebra
  let H₀ := (hopfSpec (CommRingCat.of Integers.{u})).obj A
  let B₀ := CommAlgCat.of Integers.{u} A.unop
  let i₀ : integralSpec.obj (op B₀) ≅ H.X := (Grp.forget IntegralScheme).mapIso i
  let toHopfPoints : IntegralPoints H R →* IntegralPoints H₀ R :=
    ((yonedaGrp.map i.inv).app (op (integralSpec.obj (op R)))).hom
  let φ : WithConv (B₀ →ₐ[Integers.{u}] R) ≃* IntegralPoints H₀ R := Spec.mapMulEquiv
  let q : IntegralPoints H R →* WithConv (B₀ →ₐ[Integers.{u}] R) :=
    φ.symm.toMonoidHom.comp toHopfPoints
  have hq (z : IntegralPoints H R) :
      (q z).ofConv = (pointAlgebraEquiv B₀ i₀ R).symm z := by
    apply (pointAlgebraEquiv B₀ i₀ R).injective
    rw [Equiv.apply_symm_apply]
    change φ (q z) ≫ i₀.hom = z
    rw [show φ (q z) = toHopfPoints z from φ.apply_symm_apply _]
    change (z ≫ i₀.inv) ≫ i₀.hom = z
    simp
  rw [presentationIndependent B B₀ e i₀ K]
  letI : TopologicalSpace (IntegralPoints H R) := markedPointTopology B₀ i₀ K
  have heq (z : IntegralPoints H R) (b : B₀) :
      q z b = (pointAlgebraEquiv B₀ i₀ R).symm z b :=
    congrArg (fun a : B₀ →ₐ[Integers.{u}] R => a b) (hq z)
  have heval (b : B₀) : Continuous fun z : IntegralPoints H R => q z b := by
    simp only [heq]
    exact continuous_markedEvaluation (K := K) B₀ i₀ b
  change IsTopologicalGroup (IntegralPoints H R)
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · apply (continuous_markedPoints_iff (K := K) B₀ i₀ _).mpr
    intro b
    change Continuous fun z : IntegralPoints H R × IntegralPoints H R =>
      (pointAlgebraEquiv B₀ i₀ R).symm (z.1 * z.2) b
    simp only [← heq, map_mul]
    exact continuous_convolutionEvaluation (q ∘ Prod.fst) (q ∘ Prod.snd)
      (fun a => (heval a).comp continuous_fst) (fun a => (heval a).comp continuous_snd) b
  · apply (continuous_markedPoints_iff (K := K) B₀ i₀ _).mpr
    intro b
    obtain ⟨f, hf⟩ := pointAlgebra_postcompose B₀ B₀ i₀ i₀ (GrpObj.inv (X := H.X))
    change Continuous fun z : IntegralPoints H R =>
      (pointAlgebraEquiv B₀ i₀ R).symm (z ≫ GrpObj.inv) b
    simp only [hf, AlgHom.comp_apply]
    exact continuous_markedEvaluation (K := K) B₀ i₀ (f b)

theorem markedScalarContinuity : MarkedScalarContinuity.{u} := by
  constructor
  · intro K E _ _ _ _ f hf X B e
    exact continuous_markedChangeRing f hf B e
  · intro K E _ _ _ _ _ _ _ _ f d hd hf
    exact continuous_of_valuation_power f hd hf

private theorem finiteTypeCanonical (B : IntegralAlgebra.{u})
    (h : Algebra.FiniteType Integers.{u} B) :
    @Algebra.FiniteType Integers.{u} B _ _ (integerAlgebra B) := by
  have he : B.algebra = integerAlgebra B := by
    apply Algebra.algebra_ext
    intro z
    have hz : z = (z.down : Integers.{u}) := by
      exact ULift.up_intCast _
    rw [hz, map_intCast, map_intCast]
  exact he ▸ h

theorem compactParahoric : CompactParahoric.{u,v} := by
  intro K _ _ _ _ D M G Wf V J _ _ _ _ j A p C Y T hT B e
  letI : TopologicalSpace (FieldPoints M K) := markedPointTopology B e K
  letI : TopologicalSpace G := TopologicalSpace.induced j (markedPointTopology B e K)
  letI : IsTopologicalGroup (FieldPoints M K) := markedPointGroup M.group B e
  letI : IsTopologicalGroup G := isTopologicalGroup_induced j
  have hI : IsCompact (C.I : Set G) := by
    obtain ⟨B', hB', ⟨e'⟩⟩ := finiteTypePresentation M.toIntegralMarking
    have h := (@C.compact_open B' (finiteTypeCanonical B' hB') e').1
    have he := presentationIndependent B' B e' e K
    exact Eq.mp (congrArg (fun t =>
      @IsCompact G (TopologicalSpace.induced j t) (C.I : Set G)) he) h
  have hP : IsCompact (parahoric C T : Set G) := by
    letI := Y.realization.finite_wall_group T hT
    rw [show (parahoric C T : Set G) = _ from Y.realization.face_union T]
    exact isCompact_iUnion fun w => by
      rw [DoubleCoset.doubleCoset_eq_image2, ← Set.image_uncurry_prod]
      exact (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  exact ⟨inferInstance, hP, inferInstance, isCompact_iff_compactSpace.mp hP⟩

theorem closedParahoricReductionKernel : ClosedParahoricReductionKernel.{u,v} := by
  intro K E _ _ _ _ _ _ _ _ D M G Wf V J _ _ _ _ j A p C T B e ξ hξ f hf s q hq
  letI : TopologicalSpace (FieldPoints M K) := markedPointTopology B e K
  letI : TopologicalSpace (FieldPoints M E) := markedPointTopology B e E
  letI : TopologicalSpace G := TopologicalSpace.induced j (markedPointTopology B e K)
  letI : IsTopologicalGroup (FieldPoints M E) := markedPointGroup M.group B e
  intro n
  apply isClosed_pointReductionKernel ξ hξ M.group B e q _ n
  simp only [hq]
  have hj : Continuous (j : G → FieldPoints M K) := continuous_induced_dom
  have h := (continuous_markedChangeRing f hf B e).comp (hj.comp
    (continuous_subtype_val : Continuous (Subtype.val : parahoric C T → G)))
  exact (continuous_const.mul h).mul continuous_const

theorem parahoricCoefficientContinuity : ParahoricCoefficientContinuity.{u,v} := by
  intro K _ _ _ _ D M G Wf V J _ _ _ _ j A p C T B e σ hσ τ hτ
  letI : TopologicalSpace (FieldPoints M K) := markedPointTopology B e K
  letI : TopologicalSpace G := TopologicalSpace.induced j (markedPointTopology B e K)
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  change Continuous (fun g : parahoric C T => j (τ g))
  simp only [hτ]
  have hj : Continuous (j : G → FieldPoints M K) := continuous_induced_dom
  exact (continuous_markedChangeRing σ.toRingHom hσ B e).comp (hj.comp
    (continuous_subtype_val : Continuous (Subtype.val : parahoric C T → G)))

end

end LinearAlgebraicGroups.Arithmetic.RamifiedCongruencePointTopology
