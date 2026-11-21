import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExtShiftedHom

/-!
HA-R13, boundary conclusions. The triangle closes with the negative cone
projection. Unsigned Hom connecting maps are characterized by extending a
cocycle and descending its differential, or by lifting it and taking its
differential. We prove these representative formulas before transporting
them through the canonical HA-R11 comparison. The representative existence
lemmas justify their use for every cocycle in injective models.

The general complex formulas need no injectivity or boundedness. The
specializations consequently apply to every bounded-below injective model
without imposing enough injectives on the ambient abelian category.
-/

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe w v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open CochainComplex HomComplex
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom
open Specs.AdvancedHomologicalAlgebra.ExtBoundarySigns

namespace AdvancedHomologicalAlgebra.ExtBoundarySigns

theorem triangle_second : triangleSecondType := by
  intro A _ _ _ S hS X n x
  exact preadditiveCoyoneda_homologySequenceδ_apply hS.singleTriangle n (n+1) rfl x

theorem triangle_first : triangleFirstType := by
  intro A _ _ _ S hS Y n x
  exact preadditiveYoneda_homologySequenceδ_apply hS.singleTriangle n (n+1) rfl x

theorem positive_projection : positiveProjectionType := by
  intro A _ _ _ S hS
  let := mappingCone.quasiIso_descShortComplex hS
  simp [Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift,
    _root_.DerivedCategory.triangleOfSESδ]

section Cochains
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Composition of cocycles uses the ordinary, unsigned composition of graded maps. -/
noncomputable def cocycleComp {K L M : CochainComplex A ℤ} {a b c : ℤ}
    (z : Cocycle K L a) (t : Cocycle L M b) (h : a+b=c) : Cocycle K M c :=
  Cocycle.mk (z.1.comp t.1 h) (c+1) rfl (by
    rw [δ_comp z.1 t.1 h (a+1) (b+1) (c+1) rfl rfl rfl]
    simp)

omit [HasDerivedCategory A] in
lemma cocycleComp_toHom {K L M : CochainComplex A ℤ} {a b c : ℤ}
    (z : Cocycle K L a) (t : Cocycle L M b) (h : a+b=c) :
    Cocycle.equivHomShift.symm (cocycleComp z t h) =
      ShiftedHom.comp (Cocycle.equivHomShift.symm z)
        (Cocycle.equivHomShift.symm t) (by omega) := by
  ext p
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf,
    Cochain.rightShift_v, cocycleComp, Cochain.comp, ShiftedHom.comp,
    CochainComplex.shiftFunctor_map_f', CochainComplex.shiftFunctorAdd'_inv_app_f',
    Cochain.v_comp_XIsoOfEq_hom, CochainComplex.shiftFunctorObjXIso]

lemma classToDerived_comp {K L M : CochainComplex A ℤ} {a b c : ℤ}
    (z : Cocycle K L a) (t : Cocycle L M b) (h : a+b=c) :
    classToDerived K M c (CohomologyClass.mk (cocycleComp z t h)) =
      ShiftedHom.comp (classToDerived K L a (CohomologyClass.mk z))
        (classToDerived L M b (CohomologyClass.mk t)) (by omega) := by
  simp only [AdvancedHomologicalAlgebra.ExtShiftedHom.classToDerived_mk,
    cocycleComp_toHom]
  exact ShiftedHom.map_comp _ _ _ _

omit [HasDerivedCategory A] in
lemma precomp_cone_quotient {S : ShortComplex (CochainComplex A ℤ)}
    {K : CochainComplex A ℤ} {n : ℤ} (v : Cocycle S.X₃ K n) :
    (v.precomp (mappingCone.descShortComplex S)).1 =
      (mappingCone.snd S.f).comp ((v.precomp S.g).1) (zero_add n) := by
  simp [Cocycle.precomp, mappingCone.descShortComplex, mappingCone.ofHom_desc,
    mappingCone.descCochain]

omit [HasDerivedCategory A] in
lemma first_cone_classes {S : ShortComplex (CochainComplex A ℤ)}
    {K : CochainComplex A ℤ} {n : ℤ}
    (u : Cocycle S.X₁ K n) (v : Cocycle S.X₃ K (n+1))
    (w : Cochain S.X₂ K n)
    (hf : (Cochain.ofHom S.f).comp w (zero_add n) = u.1)
    (hw : δ n (n+1) w = (v.precomp S.g).1) :
    CohomologyClass.mk (v.precomp (mappingCone.descShortComplex S)) =
      (n+1).negOnePow • CohomologyClass.mk
        (cocycleComp (-mappingCone.fst S.f) u (by omega)) := by
  apply sub_eq_zero.mp
  rw [Units.smul_def, ← CohomologyClass.mk_smul, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]
  refine ⟨mappingCone.descCochain S.f (0 : Cochain S.X₁ K (n-1)) w (by omega), ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ rfl]
  simp only [δ_zero, zero_add, hf, hw, Cocycle.coe_sub,
    Cocycle.coe_smul, cocycleComp, Cocycle.mk_coe,
    precomp_cone_quotient, Cocycle.coe_neg, Cochain.neg_comp,
    Cochain.comp_units_smul, smul_neg, sub_neg_eq_add]
  simp only [← Units.smul_def]
  abel

lemma classToDerived_precomp {K K' L : CochainComplex A ℤ} {n : ℤ}
    (z : Cocycle K L n) (f : K' ⟶ K) :
    classToDerived _ _ n (CohomologyClass.mk (z.precomp f)) =
      _root_.DerivedCategory.Q.map f ≫ classToDerived _ _ n (CohomologyClass.mk z) := by
  simp [AdvancedHomologicalAlgebra.ExtShiftedHom.classToDerived_mk,
    Cocycle.equivHomShift_symm_precomp]

lemma classToDerived_postcomp {K L L' : CochainComplex A ℤ} {n : ℤ}
    (z : Cocycle K L n) (f : L ⟶ L') :
    classToDerived _ _ n (CohomologyClass.mk (z.postcomp f)) =
      classToDerived _ _ n (CohomologyClass.mk z) ≫ (_root_.DerivedCategory.Q.map f)⟦n⟧' := by
  simp [AdvancedHomologicalAlgebra.ExtShiftedHom.classToDerived_mk,
    Cocycle.equivHomShift_symm_postcomp, Functor.commShiftIso_hom_naturality]

lemma classToDerived_units_smul {K L : CochainComplex A ℤ} {n : ℤ}
    (z : CohomologyClass K L n) (s : ℤˣ) :
    classToDerived K L n (s • z) = s • classToDerived K L n z := by
  simp [Units.smul_def]

lemma cone_boundary_class (S : ShortComplex (CochainComplex A ℤ)) :
    classToDerived _ _ 1 (CohomologyClass.mk (-mappingCone.fst S.f)) =
      _root_.DerivedCategory.Q.map (mappingCone.triangle S.f).mor₃ ≫
        (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  rw [AdvancedHomologicalAlgebra.ExtShiftedHom.classToDerived_mk]
  rfl

end Cochains

theorem ordinary_first_complex : ordinaryFirstComplexType := by
  intro A _ _ _ S hS I n u v w hf hw
  let := mappingCone.quasiIso_descShortComplex hS
  have e := congrArg (classToDerived _ _ (n+1)) (first_cone_classes u v w hf hw)
  rw [classToDerived_precomp, classToDerived_units_smul, classToDerived_comp,
    cone_boundary_class] at e
  rw [← cancel_epi (_root_.DerivedCategory.Q.map (mappingCone.descShortComplex S))]
  simpa [ShiftedHom.comp, _root_.DerivedCategory.triangleOfSESδ,
    Linear.comp_units_smul, Category.assoc] using e


theorem ordinary_second_complex : ordinarySecondComplexType := by
  intro A _ _ _ S hS K n z a b hb ha
  let := mappingCone.quasiIso_descShortComplex hS
  let l : Cocycle K (mappingCone S.f) n :=
    mappingCone.liftCocycle S.f (-a) b rfl (by
      simp only [ha, Cocycle.postcomp, Cocycle.coe_neg, Cochain.neg_comp]
      exact add_neg_cancel _)
  have hq : l.postcomp (mappingCone.descShortComplex S) = z := by
    apply Cocycle.ext
    change (mappingCone.liftCochain S.f (-a).1 b rfl).comp
      (Cochain.ofHom (mappingCone.descShortComplex S)) (add_zero n) = z.1
    simp [mappingCone.descShortComplex, mappingCone.ofHom_desc,
      mappingCone.liftCochain_descCochain, hb]
  have hp : cocycleComp l (-mappingCone.fst S.f) (by omega) = a := by
    apply Cocycle.ext
    change (mappingCone.liftCochain S.f (-a).1 b rfl).comp
      (-mappingCone.fst S.f).1 rfl = a.1
    simp [Cocycle.coe_neg, Cochain.comp_neg, mappingCone.liftCochain_fst]
  rw [← hp, classToDerived_comp, cone_boundary_class, ← hq,
    classToDerived_postcomp]
  simp [ShiftedHom.comp, _root_.DerivedCategory.triangleOfSESδ,
    Functor.map_comp, Category.assoc]


/-- Composition of shifted morphisms is natural in its final object. -/
lemma shifted_comp_postcomp {C : Type*} [Category C] [HasShift C ℤ]
    {X Y Z Z' : C} {a b c : ℤ} (f : X ⟶ Y⟦a⟧) (g : Y ⟶ Z⟦b⟧)
    (k : Z ⟶ Z') (h : b+a=c) :
    ShiftedHom.comp f g h ≫ k⟦c⟧' =
      ShiftedHom.comp f (g ≫ k⟦b⟧') h := by
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← (CategoryTheory.shiftFunctorAdd' C b a c h).inv.naturality k]
  rfl

theorem ordinary_first : ordinaryFirstType := by
  intro A _ _ _ S hS Y I ι hι n u v w hf hw
  let := hι
  have e := ordinary_first_complex A (S.map (CochainComplex.singleFunctor A 0))
    (hS.map_of_exact _) I n u v w hf hw
  dsimp only [ShortComplex.map] at e
  dsimp only [injectiveClassMap]
  rw [e, Linear.units_smul_comp, shifted_comp_postcomp]
  rfl

theorem ordinary_second : ordinarySecondType := by
  intro A _ _ _ S hS T hT ρ hρ₁ hρ₂ hρ₃ X n z a b hb ha
  let := hρ₁
  let := hρ₃
  have e := ordinary_second_complex A T hT _ n z a b hb ha
  have en := _root_.DerivedCategory.triangleOfSESδ_naturality
    (hS.map_of_exact (CochainComplex.singleFunctor A 0)) hT ρ
  have en' : _root_.DerivedCategory.triangleOfSESδ hT ≫
      (inv (_root_.DerivedCategory.Q.map ρ.τ₁))⟦(1 : ℤ)⟧' =
      inv (_root_.DerivedCategory.Q.map ρ.τ₃) ≫ hS.singleδ := by
    rw [← cancel_epi (_root_.DerivedCategory.Q.map ρ.τ₃),
      ← Category.assoc, ← en]
    simp [Functor.map_inv, Category.assoc]
    rfl
  dsimp only [injectiveClassMap]
  rw [e, shifted_comp_postcomp, en']
  simp [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rfl


section Representatives
variable {A : Type u} [Category.{v} A] [Abelian A]

lemma fromSingle_cycle_condition {X : A} {I : CochainComplex A ℤ} {n : ℤ}
    (z : Cocycle ((CochainComplex.singleFunctor A 0).obj X) I n) :
    Cochain.fromSingleEquiv (zero_add n) z.1 ≫ I.d n (n+1) = 0 := by
  have h := z.δ_eq_zero (n+1)
  rw [← Cochain.fromSingleMk_fromSingleEquiv (zero_add n) z.1,
    Cochain.δ_fromSingleMk _ _ _ (n+1) (zero_add (n+1))] at h
  simpa using congrArg (Cochain.fromSingleEquiv (zero_add (n+1))) h

end Representatives

theorem first_lifts : firstLiftsType := by
  intro A _ _ S hS I hinj n u
  let := hS.mono_f
  let := hS.epi_g
  let := hinj n
  let U := Cochain.fromSingleEquiv (zero_add n) u.1
  let W := Injective.factorThru U S.f
  have hW : S.f ≫ W = U := Injective.comp_factorThru _ _
  have hc : S.f ≫ (W ≫ I.d n (n+1)) = 0 := by
    rw [← Category.assoc, hW]
    exact fromSingle_cycle_condition u
  let V := hS.exact.desc (W ≫ I.d n (n+1)) hc
  have hV : S.g ≫ V = W ≫ I.d n (n+1) := hS.exact.g_desc _ _
  have hv : V ≫ I.d (n+1) (n+1+1) = 0 := by
    rw [← cancel_epi S.g, ← Category.assoc, hV]
    simp
  refine ⟨Cochain.fromSingleMk W (zero_add n),
    Cocycle.fromSingleMk V (zero_add (n+1)) _ rfl hv, ?_, ?_⟩
  · rw [← Cochain.fromSingleMk_precomp, hW]
    exact Cochain.fromSingleMk_fromSingleEquiv _ _
  · change δ n (n+1) (Cochain.fromSingleMk W (zero_add n)) =
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp
        (Cochain.fromSingleMk V (zero_add (n+1))) (zero_add (n+1))
    rw [Cochain.δ_fromSingleMk _ _ _ (n+1) (zero_add (n+1)),
      ← Cochain.fromSingleMk_precomp, hV]


theorem second_lifts : secondLiftsType := by
  intro A _ _ S hS hsplit X n z
  let := hS.epi_g
  let := hS.mono_f
  let σ := (hsplit n).some
  let Z := Cochain.fromSingleEquiv (zero_add n) z.1
  let B := Z ≫ σ.s
  have hB : B ≫ S.g.f n = Z := by
    dsimp [B]
    have hs : σ.s ≫ S.g.f n = 𝟙 _ := σ.s_g
    rw [Category.assoc, hs]
    simp
  have hc : (B ≫ S.X₂.d n (n+1)) ≫ S.g.f (n+1) = 0 := by
    rw [Category.assoc, ← S.g.comm, ← Category.assoc, hB]
    exact fromSingle_cycle_condition z
  let hSn := hS.map (HomologicalComplex.eval A (.up ℤ) (n+1))
  let := hSn.mono_f
  let e := hSn.exact
  let a := e.lift (B ≫ S.X₂.d n (n+1)) hc
  have ha : a ≫ S.f.f (n+1) = B ≫ S.X₂.d n (n+1) := e.lift_f _ _
  have hz : a ≫ S.X₁.d (n+1) (n+1+1) = 0 := by
    rw [← cancel_mono (S.f.f (n+1+1)), Category.assoc, ← S.f.comm,
      ← Category.assoc, ha]
    simp
  refine ⟨Cochain.fromSingleMk B (zero_add n),
    Cocycle.fromSingleMk a (zero_add (n+1)) _ rfl hz, ?_, ?_⟩
  · rw [← Cochain.fromSingleMk_postcomp, hB]
    exact Cochain.fromSingleMk_fromSingleEquiv _ _
  · change δ n (n+1) (Cochain.fromSingleMk B (zero_add n)) =
      (Cochain.fromSingleMk a (zero_add (n+1))).comp (Cochain.ofHom S.f) (add_zero (n+1))
    rw [Cochain.δ_fromSingleMk _ _ _ (n+1) (zero_add (n+1)),
      ← Cochain.fromSingleMk_postcomp, ha]


theorem second_injective_lifts : secondInjectiveLiftsType := by
  intro A _ _ S hS hinj X n z
  let := hS.mono_f
  let := hS.epi_g
  apply second_lifts A S hS (fun i => ?_) X n z
  let : Injective ((S.map (HomologicalComplex.eval A (.up ℤ) i)).X₁) := hinj i
  exact ⟨(hS.map (HomologicalComplex.eval A (.up ℤ) i)).splittingOfInjective⟩

end AdvancedHomologicalAlgebra.ExtBoundarySigns
