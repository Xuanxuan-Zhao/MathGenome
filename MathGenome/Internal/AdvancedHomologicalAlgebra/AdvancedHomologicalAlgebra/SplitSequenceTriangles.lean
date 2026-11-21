import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex CochainComplex CochainComplex.HomComplex
open CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles
namespace AdvancedHomologicalAlgebra.SplitSequenceTriangles
variable {D : Type u} [Category.{v} D] [Preadditive D]

abbrev retraction (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S) :
    Cochain S.X₂ S.X₁ 0 := Cochain.ofHoms (fun n => (σ n).r)
abbrev sectionCochain (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S) :
    Cochain S.X₃ S.X₂ 0 := Cochain.ofHoms (fun n => (σ n).s)

lemma delta_retraction (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S) :
    δ 0 1 (retraction S σ) =
      -((Cochain.ofHom S.g).comp (cocycleOfDegreewiseSplit S σ).1 (zero_add 1)) := by
  ext n _ rfl
  have hf := (σ n).r_f
  dsimp at hf
  simp only [δ_v 0 1 rfl _ n (n+1) rfl n (n+1) (by omega) rfl,
    retraction, Cochain.ofHoms_v, Int.negOnePow_one, Units.neg_smul, one_smul,
    Cochain.neg_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    cocycleOfDegreewiseSplit, Cocycle.mk_coe, Cochain.mk_v]
  have hr := (σ (n+1)).f_r
  dsimp at hr
  have h : (σ n).r ≫ S.X₁.d n (n+1) =
      ((σ n).r ≫ S.f.f n) ≫ S.X₂.d n (n+1) ≫ (σ (n+1)).r := by
    rw [Category.assoc, S.f.comm_assoc, hr, comp_id]
  rw [h, hf]
  simp [sub_comp, Category.assoc]
  abel

lemma delta_section (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S) :
    δ 0 1 (sectionCochain S σ) =
      (cocycleOfDegreewiseSplit S σ).1.comp (Cochain.ofHom S.f) (add_zero 1) := by
  ext n _ rfl
  have hf := (σ (n+1)).r_f
  have hs := (σ n).s_g
  dsimp at hf hs
  simp only [δ_v 0 1 rfl _ n (n+1) rfl n (n+1) (by omega) rfl,
    sectionCochain, Cochain.ofHoms_v, Int.negOnePow_one, Units.neg_smul, one_smul,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    cocycleOfDegreewiseSplit, Cocycle.mk_coe, Cochain.mk_v]
  simp only [Category.assoc]
  rw [hf]
  simp only [comp_sub, comp_id]
  rw [← S.g.comm_assoc]
  simp only [reassoc_of% hs]
  abel

/-- The graded discrepancy of lifts; its coboundary measures naturality. -/
abbrev liftDiscrepancy (S S' : ShortComplex (CochainComplex D ℤ))
    (σ : DegreewiseSplitting S) (σ' : DegreewiseSplitting S') (φ : S ⟶ S') :=
  ((sectionCochain S σ).comp (Cochain.ofHom φ.τ₂) (add_zero 0)).comp
    (retraction S' σ') (add_zero 0)

lemma delta_liftDiscrepancy (S S' : ShortComplex (CochainComplex D ℤ))
    (σ : DegreewiseSplitting S) (σ' : DegreewiseSplitting S') (φ : S ⟶ S') :
    δ 0 1 (liftDiscrepancy S S' σ σ' φ) =
      (cocycleOfDegreewiseSplit S σ).1.comp (Cochain.ofHom φ.τ₁) (add_zero 1) -
      (Cochain.ofHom φ.τ₃).comp (cocycleOfDegreewiseSplit S' σ').1 (zero_add 1) := by
  rw [liftDiscrepancy, δ_comp_zero_cochain _ _ 1 rfl, δ_comp_ofHom,
    delta_retraction, delta_section]
  ext n _ rfl
  have hw₁ := congrArg (fun f => f.f (n+1)) φ.comm₁₂
  have hw₂ := congrArg (fun f => f.f n) φ.comm₂₃
  have hr := (σ' (n+1)).f_r
  have hs := (σ n).s_g
  dsimp at hw₁ hw₂ hr hs
  simp only [Cochain.add_v, Cochain.sub_v, Cochain.neg_v,
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, retraction, sectionCochain, Cochain.ofHoms_v,
    cocycleOfDegreewiseSplit, Cocycle.mk_coe, Cochain.mk_v,
    comp_neg, Category.assoc]
  rw [← reassoc_of% hw₁, reassoc_of% hw₂]
  simp only [reassoc_of% hs]
  rw [hr, Category.comp_id]
  abel

noncomputable def connectingMap :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.boundaryType :=
  fun _ _ _ S σ => boundary S σ

theorem boundary_components :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.boundary_componentsType := by
  intro D _ _ S σ n
  simp [boundary, cocycleOfDegreewiseSplit]

/-- Explicit homotopy with components minus the discrepancy of the chosen lifts. -/
theorem naturalityHomotopy :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.naturalityHomotopyType := by
  intro D _ _ S S' σ σ' φ
  apply Nonempty.intro
  refine (Cochain.equivHomotopy _ _).symm
    ⟨(-(liftDiscrepancy S S' σ σ' φ)).rightShift 1 (-1) (by decide), ?_⟩
  rw [Cochain.δ_rightShift _ 1 (-1) 0 (by decide) 1 (by decide),
    δ_neg, delta_liftDiscrepancy]
  ext n
  simp [Cochain.rightShift_v _ _ _ _ _ _ _ (n+1) rfl,
    boundary, homOfDegreewiseSplit_f, cocycleOfDegreewiseSplit,
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, shiftFunctorObjXIso, Category.assoc]

theorem independent :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.independentType := by
  intro D _ _ S σ τ
  obtain ⟨h⟩ := naturalityHomotopy D S S σ τ (𝟙 S)
  apply HomotopyCategory.eq_of_homotopy _ _
  simpa using h

theorem naturality :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.naturalityType := by
  intro D _ _ S S' σ σ' φ
  dsimp only
  rw [← Functor.map_comp, ← Functor.map_comp]
  obtain ⟨h⟩ := naturalityHomotopy D S S' σ σ' φ
  exact HomotopyCategory.eq_of_homotopy _ _ h

theorem naturalityShift :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.naturalityShiftType := by
  intro D _ _ S S' σ σ' φ
  let Q := HomotopyCategory.quotient D (ComplexShape.up ℤ)
  change (Q.map (boundary S σ) ≫ (Q.commShiftIso 1).hom.app S.X₁) ≫
    (Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
      Q.map φ.τ₃ ≫ (Q.map (boundary S' σ') ≫ (Q.commShiftIso 1).hom.app S'.X₁)
  have hn : (Q.commShiftIso 1).hom.app S.X₁ ≫ (Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
      Q.map (φ.τ₁⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso 1).hom.app S'.X₁ :=
    ((Q.commShiftIso 1).hom.naturality φ.τ₁).symm
  rw [Category.assoc, hn]
  rw [← Category.assoc, naturality D S S' σ σ' φ, Category.assoc]

theorem coordinates :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.coordinatesType := by
  intro D _ _ _ S σ n
  have hf := (σ n).f_r
  have hf' := (σ (n+1)).f_r
  have hs := (σ n).s_g
  have hz := congrArg (fun f => f.f n) S.zero
  have hz' := congrArg (fun f => f.f (n+1)) S.zero
  dsimp at hf hf' hs hz hz'
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp [ShortComplex.Splitting.isoBinaryBiproduct, hf, hz]
  · ext <;> simp [ShortComplex.Splitting.isoBinaryBiproduct, hs, hz]
  · ext <;> simp [ShortComplex.Splitting.isoBinaryBiproduct,
      boundary, cocycleOfDegreewiseSplit, Category.assoc, S.f.comm_assoc, hf', hz']
    rw [← S.g.comm n (n+1), ← Category.assoc, hs, Category.id_comp]

noncomputable def canonicalComparison :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.coneComparisonType :=
  fun _ _ _ _ S => coneComparison S

theorem comparison_components :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.comparison_componentsType := by
  intro D _ _ _ S n
  simp [coneComparison, mappingCone.desc_f _ _ _ _ n (n+1) rfl,
    Specs.AdvancedHomologicalAlgebra.MappingCones.targetProjection]

lemma delta_shift_retraction (S : ShortComplex (CochainComplex D ℤ))
    (σ : DegreewiseSplitting S) :
    δ (-1) 0 ((retraction S σ).rightShift 1 (-1) (by decide)) =
      Cochain.ofHom (S.g ≫ boundary S σ) := by
  rw [Cochain.δ_rightShift _ 1 (-1) 0 (by decide) 1 (by decide), delta_retraction]
  ext n
  simp [Cochain.rightShift_v _ _ _ _ _ _ _ (n+1) rfl,
    boundary, homOfDegreewiseSplit_f, Cochain.zero_cochain_comp_v,
    shiftFunctorObjXIso]

noncomputable def comparison_boundary_homotopy [HasBinaryBiproducts D]
    (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S) :
    Homotopy (coneComparison S ≫ boundary S σ) (mappingCone.triangle S.f).mor₃ := by
  refine mappingCone.descHomotopy S.f _ _ 0
    ((retraction S σ).rightShift 1 (-1) (by decide)) ?_ ?_
  · ext n q hnq
    have hf := (σ n).f_r
    dsimp at hf
    simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      comp_f, coneComparison,
      mappingCone.inl_v_desc_f_assoc, Cochain.zero_v, zero_comp,
      δ_zero, Cochain.add_v, zero_add,
      Cochain.zero_cochain_comp_v,
      Cochain.rightShift_v (retraction S σ) 1 (-1) (show (-1 : ℤ)+1=0 by decide) n q hnq n (add_zero n),
      retraction, Cochain.ofHoms_v, reassoc_of% hf,
      mappingCone.inl_v_triangle_mor₃_f, add_neg_cancel]
  · rw [delta_shift_retraction]
    simp [coneComparison, ← Category.assoc, mappingCone.inr_desc]

/-- All three squares use the canonical quotient map, with identities on A and B. -/
noncomputable def coneRowMorphism [HasBinaryBiproducts D]
    (S : ShortComplex (CochainComplex D ℤ)) (σ : DegreewiseSplitting S) :
    mappingCone.triangleh S.f ⟶ trianglehOfDegreewiseSplit S σ where
  hom₁ := 𝟙 _
  hom₂ := 𝟙 _
  hom₃ := (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map (coneComparison S)
  comm₁ := by simp
  comm₂ := by
    change (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map (mappingCone.inr S.f) ≫
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map (coneComparison S) = _
    rw [← Functor.map_comp]
    simp [coneComparison]
  comm₃ := by
    have h := HomotopyCategory.eq_of_homotopy _ _ (comparison_boundary_homotopy S σ)
    dsimp
    simp only [← Category.assoc, ← Functor.map_comp]
    rw [h]
    simp

theorem coneRowIso :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.coneRowIsoType := by
  intro D _ _ _ _ S σ
  let f := coneRowMorphism S σ
  have h₁ : IsIso f.hom₁ := by dsimp [f, coneRowMorphism]; infer_instance
  have h₂ : IsIso f.hom₂ := by dsimp [f, coneRowMorphism]; infer_instance
  have h₃ : IsIso f.hom₃ := CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ f
    (HomotopyCategory.mappingCone_triangleh_distinguished S.f)
    (trianglehOfDegreewiseSplit_distinguished S σ) h₁ h₂
  have : IsIso f := Triangle.isIso_of_isIsos f h₁ h₂ h₃
  refine ⟨asIso f, rfl, rfl, rfl⟩

theorem negativeProjection :
    Specs.AdvancedHomologicalAlgebra.SplitSequenceTriangles.negativeProjectionType := by
  intro D _ _ _ X Y f
  simp [Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift]

end AdvancedHomologicalAlgebra.SplitSequenceTriangles
