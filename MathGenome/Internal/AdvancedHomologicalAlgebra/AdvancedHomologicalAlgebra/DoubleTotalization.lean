import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.DoubleTotalization

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category Opposite
open HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AdvancedHomologicalAlgebra.DoubleTotalization

variable {C : Type*} [Category* C] [Preadditive C]
variable {c : ComplexShape ℤ} [ComplexShape.TensorSigns c]

noncomputable def totalSum : Specs.SumType (C := C) (c := c) := fun K => K.total c
noncomputable def totalProduct : Specs.ProductType (C := C) (c := c) :=
  fun K => ((oppositeBicomplex K).total c.symm).unopSymm

theorem sumDifferential : Specs.SumDifferential (C := C) (c := c) := by
  intro K _ p p' q q' n n' hp hq h hh hv
  change K.ιTotal c p q n h ≫ (K.D₁ c n n' + K.D₂ c n n') = _
  rw [Preadditive.comp_add, K.ι_D₁, K.ι_D₂, K.d₁_eq c hp q n' hh,
    K.d₂_eq c p hq n' hv]
  change (1 : ℤˣ) • _ + c.ε p • _ = _
  simp only [one_smul]

theorem productDifferential : Specs.ProductDifferential (C := C) (c := c) := by
  intro K _ p p' q q' n n' hp hq h hh hv
  have e := sumDifferential (K := oppositeBicomplex K) p p' q q' n' n hp hq h hh hv
  have e' := congrArg Quiver.Hom.unop e
  simpa only [sumInjection, sumTotal, productProjection, productTotal,
    HomologicalComplex.unopSymm_d, unop_comp, unop_add, Units.smul_def, Linear.unop_smul,
    oppositeBicomplex, HomologicalComplex.op_d, Quiver.Hom.unop_op, epsilon_symm] using e'

theorem unchangedSumDifferential : Specs.UnchangedSumDifferential (C := C) (c := c) := by
  intro K _ p p' q q' n n' hp hq h hh hv
  simpa only [signedVertical, Linear.units_smul_comp] using
    sumDifferential K p p' q q' n n' hp hq h hh hv

theorem unchangedProductDifferential : Specs.UnchangedProductDifferential (C := C) (c := c) := by
  intro K _ p p' q q' n n' hp hq h hh hv
  simpa only [signedVertical, Linear.comp_units_smul] using
    productDifferential K p p' q q' n n' hp hq h hh hv

theorem sumSquareZero : Specs.SumSquareZero (C := C) (c := c) := by
  intro K _ i j k
  exact HomologicalComplex.d_comp_d _ i j k

theorem productSquareZero : Specs.ProductSquareZero (C := C) (c := c) := by
  intro K _ i j k
  exact HomologicalComplex.d_comp_d _ i j k

theorem productExistence : Specs.ProductExistence (C := C) (c := c) := by
  intro K
  constructor
  · intro h n
    let α := {i : ℤ × ℤ // i.1 + i.2 = n}
    let Z : α → C := fun i => (K.X i.1.1).X i.1.2
    have : HasCoproduct (fun i : α => op (Z i)) := h n
    let F := Discrete.functor Z
    have : HasColimit ((Discrete.opposite α).symm.functor ⋙ F.op) :=
      hasColimit_of_iso (F := Discrete.functor (fun i => op (Z i)))
        (Discrete.natIso (fun _ => Iso.refl _))
    have : HasColimit F.op := hasColimit_of_equivalence_comp (F := F.op) (Discrete.opposite α).symm
    exact hasLimit_of_hasColimit_op F
  · intro h n
    let _ := h n
    exact (inferInstance : HasCoproduct (fun i : {i : ℤ × ℤ // i.1 + i.2 = n} =>
      op ((K.X i.1.1).X i.1.2)))

theorem signConvention : Specs.SignConvention (C := C) (c := c) := by
  intro K
  refine ⟨?_, ?_, ?_⟩
  · intro p q q' q''
    simp [signedVertical, Linear.units_smul_comp, Linear.comp_units_smul,
      HomologicalComplex.d_comp_d]
  · intro p p' q q' hp
    simp only [signedVertical, Linear.units_smul_comp,
      ComplexShape.ε_succ c hp, Units.neg_smul]
    simp only [Preadditive.comp_neg, Linear.comp_units_smul, ← K.d_comm p p' q q', neg_add_cancel]
  · intro p q q'
    simp [signedVertical, smul_smul]

theorem productUniversal : Specs.ProductUniversal (C := C) (c := c) := by
  intro K _ n A f
  let g : A ⟶ (productTotal K).X n :=
    ((oppositeBicomplex K).totalDesc (fun p q h => (f p q h).op)).unop
  have hg : ∀ p q (h : p + q = n), g ≫ productProjection K p q n h = f p q h := by
    intro p q h
    have e := (oppositeBicomplex K).ι_totalDesc (c₁₂ := c.symm)
      (fun p q h => (f p q h).op) p q h
    exact congrArg Quiver.Hom.unop e
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  apply Quiver.Hom.op_inj
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  apply Quiver.Hom.unop_inj
  exact (hg' p q h).trans (hg p q h).symm

def homologicalReindex : Specs.HomologicalReindexType (C := C) := reverseIndices

theorem gradingSigns : Specs.GradingSigns := by
  intro p q
  exact ⟨rfl, rfl, rfl, rfl, Int.negOnePow_neg p, by rw [neg_mul_neg]⟩

variable [TotalComplexShapeSymmetry c c c]
noncomputable def sumSymmetry : Specs.SumSymmetryType (C := C) (c := c) :=
  fun K => (K.totalFlipIso c).symm

theorem sumSymmetryFormula : Specs.SumSymmetryFormula (C := C) (c := c) := by
  intro K _ p q n h
  exact K.ιTotal_totalFlipIso_f_inv c p q n h

theorem sumNaturality : Specs.SumNaturality (C := C) (c := c) := by
  intro K L _ _ f
  ext n p q h
  simp only [HomologicalComplex.comp_f, ιTotal_map_assoc,
    ιTotal_totalFlipIso_f_inv, ιTotal_totalFlipIso_f_inv_assoc,
    Linear.units_smul_comp, ιTotal_map, Linear.comp_units_smul]
  dsimp only [flip_X_X] at *
  rfl

noncomputable def productSymmetry : Specs.ProductSymmetryType (C := C) (c := c) :=
  fun K => productFlipIso K

theorem productSymmetryFormula : Specs.ProductSymmetryFormula (C := C) (c := c) := by
  intro K _ p q n h
  have e := (oppositeBicomplex K).ιTotal_totalFlipIso_f_hom c.symm p q n
    (by change q + p = n; simpa only [add_comm] using h)
  have e' := congrArg Quiver.Hom.unop e
  change (((oppositeBicomplex K).totalFlipIso c.symm).hom.f n).unop ≫
    ((oppositeBicomplex K).flip.ιTotal c.symm q p n
      (by change q + p = n; simpa only [add_comm] using h)).unop =
    ComplexShape.σ c c c p q • ((oppositeBicomplex K).ιTotal c.symm p q n h).unop
  simpa only [unop_comp, Units.smul_def, Linear.unop_smul, sigma_symm] using e' 

theorem productNaturality : Specs.ProductNaturality (C := C) (c := c) := by
  intro K L _ _ f
  ext n
  apply Quiver.Hom.op_inj
  change ((oppositeBicomplex L).totalFlipIso c.symm).hom.f n ≫
      (HomologicalComplex₂.total.map (oppositeMap K f) c.symm).f n =
    (HomologicalComplex₂.total.map (oppositeMap K.flip
      (show K.flip ⟶ L.flip from (HomologicalComplex₂.flipFunctor C c c).map f)) c.symm).f n ≫
      ((oppositeBicomplex K).totalFlipIso c.symm).hom.f n
  apply HomologicalComplex₂.total.hom_ext
  intro q p h
  change (oppositeBicomplex L).flip.ιTotal c.symm q p n h ≫
      (((oppositeBicomplex L).totalFlipIso c.symm).hom.f n ≫
      (HomologicalComplex₂.total.map (oppositeMap K f) c.symm).f n) =
    (oppositeBicomplex L).flip.ιTotal c.symm q p n h ≫
      ((HomologicalComplex₂.total.map
        (show (oppositeBicomplex L).flip ⟶ (oppositeBicomplex K).flip from
          (HomologicalComplex₂.flipFunctor Cᵒᵖ c.symm c.symm).map (oppositeMap K f)) c.symm).f n ≫
      ((oppositeBicomplex K).totalFlipIso c.symm).hom.f n)
  simp only [ιTotal_totalFlipIso_f_hom_assoc, ιTotal_map_assoc,
    ιTotal_totalFlipIso_f_hom]
  dsimp only [flip_X_X] at *
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, ιTotal_map]
  rfl

end AdvancedHomologicalAlgebra.DoubleTotalization
