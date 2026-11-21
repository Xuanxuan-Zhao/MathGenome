import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GoodTruncations

set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Limits ZeroObject CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.HomotopyAndShifts
open Specs.AdvancedHomologicalAlgebra.DerivedCategory
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels

namespace AdvancedHomologicalAlgebra.BoundedDerivedModels

variable {A : Type u} [Category.{v} A] [Abelian A]

lemma minus_quotient_obj_iff (L : CochainComplex A ℤ) :
    minus A ((Q A).obj L) ↔ ∃ b : ℤ, L.IsStrictlyLE b := Iff.rfl

lemma isStrictlyLE_mappingCone {X Y : CochainComplex A ℤ} (f : X ⟶ Y)
    (b₁ b₂ b : ℤ) [X.IsStrictlyLE b₁] [Y.IsStrictlyLE b₂]
    (h₁ : b₁ - 1 ≤ b) (h₂ : b₂ ≤ b) :
    (CochainComplex.mappingCone f).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨X.isZero_of_isStrictlyLE b₁ _ (by omega),
    Y.isZero_of_isStrictlyLE b₂ _ (by omega)⟩

instance minusContainsZero : (minus A).ContainsZero where
  exists_zero := ⟨(Q A).obj 0, (Q A).map_isZero (isZero_zero _),
    (minus_quotient_obj_iff _).mpr ⟨0, inferInstance⟩⟩

instance minusShift : (minus A).IsStableUnderShift ℤ where
  isStableUnderShiftBy m :=
    { le_shift X hX := by
        obtain ⟨X : CochainComplex A ℤ, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
        obtain ⟨b, hb⟩ := hX
        have hb : X.IsStrictlyLE b := hb
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
          minus_quotient_obj_iff]
        exact ⟨b - m, X.isStrictlyLE_shift b m (b - m) (by omega)⟩ }

instance minusCone : (minus A).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨b₁, hb₁⟩ := h₁
    obtain ⟨b₂, hb₂⟩ := h₂
    obtain ⟨f, hf⟩ := (Q A).map_surjective T.mor₁
    refine ⟨(Q A).obj (CochainComplex.mappingCone f), ?_,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
        (HomotopyCategory.mappingCone_triangleh_distinguished f)
          (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · exact ⟨max (b₁ - 1) b₂, isStrictlyLE_mappingCone f b₁ b₂ _
        (le_max_left _ _) (le_max_right _ _)⟩
    · simpa using hf.symm

instance minusTriangulated : (minus A).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- Lower bounds in K⁻ are stable under the inherited shifts. -/
instance boundedShift : (boundedInMinus A).IsStableUnderShift ℤ where
  isStableUnderShiftBy m :=
    { le_shift X hX := by
        rw [ObjectProperty.prop_shift_iff]
        delta ObjectProperty.hasShift
        change HomotopyCategory.plus A (X.obj⟦m⟧)
        exact (HomotopyCategory.plus A).le_shift m X.obj hX }

instance boundedContainsZero : (boundedInMinus A).ContainsZero where
  exists_zero := ⟨⟨(Q A).obj 0, (minus_quotient_obj_iff _).mpr ⟨0, inferInstance⟩⟩,
    IsZero.of_full_of_faithful_of_isZero (minus A).ι _ ((Q A).map_isZero (isZero_zero _)), by
      change HomotopyCategory.plus A ((Q A).obj 0)
      exact (HomotopyCategory.plus_quotient_obj_iff _).mpr ⟨0, inferInstance⟩⟩

/-- Cones retain both sorts of term bounds. The isomorphism of third vertices
is taken inside K⁻ using its fully faithful inclusion. -/
instance boundedCone : (boundedInMinus A).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    let I := minusInclusion A
    let T' := I.mapTriangle.obj T
    have hT' := I.map_distinguished T hT
    obtain ⟨a₁, ha₁⟩ := (HomotopyCategory.plus_quotient_obj_iff T.obj₁.obj.as).mp h₁
    obtain ⟨a₂, ha₂⟩ := (HomotopyCategory.plus_quotient_obj_iff T.obj₂.obj.as).mp h₂
    obtain ⟨b₁, hb₁⟩ := T.obj₁.property
    obtain ⟨b₂, hb₂⟩ := T.obj₂.property
    obtain ⟨f, hf⟩ := (Q A).map_surjective T'.mor₁
    let Z : KMinus A := ⟨(Q A).obj (CochainComplex.mappingCone f),
      max (b₁ - 1) b₂, isStrictlyLE_mappingCone f b₁ b₂ _
        (le_max_left _ _) (le_max_right _ _)⟩
    refine ⟨Z, ?_, ⟨I.preimageIso (Triangle.π₃.mapIso
      (isoTriangleOfIso₁₂ T' _ hT' (HomotopyCategory.mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) ?_))⟩⟩
    · change HomotopyCategory.plus A ((Q A).obj (CochainComplex.mappingCone f))
      rw [HomotopyCategory.plus_quotient_obj_iff]
      exact ⟨min (a₁ - 1) a₂, CochainComplex.isStrictlyGE_mappingCone f a₁ a₂ _
        (by omega) (by omega)⟩
    · simpa using hf.symm

instance boundedTriangulated : (boundedInMinus A).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

theorem homotopyBounds : homotopyBoundsType := by
  intro A _ _
  constructor
  · intro X
    exact exists_congr (fun b => CochainComplex.isStrictlyLE_iff X.as b)
  · intro X
    change HomotopyCategory.plus A ((Q A).obj X.obj.as) ↔ _
    rw [HomotopyCategory.plus_quotient_obj_iff]
    exact exists_congr (fun a => CochainComplex.isStrictlyGE_iff X.obj.as a)

theorem cohomologyBounds : cohomologyBoundsType := by
  intro A _ _ _ X
  have hGE := exists_congr (fun a => _root_.DerivedCategory.isGE_iff X a)
  have hLE := exists_congr (fun b => _root_.DerivedCategory.isLE_iff X b)
  exact ⟨hGE, hLE, and_congr hGE hLE⟩

theorem strictModels : strictModelsType := by
  intro A _ _ _ X a b
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := (_root_.DerivedCategory.isGE_iff X a).mpr h
    obtain ⟨L, hL, e⟩ := X.exists_iso_Q_obj_of_isGE a
    exact ⟨L, hL, e⟩
  · intro h
    have := (_root_.DerivedCategory.isLE_iff X b).mpr h
    obtain ⟨L, hL, e⟩ := X.exists_iso_Q_obj_of_isLE b
    exact ⟨L, hL, e⟩
  · intro h₁ h₂
    have := (_root_.DerivedCategory.isGE_iff X a).mpr h₁
    have := (_root_.DerivedCategory.isLE_iff X b).mpr h₂
    obtain ⟨L, hLa, hLb, e⟩ := X.exists_iso_Q_obj_of_isGE_of_isLE a b
    exact ⟨L, hLa, hLb, e⟩

theorem homotopyTriangulated : homotopyTriangulatedType := by
  intro A _ _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem homotopyInclusions : homotopyInclusionsType := by
  intro A _ _
  exact ⟨⟨.ofFullyFaithful _⟩, ⟨.ofFullyFaithful _⟩,
    inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem derivedTriangulated : derivedTriangulatedType := by
  intro A _ _ _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Upper truncation makes K⁻ left localizing relative to the acyclics. -/
instance minusLeftLocalizing : (minus A).IsVerdierLeftLocalizing
    (HomotopyCategory.subcategoryAcyclic A) where
  fac {X Y} f hX hY := by
    obtain ⟨X : CochainComplex A ℤ, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y : CochainComplex A ℤ, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨b, hb⟩ := hX
    have hb : X.IsStrictlyLE b := hb
    obtain ⟨f, rfl⟩ := (Q A).map_surjective f
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hY
    refine ⟨(Q A).obj (Y.truncLE b),
      (Q A).map (inv (X.ιTruncLE b) ≫ CochainComplex.truncLEMap f b),
      (Q A).map (Y.ιTruncLE b),
      (minus_quotient_obj_iff _).mpr ⟨b, inferInstance⟩, ?_, ?_⟩
    · rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
      exact hY.truncLE _
    · simp [← Functor.map_comp]

abbrev acyclicMinus (A : Type u) [Category.{v} A] [Abelian A] :=
  (HomotopyCategory.subcategoryAcyclic A).inverseImage (minusInclusion A)

/-- In K⁻, lower truncation makes Kᵇ right localizing. It preserves the
existing upper bound on the acyclic source. -/
instance boundedRightLocalizing : (boundedInMinus A).IsVerdierRightLocalizing
    (acyclicMinus A) where
  fac {X Y} f hX hY := by
    rcases X with ⟨X, hXm⟩
    rcases Y with ⟨Y, hYm⟩
    obtain ⟨X : CochainComplex A ℤ, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨Y : CochainComplex A ℤ, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    obtain ⟨b, hb⟩ := hXm
    have hb : X.IsStrictlyLE b := hb
    obtain ⟨a, ha⟩ := (HomotopyCategory.plus_quotient_obj_iff Y).mp hY
    obtain ⟨f, hf⟩ := (Q A).map_surjective f.hom
    have hX : X.Acyclic :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic X).mp hX
    let Z : KMinus A := ⟨(Q A).obj (X.truncGE a), (minus_quotient_obj_iff _).mpr ⟨b, inferInstance⟩⟩
    refine ⟨Z, (minus A).homMk ((Q A).map (X.πTruncGE a)),
      (minus A).homMk ((Q A).map (CochainComplex.truncGEMap f a ≫ inv (Y.πTruncGE a))),
      ?_, ?_, ?_⟩
    · change HomotopyCategory.plus A ((Q A).obj (X.truncGE a))
      exact (HomotopyCategory.plus_quotient_obj_iff _).mpr ⟨a, inferInstance⟩
    · change HomotopyCategory.subcategoryAcyclic A ((Q A).obj (X.truncGE a))
      rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
      exact hX.truncGE _
    · ext
      simp [← Functor.map_comp, hf]

section Localization
variable [HasDerivedCategory.{w} A]

instance minusEssSurj : (QMinus A).EssSurj where
  mem_essImage := by
    rintro ⟨X, b, hb⟩
    obtain ⟨L, hL, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isLE b
    refine ⟨⟨(Q A).obj L, b, hL⟩,
      ⟨_root_.DerivedCategory.Minus.ι.preimageIso
        ((_root_.DerivedCategory.quotientCompQhIso A).app L ≪≫ e.symm)⟩⟩

instance boundedEssSurj : (QBounded A).EssSurj where
  mem_essImage := by
    rintro ⟨X, ⟨a, ha⟩, ⟨b, hb⟩⟩
    obtain ⟨L, hLa, hLb, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE_of_isLE a b
    refine ⟨⟨⟨(Q A).obj L, b, hLb⟩, ?_⟩,
      ⟨_root_.DerivedCategory.Bounded.ι.preimageIso
        ((_root_.DerivedCategory.quotientCompQhIso A).app L ≪≫ e.symm)⟩⟩
    exact (HomotopyCategory.plus_quotient_obj_iff _).mpr ⟨a, hLa⟩

omit [HasDerivedCategory A] in
lemma minus_coneClass_eq : (acyclicMinus A).trW = WMinus A := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff,
    ← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  rfl

omit [HasDerivedCategory A] in
lemma bounded_coneClass_eq :
    ((acyclicMinus A).inverseImage (boundedInMinus A).ι).trW = WBounded A := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff, ObjectProperty.inverseImage_trW_iff,
    ← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  rfl

instance minusLocalization : (QMinus A).IsLocalization (WMinus A) := by
  rw [← minus_coneClass_eq]
  exact ((minus A).triangulatedLocalizerMorphism
    (HomotopyCategory.subcategoryAcyclic A)).isLocalization_of_isLocalizedFullyFaithful
      (L₂ := localizationQ A) (F := _root_.DerivedCategory.Minus.ι) (Iso.refl _)

instance boundedLocalization : (QBounded A).IsLocalization (WBounded A) := by
  rw [← bounded_coneClass_eq]
  let Φ := (boundedInMinus A).triangulatedLocalizerMorphism (acyclicMinus A)
  let Ψ := (minus A).triangulatedLocalizerMorphism (HomotopyCategory.subcategoryAcyclic A)
  exact (Φ.comp Ψ).isLocalization_of_isLocalizedFullyFaithful
    (L₂ := localizationQ A) (F := _root_.DerivedCategory.Bounded.ι) (Iso.refl _)

noncomputable instance minusQuotientCommShift : (QMinus A).CommShift ℤ :=
  ObjectProperty.commShiftLift ..

noncomputable instance boundedQuotientCommShift : (QBounded A).CommShift ℤ :=
  ObjectProperty.commShiftLift ..

instance minusQuotientTriangulated : (QMinus A).IsTriangulated := by
  dsimp only [QMinus]
  infer_instance

instance boundedQuotientTriangulated : (QBounded A).IsTriangulated := by
  dsimp only [QBounded]
  infer_instance

end Localization

theorem exactQuotients : exactQuotientsType := by
  intro A _ _ _
  exact ⟨inferInstance, inferInstance,
    ⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

theorem localization : Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels.localizationType := by
  intro A _ _ _
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem equivalences : equivalencesType := by
  intro A _ _ _
  exact ⟨⟨Localization.equivalenceFromModel _ _,
      ⟨Localization.qCompEquivalenceFromModelFunctorIso _ _⟩⟩,
    ⟨Localization.equivalenceFromModel _ _,
      ⟨Localization.qCompEquivalenceFromModelFunctorIso _ _⟩⟩,
    ⟨Localization.equivalenceFromModel _ _,
      ⟨Localization.qCompEquivalenceFromModelFunctorIso _ _⟩⟩⟩

end AdvancedHomologicalAlgebra.BoundedDerivedModels
