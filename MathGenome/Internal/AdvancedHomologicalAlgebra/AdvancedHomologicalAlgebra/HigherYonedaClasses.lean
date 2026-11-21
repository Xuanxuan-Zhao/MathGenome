import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DegreeOneExtensionClasses
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.MappingCones
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.Pushout
import Mathlib.Algebra.Homology.ShortComplex.Pullback

/-! HA-R15, definitions and classification. Exact finite augmented rows are
classified by their normalized positive-projection roofs. Geometric endpoint
pushouts and pullbacks and termwise direct sums give Baer addition; the class
map is additive and natural without resolution hypotheses. In degree one it
is the negative of the short exact sequence's triangle boundary. -/
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses
open Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension

namespace AdvancedHomologicalAlgebra.HigherYonedaClasses
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {X Y : 𝒜} {n : ℕ}

namespace Extension

lemma projection_naturality {E F :
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n}
    (f : E.Map F) : f.hom ≫ F.projection = E.projection := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, projection, HomologicalComplex.mkHomToSingle_f,
    ← Category.assoc, f.left_comm]

lemma map_quasiIso {E F :
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n}
    (f : E.Map F) : QuasiIso f.hom := by
  have : QuasiIso (f.hom ≫ F.augmentation) := by
    rw [f.right_comm]
    infer_instance
  exact quasiIso_of_comp_right f.hom F.augmentation

lemma exactAt (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n)
    (i : ℤ) (hi : i ≠ 0) : E.complex.ExactAt i :=
  (exactAt_iff_of_quasiIsoAt E.augmentation i).mpr
    (HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi))

lemma left_mono (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n) :
    Mono (E.complex.d (-(n : ℤ)) (-(n : ℤ) + 1)) := by
  have he := exactAt E (-(n : ℤ)) (by have := E.positive; omega)
  rw [HomologicalComplex.exactAt_iff' (K := E.complex)
    (i := -(n : ℤ) - 1) (j := -(n : ℤ)) (k := -(n : ℤ) + 1) (by simp) (by simp)] at he
  apply (ShortComplex.exact_iff_mono _ ?_).mp he
  exact (E.complex.isZero_of_isStrictlyGE (-(n : ℤ)) (-(n : ℤ) - 1)
    (by omega)).eq_of_src _ _

/-- The augmentation really is a cokernel of the preceding differential;
thus the quasi-isomorphism definition includes exactness and epimorphy at X. -/
noncomputable def augmentationIsCokernel
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n) :
    IsColimit (CokernelCofork.ofπ E.top.g E.top.zero) := by
  let T := (CochainComplex.singleFunctor 𝒜 0).obj X
  let φ := (HomologicalComplex.shortComplexFunctor 𝒜 (.up ℤ) 0).map E.augmentation
  have h₁ : (E.complex.sc 0).g = 0 := by
    change E.complex.d 0 ((ComplexShape.up ℤ).next 0) = 0
    apply (E.complex.isZero_of_isStrictlyLE 0 _ ?_).eq_of_tgt
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
    omega
  have h₂ : (T.sc 0).f = 0 := by simp [T, CochainComplex.singleFunctor]
  have h₃ : (T.sc 0).g = 0 := by simp [T, CochainComplex.singleFunctor]
  have hq : ShortComplex.QuasiIso φ := (quasiIsoAt_iff E.augmentation 0).mp inferInstance
  let t := (E.complex.sc 0).descOpcycles φ.τ₂
    (by rw [← φ.comm₁₂, h₂, comp_zero])
  have ht : IsIso t := (ShortComplex.quasiIso_iff_isIso_descOpcycles φ h₁ h₂ h₃).mp hq
  exact IsColimit.ofIsoColimit (E.complex.opcyclesIsCokernel (-1) 0 (by simp))
    (Cofork.ext (asIso t) (by simp [top, augmentedTop, t, φ, HomologicalComplex.pOpcycles]))

lemma top_exact (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n) :
    E.top.Exact := E.top.exact_of_g_is_cokernel (augmentationIsCokernel E)

lemma augmentation_epi
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n) :
    Epi (E.augmentation.f 0) := epi_of_isColimit_cofork (augmentationIsCokernel E)

/-- Conversely, every ordinary exact augmented row has a quasi-isomorphic
augmentation; the model does not impose an extra cohomological restriction. -/
lemma quasiIso_of_exact_row {X : 𝒜} {K : CochainComplex 𝒜 ℤ}
    [K.IsStrictlyLE 0] (s : K ⟶ (CochainComplex.singleFunctor 𝒜 0).obj X)
    (he : ∀ i : ℤ, i ≠ 0 → K.ExactAt i) (ht : (augmentedTop s).Exact)
    [Epi (s.f 0)] : QuasiIso s := by
  let : Epi (augmentedTop s).g := by
    change Epi (s.f 0)
    infer_instance
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = 0
  · subst i
    let T := (CochainComplex.singleFunctor 𝒜 0).obj X
    let φ := (HomologicalComplex.shortComplexFunctor 𝒜 (.up ℤ) 0).map s
    have h₁ : (K.sc 0).g = 0 := by
      change K.d 0 ((ComplexShape.up ℤ).next 0) = 0
      apply (K.isZero_of_isStrictlyLE 0 _ ?_).eq_of_tgt
      rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel 0 1 from rfl)]
      omega
    have h₂ : (T.sc 0).f = 0 := by simp [T, CochainComplex.singleFunctor]
    have h₃ : (T.sc 0).g = 0 := by simp [T, CochainComplex.singleFunctor]
    let t : K.opcycles 0 ⟶ T.X 0 := (K.sc 0).descOpcycles φ.τ₂ (by rw [← φ.comm₁₂, h₂, comp_zero])
    have hp : K.pOpcycles 0 ≫ t = s.f 0 := by
      exact (K.sc 0).p_descOpcycles _ _
    let u : T.X 0 ⟶ K.opcycles 0 := ht.gIsCokernel.desc
      (CokernelCofork.ofπ (K.pOpcycles 0) (K.d_pOpcycles (-1) 0))
    have hu : s.f 0 ≫ u = K.pOpcycles 0 := by
      exact Cofork.IsColimit.π_desc ht.gIsCokernel
    have htu : t ≫ u = 𝟙 _ := by
      apply (cancel_epi (K.pOpcycles 0)).mp
      rw [← Category.assoc, hp, hu]
      exact (Category.comp_id _).symm
    have hut : u ≫ t = 𝟙 _ := by
      apply (cancel_epi (s.f 0)).mp
      rw [← Category.assoc, hu, hp]
      exact (Category.comp_id _).symm
    have : IsIso t := ⟨⟨u, htu, hut⟩⟩
    apply (quasiIsoAt_iff s 0).mpr
    exact (ShortComplex.quasiIso_iff_isIso_descOpcycles φ h₁ h₂ h₃).mpr this
  · exact (quasiIsoAt_iff_exactAt' s i (HomologicalComplex.ExactAt.of_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi))).mpr (he i hi)

lemma projection_morphism {X' Y' : 𝒜}
    {E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n}
    {F : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X' Y' n}
    {x : X ⟶ X'} {y : Y ⟶ Y'} (f : E.Morphism F x y) :
    f.hom ≫ F.projection = E.projection ≫
      (CochainComplex.singleFunctor 𝒜 (-(n : ℤ))).map y := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, projection, HomologicalComplex.mkHomToSingle_f,
    ← Category.assoc, f.left_comm]
  simp [CochainComplex.singleFunctor, HomologicalComplex.single_map_f_self,
    Category.assoc]

/-- In degree one the exact augmented row is an ordinary short exact sequence. -/
lemma degreeOneSequence_shortExact
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    E.degreeOneSequence.ShortExact := by
  have : Mono (E.complex.d (-1) 0) := by simpa using left_mono E
  have : Epi (E.augmentation.f 0) := augmentation_epi E
  have h : E.top.ShortExact :=
    { exact := top_exact E
      mono_f := inferInstanceAs (Mono (E.complex.d (-1) 0))
      epi_g := inferInstanceAs (Epi (E.augmentation.f 0)) }
  exact ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk (S₁ := E.top) (S₂ := E.degreeOneSequence) E.left (Iso.refl _)
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X)
      (by simp [top, augmentedTop, degreeOneSequence])
      (by simp [top, augmentedTop, degreeOneSequence])) h

open CochainComplex CochainComplex.HomComplex

/-- The degree -1 part of the comparison from the ordinary cone to the row. -/
noncomputable def degreeOneCochain
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    Cochain ((singleFunctor 𝒜 0).obj Y) E.complex (-1) :=
  Cochain.single (p := 0) (q := -1)
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).hom ≫ E.left.inv) (-1)

/-- The degree zero part of the comparison from the ordinary cone to the row. -/
noncomputable def degreeOneInclusion
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    (singleFunctor 𝒜 0).obj (E.complex.X 0) ⟶ E.complex :=
  HomologicalComplex.mkHomFromSingle (𝟙 _) (by
    intro j hj
    apply (E.complex.isZero_of_isStrictlyLE 0 j (by
      change (0 : ℤ) + 1 = j at hj
      omega)).eq_of_tgt)

lemma degreeOneCochain_δ
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    δ (-1) 0 (degreeOneCochain E) = Cochain.ofHom
      ((singleFunctor 𝒜 0).map E.degreeOneSequence.f ≫ (degreeOneInclusion E)) := by
  apply Cochain.ext
  intro p q hpq
  have hq : q = p := by omega
  subst q
  by_cases hp : p = 0
  · subst p
    simp [degreeOneCochain, δ_v (-1) 0 (by omega) _ 0 0 (by omega) (-1) 1 rfl rfl,
      Cochain.single_v, degreeOneSequence, degreeOneInclusion, singleFunctor,
      HomologicalComplex.single_map_f_self, Category.assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Y p hp).eq_of_src _ _

/-- The ordinary mapping cone of the first arrow maps to the displayed row,
with positive components on both nonzero terms. -/
noncomputable def degreeOneConeToRow
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    mappingCone ((singleFunctor 𝒜 0).map E.degreeOneSequence.f) ⟶ E.complex :=
  mappingCone.desc _ (degreeOneCochain E) (degreeOneInclusion E) (degreeOneCochain_δ E)

lemma degreeOneConeToRow_augmentation
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    degreeOneConeToRow E ≫ E.augmentation = mappingCone.descShortComplex
      (E.degreeOneSequence.map (singleFunctor 𝒜 0)) := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  apply mappingCone.ext_from _ 1 0 (by omega)
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Y 1 (by omega)).eq_of_src _ _
  · simp [degreeOneConeToRow, degreeOneInclusion, mappingCone.descShortComplex,
      degreeOneSequence, CochainComplex.singleFunctor,
      HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self,
      Category.assoc]

lemma degreeOneConeToRow_projection
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    degreeOneConeToRow E ≫ E.projection =
      Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift
        ((singleFunctor 𝒜 0).map E.degreeOneSequence.f) ≫
      ((CochainComplex.singleFunctors 𝒜).shiftIso 1 (-1) 0 (by omega)).hom.app Y := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, projection, HomologicalComplex.mkHomToSingle_f]
  apply mappingCone.ext_from _ 0 (-1) (by omega)
  · simp [degreeOneConeToRow, degreeOneCochain,
      Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift,
      CochainComplex.singleFunctor, degreeOneSequence,
      HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.single]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (E.complex.X 0) (-1)
      (by omega)).eq_of_src _ _

variable [HasDerivedCategory.{w} 𝒜]

/-- The positive projection of any two-term row is the negative triangle
boundary of its actual short exact sequence. -/
lemma degreeOne_roof_eq_neg_boundary
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1)
    (hS : E.degreeOneSequence.ShortExact) :
    E.roof = -hS.singleδ := by
  let S := E.degreeOneSequence.map (singleFunctor 𝒜 0)
  have : QuasiIso (mappingCone.descShortComplex S) :=
    mappingCone.quasiIso_descShortComplex (hS.map_of_exact (singleFunctor 𝒜 0))
  have hs := congrArg (fun g => _root_.DerivedCategory.Q.map g)
    (degreeOneConeToRow_augmentation E)
  have hp := congrArg (fun g => _root_.DerivedCategory.Q.map g)
    (degreeOneConeToRow_projection E)
  simp only [Functor.map_comp] at hs hp
  have hi : _root_.DerivedCategory.Q.map
      (((CochainComplex.singleFunctors 𝒜).shiftIso 1 (-1) 0 (by omega)).hom.app Y) ≫
      ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso 1 (-1) 0 (by omega)).inv.app Y =
      (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((singleFunctor 𝒜 0).obj Y) := by
    simp [_root_.DerivedCategory.singleFunctors,
      SingleFunctors.postcomp_shiftIso_inv_app, ← Functor.map_comp_assoc,
      CochainComplex.singleFunctor]
  have hb := ExtBoundarySigns.positive_projection 𝒜 S
    (hS.map_of_exact (singleFunctor 𝒜 0))
  change inv (_root_.DerivedCategory.Q.map (mappingCone.descShortComplex S)) ≫
    _root_.DerivedCategory.Q.map
      (Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift S.f) ≫
    (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ = -hS.singleδ at hb
  apply (cancel_epi (_root_.DerivedCategory.Q.map (mappingCone.descShortComplex S))).mp
  calc
    _root_.DerivedCategory.Q.map (mappingCone.descShortComplex S) ≫ E.roof =
        _root_.DerivedCategory.Q.map (degreeOneConeToRow E) ≫
        _root_.DerivedCategory.Q.map E.projection ≫
        ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso 1 (-1) 0 (by omega)).inv.app Y := by
      rw [← hs]
      simp [roof, Category.assoc]
    _ = _root_.DerivedCategory.Q.map
        (Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift S.f) ≫
        (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ := by
      rw [← Category.assoc, hp, Category.assoc, hi]
      rfl
    _ = _root_.DerivedCategory.Q.map (mappingCone.descShortComplex S) ≫
        (-hS.singleδ) := by rw [← hb]; simp

lemma roof_eq_of_map {E F :
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n}
    (f : E.Map F) : E.roof = F.roof := by
  have hs := congrArg (fun g => _root_.DerivedCategory.Q.map g) f.right_comm
  have hp := congrArg (fun g => _root_.DerivedCategory.Q.map g) (projection_naturality f)
  simp only [Functor.map_comp] at hs hp
  apply (cancel_epi (_root_.DerivedCategory.Q.map E.augmentation)).mp
  simp only [roof, IsIso.hom_inv_id_assoc]
  rw [← hs]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, hp]

lemma roof_eq_of_equivalent {E F :
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n}
    (h : E.Equivalent F) : E.roof = F.roof := by
  induction h with
  | rel _ _ h => exact roof_eq_of_map h.some
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h h' => exact h.trans h'

lemma roof_morphism {X' Y' : 𝒜}
    {E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n}
    {F : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X' Y' n}
    {x : X ⟶ X'} {y : Y ⟶ Y'} (f : E.Morphism F x y) :
    E.roof ≫ ((_root_.DerivedCategory.singleFunctor 𝒜 0).map y)⟦(n : ℤ)⟧' =
      (_root_.DerivedCategory.singleFunctor 𝒜 0).map x ≫ F.roof := by
  have hs := congrArg (fun g => _root_.DerivedCategory.Q.map g) f.right_comm
  have hp := congrArg (fun g => _root_.DerivedCategory.Q.map g) (projection_morphism f)
  simp only [Functor.map_comp] at hs hp
  change _ = _root_.DerivedCategory.Q.map E.augmentation ≫
    (_root_.DerivedCategory.singleFunctor 𝒜 0).map x at hs
  change _ = _root_.DerivedCategory.Q.map E.projection ≫
    (_root_.DerivedCategory.singleFunctor 𝒜 (-(n : ℤ))).map y at hp
  apply (cancel_epi (_root_.DerivedCategory.Q.map E.augmentation)).mp
  simp only [roof, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% hs]
  simp only [IsIso.hom_inv_id_assoc]
  have hy := (((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso
    (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.naturality y)
  change (_root_.DerivedCategory.singleFunctor 𝒜 (-(n : ℤ))).map y ≫ _ =
    _ ≫ ((_root_.DerivedCategory.singleFunctor 𝒜 0).map y)⟦(n : ℤ)⟧' at hy
  rw [← hy, ← reassoc_of% hp]

/-- Every derived morphism has a roof with middle complex supported in the
finite interval needed for a row. No resolution hypothesis is used. -/
lemma bounded_roof {X Y : 𝒜} (n : ℕ)
    (h : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (n : ℤ)) :
    ∃ (K : CochainComplex 𝒜 ℤ) (_ : K.IsStrictlyGE (-(n : ℤ)))
      (_ : K.IsStrictlyLE 0)
      (s : K ⟶ (CochainComplex.singleFunctor 𝒜 0).obj X) (_ : QuasiIso s)
      (g : K ⟶ (CochainComplex.singleFunctor 𝒜 (-(n : ℤ))).obj Y),
      h = inv (_root_.DerivedCategory.Q.map s) ≫ _root_.DerivedCategory.Q.map g ≫
        ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso
          (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app Y := by
  let U := (CochainComplex.singleFunctor 𝒜 0).obj X
  have : U.IsStrictlyGE (-(n : ℤ)) :=
    U.isStrictlyGE_of_ge (-(n : ℤ)) 0 (by omega)
  let I := ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso
    (n : ℤ) (-(n : ℤ)) 0 (by omega)).app Y
  obtain ⟨K, hge, hle, s, hs, g, hg⟩ :=
    _root_.DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE
      (-(n : ℤ)) 0 (h ≫ I.hom)
  have hq : QuasiIso s := (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso 𝒜 s).mp hs
  refine ⟨K, hge, hle, s, hq, g, ?_⟩
  rw [← Category.assoc, ← hg]
  simp [I]

lemma normalization_involutive {X Y : 𝒜} (n : ℕ)
    (a : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (n : ℤ)) :
    normalization n • (normalization n • a) = a := by
  rw [smul_smul]
  simp [normalization, Int.units_mul_self]

end Extension

/-- A homotopy change of the endpoint map gives a shear isomorphism of
pushouts. This is the categorical form of (y,b) ↦ (y-h(b),b). -/
noncomputable def pushoutShear {A B Y : 𝒜} (d : A ⟶ B) (f : A ⟶ Y) (h : B ⟶ Y) :
    pushout d f ≅ pushout d (f + d ≫ h) where
  hom := pushout.desc
    (pushout.inl d (f + d ≫ h) - h ≫ pushout.inr d (f + d ≫ h))
    (pushout.inr d (f + d ≫ h)) (by
      rw [Preadditive.comp_sub, pushout.condition, Preadditive.add_comp]
      simp only [Category.assoc]
      abel)
  inv := pushout.desc
    (pushout.inl d f + h ≫ pushout.inr d f) (pushout.inr d f) (by
      simp [Preadditive.comp_add, Preadditive.add_comp, pushout.condition,
        Category.assoc])
  hom_inv_id := by
    apply pushout.hom_ext <;>
      simp [Preadditive.sub_comp, Category.assoc]
  inv_hom_id := by
    apply pushout.hom_ext <;>
      simp [Preadditive.add_comp, Category.assoc]

@[reassoc (attr := simp)]
lemma pushoutShear_inr {A B Y : 𝒜} (d : A ⟶ B) (f : A ⟶ Y) (h : B ⟶ Y) :
    pushout.inr d f ≫ (pushoutShear d f h).hom = pushout.inr d (f + d ≫ h) := by
  simp [pushoutShear]

@[reassoc (attr := simp)]
lemma pushoutShear_inl {A B Y : 𝒜} (d : A ⟶ B) (f : A ⟶ Y) (h : B ⟶ Y) :
    pushout.inl d f ≫ (pushoutShear d f h).hom =
      pushout.inl d (f + d ≫ h) - h ≫ pushout.inr d (f + d ≫ h) := by
  simp [pushoutShear]

/-- The shear fixes the two endpoints of a pushed-out row. -/
lemma pushoutShear_endpoints (S : ShortComplex 𝒜) {Y : 𝒜}
    (f : S.X₁ ⟶ Y) (h : S.X₂ ⟶ Y) :
    (S.push f).f ≫ (pushoutShear S.f f h).hom = (S.push (f + S.f ≫ h)).f ∧
    (pushoutShear S.f f h).hom ≫ (S.push (f + S.f ≫ h)).g = (S.push f).g := by
  constructor
  · exact pushoutShear_inr _ _ _
  · apply pushout.hom_ext <;>
      simp [Category.assoc, ShortComplex.push, pushoutShear, Preadditive.sub_comp]

theorem exact_row : exactRowType := by
  intro 𝒜 _ _ X Y n E
  exact ⟨Extension.exactAt E, Extension.left_mono E, Extension.top_exact E,
    Extension.augmentation_epi E⟩

theorem row_augmentation : rowAugmentationType := by
  intro 𝒜 _ _ X K hK s he ht hs
  exact Extension.quasiIso_of_exact_row s he ht

theorem invariant : invariantType := by
  intro 𝒜 _ _ _ X Y n E F h
  simp only [Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.yonedaClass,
    Extension.roof_eq_of_equivalent h]

theorem degree_one : degreeOneType := by
  intro 𝒜 _ _ _ X Y E
  simp [Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.yonedaClass,
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.normalization]

theorem degree_one_boundary : degreeOneBoundaryType := by
  intro 𝒜 _ _ _ X Y E
  exact ⟨Extension.degreeOneSequence_shortExact E,
    (degree_one 𝒜 X Y E).trans
      (Extension.degreeOne_roof_eq_neg_boundary E _)⟩

theorem map_naturality : mapNaturalityType := by
  intro 𝒜 _ _ _ X Y X' Y' n E F x y f
  simpa only [yonedaClass, Units.smul_def, Linear.smul_comp, Linear.comp_smul] using
    congrArg (fun z => normalization n • z) (Extension.roof_morphism f)

theorem quotient_map : quotientMapType := by
  intro 𝒜 _ _ _ X Y n
  exact ⟨Quotient.lift (fun E => E.yonedaClass) (fun E F h => invariant 𝒜 X Y _ E F h),
    fun _ => rfl⟩

end AdvancedHomologicalAlgebra.HigherYonedaClasses

namespace AdvancedHomologicalAlgebra.HigherYonedaClasses
namespace EndpointPush
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

noncomputable def disk (Y : 𝒜) (a : ℤ) : CochainComplex 𝒜 ℤ :=
  HomologicalComplex.double (𝟙 Y) (show (ComplexShape.up ℤ).Rel a (a+1) by simp)
noncomputable def disk₀ (Y : 𝒜) (a : ℤ) : (disk Y a).X a ≅ Y :=
  HomologicalComplex.doubleXIso₀ _ _
noncomputable def disk₁ (Y : 𝒜) (a : ℤ) : (disk Y a).X (a+1) ≅ Y :=
  HomologicalComplex.doubleXIso₁ _ _ (by omega)
lemma disk_d (Y : 𝒜) (a : ℤ) : (disk Y a).d a (a+1) = (disk₀ Y a).hom ≫ (disk₁ Y a).inv := by
  simpa only [disk, disk₀, disk₁, Category.id_comp] using
    HomologicalComplex.double_d (𝟙 Y) (show (ComplexShape.up ℤ).Rel a (a+1) by simp) (by omega)
lemma disk_zero (Y : 𝒜) (a i : ℤ) (h : i ≠ a) (h' : i ≠ a+1) :
    IsZero ((disk Y a).X i) := HomologicalComplex.isZero_double_X _ _ _ h h'
lemma disk_acyclic (Y : 𝒜) (a : ℤ) : (disk Y a).Acyclic := by
  intro i
  by_cases h : i = a
  · subst i
    rw [HomologicalComplex.exactAt_iff' (K := disk Y a) (i := a-1) (j := a) (k := a+1) (by simp) (by simp)]
    apply (ShortComplex.exact_iff_mono _ ?_).2
    · change Mono ((disk Y a).d a (a+1))
      rw [disk_d]
      infer_instance
    · change (disk Y a).d (a-1) a = 0
      exact (disk_zero Y a (a-1) (by omega) (by omega)).eq_zero_of_src _
  · by_cases h' : i = a+1
    · subst i
      rw [HomologicalComplex.exactAt_iff' (K := disk Y a) (i := a) (j := a+1) (k := a+2) (by simp) (by simp; omega)]
      apply (ShortComplex.exact_iff_epi _ ?_).2
      · change Epi ((disk Y a).d a (a+1))
        rw [disk_d]
        infer_instance
      · change (disk Y a).d (a+1) (a+2) = 0
        exact (disk_zero Y a (a+2) (by omega) (by omega)).eq_zero_of_tgt _
    · exact HomologicalComplex.ExactAt.of_isZero (disk_zero Y a i h h')

noncomputable def fromDisk {Y : 𝒜} {a : ℤ} {K : CochainComplex 𝒜 ℤ}
    (f : Y ⟶ K.X a) : disk Y a ⟶ K :=
  HomologicalComplex.mkHomFromDouble (by simp) (by omega)
    f (f ≫ K.d a (a+1)) (by simp) (by simp)
@[simp] lemma fromDisk_f₀ {Y : 𝒜} {a : ℤ} {K : CochainComplex 𝒜 ℤ}
    (f : Y ⟶ K.X a) : (fromDisk f).f a = (disk₀ Y a).hom ≫ f := by
  exact HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _
@[simp] lemma fromDisk_f₁ {Y : 𝒜} {a : ℤ} {K : CochainComplex 𝒜 ℤ}
    (f : Y ⟶ K.X a) : (fromDisk f).f (a+1) = (disk₁ Y a).hom ≫ f ≫ K.d a (a+1) := by
  simp only [fromDisk, HomologicalComplex.mkHomFromDouble_f₁, disk₁]
noncomputable def diskMap {Y Z : 𝒜} (f : Y ⟶ Z) (a : ℤ) : disk Y a ⟶ disk Z a :=
  fromDisk (f ≫ (disk₀ Z a).inv)
@[simp] lemma diskMap_f₀ {Y Z : 𝒜} (f : Y ⟶ Z) (a : ℤ) :
    (diskMap f a).f a = (disk₀ Y a).hom ≫ f ≫ (disk₀ Z a).inv := by
  simp [diskMap]
@[simp] lemma diskMap_f₁ {Y Z : 𝒜} (f : Y ⟶ Z) (a : ℤ) :
    (diskMap f a).f (a+1) = (disk₁ Y a).hom ≫ f ≫ (disk₁ Z a).inv := by
  simp [diskMap, disk_d]

lemma disk_mono {X Y : 𝒜} {n : ℕ} (E : Extension X Y n) :
    Mono (fromDisk E.left.inv) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  by_cases h : i = -(n:ℤ)
  · subst i
    simp only [fromDisk_f₀]
    infer_instance
  · by_cases h' : i = -(n:ℤ)+1
    · subst i
      rw [fromDisk_f₁]
      have := AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.left_mono E
      infer_instance
    · exact ⟨fun _ _ _ => (disk_zero Y _ _ h h').eq_of_tgt _ _⟩

lemma quasiIso_of_shortExact_of_acyclic_left
    {S : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact) (h : S.X₁.Acyclic) :
    QuasiIso S.g := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₂ i).mono_g ((h i).isZero_homology.eq_zero_of_src _)
  have : Epi (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₃ i (i+1) (by simp)).epi_f ((h (i+1)).isZero_homology.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

lemma disk_hom_ext {Y : 𝒜} {a : ℤ} {K : CochainComplex 𝒜 ℤ}
    {f g : disk Y a ⟶ K} (h : f.f a = g.f a) : f = g := by
  apply HomologicalComplex.from_double_hom_ext h
  have : IsIso ((disk Y a).d a (a+1)) := by rw [disk_d]; infer_instance
  apply (cancel_epi ((disk Y a).d a (a+1))).mp
  rw [← f.comm, ← g.comm, h]

variable {X Y Y' : 𝒜} {n : ℕ}
noncomputable def pushComplex (E : Extension X Y n) (y : Y ⟶ Y') : CochainComplex 𝒜 ℤ :=
  pushout (fromDisk E.left.inv) (diskMap y (-(n:ℤ)))
noncomputable def pushInl (E : Extension X Y n) (y : Y ⟶ Y') : E.complex ⟶ pushComplex E y :=
  pushout.inl _ _
noncomputable def pushInr (E : Extension X Y n) (y : Y ⟶ Y') : disk Y' (-(n:ℤ)) ⟶ pushComplex E y :=
  pushout.inr _ _
lemma push_isPushout (E : Extension X Y n) (y : Y ⟶ Y') (i : ℤ) :
    IsPushout ((fromDisk E.left.inv).f i) ((diskMap y (-(n:ℤ))).f i)
      ((pushInl E y).f i) ((pushInr E y).f i) :=
  (IsPushout.of_hasPushout (fromDisk E.left.inv) (diskMap y (-(n:ℤ)))).map
    (HomologicalComplex.eval 𝒜 (.up ℤ) i)

lemma disk_augmentation (E : Extension X Y n) : fromDisk E.left.inv ≫ E.augmentation = 0 := by
  apply disk_hom_ext
  exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X (-(n:ℤ)) (by
    have := E.positive; omega)).eq_of_tgt _ _
noncomputable def pushAugmentation (E : Extension X Y n) (y : Y ⟶ Y') :
    pushComplex E y ⟶ (CochainComplex.singleFunctor 𝒜 0).obj X :=
  pushout.desc E.augmentation 0 (by simp only [disk_augmentation, comp_zero])

lemma pushInl_quasiIso (E : Extension X Y n) (y : Y ⟶ Y') : QuasiIso (pushInl E y) := by
  let f := fromDisk E.left.inv
  have : Mono f := disk_mono E
  let S := ShortComplex.cokernelSequence f
  have : Mono S.f := ‹Mono f›
  have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact f }
  have hS' : (S.push (diskMap y (-(n:ℤ)))).ShortExact := hS.push _
  have : QuasiIso S.g := quasiIso_of_shortExact_of_acyclic_left hS (disk_acyclic _ _)
  have : QuasiIso (S.push (diskMap y (-(n:ℤ)))).g :=
    quasiIso_of_shortExact_of_acyclic_left hS' (disk_acyclic _ _)
  have hcomp : pushInl E y ≫ (S.push (diskMap y (-(n:ℤ)))).g = S.g := by
    exact pushout.inl_desc _ _ _
  have : QuasiIso (pushInl E y ≫ (S.push (diskMap y (-(n:ℤ)))).g) := by
    rw [hcomp]
    infer_instance
  exact quasiIso_of_comp_right (pushInl E y) (S.push (diskMap y (-(n:ℤ)))).g

lemma pushAugmentation_quasiIso (E : Extension X Y n) (y : Y ⟶ Y') :
    QuasiIso (pushAugmentation E y) := by
  have := pushInl_quasiIso E y
  have : QuasiIso (pushInl E y ≫ pushAugmentation E y) := by
    change QuasiIso (pushout.inl _ _ ≫ pushout.desc E.augmentation 0 _)
    simpa only [pushout.inl_desc] using E.exact
  exact quasiIso_of_comp_left (pushInl E y) (pushAugmentation E y)

lemma pushComplex_isStrictlyGE (E : Extension X Y n) (y : Y ⟶ Y') :
    (pushComplex E y).IsStrictlyGE (-(n:ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [IsZero.iff_id_eq_zero]
  apply (push_isPushout E y i).hom_ext
  · exact (E.complex.isZero_of_isStrictlyGE (-(n:ℤ)) i hi).eq_of_src _ _
  · exact (disk_zero Y' (-(n:ℤ)) i (by omega) (by omega)).eq_of_src _ _

lemma pushComplex_isStrictlyLE (E : Extension X Y n) (y : Y ⟶ Y') :
    (pushComplex E y).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [IsZero.iff_id_eq_zero]
  apply (push_isPushout E y i).hom_ext
  · exact (E.complex.isZero_of_isStrictlyLE 0 i hi).eq_of_src _ _
  · have := E.positive
    exact (disk_zero Y' (-(n:ℤ)) i (by omega) (by omega)).eq_of_src _ _

lemma pushInr_isIso (E : Extension X Y n) (y : Y ⟶ Y') :
    IsIso ((pushInr E y).f (-(n:ℤ))) := by
  have h : IsIso ((fromDisk E.left.inv).f (-(n:ℤ))) := by
    rw [fromDisk_f₀]
    infer_instance
  exact (push_isPushout E y (-(n:ℤ))).isIso_inr_of_isIso
noncomputable def pushLeft (E : Extension X Y n) (y : Y ⟶ Y') :
    (pushComplex E y).X (-(n:ℤ)) ≅ Y' := by
  have := pushInr_isIso E y
  exact (asIso ((pushInr E y).f (-(n:ℤ)))).symm ≪≫ disk₀ Y' (-(n:ℤ))

lemma push_left_comm (E : Extension X Y n) (y : Y ⟶ Y') :
    (pushInl E y).f (-(n:ℤ)) ≫ (pushLeft E y).hom = E.left.hom ≫ y := by
  have := pushInr_isIso E y
  apply (cancel_epi ((disk₀ Y (-(n:ℤ))).hom ≫ E.left.inv)).mp
  have hh := (push_isPushout E y (-(n:ℤ))).w
  rw [fromDisk_f₀, diskMap_f₀] at hh
  dsimp [pushLeft]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Category.assoc, hh]
  simp

noncomputable def push (E : Extension X Y n) (y : Y ⟶ Y') : Extension X Y' n where
  positive := E.positive
  complex := pushComplex E y
  supportedGE := pushComplex_isStrictlyGE E y
  supportedLE := pushComplex_isStrictlyLE E y
  left := pushLeft E y
  augmentation := pushAugmentation E y
  exact := pushAugmentation_quasiIso E y
noncomputable def pushMorphism (E : Extension X Y n) (y : Y ⟶ Y') :
    E.Morphism (push E y) (𝟙 X) y where
  hom := pushInl E y
  left_comm := push_left_comm E y
  right_comm := by simp [push, pushInl, pushAugmentation]

noncomputable def pushFirst (E : Extension X Y n) (y : Y ⟶ Y') :
    Y' ⟶ (pushComplex E y).X (-(n:ℤ)+1) :=
  (disk₁ Y' (-(n:ℤ))).inv ≫ (pushInr E y).f (-(n:ℤ)+1)

lemma push_first_isPushout (E : Extension X Y n) (y : Y ⟶ Y') :
    IsPushout (E.left.inv ≫ E.complex.d (-(n:ℤ)) (-(n:ℤ)+1)) y
      ((pushInl E y).f (-(n:ℤ)+1)) (pushFirst E y) := by
  apply (push_isPushout E y (-(n:ℤ)+1)).of_iso
      (disk₁ Y (-(n:ℤ))) (Iso.refl _) (disk₁ Y' (-(n:ℤ))) (Iso.refl _)
  · simp
  · simp
  · simp
  · simp [pushFirst]

lemma pushFirst_eq (E : Extension X Y n) (y : Y ⟶ Y') :
    (pushLeft E y).inv ≫ (pushComplex E y).d (-(n:ℤ)) (-(n:ℤ)+1) = pushFirst E y := by
  have := pushInr_isIso E y
  dsimp [pushLeft]
  rw [Category.assoc, (pushInr E y).comm, disk_d]
  simp [pushFirst]

lemma push_endpoint_isPushout (E : Extension X Y n) (y : Y ⟶ Y') :
    IsPushout (E.left.inv ≫ E.complex.d (-(n:ℤ)) (-(n:ℤ)+1)) y
      ((pushInl E y).f (-(n:ℤ)+1))
      ((push E y).left.inv ≫ (push E y).complex.d (-(n:ℤ)) (-(n:ℤ)+1)) := by
  change IsPushout _ _ _ ((pushLeft E y).inv ≫ (pushComplex E y).d (-(n:ℤ)) (-(n:ℤ)+1))
  rw [pushFirst_eq]
  exact push_first_isPushout E y

lemma pushInl_isIso (E : Extension X Y n) (y : Y ⟶ Y') (i : ℤ)
    (hi : i ≠ -(n:ℤ)) (hi' : i ≠ -(n:ℤ)+1) :
    IsIso ((pushInl E y).f i) := by
  have := (disk_zero Y (-(n:ℤ)) i hi hi').isIso
    (disk_zero Y' (-(n:ℤ)) i hi hi') ((diskMap y (-(n:ℤ))).f i)
  exact (push_isPushout E y i).isIso_inl_of_isIso

variable {X' : 𝒜}
lemma fromDisk_morphism {E : Extension X Y n} {F : Extension X' Y' n}
    {x : X ⟶ X'} {y : Y ⟶ Y'} (f : E.Morphism F x y) :
    fromDisk E.left.inv ≫ f.hom = diskMap y (-(n:ℤ)) ≫ fromDisk F.left.inv := by
  apply disk_hom_ext
  simp only [HomologicalComplex.comp_f, fromDisk_f₀, diskMap_f₀,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← cancel_mono F.left.hom]
  simp [f.left_comm, Category.assoc]

noncomputable def pushDescHom {E : Extension X Y n} {F : Extension X' Y' n}
    {x : X ⟶ X'} {y : Y ⟶ Y'} (f : E.Morphism F x y) :
    (push E y).complex ⟶ F.complex :=
  pushout.desc f.hom (fromDisk F.left.inv) (fromDisk_morphism f)

noncomputable def pushDescMorphism {E : Extension X Y n} {F : Extension X' Y' n}
    {x : X ⟶ X'} {y : Y ⟶ Y'} (f : E.Morphism F x y) :
    (push E y).Morphism F x (𝟙 Y') where
  hom := pushDescHom f
  left_comm := by
    have := pushInr_isIso E y
    apply (cancel_epi ((pushInr E y).f (-(n:ℤ)))).mp
    have hh : (pushInr E y).f (-(n:ℤ)) ≫ (pushDescHom f).f (-(n:ℤ)) =
        (fromDisk F.left.inv).f (-(n:ℤ)) := by
      exact HomologicalComplex.congr_hom (pushout.inr_desc _ _ _) _
    rw [← Category.assoc, hh, fromDisk_f₀]
    simp [push, pushLeft]
  right_comm := by
    apply pushout.hom_ext
    · simpa [pushDescHom, push, pushAugmentation, Category.assoc] using f.right_comm
    · simp [pushDescHom, push, pushAugmentation, disk_augmentation]

noncomputable def pushMap {E F : Extension X Y n} (f : E.Map F) (y : Y ⟶ Y') :
    (push E y).Map (push F y) := by
  let g : E.Morphism (push F y) (𝟙 X) y :=
    { hom := f.hom ≫ pushInl F y
      left_comm := by
        change (f.hom ≫ pushInl F y).f (-(n:ℤ)) ≫ (pushLeft F y).hom = _
        rw [HomologicalComplex.comp_f, Category.assoc, push_left_comm]
        rw [← Category.assoc, f.left_comm]
      right_comm := by
        simp [push, pushAugmentation, pushInl, Category.assoc, f.right_comm] }
  let q := pushDescMorphism g
  exact { hom := q.hom
          left_comm := by simpa using q.left_comm
          right_comm := by simpa using q.right_comm }

lemma push_equivalent {E F : Extension X Y n} (h : E.Equivalent F) (y : Y ⟶ Y') :
    (push E y).Equivalent (push F y) := by
  induction h with
  | rel E F h => exact Relation.EqvGen.rel _ _ ⟨pushMap h.some y⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ h => exact Relation.EqvGen.symm _ _ h
  | trans _ _ _ _ _ h h' => exact Relation.EqvGen.trans _ _ _ h h'

noncomputable def pushQuotient (X : 𝒜) {Y Y' : 𝒜} (n : ℕ) (y : Y ⟶ Y') :
    Quotient (Extension.extensionSetoid X Y n) → Quotient (Extension.extensionSetoid X Y' n) :=
  Quotient.map (fun E => push E y) (fun _ _ h => push_equivalent h y)

open CochainComplex CochainComplex.HomComplex
noncomputable def shearCochain (E : Extension X Y n) (y : Y ⟶ Y')
    (h : E.complex.X (-(n:ℤ)+1) ⟶ Y') : Cochain E.complex (push E y).complex (-1) :=
  Cochain.single (p := -(n:ℤ)+1) (q := -(n:ℤ))
    (h ≫ (push E y).left.inv) (-1)
noncomputable def shearBoundary (E : Extension X Y n) (y : Y ⟶ Y')
    (h : E.complex.X (-(n:ℤ)+1) ⟶ Y') : E.complex ⟶ (push E y).complex :=
  Cocycle.homOf (Cocycle.mk (δ (-1) 0 (shearCochain E y h)) 1 (by omega) (δ_δ _ _ _ _))

lemma shearBoundary_left (E : Extension X Y n) (y : Y ⟶ Y')
    (h : E.complex.X (-(n:ℤ)+1) ⟶ Y') :
    (shearBoundary E y h).f (-(n:ℤ)) ≫ (push E y).left.hom =
      E.complex.d (-(n:ℤ)) (-(n:ℤ)+1) ≫ h := by
  simp only [shearBoundary, Cocycle.homOf_f, Cocycle.mk_coe]
  rw [δ_v (-1) 0 (by omega) _ (-(n:ℤ)) (-(n:ℤ)) (by omega) (-(n:ℤ)-1) (-(n:ℤ)+1) rfl rfl]
  simp [shearCochain, Cochain.single_v_eq_zero _ _ _ _ _ (show -(n:ℤ) ≠ -(n:ℤ)+1 by omega),
    Cochain.single_v, Category.assoc]

lemma shearBoundary_augmentation (E : Extension X Y n) (y : Y ⟶ Y')
    (h : E.complex.X (-(n:ℤ)+1) ⟶ Y') :
    shearBoundary E y h ≫ (push E y).augmentation = 0 := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply,
    shearBoundary, Cocycle.homOf_f, Cocycle.mk_coe]
  rw [δ_v (-1) 0 (by omega) _ 0 0 (by omega) (-1) 1 rfl rfl]
  have hn : (1:ℤ) ≠ -(n:ℤ)+1 := by have := E.positive; omega
  simp [shearCochain, Cochain.single_v_eq_zero _ _ _ _ _ hn,
    Category.assoc, (push E y).augmentation_zero]

noncomputable def shearMorphism (E : Extension X Y n) (y : Y ⟶ Y')
    (h : E.complex.X (-(n:ℤ)+1) ⟶ Y') :
    E.Morphism (push E (y + E.left.inv ≫ E.complex.d (-(n:ℤ)) (-(n:ℤ)+1) ≫ h)) (𝟙 X) y where
  hom := (pushMorphism E _).hom - shearBoundary E _ h
  left_comm := by
    rw [HomologicalComplex.sub_f_apply, Preadditive.sub_comp, (pushMorphism E _).left_comm, shearBoundary_left]
    simp only [Preadditive.comp_add, Iso.hom_inv_id_assoc]
    abel
  right_comm := by
    rw [Preadditive.sub_comp, shearBoundary_augmentation, sub_zero]
    exact (pushMorphism E _).right_comm

lemma push_shear_equivalent (E : Extension X Y n) (y : Y ⟶ Y')
    (h : E.complex.X (-(n:ℤ)+1) ⟶ Y') :
    (push E y).Equivalent (push E (y + E.left.inv ≫ E.complex.d (-(n:ℤ)) (-(n:ℤ)+1) ≫ h)) := by
  let g := pushDescMorphism (shearMorphism E y h)
  apply Relation.EqvGen.rel
  refine ⟨{ hom := g.hom, left_comm := ?_, right_comm := ?_ }⟩
  · simpa using g.left_comm
  · simpa using g.right_comm

lemma push_equivalent_of_morphism {E : Extension X Y n} {F : Extension X Y' n}
    {y : Y ⟶ Y'} (f : E.Morphism F (𝟙 X) y) :
    (push E y).Equivalent F := by
  let g := pushDescMorphism f
  apply Relation.EqvGen.rel
  refine ⟨{ hom := g.hom, left_comm := ?_, right_comm := ?_ }⟩
  · simpa using g.left_comm
  · simpa using g.right_comm

lemma equivalent_of_common_morphism {A : 𝒜} {V : Extension X A n}
    {E F : Extension X Y n} {y z : A ⟶ Y}
    (f : V.Morphism E (𝟙 X) y) (g : V.Morphism F (𝟙 X) z)
    (h : V.complex.X (-(n:ℤ)+1) ⟶ Y)
    (hy : y = z + (V.left.inv ≫ V.complex.d (-(n:ℤ)) (-(n:ℤ)+1)) ≫ h) :
    E.Equivalent F := by
  have hs := push_shear_equivalent V z h
  have hs' : (push V z).Equivalent (push V y) := by
    simpa only [hy, Category.assoc] using hs
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (push_equivalent_of_morphism f))
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hs')
      (push_equivalent_of_morphism g))

end EndpointPush

end AdvancedHomologicalAlgebra.HigherYonedaClasses

open CochainComplex CochainComplex.HomComplex

namespace AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The cone of a stalk map has the domain as its degree -1 term. -/
noncomputable def stalkConeLeftIso (S : ShortComplex 𝒜) :
    (mappingCone ((singleFunctor 𝒜 0).map S.f)).X (-1) ≅ S.X₁ where
  hom := (mappingCone.fst ((singleFunctor 𝒜 0).map S.f)).1.v (-1) 0 (by omega) ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).hom
  inv := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₁).inv ≫
    (mappingCone.inl ((singleFunctor 𝒜 0).map S.f)).v 0 (-1) (by omega)
  hom_inv_id := by
    apply mappingCone.ext_from _ 0 (-1) (by omega)
    · simp
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ (-1) (by omega)).eq_of_src _ _
  inv_hom_id := by simp

/-- An ordinary short exact sequence, represented by its positive two-term cone. -/
noncomputable def ofShortExact (S : ShortComplex 𝒜) (hS : S.ShortExact) :
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension S.X₃ S.X₁ 1 where
  positive := by omega
  complex := mappingCone ((singleFunctor 𝒜 0).map S.f)
  supportedGE := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₁ (i+1) (by omega),
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ i (by omega)⟩
  supportedLE := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [mappingCone.isZero_X_iff]
    exact ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₁ (i+1) (by omega),
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ i (by omega)⟩
  left := stalkConeLeftIso S
  augmentation := mappingCone.descShortComplex (S.map (singleFunctor 𝒜 0))
  exact := mappingCone.quasiIso_descShortComplex (hS.map_of_exact _)

lemma ofShortExact_projection (S : ShortComplex 𝒜) (hS : S.ShortExact) :
    (ofShortExact S hS).projection =
      Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift
        ((singleFunctor 𝒜 0).map S.f) ≫
      ((CochainComplex.singleFunctors 𝒜).shiftIso 1 (-1) 0 (by omega)).hom.app S.X₁ := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, projection, HomologicalComplex.mkHomToSingle_f]
  apply mappingCone.ext_from _ 0 (-1) (by omega)
  · simp [ofShortExact, stalkConeLeftIso,
      Specs.AdvancedHomologicalAlgebra.MappingCones.projectionToShift,
      CochainComplex.singleFunctor, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.single]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ (-1) (by omega)).eq_of_src _ _

variable {X Y : 𝒜}

noncomputable def toShortExtension
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    Specs.AdvancedHomologicalAlgebra.DegreeOneExtensionClasses.Extension Y X where
  B := E.complex.X 0
  i := E.degreeOneSequence.f
  p := E.degreeOneSequence.g
  zero := E.degreeOneSequence.zero
  shortExact := degreeOneSequence_shortExact E

/-- A map of the middle terms of two ordinary degree-one sequences induces
an endpoint-fixing map from the cone model of the first row to the second. -/
noncomputable def degreeOneConeMap
    (E F : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1)
    (b : E.complex.X 0 ⟶ F.complex.X 0)
    (hi : E.degreeOneSequence.f ≫ b = F.degreeOneSequence.f)
    (hp : b ≫ F.degreeOneSequence.g = E.degreeOneSequence.g) :
    (ofShortExact E.degreeOneSequence (degreeOneSequence_shortExact E)).Map F where
  hom := mappingCone.desc _ (degreeOneCochain F)
    ((singleFunctor 𝒜 0).map b ≫ degreeOneInclusion F) (by
      rw [degreeOneCochain_δ, ← hi, Functor.map_comp, Category.assoc])
  left_comm := by
    change (mappingCone.desc _ _ _ _).f (-1) ≫ F.left.hom =
      (stalkConeLeftIso E.degreeOneSequence).hom
    apply mappingCone.ext_from _ 0 (-1) (by omega)
    · simp [degreeOneCochain, stalkConeLeftIso, degreeOneSequence]
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (E.complex.X 0) (-1) (by omega)).eq_of_src _ _
  right_comm := by
    apply HomologicalComplex.to_single_hom_ext
    simp only [HomologicalComplex.comp_f]
    apply mappingCone.ext_from _ 1 0 (by omega)
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Y 1 (by omega)).eq_of_src _ _
    · have hp' : b ≫ F.augmentation.f 0 = E.augmentation.f 0 :=
        (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom).mp
          (by simpa [degreeOneSequence, Category.assoc] using hp)
      simpa [mappingCone.descShortComplex, degreeOneInclusion,
        CochainComplex.singleFunctor, HomologicalComplex.mkHomFromSingle_f,
        HomologicalComplex.single_map_f_self, ofShortExact, degreeOneSequence,
        Category.assoc] using hp'

/-- The geometric Baer operation in degree one: use the actual direct sum,
diagonal pullback, and codiagonal pushout of the ordinary short exact rows. -/
noncomputable def degreeOneBaer
    (E F : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1 :=
  ofShortExact ((toShortExtension E).baer (toShortExtension F)).sequence
    ((toShortExtension E).baer (toShortExtension F)).shortExact

variable [HasDerivedCategory.{w} 𝒜]

lemma ofShortExact_yonedaClass (S : ShortComplex 𝒜) (hS : S.ShortExact) :
    (ofShortExact S hS).yonedaClass = -hS.singleδ := by
  let := mappingCone.quasiIso_descShortComplex (hS.map_of_exact (singleFunctor 𝒜 0))
  have hp := congrArg (fun g => _root_.DerivedCategory.Q.map g) (ofShortExact_projection S hS)
  simp only [Functor.map_comp] at hp
  have hi : _root_.DerivedCategory.Q.map
      (((CochainComplex.singleFunctors 𝒜).shiftIso 1 (-1) 0 (by omega)).hom.app S.X₁) ≫
      ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso 1 (-1) 0 (by omega)).inv.app S.X₁ =
      (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((singleFunctor 𝒜 0).obj S.X₁) := by
    simp [_root_.DerivedCategory.singleFunctors,
      SingleFunctors.postcomp_shiftIso_inv_app, ← Functor.map_comp_assoc,
      CochainComplex.singleFunctor]
  have hb := AdvancedHomologicalAlgebra.ExtBoundarySigns.positive_projection 𝒜
    (S.map (singleFunctor 𝒜 0)) (hS.map_of_exact _)
  have hn : normalization 1 = 1 := by decide
  rw [yonedaClass, hn, one_smul, roof]
  change inv (_root_.DerivedCategory.Q.map (mappingCone.descShortComplex
      (S.map (singleFunctor 𝒜 0)))) ≫
    _root_.DerivedCategory.Q.map (ofShortExact S hS).projection ≫
    ((_root_.DerivedCategory.singleFunctors 𝒜).shiftIso 1 (-1) 0 (by omega)).inv.app S.X₁ = _
  rw [hp]
  rw [Category.assoc, hi]
  exact hb

lemma degreeOne_yonedaClass_eq_neg_boundary
    (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    E.yonedaClass = -(toShortExtension E).boundary := by
  simpa [yonedaClass, normalization, toShortExtension] using
    degreeOne_roof_eq_neg_boundary E (degreeOneSequence_shortExact E)

lemma degreeOne_yonedaClass_baer
    (E F : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1) :
    (degreeOneBaer E F).yonedaClass = E.yonedaClass + F.yonedaClass := by
  rw [degreeOneBaer, ofShortExact_yonedaClass]
  change -((toShortExtension E).baer (toShortExtension F)).boundary = _
  rw [AdvancedHomologicalAlgebra.DegreeOneExtensionClasses.boundary_baer, neg_add,
    ← degreeOne_yonedaClass_eq_neg_boundary E, ← degreeOne_yonedaClass_eq_neg_boundary F]

lemma degreeOne_equivalent_of_yonedaClass_eq
    (E F : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1)
    (h : E.yonedaClass = F.yonedaClass) : E.Equivalent F := by
  have he := degreeOne_roof_eq_neg_boundary E (degreeOneSequence_shortExact E)
  have hf := degreeOne_roof_eq_neg_boundary F (degreeOneSequence_shortExact F)
  have hb : (toShortExtension E).boundary = (toShortExtension F).boundary := by
    apply neg_injective
    change -(degreeOneSequence_shortExact E).singleδ =
      -(degreeOneSequence_shortExact F).singleδ
    rw [← he, ← hf]
    simpa [yonedaClass, normalization] using h
  obtain ⟨b, hi, hp⟩ :=
    AdvancedHomologicalAlgebra.DegreeOneExtensionClasses.equivalent_of_boundary_eq
      (toShortExtension E) (toShortExtension F) hb
  let C := ofShortExact E.degreeOneSequence (degreeOneSequence_shortExact E)
  have hCE : C.Related E := ⟨degreeOneConeMap E E (𝟙 _) (by simp [degreeOneSequence]) (by simp [degreeOneSequence])⟩
  have hCF : C.Related F := ⟨degreeOneConeMap E F b.hom hi hp⟩
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hCE))
    (Relation.EqvGen.rel _ _ hCF)

lemma degreeOne_yonedaClass_surjective
    (h : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (1 : ℤ)) :
    ∃ E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1,
      E.yonedaClass = h := by
  obtain ⟨E, hE⟩ :=
    AdvancedHomologicalAlgebra.DegreeOneExtensionClasses.boundary_surjective (-h)
  refine ⟨ofShortExact E.sequence E.shortExact, ?_⟩
  rw [ofShortExact_yonedaClass]
  change -E.boundary = h
  rw [hE, neg_neg]

end AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension

namespace AdvancedHomologicalAlgebra.HigherYonedaClasses
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable (X Y : 𝒜)

/-- Full set classification for arbitrary two-term row models, using the
positive projection and the endpoint-map-generated equivalence. -/
theorem degree_one_classification :
    ∃ e : Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X Y 1) ≃
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (1 : ℤ),
      ∀ E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1,
        e ⟦E⟧ = E.yonedaClass := by
  let f : Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X Y 1) →
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (1 : ℤ) :=
    Quotient.lift (fun E => E.yonedaClass) (fun E F h => invariant 𝒜 X Y 1 E F h)
  have hinj : Function.Injective f := by
    intro x y
    induction x using Quotient.inductionOn with | _ E =>
      induction y using Quotient.inductionOn with | _ F =>
        intro h
        exact Quotient.sound (Extension.degreeOne_equivalent_of_yonedaClass_eq E F h)
  have hsurj : Function.Surjective f := by
    intro h
    obtain ⟨E, hE⟩ := Extension.degreeOne_yonedaClass_surjective h
    exact ⟨⟦E⟧, hE⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun E => rfl⟩

/-- The degree-one bijection respects the independently constructed geometric
Baer operation on the endpoint-map quotient. -/
theorem degree_one_baer_classification :
    ∃ inst : AddCommGroup (Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X Y 1)),
    letI := inst
    ∃ e : Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X Y 1) ≃+
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (1 : ℤ),
      (∀ E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1,
        e ⟦E⟧ = E.yonedaClass) ∧
      ∀ E F : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y 1,
        (⟦E⟧ : Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X Y 1)) +
          ⟦F⟧ = ⟦Extension.degreeOneBaer E F⟧ := by
  obtain ⟨e, he⟩ := degree_one_classification X Y
  refine ⟨e.addCommGroup, ?_⟩
  letI := e.addCommGroup
  refine ⟨e.addEquiv, he, ?_⟩
  intro E F
  apply e.injective
  change e (e.symm (e ⟦E⟧ + e ⟦F⟧)) = e ⟦Extension.degreeOneBaer E F⟧
  rw [e.apply_symm_apply, he, he, he, Extension.degreeOne_yonedaClass_baer]

end AdvancedHomologicalAlgebra.HigherYonedaClasses

namespace AdvancedHomologicalAlgebra.HigherYonedaClasses
namespace EndpointPull
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

lemma acyclic_left_of_shortExact_of_quasiIso
    {S : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact) [QuasiIso S.g] :
    S.X₁.Acyclic := by
  intro i
  exact hS.exactAt_X₁ i

variable {X X' Y : 𝒜} {n : ℕ}
lemma augmentation_epi (E : Extension X Y n) : Epi E.augmentation := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  by_cases hi : i = 0
  · subst i
    exact AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.augmentation_epi E
  · exact ⟨fun _ _ _ => (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi).eq_of_src _ _⟩

noncomputable def pullComplex (E : Extension X Y n) (x : X' ⟶ X) : CochainComplex 𝒜 ℤ :=
  pullback ((CochainComplex.singleFunctor 𝒜 0).map x) E.augmentation
noncomputable def pullAugmentation (E : Extension X Y n) (x : X' ⟶ X) :
    pullComplex E x ⟶ (CochainComplex.singleFunctor 𝒜 0).obj X' := pullback.fst _ _
noncomputable def pullSnd (E : Extension X Y n) (x : X' ⟶ X) :
    pullComplex E x ⟶ E.complex := pullback.snd _ _
lemma pull_isPullback (E : Extension X Y n) (x : X' ⟶ X) (i : ℤ) :
    IsPullback ((pullAugmentation E x).f i) ((pullSnd E x).f i)
      (((CochainComplex.singleFunctor 𝒜 0).map x).f i) (E.augmentation.f i) :=
  (IsPullback.of_hasPullback _ _).map (HomologicalComplex.eval 𝒜 (.up ℤ) i)

lemma pullAugmentation_quasiIso (E : Extension X Y n) (x : X' ⟶ X) :
    QuasiIso (pullAugmentation E x) := by
  have := augmentation_epi E
  let S := ShortComplex.kernelSequence E.augmentation
  have : Epi S.g := ‹Epi E.augmentation›
  have : QuasiIso S.g := E.exact
  have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact _ }
  exact EndpointPush.quasiIso_of_shortExact_of_acyclic_left (hS.pull ((CochainComplex.singleFunctor 𝒜 0).map x))
    (acyclic_left_of_shortExact_of_quasiIso (S := S) hS)

lemma pullSnd_isIso (E : Extension X Y n) (x : X' ⟶ X) (i : ℤ) (hi : i ≠ 0) :
    IsIso ((pullSnd E x).f i) := by
  have : IsIso (((CochainComplex.singleFunctor 𝒜 0).map x).f i) :=
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X' i hi).isIso
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi) _
  exact (pull_isPullback E x i).isIso_snd_of_isIso

noncomputable def pull (E : Extension X Y n) (x : X' ⟶ X) : Extension X' Y n where
  positive := E.positive
  complex := pullComplex E x
  supportedGE := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have := E.positive
    have := pullSnd_isIso E x i (by omega)
    exact (E.complex.isZero_of_isStrictlyGE _ i hi).of_iso (asIso ((pullSnd E x).f i))
  supportedLE := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have := pullSnd_isIso E x i (by omega)
    exact (E.complex.isZero_of_isStrictlyLE _ i hi).of_iso (asIso ((pullSnd E x).f i))
  left := by
    have := E.positive
    have := pullSnd_isIso E x (-(n:ℤ)) (by omega)
    exact asIso ((pullSnd E x).f (-(n:ℤ))) ≪≫ E.left
  augmentation := pullAugmentation E x
  exact := pullAugmentation_quasiIso E x

noncomputable def pullMorphism (E : Extension X Y n) (x : X' ⟶ X) :
    (pull E x).Morphism E x (𝟙 Y) where
  hom := pullSnd E x
  left_comm := by simp [pull]
  right_comm := by simpa only [pullSnd, pull, pullAugmentation] using (pullback.condition (f := (CochainComplex.singleFunctor 𝒜 0).map x) (g := E.augmentation)).symm
end EndpointPull

/-- The degree-zero classes are Hom, with the accepted additive stalk comparison. -/
theorem degree_zero_classification : zeroClassificationType := by
  intro 𝒜 _ _ _ X Y
  obtain ⟨e, he⟩ := AdvancedHomologicalAlgebra.ExtShiftedHom.zero 𝒜 X Y
  exact ⟨AddEquiv.ulift.trans e, he⟩

/-- Degree-zero endpoint maps agree with ordinary composition under the comparison. -/
theorem degree_zero_naturality : zeroNaturalityType := by
  intro 𝒜 _ _ _ X X' Y Y' a b f
  exact AdvancedHomologicalAlgebra.ExtShiftedHom.zero_natural 𝒜 X X' Y Y' a b f.down

end AdvancedHomologicalAlgebra.HigherYonedaClasses

namespace AdvancedHomologicalAlgebra.HigherYonedaClasses.Classification
open CategoryTheory Category Limits ComplexShape
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : CochainComplex C ℤ}

lemma homotopy_at_lower_bound {f g : K ⟶ L} (h : Homotopy f g)
    (a : ℤ) [L.IsStrictlyGE a] :
    f.f a = K.d a (a+1) ≫ h.hom (a+1) a + g.f a := by
  have hz : L.d (a-1) a = 0 :=
    (L.isZero_of_isStrictlyGE a (a-1) (by omega)).eq_of_src _ _
  simpa only [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel a (a+1) from rfl),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (a-1) a from by change a - 1 + 1 = a; omega),
    hz, comp_zero, add_zero] using h.comm a

lemma homotopic_eq_of_bounds {f g : K ⟶ L} (h : Homotopy f g)
    (a : ℤ) [K.IsStrictlyLE a] [L.IsStrictlyGE a] : f = g := by
  ext i
  rcases lt_trichotomy i a with hi | rfl | hi
  · exact (L.isZero_of_isStrictlyGE a i hi).eq_of_tgt _ _
  · have hz : K.d i (i+1) = 0 :=
      (K.isZero_of_isStrictlyLE i (i+1) (by omega)).eq_of_tgt _ _
    simpa only [hz, zero_comp, zero_add] using homotopy_at_lower_bound h i
  · exact (K.isZero_of_isStrictlyLE a i hi).eq_of_src _ _

lemma homotopy_at_lower_bound_desc {U : CochainComplex C ℤ}
    (q : K ⟶ U) {f g : K ⟶ L} (h : Homotopy f g)
    (f' g' : U ⟶ L) (hf : q ≫ f' = f) (hg : q ≫ g' = g)
    (a : ℤ) [L.IsStrictlyGE a] [Epi (q.f a)] [IsIso (q.f (a+1))] :
    f'.f a = U.d a (a+1) ≫ (inv (q.f (a+1)) ≫ h.hom (a+1) a) + g'.f a := by
  apply (cancel_epi (q.f a)).mp
  rw [Preadditive.comp_add, ← Category.assoc, q.comm a (a+1), Category.assoc,
    IsIso.hom_inv_id_assoc]
  have hf' := congrArg (fun t : K ⟶ L => t.f a) hf
  have hg' := congrArg (fun t : K ⟶ L => t.f a) hg
  change q.f a ≫ f'.f a = f.f a at hf'
  change q.f a ≫ g'.f a = g.f a at hg'
  rw [hf', hg']
  exact homotopy_at_lower_bound h a

lemma truncGE_epi_at (a i : ℤ) : Epi ((K.πTruncGE a).f i) := by
  dsimp [CochainComplex.πTruncGE]
  infer_instance

lemma truncGE_isIso_at_next (a : ℤ) : IsIso ((K.πTruncGE a).f (a+1)) := by
  change IsIso ((HomologicalComplex.πTruncGE K (embeddingUpIntGE a)).f (a+1))
  dsimp [HomologicalComplex.πTruncGE]
  rw [(embeddingUpIntGE a).isIso_liftExtend_f_iff _ _ (i:=1) (by simp)]
  exact K.isIso_restrictionToTruncGE' (embeddingUpIntGE a) 1 (by
    rw [boundaryGE_embeddingUpIntGE_iff]; omega)


open Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses

lemma bounded_roof_extension [HasDerivedCategory C] (X Y : C) (n : ℕ) (hn : 0 < n)
    (f : _root_.DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj X) ⟶
      _root_.DerivedCategory.Q.obj ((CochainComplex.singleFunctor C (-(n : ℤ))).obj Y)) :
    ∃ (A : C) (E : Extension X A n) (y : A ⟶ Y),
      f = inv (_root_.DerivedCategory.Q.map E.augmentation) ≫
        _root_.DerivedCategory.Q.map (E.projection ≫
          (CochainComplex.singleFunctor C (-(n : ℤ))).map y) := by
  have : ((CochainComplex.singleFunctor C 0).obj X).IsStrictlyGE (-(n : ℤ)) :=
    CochainComplex.isStrictlyGE_of_ge _ _ 0 (by omega)
  obtain ⟨U, hGE, hLE, s, hs, g, hg⟩ :=
    _root_.DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE (-(n : ℤ)) 0 f
  haveI := hGE
  haveI := hLE
  haveI : QuasiIso s := (_root_.DerivedCategory.isIso_Q_map_iff_quasiIso C s).mp hs
  let E : Extension X (U.X (-(n : ℤ))) n :=
    ⟨hn, U, hGE, hLE, Iso.refl _, s, inferInstance⟩
  let y : U.X (-(n : ℤ)) ⟶ Y :=
    g.f (-(n : ℤ)) ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) (-(n : ℤ)) Y).hom
  refine ⟨_, E, y, ?_⟩
  have hg' : E.projection ≫ (CochainComplex.singleFunctor C (-(n : ℤ))).map y = g := by
    apply HomologicalComplex.to_single_hom_ext
    simp [E, y, Extension.projection, CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self]
  simpa only [hg'] using hg


noncomputable def cochainRightFraction {X Y E : CochainComplex C ℤ}
    (s : E ⟶ X) [QuasiIso s] (p : E ⟶ Y) :
    (HomotopyCategory.quasiIso C (.up ℤ)).RightFraction
      ((HomotopyCategory.quotient C (.up ℤ)).obj X)
      ((HomotopyCategory.quotient C (.up ℤ)).obj Y) :=
  ⟨(HomotopyCategory.quotient C (.up ℤ)).map s,
    (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mpr (inferInstance : QuasiIso s),
    (HomotopyCategory.quotient C (.up ℤ)).map p⟩

lemma cochain_refinement_of_Qh_roof_eq [HasDerivedCategory C]
    {X Y E F : CochainComplex C ℤ}
    (s : E ⟶ X) (s' : F ⟶ X) [QuasiIso s] [QuasiIso s']
    (p : E ⟶ Y) (p' : F ⟶ Y)
    (h : (cochainRightFraction s p).map _root_.DerivedCategory.Qh (Localization.inverts _ _) =
      (cochainRightFraction s' p').map _root_.DerivedCategory.Qh (Localization.inverts _ _)) :
    ∃ (T : CochainComplex C ℤ) (a : T ⟶ E) (b : T ⟶ F),
      QuasiIso a ∧ QuasiIso b ∧
      Nonempty (Homotopy (a ≫ s) (b ≫ s')) ∧
      Nonempty (Homotopy (a ≫ p) (b ≫ p')) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  let r := cochainRightFraction s p
  let r' := cochainRightFraction s' p'
  obtain ⟨Z, a, b, hab, hab', hw⟩ :=
    (MorphismProperty.RightFraction.map_eq_iff _root_.DerivedCategory.Qh W r r').mp h
  have ha : W a := by
    intro i
    exact (MorphismProperty.isomorphisms C).of_postcomp
      ((HomotopyCategory.homologyFunctor C (.up ℤ) i).map a)
      ((HomotopyCategory.homologyFunctor C (.up ℤ) i).map r.s)
      (r.hs i) (by simpa only [Functor.map_comp] using hw i)
  have hw' : W (b ≫ r'.s) := hab ▸ hw
  have hb : W b := by
    intro i
    exact (MorphismProperty.isomorphisms C).of_postcomp
      ((HomotopyCategory.homologyFunctor C (.up ℤ) i).map b)
      ((HomotopyCategory.homologyFunctor C (.up ℤ) i).map r'.s)
      (r'.hs i) (by simpa only [Functor.map_comp] using hw' i)
  obtain ⟨T, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨a, rfl⟩ := q.map_surjective a
  obtain ⟨b, rfl⟩ := q.map_surjective b
  refine ⟨T, a, b, ?_, ?_, ?_, ?_⟩
  · simpa only [q, W, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using ha
  · simpa only [q, W, HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomologicalComplex.mem_quasiIso_iff] using hb
  · exact ⟨HomotopyCategory.homotopyOfEq _ _ (by
      simpa only [q, r, r', cochainRightFraction, Functor.map_comp] using hab)⟩
  · exact ⟨HomotopyCategory.homotopyOfEq _ _ (by
      simpa only [q, r, r', cochainRightFraction, Functor.map_comp] using hab')⟩

lemma cochainRightFraction_map [HasDerivedCategory C]
    {X Y E : CochainComplex C ℤ} (s : E ⟶ X) [QuasiIso s] (p : E ⟶ Y) :
    (cochainRightFraction s p).map _root_.DerivedCategory.Qh (Localization.inverts _ _) =
      (_root_.DerivedCategory.quotientCompQhIso C).hom.app X ≫
        inv (_root_.DerivedCategory.Q.map s) ≫ _root_.DerivedCategory.Q.map p ≫
        (_root_.DerivedCategory.quotientCompQhIso C).inv.app Y := by
  let r := cochainRightFraction s p
  have : IsIso (_root_.DerivedCategory.Qh.map r.s) := inferInstance
  apply (cancel_epi (_root_.DerivedCategory.Qh.map r.s)).mp
  rw [r.map_s_comp_map]
  dsimp only [r, cochainRightFraction]
  rw [← Category.assoc, _root_.DerivedCategory.quotientCompQhIso_hom_naturality,
    Category.assoc, IsIso.hom_inv_id_assoc,
    ← Category.assoc, ← _root_.DerivedCategory.quotientCompQhIso_hom_naturality,
    Category.assoc, Iso.hom_inv_id_app]
  simp

lemma cochain_refinement_of_roof_eq [HasDerivedCategory C]
    {X Y E F : CochainComplex C ℤ}
    (s : E ⟶ X) (s' : F ⟶ X) [QuasiIso s] [QuasiIso s']
    (p : E ⟶ Y) (p' : F ⟶ Y)
    (h : inv (_root_.DerivedCategory.Q.map s) ≫ _root_.DerivedCategory.Q.map p =
        inv (_root_.DerivedCategory.Q.map s') ≫ _root_.DerivedCategory.Q.map p') :
    ∃ (T : CochainComplex C ℤ) (a : T ⟶ E) (b : T ⟶ F),
      QuasiIso a ∧ QuasiIso b ∧
      Nonempty (Homotopy (a ≫ s) (b ≫ s')) ∧
      Nonempty (Homotopy (a ≫ p) (b ≫ p')) := by
  apply cochain_refinement_of_Qh_roof_eq s s' p p'
  rw [cochainRightFraction_map, cochainRightFraction_map]
  simpa only [← Category.assoc] using congrArg
    (fun z => (_root_.DerivedCategory.quotientCompQhIso C).hom.app X ≫ z ≫
      (_root_.DerivedCategory.quotientCompQhIso C).inv.app Y) h

lemma extension_refinement_of_roof_eq [HasDerivedCategory C]
    {X Y : C} {n : ℕ} (E F : Extension X Y n) (he : E.roof = F.roof) :
    ∃ (A : C) (V : Extension X A n) (y z : A ⟶ Y),
      Nonempty (V.Morphism E (𝟙 X) y) ∧
      Nonempty (V.Morphism F (𝟙 X) z) ∧
      ∃ (h : V.complex.X (-(n:ℤ)+1) ⟶ Y),
        y = z + (V.left.inv ≫ V.complex.d (-(n:ℤ)) (-(n:ℤ)+1)) ≫ h := by
  have hroof : inv (_root_.DerivedCategory.Q.map E.augmentation) ≫ _root_.DerivedCategory.Q.map E.projection =
      inv (_root_.DerivedCategory.Q.map F.augmentation) ≫ _root_.DerivedCategory.Q.map F.projection := by
    apply (cancel_mono (((_root_.DerivedCategory.singleFunctors C).shiftIso
      (n:ℤ) (-(n:ℤ)) 0 (by omega)).inv.app Y)).mp
    simpa only [Extension.roof, Category.assoc] using he
  obtain ⟨T, e, f, heq, hfq, ⟨haug⟩, ⟨hpr⟩⟩ :=
    cochain_refinement_of_roof_eq E.augmentation F.augmentation E.projection F.projection hroof
  haveI := heq
  haveI := hfq
  let B := T.truncLE 0
  let e₀ : B ⟶ E.complex := T.ιTruncLE 0 ≫ e
  let f₀ : B ⟶ F.complex := T.ιTruncLE 0 ≫ f
  haveI : QuasiIso (CochainComplex.truncLEMap e 0) :=
    (CochainComplex.quasiIso_truncLEMap_iff e 0).mpr (fun _ _ => inferInstance)
  haveI : QuasiIso (CochainComplex.truncLEMap f 0) :=
    (CochainComplex.quasiIso_truncLEMap_iff f 0).mpr (fun _ _ => inferInstance)
  haveI : QuasiIso e₀ := by
    dsimp [e₀]
    rw [← CochainComplex.ιTruncLE_naturality]
    infer_instance
  haveI : QuasiIso f₀ := by
    dsimp [f₀]
    rw [← CochainComplex.ιTruncLE_naturality]
    infer_instance
  have haug₀ : e₀ ≫ E.augmentation = f₀ ≫ F.augmentation := by
    apply homotopic_eq_of_bounds _ 0
    simpa only [e₀, f₀, Category.assoc] using haug.compLeft (T.ιTruncLE 0)
  have hpr₀ : Homotopy (e₀ ≫ E.projection) (f₀ ≫ F.projection) := by
    simpa only [e₀, f₀, Category.assoc] using hpr.compLeft (T.ιTruncLE 0)
  let U := B.truncGE (-(n:ℤ))
  let q : B ⟶ U := B.πTruncGE (-(n:ℤ))
  let e₁ : U ⟶ E.complex := CochainComplex.truncGEMap e₀ (-(n:ℤ)) ≫
    inv (E.complex.πTruncGE (-(n:ℤ)))
  let f₁ : U ⟶ F.complex := CochainComplex.truncGEMap f₀ (-(n:ℤ)) ≫
    inv (F.complex.πTruncGE (-(n:ℤ)))
  have hqe : q ≫ e₁ = e₀ := by simp [q, e₁]
  have hqf : q ≫ f₁ = f₀ := by simp [q, f₁]
  haveI : QuasiIso (CochainComplex.truncGEMap e₀ (-(n:ℤ))) :=
    (CochainComplex.quasiIso_truncGEMap_iff e₀ (-(n:ℤ))).mpr (fun _ _ => inferInstance)
  haveI : QuasiIso e₁ := by dsimp [e₁]; infer_instance
  haveI : Epi q := by dsimp [q, CochainComplex.πTruncGE]; infer_instance
  have haug₁ : e₁ ≫ E.augmentation = f₁ ≫ F.augmentation := by
    apply (cancel_epi q).mp
    simpa only [← Category.assoc, hqe, hqf] using haug₀
  let V : Extension X (U.X (-(n:ℤ))) n :=
    ⟨E.positive, U, inferInstance, inferInstance, Iso.refl _, e₁ ≫ E.augmentation, inferInstance⟩
  let y : U.X (-(n:ℤ)) ⟶ Y := e₁.f (-(n:ℤ)) ≫ E.left.hom
  let z : U.X (-(n:ℤ)) ⟶ Y := f₁.f (-(n:ℤ)) ≫ F.left.hom
  refine ⟨_, V, y, z, ?_, ?_, ?_⟩
  · exact ⟨⟨e₁, by simp [V, y], by simp [V]⟩⟩
  · exact ⟨⟨f₁, by simp [V, z], by simpa [V] using haug₁.symm⟩⟩
  · haveI : Epi (q.f (-(n:ℤ))) := truncGE_epi_at _ _
    haveI : IsIso (q.f (-(n:ℤ)+1)) := truncGE_isIso_at_next _
    have hb := homotopy_at_lower_bound_desc q hpr₀ (e₁ ≫ E.projection) (f₁ ≫ F.projection)
      (by rw [← Category.assoc, hqe]) (by rw [← Category.assoc, hqf]) (-(n:ℤ))
    let t := (HomologicalComplex.singleObjXSelf (.up ℤ) (-(n:ℤ)) Y).hom
    refine ⟨(inv (q.f (-(n:ℤ)+1)) ≫ hpr₀.hom (-(n:ℤ)+1) (-(n:ℤ))) ≫ t, ?_⟩
    have hb' := congrArg (fun k => k ≫ t) hb
    simpa [HomologicalComplex.comp_f, Extension.projection, V, y, z, t,
      Preadditive.add_comp, Category.assoc, add_comm] using hb'


lemma extension_equivalent_of_roof_eq [HasDerivedCategory C]
    {X Y : C} {n : ℕ} (E F : Extension X Y n) (he : E.roof = F.roof) :
    E.Equivalent F := by
  obtain ⟨A,V,y,z,⟨a⟩,⟨b⟩,h,hrel⟩ := extension_refinement_of_roof_eq E F he
  let a' := EndpointPush.pushDescMorphism a
  let b' := EndpointPush.pushDescMorphism b
  have ha : (EndpointPush.push V y).Equivalent E := by
    apply Relation.EqvGen.rel
    exact ⟨⟨a'.hom, by simpa using a'.left_comm, by simpa using a'.right_comm⟩⟩
  have hb : (EndpointPush.push V z).Equivalent F := by
    apply Relation.EqvGen.rel
    exact ⟨⟨b'.hom, by simpa using b'.left_comm, by simpa using b'.right_comm⟩⟩
  have hs : (EndpointPush.push V z).Equivalent (EndpointPush.push V y) := by
    have hrel' : y = z + V.left.inv ≫ V.complex.d (-(n:ℤ)) (-(n:ℤ)+1) ≫ h := by
      simpa only [Category.assoc] using hrel
    simpa only [← hrel'] using EndpointPush.push_shear_equivalent V z h
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ha)
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hs) hb)

lemma extension_equivalent_of_yonedaClass_eq [HasDerivedCategory C]
    {X Y : C} {n : ℕ} (E F : Extension X Y n) (he : E.yonedaClass = F.yonedaClass) :
    E.Equivalent F := by
  apply extension_equivalent_of_roof_eq E F
  have h := congrArg (fun z => Extension.normalization n • z) he
  simpa only [Extension.yonedaClass,
    AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.normalization_involutive] using h

lemma raw_push_roof [HasDerivedCategory C]
    {X A Y : C} {n : ℕ} (E : Extension X A n) (y : A ⟶ Y) :
    inv (_root_.DerivedCategory.Q.map (EndpointPush.push E y).augmentation) ≫
      _root_.DerivedCategory.Q.map (EndpointPush.push E y).projection =
    inv (_root_.DerivedCategory.Q.map E.augmentation) ≫
      _root_.DerivedCategory.Q.map (E.projection ≫ (CochainComplex.singleFunctor C (-(n:ℤ))).map y) := by
  let f := EndpointPush.pushMorphism E y
  have haug : f.hom ≫ (EndpointPush.push E y).augmentation = E.augmentation := by
    simpa using f.right_comm
  have hs : _root_.DerivedCategory.Q.map E.augmentation =
      _root_.DerivedCategory.Q.map f.hom ≫ _root_.DerivedCategory.Q.map (EndpointPush.push E y).augmentation := by
    rw [← Functor.map_comp, haug]
  have hp : _root_.DerivedCategory.Q.map f.hom ≫ _root_.DerivedCategory.Q.map (EndpointPush.push E y).projection =
      _root_.DerivedCategory.Q.map (E.projection ≫ (CochainComplex.singleFunctor C (-(n:ℤ))).map y) := by
    rw [← Functor.map_comp,
      AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.projection_morphism f]
  apply (cancel_epi (_root_.DerivedCategory.Q.map E.augmentation)).mp
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [hs]
  simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hp

lemma extension_roof_surjective [HasDerivedCategory C]
    {X Y : C} {n : ℕ} (hn : 0 < n)
    (f : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (n:ℤ)) :
    ∃ E : Extension X Y n, E.roof = f := by
  let I := ((_root_.DerivedCategory.singleFunctors C).shiftIso (n:ℤ) (-(n:ℤ)) 0 (by omega)).app Y
  obtain ⟨A,E,y,hE⟩ := bounded_roof_extension X Y n hn (f ≫ I.hom)
  refine ⟨EndpointPush.push E y, ?_⟩
  change inv (_root_.DerivedCategory.Q.map (EndpointPush.push E y).augmentation) ≫
    _root_.DerivedCategory.Q.map (EndpointPush.push E y).projection ≫ I.inv = f
  rw [← Category.assoc, raw_push_roof, ← hE]
  simp

lemma extension_yonedaClass_surjective [HasDerivedCategory C]
    {X Y : C} {n : ℕ} (hn : 0 < n)
    (f : Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y (n:ℤ)) :
    ∃ E : Extension X Y n, E.yonedaClass = f := by
  obtain ⟨E,he⟩ := extension_roof_surjective hn (Extension.normalization n • f)
  refine ⟨E, ?_⟩
  rw [Extension.yonedaClass, he,
    AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.normalization_involutive]

lemma higher_classification :
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.classificationType := by
  intro C _ _ _ X Y n
  let f : Quotient (Extension.extensionSetoid X Y (n+1)) →
      Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.Ext X Y ((n+1:ℕ):ℤ) :=
    Quotient.lift (fun E => E.yonedaClass)
      (fun E F h => AdvancedHomologicalAlgebra.HigherYonedaClasses.invariant C X Y _ E F h)
  have hinj : Function.Injective f := by
    intro x y
    induction x using Quotient.inductionOn with | _ E =>
      induction y using Quotient.inductionOn with | _ F =>
        intro h
        exact Quotient.sound (extension_equivalent_of_yonedaClass_eq E F h)
  have hsurj : Function.Surjective f := by
    intro h
    obtain ⟨E,he⟩ := extension_yonedaClass_surjective (by omega) h
    exact ⟨⟦E⟧, he⟩
  exact ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩, fun E => rfl⟩

end AdvancedHomologicalAlgebra.HigherYonedaClasses.Classification

namespace AdvancedHomologicalAlgebra.HigherYonedaClasses
variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {X X' Y Y' : 𝒜} {n : ℕ}

noncomputable def pushoutData (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n)
    (y : Y ⟶ Y') : E.PushoutData y where
  row := EndpointPush.push E y
  comparison := EndpointPush.pushMorphism E y
  endpoint := EndpointPush.push_endpoint_isPushout E y
  unchanged := EndpointPush.pushInl_isIso E y

noncomputable def pullbackData (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n)
    (x : X' ⟶ X) : E.PullbackData x where
  row := EndpointPull.pull E x
  comparison := EndpointPull.pullMorphism E x
  endpoint := EndpointPull.pull_isPullback E x 0
  unchanged := EndpointPull.pullSnd_isIso E x

/-- The actual geometric Baer row. -/
noncomputable def baer (E F : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n) :
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n :=
  EndpointPush.push (EndpointPull.pull (directSum E F) (biprod.lift (𝟙 X) (𝟙 X)))
    (biprod.desc (𝟙 Y) (𝟙 Y))

variable [HasDerivedCategory.{w} 𝒜]

lemma yonedaClass_push (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n)
    (y : Y ⟶ Y') :
    (EndpointPush.push E y).yonedaClass = E.yonedaClass ≫
      ((_root_.DerivedCategory.singleFunctor 𝒜 0).map y)⟦(n:ℤ)⟧' := by
  symm
  simpa using map_naturality 𝒜 X Y X Y' n E (EndpointPush.push E y) (𝟙 X) y
    (EndpointPush.pushMorphism E y)

lemma yonedaClass_pull (E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n)
    (x : X' ⟶ X) :
    (EndpointPull.pull E x).yonedaClass =
      (_root_.DerivedCategory.singleFunctor 𝒜 0).map x ≫ E.yonedaClass := by
  simpa using map_naturality 𝒜 X' Y X Y n (EndpointPull.pull E x) E x (𝟙 Y)
    (EndpointPull.pullMorphism E x)

lemma yonedaClass_baer (E F : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y n) :
    (baer E F).yonedaClass = E.yonedaClass + F.yonedaClass := by
  have h₁ := map_naturality 𝒜 (X ⊞ X) (Y ⊞ Y) X Y n
    (directSum E F) E biprod.fst biprod.fst (directSumFst E F)
  have h₂ := map_naturality 𝒜 (X ⊞ X) (Y ⊞ Y) X Y n
    (directSum E F) F biprod.snd biprod.snd (directSumSnd E F)
  have hc : (biprod.desc (𝟙 Y) (𝟙 Y) : Y ⊞ Y ⟶ Y) = biprod.fst + biprod.snd := by
    apply biprod.hom_ext' <;> simp
  dsimp only [baer]
  rw [yonedaClass_push, yonedaClass_pull, hc]
  simp only [Functor.map_add, Preadditive.comp_add, Category.assoc]
  rw [h₁, h₂]
  simp [← Functor.map_comp_assoc]

theorem pushout_exists : pushoutType := by
  intro 𝒜 _ _ X Y Y' n E y
  exact ⟨pushoutData E y⟩

theorem pullback_exists : pullbackType := by
  intro 𝒜 _ _ X X' Y n E x
  exact ⟨pullbackData E x⟩

theorem endpoint_naturality : endpointNaturalityType := by
  intro 𝒜 _ _ _ X X' Y Y' n E x y
  refine ⟨pullbackData E x, pushoutData (EndpointPull.pull E x) y, ?_⟩
  change (EndpointPush.push (EndpointPull.pull E x) y).yonedaClass = _
  rw [yonedaClass_push, yonedaClass_pull]
  simp [Specs.AdvancedHomologicalAlgebra.ExtShiftedHom.extMap, Category.assoc]
end AdvancedHomologicalAlgebra.HigherYonedaClasses

namespace AdvancedHomologicalAlgebra.HigherYonedaClasses

theorem classification : classificationType := Classification.higher_classification

theorem baer_classification : baerClassificationType := by
  intro 𝒜 _ _ _ X Y n
  obtain ⟨e, he⟩ := classification 𝒜 X Y n
  refine ⟨e.addCommGroup, ?_⟩
  let := e.addCommGroup
  refine ⟨e.addEquiv, he, ?_⟩
  intro E F
  refine ⟨pullbackData (directSum E F) (biprod.lift (𝟙 X) (𝟙 X)),
    pushoutData (EndpointPull.pull (directSum E F) (biprod.lift (𝟙 X) (𝟙 X)))
      (biprod.desc (𝟙 Y) (𝟙 Y)), ?_⟩
  apply e.injective
  change e (e.symm (e ⟦E⟧ + e ⟦F⟧)) = e ⟦baer E F⟧
  rw [e.apply_symm_apply, he, he, he, yonedaClass_baer]

end AdvancedHomologicalAlgebra.HigherYonedaClasses

namespace AdvancedHomologicalAlgebra.HigherYonedaClasses
open Specs.AdvancedHomologicalAlgebra.ExtShiftedHom

/-- The derived endpoint action is additive before any quotient comparison. -/
noncomputable def extEndpointMap {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] {X X' Y Y' : 𝒜}
    (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℤ) : Ext X Y n →+ Ext X' Y' n where
  toFun := extMap a b n
  map_zero' := by simp [extMap]
  map_add' f g := by simp [extMap, Preadditive.comp_add, Preadditive.add_comp]

theorem natural_additive_classification :
    Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.naturalAdditiveClassificationType := by
  intro 𝒜 _ _ _ n
  let f (X Y : 𝒜) := Classical.choose (Classification.higher_classification 𝒜 X Y n)
  have hf (X Y : 𝒜) : ∀ E : Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension X Y (n+1),
      f X Y ⟦E⟧ = E.yonedaClass :=
    Classical.choose_spec (Classification.higher_classification 𝒜 X Y n)
  let g (X Y : 𝒜) : AddCommGroup (Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X Y (n+1))) :=
    (f X Y).addCommGroup
  refine ⟨g, ?_⟩
  letI (X Y : 𝒜) : AddCommGroup (Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X Y (n+1))) := g X Y
  let e (X Y : 𝒜) : Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X Y (n+1)) ≃+
      Ext X Y ((n+1:ℕ):ℤ) := (f X Y).addEquiv
  refine ⟨e, hf, ?_, ?_⟩
  · intro X Y E F
    refine ⟨pullbackData (directSum E F) (biprod.lift (𝟙 X) (𝟙 X)),
      pushoutData (EndpointPull.pull (directSum E F) (biprod.lift (𝟙 X) (𝟙 X)))
        (biprod.desc (𝟙 Y) (𝟙 Y)), ?_⟩
    apply (e X Y).injective
    change (f X Y) ((f X Y).symm ((f X Y) ⟦E⟧ + (f X Y) ⟦F⟧)) =
      (f X Y) ⟦baer E F⟧
    rw [Equiv.apply_symm_apply, hf, hf, hf, yonedaClass_baer]
  · intro X X' Y Y' a b
    let φ : Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X Y (n+1)) →+
        Quotient (Specs.AdvancedHomologicalAlgebra.HigherYonedaClasses.Extension.extensionSetoid X' Y' (n+1)) :=
      (e X' Y').symm.toAddMonoidHom.comp
        ((extEndpointMap a b ((n+1:ℕ):ℤ)).comp (e X Y).toAddMonoidHom)
    have hφ (q) : e X' Y' (φ q) = extMap a b ((n+1:ℕ):ℤ) (e X Y q) := by
      change e X' Y' ((e X' Y').symm (extMap a b ((n+1:ℕ):ℤ) (e X Y q))) = _
      exact (e X' Y').apply_symm_apply _
    refine ⟨φ, ?_, hφ⟩
    intro E
    obtain ⟨P, O, hO⟩ := endpoint_naturality 𝒜 X X' Y Y' (n+1) E a b
    refine ⟨P, O, ?_⟩
    apply (e X' Y').injective
    rw [hφ]
    change extMap a b ((n+1:ℕ):ℤ) (f X Y ⟦E⟧) = f X' Y' ⟦O.row⟧
    rw [hf, hf]
    exact hO.symm
end AdvancedHomologicalAlgebra.HigherYonedaClasses
