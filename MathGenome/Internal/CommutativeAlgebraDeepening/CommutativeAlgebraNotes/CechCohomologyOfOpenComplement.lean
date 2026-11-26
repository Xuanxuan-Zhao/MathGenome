import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.AffineTildeAcyclicity
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open HomologicalComplex MonoidalCategory

set_option linter.style.haveILetI false
open Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement

namespace CommutativeAlgebraNotes

set_option backward.isDefEq.respectTransparency false

universe u w

variable {R : CommRingCat.{u}}

private lemma basicOpen_le_complement (I : Ideal R) {f : R} (hf : f ∈ I) :
    PrimeSpectrum.basicOpen f ≤ complement R I := by
  intro p hp hc
  exact hp (hc hf)

theorem tildeComplement_distinguishedCover : DistinguishedCover.{u} := by
  intro R I rs hI
  apply le_antisymm
  · intro p hp
    rw [Opens.mem_iSup]
    by_contra h
    apply hp
    change I ≤ p.asIdeal
    rw [← hI, Ideal.span_le]
    intro f hf
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hf
    by_contra hj
    exact h ⟨j, hj⟩
  · apply iSup_le
    intro i
    apply basicOpen_le_complement I
    rw [← hI]
    exact Ideal.subset_span (List.get_mem _ _)

private lemma toOpen_basic_zero (M : ModuleCat.{u} R) (f : R) (x : M) :
    tilde.toOpen M (PrimeSpectrum.basicOpen f) x = 0 ↔ ∃ n : ℕ, f ^ n • x = 0 := by
  rw [show tilde.toOpen M (PrimeSpectrum.basicOpen f) x =
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom x from rfl,
    IsLocalizedModule.eq_zero_iff (Submonoid.powers f)
      (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom]
  exact ⟨fun ⟨⟨_, n, rfl⟩, hn⟩ => ⟨n, hn⟩,
    fun ⟨n, hn⟩ => ⟨⟨_, n, rfl⟩, hn⟩⟩

private lemma sections_restrict_toOpen (M : ModuleCat.{u} R) {V W : (Spec R).Opens}
    (h : V ≤ W) (x : M) :
    (restrict R h).app (tilde M) (tilde.toOpen M W x) = tilde.toOpen M V x :=
  congr($(tilde.toOpen_res M W V (homOfLE h)) x)

theorem tildeComplement_torsionKernel : TorsionKernel.{u} := by
  intro R _ I M x
  change tilde.toOpen M (complement R I) x = 0 ↔ x ∈ idealTorsion I M
  constructor
  · intro hx
    let A : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M x)
    have hIA : I ≤ A.radical := by
      intro f hf
      have hz : tilde.toOpen M (PrimeSpectrum.basicOpen f) x = 0 := by
        exact (sections_restrict_toOpen M (basicOpen_le_complement I hf) x).symm.trans
          (hx.symm ▸ ((restrict R (basicOpen_le_complement I hf)).app (tilde M)).hom.map_zero)
      obtain ⟨n, hn⟩ := (toOpen_basic_zero M f x).mp hz
      exact ⟨n, hn⟩
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIA (IsNoetherian.noetherian I)
    apply (mem_idealTorsion _ _).mpr
    refine ⟨n + 1, by omega, fun f hf => ?_⟩
    apply hn
    exact Ideal.pow_le_pow_right (by omega : n ≤ n + 1) hf
  · intro hx
    obtain ⟨n, _, hn⟩ := (mem_idealTorsion _ _).mp hx
    apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj (tilde M)).2
    intro p hp
    change ¬ (I : Set R) ⊆ p.asIdeal at hp
    obtain ⟨f, hf, hfp⟩ := Set.not_subset.mp hp
    refine ⟨PrimeSpectrum.basicOpen f, basicOpen_le_complement I hf,
      hfp, ?_⟩
    rw [map_zero]
    change (restrict R (basicOpen_le_complement I hf)).app (tilde M)
      (tilde.toOpen M (complement R I) x) = 0
    exact (sections_restrict_toOpen M (basicOpen_le_complement I hf) x).trans
      ((toOpen_basic_zero M f x).mpr ⟨n, hn (f ^ n) (Ideal.pow_mem_pow hf n)⟩)

private lemma torsion_restrict_zero [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R) :
    (idealTorsionInclusion I).app M ≫ (toSections R (complement R I)).app M = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  exact (tildeComplement_torsionKernel R I M x.val).mpr x.property

theorem tildeComplement_injectiveSectionsExact : InjectiveSectionsExact.{u} := by
  intro R _ I Q _
  refine ⟨torsion_restrict_zero I Q, ?_⟩
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro x
    exact (tildeComplement_torsionKernel R I Q x).trans
      ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.property⟩
  · exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  · exact (ModuleCat.epi_iff_surjective _).mpr (tildeSectionsSurjective R Q _)

section Projection

open Specs.CommutativeAlgebraNotes.InjectiveCechComparison
  (singleZero factorProjection dropFactor projection)
open private rowIso rowFunctor torsionComplex doubleComparison totalComparison
  rowComparison totalComparison_quasiIso cechTensor_quasiIso unitRowIso doubleTensor
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
open private projection_natural from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveCechComparison

private abbrev Cpx (S : Type u) [CommRing S] := CochainComplex (ModuleCat.{u} S) ℤ

variable {S : Type u} [CommRing S]

private def ringProjection : (rs : List S) → CechComplex rs ⟶ 𝟙_ (Cpx S)
  | [] => 𝟙 _
  | r :: rs => (factorProjection r ⊗ₘ ringProjection rs) ≫ (λ_ (𝟙_ (Cpx S))).hom

private lemma projection_eq_tensor (rs : List S) (K : Cpx S) :
    projection rs K = (ringProjection rs ⊗ₘ 𝟙 K) ≫ (λ_ K).hom := by
  induction rs with
  | nil =>
    change (λ_ K).hom = (𝟙 (𝟙_ (Cpx S)) ⊗ₘ 𝟙 K) ≫ (λ_ K).hom
    simp
  | cons r rs ih =>
    change (α_ _ _ K).hom ≫
      ((factorProjection r ⊗ₘ 𝟙 (CechComplex rs ⊗ K)) ≫ (λ_ (CechComplex rs ⊗ K)).hom) ≫
        projection rs K =
      (((factorProjection r ⊗ₘ ringProjection rs) ≫ (λ_ (𝟙_ (Cpx S))).hom) ⊗ₘ 𝟙 K) ≫
        (λ_ K).hom
    rw [ih]
    simp only [Category.assoc, ← leftUnitor_naturality_assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.id_comp]
    rw [← associator_naturality_assoc, leftUnitor_tensor_hom_assoc,
      Iso.hom_inv_id_assoc]
    have h := tensorHom_comp_tensorHom_assoc (factorProjection r ⊗ₘ ringProjection rs)
      (𝟙 K) ((λ_ (𝟙_ (Cpx S))).hom) (𝟙 K) (λ_ K).hom
    rw [Category.id_comp] at h
    have hi : (factorProjection r ≫ 𝟙 (𝟙_ (Cpx S))) ⊗ₘ ringProjection rs =
        factorProjection r ⊗ₘ ringProjection rs :=
      congrArg (fun f => f ⊗ₘ ringProjection rs) (Category.comp_id (factorProjection r))
    rw [hi]
    exact h

private def cochainTorsionInclusion (I : Ideal S) : torsionComplex I ⟶ 𝟭 (Cpx S) :=
  (idealTorsionInclusion I).mapHomologicalComplex (.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom

private lemma total_projection (I : Ideal S) (rs : List S)
    (η : idealTorsionFunctor I ⋙ singleZero S ⟶ singleZero S ⋙ tensorLeft (CechComplex rs))
    (hη : ∀ M,
      η.app M ≫ projection rs ((singleZero S).obj M) =
        (singleZero S).map ((idealTorsionInclusion I).app M))
    (K : Cpx S) :
    (totalComparison I rs η).app K ≫ projection rs K =
      (cochainTorsionInclusion I).app K := by
  let T := (torsionComplex I).obj K
  let p := ringProjection rs
  let inc := (cochainTorsionInclusion I).app K
  have hrow (M : ModuleCat.{u} S) (i : ℤ) :
      ((rowComparison I rs η).app M).f i ≫ (p.f i ▷ M) =
        ((𝟙_ (Cpx S)).X i ◁ (idealTorsionInclusion I).app M) := by
    let L := (singleZero S).obj M
    let U := 𝟙_ (Cpx S)
    have h := hη M
    rw [projection_eq_tensor] at h
    have h' : η.app M ≫ (p ⊗ₘ 𝟙 L) =
        (singleZero S).map ((idealTorsionInclusion I).app M) ≫ (λ_ L).inv := by
      rw [← h, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply (cancel_mono ((rowIso U).hom.app M |>.f i)).mp
    have hp :
        (p.f i ▷ M) ≫ ((rowIso U).hom.app M).f i =
          ((rowIso (CechComplex rs)).hom.app M).f i ≫ (p ⊗ₘ 𝟙 L).f i := by
      change _ = ιTensorObj (CechComplex rs) L i 0 i _ ≫
        (HomologicalComplex.tensorHom p (𝟙 L)).f i
      rw [ι_mapBifunctorMap]
      change _ = ((p.f i ▷ M) ≫ (U.X i ◁ 𝟙 M)) ≫ ιTensorObj U L i 0 i _
      simp only [whiskerLeft_id]
      rfl
    rw [Category.assoc, hp, ← HomologicalComplex.comp_f_assoc]
    have ha : (rowComparison I rs η).app M ≫ (rowIso (CechComplex rs)).hom.app M =
        unitRowIso.hom.app ((idealTorsionFunctor I).obj M) ≫ η.app M := by
      simp [rowComparison]
    rw [ha, ← HomologicalComplex.comp_f]
    have hnat := (rowIso U).hom.naturality ((idealTorsionInclusion I).app M)
    apply Eq.trans _ (congrArg (fun f => HomologicalComplex.Hom.f f i) hnat.symm)
    congr 1
    have hu (N : ModuleCat.{u} S) : unitRowIso.hom.app N =
        (rowIso U).hom.app N ≫ (λ_ ((singleZero S).obj N)).hom := by
      simp [unitRowIso, U]
      rfl
    rw [hu, Category.assoc, h', Category.assoc]
    congr 1
    have hnat' := leftUnitor_naturality ((singleZero S).map ((idealTorsionInclusion I).app M))
    rw [← Category.assoc, ← hnat', Category.assoc]
    change _ ≫ (λ_ L).hom ≫ (λ_ L).inv = _
    rw [Iso.hom_inv_id, Category.comp_id]
    rfl
  have ht :
      HomologicalComplex₂.total.map (doubleComparison I rs η K) (.up ℤ) ≫
        (p ⊗ₘ 𝟙 K) = (𝟙 (𝟙_ (Cpx S)) ⊗ₘ inc) := by
    apply HomologicalComplex.hom_ext
    intro n
    apply mapBifunctor.hom_ext
    intro i j hij
    rw [HomologicalComplex.comp_f]
    rw [HomologicalComplex₂.ιTotal_map_assoc]
    change ((doubleComparison I rs η K).f i).f j ≫
        ιTensorObj (CechComplex rs) K i j n hij ≫ (HomologicalComplex.tensorHom p (𝟙 K)).f n =
      ιTensorObj (𝟙_ (Cpx S)) T i j n hij ≫ (HomologicalComplex.tensorHom (𝟙 _) inc).f n
    rw [ι_mapBifunctorMap, ι_mapBifunctorMap]
    change ((rowComparison I rs η).app (K.X j)).f i ≫
        (p.f i ▷ K.X j) ≫ ((𝟙_ (Cpx S)).X i ◁ 𝟙 (K.X j)) ≫
        ιTensorObj (𝟙_ (Cpx S)) K i j n hij =
      (𝟙 ((𝟙_ (Cpx S)).X i) ▷ T.X j) ≫ ((𝟙_ (Cpx S)).X i ◁ inc.f j) ≫
        ιTensorObj (𝟙_ (Cpx S)) K i j n hij
    rw [whiskerLeft_id, id_whiskerRight, Category.id_comp, Category.id_comp,
      ← Category.assoc, hrow]
    rfl
  change (λ_ T).inv ≫ HomologicalComplex₂.total.map (doubleComparison I rs η K) (.up ℤ) ≫
      projection rs K = inc
  rw [projection_eq_tensor, ← Category.assoc (HomologicalComplex₂.total.map _ _) _ _,
    ht, id_tensorHom, leftUnitor_naturality, Iso.inv_hom_id_assoc]

end Projection

section ConeFunctor

open CochainComplex CategoryTheory.Functor

variable {A : Type*} [Category A]

private def coneFunctor {F G : A ⥤ Cpx R} (f : F ⟶ G) : A ⥤ Cpx R where
  obj X := mappingCone (f.app X)
  map {X Y} a := mappingCone.map (f.app X) (f.app Y) (F.map a) (G.map a) (f.naturality a).symm
  map_id X := by
    simp only [F.map_id, G.map_id]
    exact mappingCone.map_id _
  map_comp a b := by
    simp only [F.map_comp, G.map_comp]
    exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

private def coneMapNat {F G F' G' : A ⥤ Cpx R} (f : F ⟶ G) (g : F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (w : f ≫ b = a ≫ g) :
    coneFunctor f ⟶ coneFunctor g where
  app X := mappingCone.map (f.app X) (g.app X) (a.app X) (b.app X)
    (congrArg (fun t => t.app X) w)
  naturality X Y k := by
    dsimp only [coneFunctor]
    rw [← mappingCone.map_comp, ← mappingCone.map_comp]
    congr 1
    · exact a.naturality k
    · exact b.naturality k

private def coneInr {F G : A ⥤ Cpx R} (f : F ⟶ G) : G ⟶ coneFunctor f where
  app X := mappingCone.inr (f.app X)
  naturality _ _ _ := (mappingCone.triangleMap _ _ _ _ _).comm₂.symm

private def coneToShift {F G : A ⥤ Cpx R} (f : F ⟶ G) :
    coneFunctor f ⟶ F ⋙ shiftFunctor (Cpx R) (1 : ℤ) where
  app X := (mappingCone.triangle (f.app X)).mor₃
  naturality _ _ _ := (mappingCone.triangleMap _ _ _ _ _).comm₃.symm

private def rotateConeMap {F G : A ⥤ Cpx R} (f : F ⟶ G) :
    coneFunctor (coneInr f) ⟶ F ⋙ shiftFunctor (Cpx R) (1 : ℤ) where
  app X := (mappingCone.rotateHomotopyEquiv (f.app X)).inv
  naturality X Y k := by
    change mappingCone.map _ _ (G.map k) ((coneFunctor f).map k)
      ((coneInr f).naturality k).symm ≫
        (mappingCone.rotateHomotopyEquiv (f.app Y)).inv =
      (mappingCone.rotateHomotopyEquiv (f.app X)).inv ≫ (F.map k)⟦(1 : ℤ)⟧'
    apply HomologicalComplex.hom_ext
    intro n
    apply mappingCone.ext_from _ (n + 1) n rfl
    · simp [mappingCone.rotateHomotopyEquiv, mappingCone.map, coneInr]
    · have h := HomologicalComplex.congr_hom ((coneToShift f).naturality k) n
      simpa [mappingCone.rotateHomotopyEquiv, mappingCone.map, coneToShift, coneInr] using h

end ConeFunctor

section Resolution

open private totalComparison totalComparison_quasiIso cechTensor_quasiIso
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
open private projection_natural from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveCechComparison

open Specs.CommutativeAlgebraNotes.InjectiveCechComparison (singleZero projection)
open scoped ZeroObject
open CategoryTheory.Pretriangulated
open CochainComplex

private def fromModuleComplex (U : (Spec R).Opens) :
    𝟭 (Cpx R) ⟶ sectionComplex R U :=
  (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv ≫
    (toSections R U).mapHomologicalComplex (.up ℤ)

private lemma fromModuleComplex_restrict (J : Cpx R) (U : (Spec R).Opens) :
    (fromModuleComplex (⊤ : (Spec R).Opens)).app J ≫
      (restrictComplex R (le_top : U ≤ ⊤)).app J = (fromModuleComplex U).app J := by
  apply HomologicalComplex.hom_ext
  intro n
  exact tilde.toOpen_res (J.X n) ⊤ U (homOfLE le_top)

private instance fromModuleComplex_top_isIso (J : Cpx R) :
    IsIso ((fromModuleComplex (⊤ : (Spec R).Opens)).app J) := by
  have (n : ℤ) : IsIso (((fromModuleComplex (⊤ : (Spec R).Opens)).app J).f n) :=
    inferInstanceAs (IsIso (tilde.toOpen (J.X n) ⊤))
  exact HomologicalComplex.Hom.isIso_of_components _

private def torsionSectionsComplex [IsNoetherianRing R] (I : Ideal R) (J : Cpx R) :
    ShortComplex (Cpx R) :=
  ShortComplex.mk ((cochainTorsionInclusion I).app J)
    ((fromModuleComplex (complement R I)).app J) (by
      apply HomologicalComplex.hom_ext
      intro n
      exact torsion_restrict_zero I (J.X n))

private lemma torsionSectionsComplex_exact [IsNoetherianRing R] (I : Ideal R) (J : Cpx R)
    (hJ : ∀ n, Injective (J.X n)) : (torsionSectionsComplex I J).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  letI := hJ n
  obtain ⟨_, h⟩ := tildeComplement_injectiveSectionsExact R I (J.X n)
  exact h

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

private def coneTriangleIso {A B A' B' : Cpx R} {f : A ⟶ B} {g : A' ⟶ B'}
    (a : A ⟶ A') (b : B ⟶ B') (w : f ≫ b = a ≫ g) [QuasiIso a] [QuasiIso b] :
    DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle f) ≅
      DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle g) := by
  let m := DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap f g a b w)
  have ha : IsIso m.hom₁ := inferInstanceAs (IsIso (DerivedCategory.Q.map a))
  have hb : IsIso m.hom₂ := inferInstanceAs (IsIso (DerivedCategory.Q.map b))
  have hc := isIso₃_of_isIso₁₂ m (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g) ha hb
  letI := Triangle.isIso_of_isIsos m ha hb hc
  exact asIso m

theorem cechFlasqueConeComparison : FlasqueConeComparison.{u,w} := by
  intro R _ _ I rs hrs U M J ι hι hge hJ
  letI := hι
  letI := hge
  obtain ⟨η, hη, hηQ⟩ := idealTorsionCechComparison I rs hrs
  have hK := cechTensor_quasiIso rs ι hι
  have hcmp := totalComparison_quasiIso I rs η hηQ ⟨J, 0, hge⟩ hJ
  let P := projection rs J
  let T := torsionSectionsComplex I J
  let e₁ := coneTriangleIso ((cechTensorFunctor rs).map ι) ι (projection_natural rs ι).symm
  let e₂ := coneTriangleIso ((totalComparison I rs η).app J) (𝟙 J)
    (by
      change (cochainTorsionInclusion I).app J ≫ 𝟙 J =
        (totalComparison I rs η).app J ≫ projection rs J
      exact (Category.comp_id _).trans (total_projection I rs η hη J).symm :
      T.f ≫ 𝟙 J = (totalComparison I rs η).app J ≫ P)
  let S := DerivedCategory.triangleOfSES (torsionSectionsComplex_exact I J hJ)
  let e₃ := DerivedCategory.triangleOfSESIso (torsionSectionsComplex_exact I J hJ)
  let t := (restrictComplex R (le_top : U ≤ ⊤)).app J
  let V := DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle t)
  have hS : S ∈ distTriang _ := DerivedCategory.triangleOfSES_distinguished _
  have hV : V ∈ distTriang _ := DerivedCategory.mappingCocone_triangle_distinguished t
  let a := DerivedCategory.Q.map ((fromModuleComplex (⊤ : (Spec R).Opens)).app J)
  let b := 𝟙 (DerivedCategory.Q.obj ((sectionComplex R U).obj J))
  have w : S.rotate.mor₁ ≫ b = a ≫ V.rotate.mor₁ := by
    change DerivedCategory.Q.map ((fromModuleComplex U).app J) ≫ 𝟙 _ =
      DerivedCategory.Q.map ((fromModuleComplex (⊤ : (Spec R).Opens)).app J) ≫
        DerivedCategory.Q.map t
    rw [Category.comp_id, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (fromModuleComplex_restrict J U).symm
  let m := completeDistinguishedTriangleMorphism S.rotate V.rotate
    (rot_of_distTriang _ hS) (rot_of_distTriang _ hV) a b w
  have ha : IsIso m.hom₁ := inferInstanceAs (IsIso a)
  have hb : IsIso m.hom₂ := inferInstanceAs (IsIso b)
  have hc := isIso₃_of_isIso₁₂ m (rot_of_distTriang _ hS) (rot_of_distTriang _ hV) ha hb
  letI := Triangle.isIso_of_isIsos m ha hb hc
  let e₄ := (Functor.FullyFaithful.ofFullyFaithful (rotate _)).preimageIso (asIso m)
  exact ⟨e₁ ≪≫ e₂.symm ≪≫ e₃.symm ≪≫ e₄⟩

end Resolution


section Unaugmented

open CategoryTheory.Pretriangulated CochainComplex
open scoped ZeroObject
open AdvancedHomologicalAlgebra.AcyclicTermComparison
  (brutalCutIncl brutalCut_isZero_X brutalCutXIso)
open Specs.CommutativeAlgebraNotes.InjectiveCechComparison (singleZero projection)
open private projection_natural coefficients_isZero_neg
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveCechComparison
open private cutX cutIn from
  MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicTermComparison

private abbrev augmented (rs : List R) := singleZero R ⋙ cechTensorFunctor rs

private def projectionNat (rs : List R) : augmented rs ⟶ singleZero R where
  app M := projection rs ((singleZero R).obj M)
  naturality _ _ f := projection_natural rs ((singleZero R).map f)

private def cechTailInclusion (rs : List R) :
    augmented rs ⋙ positiveTail R ⟶ augmented rs :=
  Functor.whiskerLeft _ (positiveTailInclusion R) ≫ (Functor.rightUnitor _).hom

private def cechTailSequence (rs : List R) (M : ModuleCat.{u} R) :
    ShortComplex (Cpx R) :=
  ShortComplex.mk ((cechTailInclusion rs).app M) ((projectionNat rs).app M) (by
    apply HomologicalComplex.hom_ext
    intro n
    by_cases hn : 1 ≤ n
    · exact (isZero_single_obj_X (.up ℤ) 0 M n (by omega)).eq_of_tgt _ _
    · exact (brutalCut_isZero_X _ (1 ≤ ·) n hn).eq_of_src _ _)

private lemma cechTailSequence_exact (rs : List R) (M : ModuleCat.{u} R) :
    (cechTailSequence rs M).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let S := (cechTailSequence rs M).map (HomologicalComplex.eval _ (.up ℤ) n)
  change S.ShortExact
  by_cases hn : 1 ≤ n
  · have h₃ : IsZero S.X₃ := isZero_single_obj_X (.up ℤ) 0 M n (by omega)
    have h₁ : IsIso S.f := by
      change IsIso ((brutalCutIncl (cechCoefficients rs M) 1).f n)
      exact inferInstanceAs (IsIso (brutalCutXIso (cechCoefficients rs M) (1 ≤ ·) n hn).hom)
    letI := h₁
    exact ShortComplex.ShortExact.mk' ((S.exact_iff_epi (h₃.eq_of_tgt _ _)).mpr inferInstance)
      inferInstance (h₃.epi _)
  · have h₁ : IsZero S.X₁ := brutalCut_isZero_X _ (1 ≤ ·) n hn
    by_cases hz : n = 0
    · subst n
      letI : IsIso S.g := cechProjection_degreeZero rs M
      exact ShortComplex.ShortExact.mk'
        ((S.exact_iff_mono (h₁.eq_of_src _ _)).mpr inferInstance) (h₁.mono _) inferInstance
    · have h₂ : IsZero S.X₂ := coefficients_isZero_neg rs M n (by omega)
      have h₃ : IsZero S.X₃ := isZero_single_obj_X (.up ℤ) 0 M n hz
      exact ShortComplex.ShortExact.mk' (S.exact_of_isZero_X₂ h₂) (h₁.mono _) (h₃.epi _)

private def cechTailSequenceMap (rs : List R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    cechTailSequence rs M ⟶ cechTailSequence rs N :=
  ShortComplex.Hom.mk ((augmented rs ⋙ positiveTail R).map f) ((augmented rs).map f)
    ((singleZero R).map f)
    ((cechTailInclusion rs).naturality f) ((projectionNat rs).naturality f)

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

theorem cechComplement_cechTriangle : CechTriangle.{u,w} := by
  intro R _ rs
  let Q : Cpx R ⥤ DerivedCategory (ModuleCat.{u} R) := DerivedCategory.Q
  let c := Q.commShiftIso (1 : ℤ)
  let L := augmented rs ⋙ positiveTail R
  let Sh := CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ)
  let δ₀ : singleZero R ⋙ Q ⟶ L ⋙ Q ⋙ Sh :=
    { app M := DerivedCategory.triangleOfSESδ (cechTailSequence_exact rs M)
      naturality M N f := (DerivedCategory.triangleOfSESδ_naturality
        (cechTailSequence_exact rs M) (cechTailSequence_exact rs N)
        (cechTailSequenceMap rs f)).symm }
  let δ : singleZero R ⋙ Q ⟶ unaugmented R rs ⋙ Q :=
    δ₀ ≫ Functor.whiskerLeft L c.inv
  let ε : unaugmented R rs ⋙ Q ⟶ (augmented rs ⋙ Q) ⋙ Sh :=
    Functor.whiskerLeft L c.hom ≫
      (-(Functor.whiskerRight (Functor.whiskerRight (cechTailInclusion rs) Q) Sh))
  refine ⟨projectionNat rs, fun _ => rfl, δ, ε, fun M => ?_⟩
  let T := DerivedCategory.triangleOfSES (cechTailSequence_exact rs M)
  apply isomorphic_distinguished _ (rot_of_distTriang T (DerivedCategory.triangleOfSES_distinguished _))
  refine Triangle.isoMk _ T.rotate (Iso.refl (Q.obj ((augmented rs).obj M)))
    (Iso.refl (Q.obj ((singleZero R).obj M))) (c.app (L.obj M)) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change (DerivedCategory.triangleOfSESδ (cechTailSequence_exact rs M) ≫
      (c.app (L.obj M)).inv) ≫ (c.app (L.obj M)).hom = 𝟙 _ ≫ _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    rfl
  · change _ ≫ Sh.map (𝟙 _) = _
    rw [Sh.map_id]
    exact (Category.comp_id _).trans rfl

private def cechTailDesc (rs : List R) :
    coneFunctor (cechTailInclusion rs) ⟶ singleZero R where
  app M := mappingCone.descShortComplex (cechTailSequence rs M)
  naturality _ _ f := mappingCone.descShortComplex_naturality (cechTailSequenceMap rs f)

private def cechTailConeMap (rs : List R) :
    coneFunctor (coneInr (cechTailInclusion rs)) ⟶ coneFunctor (projectionNat rs) :=
  coneMapNat _ _ (𝟙 _) (cechTailDesc rs) (by
    ext M : 2
    exact (mappingCone.inr_descShortComplex (cechTailSequence rs M)).trans
      (Category.id_comp _).symm)

private def cechTailConeIso (rs : List R) :
    coneFunctor (projectionNat rs) ⋙ DerivedCategory.Q ≅ unaugmented R rs ⋙ DerivedCategory.Q := by
  let Q : Cpx R ⥤ DerivedCategory (ModuleCat.{u} R) := DerivedCategory.Q
  let a := Functor.whiskerRight (cechTailConeMap rs) Q
  let b := Functor.whiskerRight (rotateConeMap (cechTailInclusion rs)) Q
  have ha (M : ModuleCat.{u} R) : IsIso (a.app M) := by
    letI : QuasiIso ((cechTailDesc rs).app M) :=
      mappingCone.quasiIso_descShortComplex (cechTailSequence_exact rs M)
    let e := coneTriangleIso (𝟙 ((augmented rs).obj M)) ((cechTailDesc rs).app M)
      (by
        exact (mappingCone.inr_descShortComplex (cechTailSequence rs M)).trans
          (Category.id_comp _).symm :
        (coneInr (cechTailInclusion rs)).app M ≫ (cechTailDesc rs).app M =
          𝟙 ((augmented rs).obj M) ≫ (projectionNat rs).app M)
    exact inferInstanceAs (IsIso (e.hom.hom₃))
  have hb (M : ModuleCat.{u} R) : IsIso (b.app M) := by
    let h := (mappingCone.rotateHomotopyEquiv ((cechTailInclusion rs).app M)).symm.quasiIso_hom
    exact inferInstanceAs (IsIso (Q.map (mappingCone.rotateHomotopyEquiv
      ((cechTailInclusion rs).app M)).inv))
  letI : IsIso a := NatIso.isIso_of_isIso_app a
  letI : IsIso b := NatIso.isIso_of_isIso_app b
  exact (asIso a).symm ≪≫ asIso b

end Unaugmented

section DerivedSections

open AdvancedHomologicalAlgebra
open AdvancedHomologicalAlgebra.SheafTheory (IsFlasque)
open Specs.AdvancedHomologicalAlgebra.FlasqueAcyclicity
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

attribute [local instance] HasDerivedCategory.standard

private abbrev sheafEvaluation (R : CommRingCat.{u}) (U : (Spec R).Opens) :=
  SheafOfModules.evaluation.{u} (Spec R).ringCatSheaf (op U)

private abbrev sectionScalars (R : CommRingCat.{u}) (U : (Spec R).Opens) :=
  ModuleCat.restrictScalars.{u} ((Spec R).ringCatSheaf.obj.map
    ((initialOpOfTerminal (isTerminalTop : IsTerminal (⊤ : (Spec R).Opens))).to (op U))).hom ⋙
  ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).inv.hom

private lemma sections_eq_evaluation (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    sections R U = sheafEvaluation R U ⋙ sectionScalars R U := rfl

private instance sections_leftExact (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    PreservesFiniteLimits (sections R U) := by
  rw [sections_eq_evaluation]
  haveI : PreservesFiniteLimits (sheafEvaluation R U) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

private lemma sheafSections_acyclic (R : CommRingCat.{u}) (U : (Spec R).Opens)
    (F : (Spec R).Modules) (hF : IsFlasque (Spec R).ringCatSheaf F) :
    rightAcyclicValue (sections R U) F := by
  apply (AcyclicTermComparison.rightVanishing _ _ (sections R U) F).mpr
  intro n
  let G := sheafEvaluation R U
  let H := sectionScalars R U
  letI : G.Additive := ⟨by intros; rfl⟩
  letI : (sections R U).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive _
  letI : H.Additive := inferInstanceAs ((sectionScalars R U).Additive)
  let I := injectiveResolution F
  let K := (G.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have h := FlasqueAcyclicity.flasqueAcyclic (Spec R).ringCatSheaf U F hF n
  have hK : IsZero (K.homology (n + 1)) := by
    exact h.of_iso (((CechToCohomology.natRightDerivedIso G (n + 1)).app F ≪≫
      I.isoRightDerivedObj G (n + 1)).symm)
  let e : (sections R U).mapHomologicalComplex (.up ℕ) ≅
      G.mapHomologicalComplex (.up ℕ) ⋙ H.mapHomologicalComplex (.up ℕ) :=
    (Functor.mapHomologicalComplexCompIso
      (F := G) (G := H) (H := sections R U)
      (eqToIso (sections_eq_evaluation R U).symm) _).symm
  have hz := H.map_isZero hK
  have he : ((H.mapHomologicalComplex (.up ℕ)).obj K).ExactAt (n + 1) := by
    apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
    exact hz.of_iso ((K.sc (n + 1)).mapHomologyIso H)
  exact he.isZero_homology.of_iso
    (((CechToCohomology.natRightDerivedIso (sections R U) (n + 1)).app F ≪≫
      I.isoRightDerivedObj (sections R U) (n + 1) ≪≫
      (homologyFunctor _ (.up ℕ) (n + 1)).mapIso (e.app I.cocomplex)))

theorem flasqueComputesSections : FlasqueComputesSections.{u} := by
  intro R U K hK
  haveI : IsIso ((sections R U).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient (Spec R).Modules).obj K)) :=
    AcyclicTermComparison.rightComparison _ _ _ _ (fun q =>
      sheafSections_acyclic R U (K.obj.X q) (hK q))
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  infer_instance

end DerivedSections

section Naturality

open CochainComplex CategoryTheory.Functor
open Specs.CommutativeAlgebraNotes.InjectiveCechComparison (singleZero projection)

attribute [local instance] HasDerivedCategory.standard
open private tilde_preservesHomology from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.AffineTildeAcyclicity
open private projection_natural from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.InjectiveCechComparison
open private totalComparison totalComparison_quasiIso cechTensor_quasiIso
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison

private abbrev QMod := DerivedCategory.Q (C := ModuleCat.{u} R)
private abbrev QModPlus := DerivedCategory.Plus.Q (C := ModuleCat.{u} R)
private abbrev QSheafPlus := DerivedCategory.Plus.Q (C := (Spec R).Modules)

private def resolution (M : ModuleCat.{u} R) : Cpx R :=
  (injectiveResolution M).cocomplex.extend (ComplexShape.embeddingUpIntGE 0)

private def resolutionAug (M : ModuleCat.{u} R) : (singleZero R).obj M ⟶ resolution M :=
  (extendSingleIso (ComplexShape.embeddingUpIntGE 0) M (0 : ℕ) (0 : ℤ) rfl).inv ≫
    extendMap (injectiveResolution M).ι (ComplexShape.embeddingUpIntGE 0)

private instance (M : ModuleCat.{u} R) : QuasiIso (resolutionAug M) := by
  dsimp [resolutionAug]
  infer_instance

private def resolutionMap {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    resolution M ⟶ resolution N :=
  extendMap (InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M))
    (ComplexShape.embeddingUpIntGE 0)

private lemma resolutionAug_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (singleZero R).map f ≫ resolutionAug N = resolutionAug M ≫ resolutionMap f := by
  unfold resolutionAug resolutionMap
  simp only [Category.assoc]
  erw [← extendMap_comp, InjectiveResolution.desc_commutes, extendMap_comp, ← Category.assoc]
  rw [← Category.assoc (extendSingleIso (ComplexShape.embeddingUpIntGE 0) M 0 0 rfl).inv]
  apply congrArg (fun g => g ≫ extendMap (injectiveResolution N).ι (ComplexShape.embeddingUpIntGE 0))
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    have h0 : (ComplexShape.embeddingUpIntGE 0).f (0 : ℕ) = 0 := rfl
    simp [extendSingleIso_inv_f, extendMap_f _ _ h0, HomologicalComplex.single_map_f_self,
      Category.assoc]
  · exact (isZero_single_obj_X (.up ℤ) 0 M n hn).eq_of_src _ _

private def resolutionPlus (M : ModuleCat.{u} R) : CochainComplex.Plus (ModuleCat.{u} R) :=
  ⟨resolution M, 0, by
    change CochainComplex.IsStrictlyGE
      ((injectiveResolution M).cocomplex.extend (ComplexShape.embeddingUpIntGE 0)) 0
    infer_instance⟩

private def sheafResolution (M : ModuleCat.{u} R) : CochainComplex.Plus (Spec R).Modules :=
  (tilde.functor R).mapCochainComplexPlus.obj (resolutionPlus M)

private def sheafAug (M : ModuleCat.{u} R) :
    (sheafStalkPlus R).obj (tilde M) ⟶ sheafResolution M :=
  ObjectProperty.homMk (((tilde.functor R).mapCochainComplexSingleFunctor 0).inv.app M ≫
    ((tilde.functor R).mapHomologicalComplex (.up ℤ)).map (resolutionAug M))

private lemma sheafAug_quasiIso (M : ModuleCat.{u} R) :
    CochainComplex.Plus.quasiIso (Spec R).Modules (sheafAug M) := by
  let F := tilde.functor R
  letI : F.PreservesHomology := tilde_preservesHomology R
  have h := quasiIso_map_of_preservesHomology (resolutionAug M) F
  change QuasiIso ((F.mapCochainComplexSingleFunctor 0).inv.app M ≫
    (F.mapHomologicalComplex (.up ℤ)).map (resolutionAug M))
  exact quasiIso_comp _ _

private def sheafResolutionMap {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    sheafResolution M ⟶ sheafResolution N :=
  (tilde.functor R).mapCochainComplexPlus.map (ObjectProperty.homMk (resolutionMap f))

private lemma sheafAug_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (sheafStalkPlus R).map (tilde.map f) ≫ sheafAug N =
      sheafAug M ≫ sheafResolutionMap f := by
  apply ObjectProperty.hom_ext
  let F := tilde.functor R
  let e := (F.mapCochainComplexSingleFunctor 0).inv
  let S := CochainComplex.singleFunctor (Spec R).Modules 0
  let G := F.mapHomologicalComplex (.up ℤ)
  change S.map (F.map f) ≫ (e.app N ≫ G.map (resolutionAug N)) =
    (e.app M ≫ G.map (resolutionAug M)) ≫ G.map (resolutionMap f)
  have h := e.naturality f
  change S.map (F.map f) ≫ e.app N = e.app M ≫ G.map ((singleZero R).map f) at h
  rw [← Category.assoc, h, Category.assoc, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, resolutionAug_naturality]

private def sectionsComparison [IsNoetherianRing R] (U : (Spec R).Opens)
    (M : ModuleCat.{u} R) :
    QMod.obj ((sectionComplex R U).obj (resolution M)) ≅ (derivedSections R U).obj M := by
  let F := sections R U
  let J := sheafResolution M
  letI : IsIso (F.rightDerivedFunctorPlusUnit.app J) :=
    flasqueComputesSections R U J (fun n => by
      haveI : Injective ((resolution M).X n) := by
        change Injective (((injectiveResolution M).cocomplex.extend
          (ComplexShape.embeddingUpIntGE 0)).X n)
        infer_instance
      exact tildeFlasque R ((resolution M).X n))
  let e := (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)).app
    (F.mapCochainComplexPlus.obj J)
  letI : IsIso (QSheafPlus.map (sheafAug M)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso _) _ (sheafAug_quasiIso M)
  exact e.symm ≪≫ DerivedCategory.Plus.ι.mapIso
    (asIso (F.rightDerivedFunctorPlusUnit.app J) ≪≫
      (asIso (F.rightDerivedFunctorPlus.map (QSheafPlus.map (sheafAug M)))).symm)

private lemma sectionsComparison_naturality [IsNoetherianRing R] (U : (Spec R).Opens)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    QMod.map ((sectionComplex R U).map (resolutionMap f)) ≫ (sectionsComparison U N).hom =
      (sectionsComparison U M).hom ≫ (derivedSections R U).map f := by
  let F := sections R U
  let D := F.rightDerivedFunctorPlus
  let L := DerivedCategory.Plus.ι (C := ModuleCat.{u} R)
  let φ := sheafResolutionMap f
  let ψ := F.mapCochainComplexPlus.map φ
  let S := DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)
  let f' := (sheafStalkPlus R).map (tilde.map f)
  let a := D.map (QSheafPlus.map (sheafAug M))
  let b := D.map (QSheafPlus.map (sheafAug N))
  haveI : IsIso a := by
    haveI : IsIso (QSheafPlus.map (sheafAug M)) :=
      Localization.inverts _ (CochainComplex.Plus.quasiIso _) _ (sheafAug_quasiIso M)
    dsimp [a]
    infer_instance
  haveI : IsIso b := by
    haveI : IsIso (QSheafPlus.map (sheafAug N)) :=
      Localization.inverts _ (CochainComplex.Plus.quasiIso _) _ (sheafAug_quasiIso N)
    dsimp [b]
    infer_instance
  have w : D.map (QSheafPlus.map f') ≫ b = a ≫ D.map (QSheafPlus.map φ) := by
    simp only [a, b, ← Functor.map_comp]
    exact congrArg (fun k => D.map (QSheafPlus.map k)) (sheafAug_naturality f)
  have wi : D.map (QSheafPlus.map φ) ≫ inv b = inv a ≫ D.map (QSheafPlus.map f') := by
    apply (cancel_epi a).mp
    rw [← Category.assoc, ← w, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  have h₁ : QMod.map ((sectionComplex R U).map (resolutionMap f)) ≫
      S.inv.app (F.mapCochainComplexPlus.obj (sheafResolution N)) =
      S.inv.app (F.mapCochainComplexPlus.obj (sheafResolution M)) ≫ L.map (QModPlus.map ψ) :=
    S.inv.naturality ψ
  change QMod.map ((sectionComplex R U).map (resolutionMap f)) ≫
      (S.inv.app (F.mapCochainComplexPlus.obj (sheafResolution N)) ≫
        L.map (F.rightDerivedFunctorPlusUnit.app (sheafResolution N) ≫ inv b)) =
    (S.inv.app (F.mapCochainComplexPlus.obj (sheafResolution M)) ≫
      L.map (F.rightDerivedFunctorPlusUnit.app (sheafResolution M) ≫ inv a)) ≫
      L.map (D.map (QSheafPlus.map f'))
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  congr 1
  have hu := F.rightDerivedFunctorPlusUnit.naturality φ
  change QModPlus.map ψ ≫ _ = _ ≫ D.map (QSheafPlus.map φ) at hu
  rw [← Category.assoc, hu, Category.assoc, wi, Category.assoc]

private lemma sectionsComparison_restrict [IsNoetherianRing R] {U V : (Spec R).Opens}
    (h : U ≤ V) (M : ModuleCat.{u} R) :
    QMod.map ((restrictComplex R h).app (resolution M)) ≫ (sectionsComparison U M).hom =
      (sectionsComparison V M).hom ≫ (derivedRestriction R h).app M := by
  let F := sections R V
  let G := sections R U
  let τ := restrict R h
  let L := DerivedCategory.Plus.ι (C := ModuleCat.{u} R)
  let J := sheafResolution M
  let x := QSheafPlus.map (sheafAug M)
  haveI : IsIso x := Localization.inverts _ (CochainComplex.Plus.quasiIso _) _ (sheafAug_quasiIso M)
  let S := DerivedCategory.Plus.QCompιIso (ModuleCat.{u} R)
  let ψ := τ.mapCochainComplexPlus.app J
  have hi : inv (F.rightDerivedFunctorPlus.map x) ≫ τ.rightDerivedFunctorPlus.app _ =
      τ.rightDerivedFunctorPlus.app _ ≫ inv (G.rightDerivedFunctorPlus.map x) := by
    apply (cancel_epi (F.rightDerivedFunctorPlus.map x)).mp
    have hn := τ.rightDerivedFunctorPlus.naturality x
    change F.rightDerivedFunctorPlus.map x ≫ _ = _ ≫ G.rightDerivedFunctorPlus.map x at hn
    rw [IsIso.hom_inv_id_assoc, ← Category.assoc, hn, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  change QMod.map ψ.hom ≫
      (S.inv.app (G.mapCochainComplexPlus.obj J) ≫ L.map (G.rightDerivedFunctorPlusUnit.app J ≫
        inv (G.rightDerivedFunctorPlus.map x))) =
    (S.inv.app (F.mapCochainComplexPlus.obj J) ≫ L.map (F.rightDerivedFunctorPlusUnit.app J ≫
        inv (F.rightDerivedFunctorPlus.map x))) ≫
      L.map (τ.rightDerivedFunctorPlus.app _)
  have hn := S.inv.naturality ψ
  change QMod.map ψ.hom ≫ S.inv.app (G.mapCochainComplexPlus.obj J) =
    S.inv.app (F.mapCochainComplexPlus.obj J) ≫ L.map (QModPlus.map ψ) at hn
  rw [← Category.assoc, hn, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  congr 1
  have hf := τ.rightDerivedFunctorPlus_fac_app J
  change _ ≫ _ = QModPlus.map ψ ≫ _ at hf
  simp only [Category.assoc]
  rw [hi, ← Category.assoc (F.rightDerivedFunctorPlusUnit.app J), hf, Category.assoc]

private def affineComparison [IsNoetherianRing R] :
    singleZero R ⋙ QMod ≅ derivedSections R ⊤ :=
  NatIso.ofComponents (fun M =>
    asIso (QMod.map (resolutionAug M)) ≪≫
      QMod.mapIso (asIso ((fromModuleComplex (⊤ : (Spec R).Opens)).app (resolution M))) ≪≫
      sectionsComparison ⊤ M) (by
    intro M N f
    simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Functor.comp_map, Category.assoc]
    rw [← Functor.map_comp_assoc, resolutionAug_naturality, Functor.map_comp, Category.assoc]
    have h := (fromModuleComplex (⊤ : (Spec R).Opens)).naturality (resolutionMap f)
    change resolutionMap f ≫ _ = _ at h
    have hQ := congrArg QMod.map h
    simp only [Functor.map_comp] at hQ
    rw [← Category.assoc (QMod.map (resolutionMap f)), hQ, Category.assoc,
      sectionsComparison_naturality])

private def complexProjection (rs : List R) : cechTensorFunctor rs ⟶ 𝟭 (Cpx R) where
  app J := projection rs J
  naturality _ _ f := projection_natural rs f

private def torsionSectionsComplexMap [IsNoetherianRing R] (I : Ideal R)
    {J K : Cpx R} (f : J ⟶ K) : torsionSectionsComplex I J ⟶ torsionSectionsComplex I K where
  τ₁ := ((idealTorsionFunctor I).mapHomologicalComplex (.up ℤ)).map f
  τ₂ := f
  τ₃ := (sectionComplex R (complement R I)).map f
  comm₁₂ := (cochainTorsionInclusion I).naturality f
  comm₂₃ := (fromModuleComplex (complement R I)).naturality f

private def torsionConeDesc [IsNoetherianRing R] (I : Ideal R) :
    coneFunctor (cochainTorsionInclusion I) ⟶ sectionComplex R (complement R I) where
  app J := mappingCone.descShortComplex (torsionSectionsComplex I J)
  naturality _ _ f :=
    mappingCone.descShortComplex_naturality (torsionSectionsComplexMap I f)

set_option maxHeartbeats 800000 in
private theorem openComplementConeIso [IsNoetherianRing R] (I : Ideal R) (rs : List R)
    (hI : Ideal.span {r | r ∈ rs} = I) :
    ∃ e : coneFunctor (projectionNat rs) ⋙ QMod ≅ derivedSections R (complement R I),
      ∀ M, QMod.map ((coneInr (projectionNat rs)).app M) ≫ e.hom.app M =
        QMod.map (resolutionAug M ≫ (fromModuleComplex (complement R I)).app (resolution M)) ≫
          (sectionsComparison (complement R I) M).hom := by
  classical
  choose η hη hQ using idealTorsionCechComparison I rs hI
  let χ := totalComparison I rs η
  let P := complexProjection rs
  let T := cochainTorsionInclusion I
  let C := coneFunctor P ⋙ QMod
  let a := whiskerRight (coneMapNat T P χ (𝟙 _) (by
    ext J : 2
    exact (Category.comp_id _).trans (total_projection I rs η hη J).symm)) QMod
  let d := whiskerRight (torsionConeDesc I) QMod
  let U := complement R I
  have ha (M : ModuleCat.{u} R) : IsIso (a.app (resolution M)) := by
    let J := resolution M
    have hJ (n : ℤ) : Injective (J.X n) := by
      change Injective (((injectiveResolution M).cocomplex.extend
        (ComplexShape.embeddingUpIntGE 0)).X n)
      infer_instance
    haveI : QuasiIso (χ.app J) :=
      totalComparison_quasiIso I rs η hQ (resolutionPlus M) hJ
    let e := coneTriangleIso (χ.app J) (𝟙 J)
      (by exact (Category.comp_id _).trans (total_projection I rs η hη J).symm :
        T.app J ≫ 𝟙 J = χ.app J ≫ P.app J)
    exact inferInstanceAs (IsIso e.hom.hom₃)
  have hd (M : ModuleCat.{u} R) : IsIso (d.app (resolution M)) := by
    have hJ (n : ℤ) : Injective ((resolution M).X n) := by
      change Injective (((injectiveResolution M).cocomplex.extend
        (ComplexShape.embeddingUpIntGE 0)).X n)
      infer_instance
    have := mappingCone.quasiIso_descShortComplex (torsionSectionsComplex_exact I _ hJ)
    exact inferInstanceAs (IsIso (QMod.map (mappingCone.descShortComplex
      (torsionSectionsComplex I (resolution M)))))
  have hc (M : ModuleCat.{u} R) : IsIso (C.map (resolutionAug M)) := by
    let ι := resolutionAug M
    have := cechTensor_quasiIso rs ι inferInstance
    let e := coneTriangleIso ((cechTensorFunctor rs).map ι) ι (projection_natural rs ι).symm
    exact inferInstanceAs (IsIso e.hom.hom₃)
  refine ⟨NatIso.ofComponents (fun M => asIso (C.map (resolutionAug M)) ≪≫
    (asIso (a.app (resolution M))).symm ≪≫ asIso (d.app (resolution M)) ≪≫
      sectionsComparison U M) ?_, ?_⟩
  · intro M N f
    let j := resolutionMap f
    have hj : C.map ((singleZero R).map f) ≫ C.map (resolutionAug N) =
        C.map (resolutionAug M) ≫ C.map j := by
      simpa only [Functor.map_comp] using congrArg C.map (resolutionAug_naturality f)
    have wa := a.naturality j
    have wi : C.map j ≫ inv (a.app (resolution N)) =
        inv (a.app (resolution M)) ≫ (coneFunctor T ⋙ QMod).map j := by
      apply (cancel_epi (a.app (resolution M))).mp
      rw [← Category.assoc, ← wa, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        IsIso.hom_inv_id_assoc]
    change C.map ((singleZero R).map f) ≫
        (C.map (resolutionAug N) ≫ inv (a.app (resolution N)) ≫
          d.app (resolution N) ≫ (sectionsComparison U N).hom) =
      (C.map (resolutionAug M) ≫ inv (a.app (resolution M)) ≫
          d.app (resolution M) ≫ (sectionsComparison U M).hom) ≫ (derivedSections R U).map f
    simp only [Category.assoc]
    rw [← Category.assoc (C.map ((singleZero R).map f)), hj, Category.assoc,
      ← Category.assoc (C.map j), wi, Category.assoc]
    have w := d.naturality_assoc j (sectionsComparison U N).hom
    change (coneFunctor T ⋙ QMod).map j ≫ d.app (resolution N) ≫
        (sectionsComparison U N).hom =
      d.app (resolution M) ≫
        QMod.map ((sectionComplex R U).map j) ≫ (sectionsComparison U N).hom at w
    rw [w, sectionsComparison_naturality U f]

  · intro M
    let J := resolution M
    let ι := resolutionAug M
    have h₁ : QMod.map ((coneInr (projectionNat rs)).app M) ≫ C.map ι =
        QMod.map ι ≫ QMod.map ((coneInr P).app J) := by
      change QMod.map ((coneInr P).app ((singleZero R).obj M)) ≫
          QMod.map ((coneFunctor P).map ι) =
        QMod.map ι ≫ QMod.map ((coneInr P).app J)
      have h := ((coneInr P).naturality ι).symm
      change (coneInr P).app ((singleZero R).obj M) ≫ (coneFunctor P).map ι =
        ι ≫ (coneInr P).app J at h
      simpa only [Functor.map_comp] using congrArg QMod.map h
    have h₂ : QMod.map ((coneInr T).app J) ≫ a.app J = QMod.map ((coneInr P).app J) := by
      let m := mappingCone.triangleMap (T.app J) (P.app J) (χ.app J) (𝟙 J)
        ((Category.comp_id _).trans (total_projection I rs η hη J).symm)
      have h : (coneInr T).app J ≫ m.hom₃ = (coneInr P).app J :=
        m.comm₂.trans (Category.id_comp _)
      change QMod.map ((coneInr T).app J) ≫ QMod.map m.hom₃ = _
      exact (QMod.map_comp _ _).symm.trans (congrArg QMod.map h)
    have h₃ : QMod.map ((coneInr P).app J) ≫ inv (a.app J) =
        QMod.map ((coneInr T).app J) := by
      rw [← h₂, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    have h₄ : QMod.map ((coneInr T).app J) ≫ d.app J =
        QMod.map ((fromModuleComplex U).app J) := by
      change QMod.map ((coneInr T).app J) ≫ QMod.map ((torsionConeDesc I).app J) = _
      exact (QMod.map_comp _ _).symm.trans
        (congrArg QMod.map (mappingCone.inr_descShortComplex (torsionSectionsComplex I J)))
    change QMod.map ((coneInr (projectionNat rs)).app M) ≫
      (C.map ι ≫ inv (a.app J) ≫ d.app J ≫ (sectionsComparison U M).hom) = _
    rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc (QMod.map ((coneInr P).app J)),
      h₃, ← Category.assoc (QMod.map ((coneInr T).app J)), h₄, Functor.map_comp, Category.assoc]

open CategoryTheory.Pretriangulated

theorem cechNaturalDerivedComparison : NaturalDerivedComparison.{u} := by
  intro R _ I rs hrs U
  obtain ⟨e, he⟩ := openComplementConeIso I rs hrs
  let x := affineComparison (R := R)
  let t := cechTailConeIso (R := R) rs
  let c := whiskerRight (coneInr (projectionNat rs)) QMod
  let eU := t.symm ≪≫ e
  let b := c ≫ t.hom
  let δ₀ := whiskerRight (coneToShift (projectionNat rs)) QMod ≫
    whiskerLeft (augmented rs) (QMod.commShiftIso (1 : ℤ)).hom
  have hres : x.hom ≫ derivedRestriction R (le_top : U ≤ ⊤) = c ≫ e.hom := by
    ext M : 2
    change (QMod.map (resolutionAug M) ≫
      QMod.map ((fromModuleComplex (⊤ : (Spec R).Opens)).app (resolution M)) ≫
        (sectionsComparison ⊤ M).hom) ≫ (derivedRestriction R (le_top : U ≤ ⊤)).app M =
      QMod.map ((coneInr (projectionNat rs)).app M) ≫ e.hom.app M
    rw [he, Category.assoc, Category.assoc, ← sectionsComparison_restrict]
    simp only [← Functor.map_comp_assoc]
    rw [fromModuleComplex_restrict]
  refine ⟨x, eU, b, e.inv ≫ δ₀, ?_, ?_⟩
  · simpa only [b, eU, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc] using hres
  · intro M
    let T := QMod.mapTriangle.obj (mappingCone.triangle (projection rs ((singleZero R).obj M)))
    apply isomorphic_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished
      (projection rs ((singleZero R).obj M)))
    apply Iso.symm
    refine Triangle.isoMk T _ (Iso.refl (QMod.obj ((augmented rs).obj M)))
      (x.app M) (e.app M) ?_ ?_ ?_
    · exact (Category.id_comp _).symm
    · exact (congrArg (fun η => η.app M) hres).symm
    · change δ₀.app M ≫ (CategoryTheory.shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
        e.hom.app M ≫ (e.inv.app M ≫ δ₀.app M)
      rw [(CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (1 : ℤ)).map_id]
      exact (Category.comp_id (δ₀.app M)).trans (Iso.hom_inv_id_app_assoc e M _).symm

end Naturality

end CommutativeAlgebraNotes
