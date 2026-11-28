import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SmallCochainComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SingularCochainSheaves
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SmallChainHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HomologicalComplex
open P202Specs.CohomologyPairs P202Specs.SingularChains P202Specs.SmallChainHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace RepTheorySurvey.Geometric.SmallCochainComparison

open Analytic Analytic.SingularCochains Analytic.SmallCochains
open private agree_near_point simplexInclusion dualExact from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SingularCochainSheaves

abbrev sectionsRestriction : Analytic.SmallCochains.Expected.SectionsRestrictionType.{u} :=
  @Analytic.SmallCochains.sectionsRestriction

theorem sectionMap_naturality : Analytic.SmallCochains.Expected.RestrictionNaturality.{u} := by
  intro X V U i
  ext q : 1
  exact ((complexUnit X).f q).naturality i.op

theorem sectionMap_eq_zero_iff : Analytic.SmallCochains.Expected.KernelCharacterization.{u} := by
  classical
  intro X U q c
  let P := (presheafComplex X).X (q : ℤ)
  let S := (sheafComplex X).X (q : ℤ)
  let η := unit X (q : ℤ)
  change η.app (op U) c = 0 ↔ _
  constructor
  · intro hc
    have hlocal (x : U) : ∃ (W : Opens X) (i : W ⟶ U),
        x.val ∈ W ∧ P.map i.op c = 0 := by
      obtain ⟨W, hx, i, _, hi⟩ :=
        agree_near_point q x.property x.property c 0 (by
          change S.presheaf.germ U x.val x.property (η.app (op U) c) =
            S.presheaf.germ U x.val x.property (η.app (op U) 0)
          rw [hc, show η.app (op U) 0 = 0 from map_zero _])
      exact ⟨W, i, hx, by simpa only [map_zero] using hi⟩
    choose W i hx hi using hlocal
    let cover : OpenCover (TopCat.of U) U :=
      ⟨fun x => Subtype.val ⁻¹' (W x : Set X),
        fun x => (W x).isOpen.preimage continuous_subtype_val, fun x => ⟨x, hx x⟩⟩
    refine ⟨U, cover, fun s x hs => ?_⟩
    let t := simplexInclusion s (fun z => hs ⟨z, rfl⟩)
    have ht : includeSimplex (i x) t = s := by
      apply ContinuousMap.ext
      intro z
      rfl
    rw [← ht, ← SingularCochainSheaves.coordinates_restrict, hi x, map_zero]
    rfl
  · rintro ⟨ι, cover, hcover⟩
    apply TopCat.Presheaf.section_ext S
    intro x hx
    obtain ⟨j, hj⟩ := cover.covers ⟨x, hx⟩
    let W := U.isOpenEmbedding.functor.obj (⟨cover.sets j, cover.isOpen j⟩ : Opens (TopCat.of U))
    let i : W ⟶ U := homOfLE (by
      rintro _ ⟨y, _, rfl⟩
      exact y.property)
    have hxW : x ∈ W := ⟨⟨x, hx⟩, hj, rfl⟩
    have hlocal : P.map i.op c = 0 := by
      apply (coordinates W q).injective
      funext s
      rw [SingularCochainSheaves.coordinates_restrict, map_zero]
      apply hcover (includeSimplex i s) j
      rintro _ ⟨z, rfl⟩
      obtain ⟨y, hy, he⟩ := (s z).property
      have eq : (includeSimplex i s) z = y := Subtype.ext he.symm
      exact eq ▸ hy
    have hη : S.obj.map i.op (η.app (op U) c) = 0 := by
      have hnat : η.app (op W) (P.map i.op c) = S.obj.map i.op (η.app (op U) c) :=
        congrArg (fun f => f c) (η.naturality i.op)
      rw [← hnat, hlocal, map_zero]
    rw [← TopCat.Presheaf.germ_res_apply S.presheaf i x hxW, hη, map_zero, map_zero]

private abbrev ChainsZ := ChainComplex Coeff.{u} ℤ
private abbrev CochainsZ := CochainComplex Coeff.{u} ℤ

private abbrev chainDual : (ChainsZ.{u})ᵒᵖ ⥤ CochainsZ.{u} :=
  dualComplexFunctor ℚ Values.{u} (.down ℤ)

private theorem ordinary_isZero_neg (Y : TopCat.{u}) (i : ℤ) (hi : i < 0) :
    IsZero ((ordinaryCochains ℚ Values.{u} Y).X i) :=
  (dualFunctor ℚ Values.{u}).map_isZero
    (P202.SingularChains.ordinary_negative_chains ℚ ℚ Y i hi).op

private abbrev smallInclusionInt {Y : TopCat.{u}} {ι : Type u} (cover : OpenCover Y ι) :
    (smallComplex ℚ cover).extend (degreeEmbedding 0) ⟶ ordinaryComplex ℚ ℚ Y :=
  extendMap (smallInclusion ℚ cover) (degreeEmbedding 0)

private theorem smallInclusionInt_mono {Y : TopCat.{u}} {ι : Type u} (cover : OpenCover Y ι) :
    Mono (smallInclusionInt cover) := by
  apply mono_of_mono_f
  intro i
  by_cases hi : i < 0
  · have hs : IsZero (((smallComplex ℚ cover).extend (degreeEmbedding 0)).X i) :=
      (smallComplex ℚ cover).isZero_extend_X _ _ (by
        intro j
        change (0 : ℤ) + j ≠ i
        omega)
    exact hs.mono _
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg (by omega)⟩
    rw [extendMap_f _ _ (show (degreeEmbedding 0).f n = (n : ℤ) by simp [degreeEmbedding])]
    have : Mono ((smallInclusion ℚ cover).f n) :=
      (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
    infer_instance

private theorem smallQuotient_acyclic {Y : TopCat.{u}} {ι : Type u} (cover : OpenCover Y ι) :
    (cokernel (smallInclusionInt cover)).Acyclic := by
  have h : QuasiIso (smallInclusion ℚ cover) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).mpr
      (P202.SmallChainHomology.absoluteComparison ℚ Y ι cover n)
  have hS : (ShortComplex.cokernelSequence (smallInclusionInt cover)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := smallInclusionInt_mono cover
      epi_g := inferInstance }
  exact hS.acyclic_X₃ ((quasiIso_extendMap_iff _ _).mpr h)

private theorem cochain_exactAt_iff (K : CochainsZ.{u}) (i : ℤ) :
    K.ExactAt i ↔ (K.sc' (i - 1) i (i + 1)).Exact :=
  K.exactAt_iff' (i - 1) i (i + 1)
    (ComplexShape.prev_eq' (.up ℤ) (show (i - 1) + 1 = i by omega))
    (ComplexShape.next_eq' (.up ℤ) (show i + 1 = i + 1 from rfl))

private theorem dual_acyclic (K : ChainsZ.{u}) (hK : K.Acyclic) :
    (chainDual.obj (op K)).Acyclic := by
  intro i
  rw [cochain_exactAt_iff]
  have h : (K.sc' (i + 1) i (i - 1)).Exact :=
    (K.exactAt_iff' (i + 1) i (i - 1)
      (ComplexShape.prev_eq' (.down ℤ) (show i + 1 = i + 1 from rfl))
      (ComplexShape.next_eq' (.down ℤ) (show (i - 1) + 1 = i by omega))).mp (hK i)
  exact dualExact _ h

/-- Dualizing the small-chain quotient sequence identifies the quotient dual
with the cochains annihilating the small subcomplex. -/
private abbrev coverQuotientSequence {Y : TopCat.{u}} {ι : Type u} (cover : OpenCover Y ι) :
    ShortComplex CochainsZ.{u} :=
  (ShortComplex.cokernelSequence (smallInclusionInt cover)).op.map chainDual

private theorem coverQuotientSequence_exact {Y : TopCat.{u}} {ι : Type u}
    (cover : OpenCover Y ι) (i : ℤ) :
    ((coverQuotientSequence cover).map (eval Coeff.{u} (.up ℤ) i)).Exact :=
  dualExact _ ((ShortComplex.cokernelSequence_exact (smallInclusionInt cover)).map
    (eval Coeff.{u} (.down ℤ) i))

private theorem coverQuotientSequence_injective {Y : TopCat.{u}} {ι : Type u}
    (cover : OpenCover Y ι) (i : ℤ) :
    Function.Injective ((coverQuotientSequence cover).f.f i) := by
  let π := cokernel.π (smallInclusionInt cover)
  have hπ : Function.Surjective (π.f i) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  intro a b hab
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hπ x
  exact LinearMap.congr_fun hab y

private theorem coverRestriction_eq_zero_iff {X : TopCat.{u}} {ι : Type u} (U : Opens X)
    (cover : OpenCover (TopCat.of U) ι) (q : ℕ)
    (c : (ordinaryCochains ℚ Values.{u} (TopCat.of U)).X (q : ℤ)) :
    (coverQuotientSequence cover).g.f (q : ℤ) c = 0 ↔
      ∀ (s : SimplexIn U q) (j : ι), Set.range s ⊆ cover.sets j → coordinates U q c s = 0 := by
  let Y := TopCat.of U
  let e := degreeEmbedding 0
  have he : e.f q = (q : ℤ) := by change (0 : ℤ) + q = q; simp
  let J := (smallComplex ℚ cover).extendXIso e he
  let c₀ : (ordinaryComplex ℚ ℚ Y).X (q : ℤ) →ₗ[ℚ] Values.{u} := c
  let c' := ordinaryCochainsEquiv ℚ Values.{u} Y q c
  let r : ((smallComplex ℚ cover).extend e).X (q : ℤ) →ₗ[ℚ] Values.{u} :=
    (coverQuotientSequence cover).g.f (q : ℤ) c
  have hrestrict (z : ((smallComplex ℚ cover).extend e).X (q : ℤ)) :
      r z = c' (J.hom z).val := by
    change c₀ ((smallInclusionInt cover).f (q : ℤ) z) = _
    rw [extendMap_f _ _ he]
    rfl
  have hcoords (s : Simplex Y q) :
      coordinates U q c (simplexEquiv Y q s) = c' (Finsupp.single s 1) := by
    change c' (Finsupp.single ((simplexEquiv Y q).symm (simplexEquiv Y q s)) 1) = _
    rw [Equiv.symm_apply_apply]
  change r = 0 ↔ _
  constructor
  · intro h s j hs
    let t := (simplexEquiv Y q).symm s
    have ht : Set.range (simplexEquiv Y q t) ⊆ cover.sets j := by
      simpa only [t, Equiv.apply_symm_apply] using hs
    let x : smallModule ℚ cover q :=
      ⟨Finsupp.single t 1, Finsupp.single_mem_supported ℚ 1 ⟨j, ht⟩⟩
    have hz : (J.hom (J.inv x) : smallModule ℚ cover q) = x :=
      congrArg (fun f => f x) J.inv_hom_id
    have h' := hrestrict (J.inv x)
    rw [h, hz] at h'
    rw [← show simplexEquiv Y q t = s from Equiv.apply_symm_apply _ _, hcoords]
    exact h'.symm
  · intro h
    have hz : smallModule ℚ cover q ≤ c'.ker := by
      rw [P202.SmallChainHomology.smallModule_eq_span, Submodule.span_le]
      rintro _ ⟨s, ⟨j, hj⟩, rfl⟩
      change c' (Finsupp.single s 1) = 0
      rw [← hcoords]
      exact h (simplexEquiv Y q s) j hj
    apply LinearMap.ext
    intro z
    rw [hrestrict]
    exact hz (J.hom z).property

private theorem coverQuotient_to_section_zero {X : TopCat.{u}} {ι : Type u}
    (U : Opens X) (cover : OpenCover (TopCat.of U) ι) (i : ℤ)
    (b : (coverQuotientSequence cover).X₁.X i) :
    (sectionMap U).f i ((coverQuotientSequence cover).f.f i b) = 0 := by
  let S := coverQuotientSequence cover
  by_cases hi : i < 0
  · have hs : Subsingleton (S.X₂.X i) :=
      ModuleCat.subsingleton_of_isZero (ordinary_isZero_neg (TopCat.of U) i hi)
    rw [show S.f.f i b = 0 from hs.elim _ _, map_zero]
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg (by omega)⟩
    apply (sectionMap_eq_zero_iff U m _).mpr
    refine ⟨ι, cover, (coverRestriction_eq_zero_iff U cover m _).mp ?_⟩
    exact congrArg (fun g => g b) (congr_hom S.zero (m : ℤ))

/-- Each cocycle in the kernel lifts to the dual for a single cover. A
primitive in that dual vanishes on the same cover and hence lies in the kernel. -/
private theorem sectionKernel_acyclic {X : TopCat.{u}} (U : Opens X) :
    (kernel (sectionMap U)).Acyclic := by
  let f := sectionMap U
  let κ := kernel.ι f
  let K := kernel f
  let C := ordinaryCochains ℚ Values.{u} (TopCat.of U)
  have hκ (i : ℤ) : Function.Injective (κ.f i) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  intro i
  apply (cochain_exactAt_iff K i).mpr
  apply ((K.sc' (i - 1) i (i + 1)).moduleCat_exact_iff).mpr
  intro x hx
  change K.d i (i + 1) x = 0 at hx
  change ∃ y : K.X (i - 1), K.d (i - 1) i y = x
  by_cases hi : i < 0
  · have hs := ModuleCat.subsingleton_of_isZero (ordinary_isZero_neg (TopCat.of U) i hi)
    exact ⟨0, hκ i (hs.elim _ _)⟩
  have hzero : f.f i (κ.f i x) = 0 :=
    congrArg (fun g => g x) (congr_hom (kernel.condition f) i)
  have hcover : ∃ (ι : Type u) (cover : OpenCover (TopCat.of U) ι),
      (coverQuotientSequence cover).g.f i (κ.f i x) = 0 := by
    revert x
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg (by omega)⟩
    intro x hx hzero
    obtain ⟨ι, cover, h⟩ := (sectionMap_eq_zero_iff U n (κ.f (n : ℤ) x)).mp hzero
    exact ⟨ι, cover, (coverRestriction_eq_zero_iff U cover n _).mpr h⟩
  obtain ⟨ι, cover, hcover⟩ := hcover
  let S := coverQuotientSequence cover
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (coverQuotientSequence_exact cover i) (κ.f i x) hcover
  change S.f.f i z = κ.f i x at hz
  have hzc : S.X₁.d i (i + 1) z = 0 := by
    apply coverQuotientSequence_injective cover (i + 1)
    calc
      _ = C.d i (i + 1) (S.f.f i z) := (congrArg (fun g => g z) (S.f.comm i (i + 1))).symm
      _ = κ.f (i + 1) (K.d i (i + 1) x) := by
        rw [hz]
        exact congrArg (fun g => g x) (κ.comm i (i + 1))
      _ = _ := by rw [hx, map_zero, map_zero]
  have hA : S.X₁.Acyclic := dual_acyclic _ (smallQuotient_acyclic cover)
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((cochain_exactAt_iff _ i).mp (hA i)) z hzc
  change S.X₁.d (i - 1) i b = z at hb
  let c := S.f.f (i - 1) b
  have hc : f.f (i - 1) c = 0 := coverQuotient_to_section_zero U cover (i - 1) b
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((ShortComplex.kernelSequence_exact f).map (eval Coeff.{u} (.up ℤ) (i - 1))) c hc
  change κ.f (i - 1) y = c at hy
  refine ⟨y, hκ i ?_⟩
  calc
    _ = C.d (i - 1) i (κ.f (i - 1) y) := (congrArg (fun g => g y) (κ.comm (i - 1) i)).symm
    _ = S.f.f i (S.X₁.d (i - 1) i b) := by
      rw [hy]
      exact congrArg (fun g => g b) (S.f.comm (i - 1) i)
    _ = κ.f i x := by rw [hb, hz]

theorem sectionMap_quasiIso : Analytic.SmallCochains.Expected.Comparison.{u} := by
  intro X _ _ _ U
  let f := sectionMap U
  have hf : Epi f := by
    apply epi_of_epi_f
    intro i
    apply (ModuleCat.epi_iff_surjective _).mpr
    by_cases hi : i < 0
    · have h : IsZero ((sheafComplex X).X i) :=
        (CochainComplex.isStrictlyGE_iff _ _).mp
          (SingularCochainSheaves.nonnegativeSupport X) i hi
      have hs : Subsingleton ((evaluatedComplex U).X i) :=
        ModuleCat.subsingleton_of_isZero ((sectionsOn U).map_isZero h)
      exact fun s => ⟨0, hs.elim _ _⟩
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, Int.toNat_of_nonneg (by omega)⟩
      exact SingularCochainSheaves.sectionSurjective X U n
  let S := ShortComplex.kernelSequence f
  have hS : S.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstance
      epi_g := hf }
  have hK : S.X₁.Acyclic := sectionKernel_acyclic U
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (homologyMap S.g i)
  have hm : Mono (homologyMap S.g i) := by
    have h := hS.homology_exact₂ i
    refine (ShortComplex.exact_iff_mono _ ?_).mp h
    exact ((hK i).isZero_homology).eq_of_src _ _
  have he : Epi (homologyMap S.g i) := by
    have h := hS.homology_exact₃ i (i + 1) (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)
    refine (ShortComplex.exact_iff_epi _ ?_).mp h
    exact ((hK (i + 1)).isZero_homology).eq_of_tgt _ _
  exact isIso_of_mono_of_epi _

end RepTheorySurvey.Geometric.SmallCochainComparison
