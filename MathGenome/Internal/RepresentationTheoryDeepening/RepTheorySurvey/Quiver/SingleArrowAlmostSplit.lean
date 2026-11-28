import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Quiver.SingleArrowAlmostSplit
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.Forms
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Quiver.SingleArrowObjects
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.Schur

/-! The nonsplit extension and the almost split properties for a single arrow. -/

open CategoryTheory CategoryTheory.Limits
open scoped RM03.OneArrowSpec ZeroObject

namespace RepTheorySurvey.Quiver.SingleArrowAlmostSplit

open SingleArrowObjects (S₁ S₂ P₁ representative)
open SingleArrowObjectsSpec (Kind Vertex Rep)
open SingleArrowAlmostSplitSpec (sourceVertex targetVertex)
open RM03.QuiverRepresentation (vertex arrow component)
open RM03.OneArrowSpec (edge)

noncomputable abbrev inclusion.{w, d} := SingleArrowAlmostSplitSpec.inclusion.{w, d}
noncomputable abbrev projection.{w, d} := SingleArrowAlmostSplitSpec.projection.{w, d}
noncomputable abbrev sequence.{w, d} := SingleArrowAlmostSplitSpec.sequence.{w, d}

universe w d

variable {k : Type w} [Field k]

private theorem source_zero : IsZero (vertex (S₂.{w, d} k) false) := by
  change IsZero (vertex (Forms.vertexSimple.{0, 0, w, d} k (true : Vertex)) false)
  rw [Forms.vertexSimple_vertex_of_ne.{0, 0, w, d} k (by decide : (false : Vertex) ≠ true)]
  exact ModuleCat.isZero_of_subsingleton _

private theorem target_zero : IsZero (vertex (S₁.{w, d} k) true) := by
  change IsZero (vertex (Forms.vertexSimple.{0, 0, w, d} k (false : Vertex)) true)
  rw [Forms.vertexSimple_vertex_of_ne.{0, 0, w, d} k (by decide : (true : Vertex) ≠ false)]
  exact ModuleCat.isZero_of_subsingleton _

private theorem arrow_identity : arrow (P₁.{w, d} k) edge = LinearMap.id :=
  RM03.QuiverRepresentation.arrow_ofArrows _ _ edge

private theorem source_arrow : arrow (S₁.{w, d} k) edge = 0 :=
  Forms.vertexSimple_arrow.{0, 0, w, d} k (false : Vertex) edge

private theorem target_arrow : arrow (S₂.{w, d} k) edge = 0 :=
  Forms.vertexSimple_arrow.{0, 0, w, d} k (true : Vertex) edge

private theorem inclusion_app_true :
    (inclusion.{w, d} k).app (true : Vertex) = eqToHom (targetVertex k) := rfl

private theorem projection_app_false :
    (projection.{w, d} k).app (false : Vertex) = eqToHom (sourceVertex k) := rfl

private theorem hom_ext {V W : Rep.{w, d} k} {f g : V ⟶ W}
    (h₀ : f.app (false : Vertex) = g.app (false : Vertex))
    (h₁ : f.app (true : Vertex) = g.app (true : Vertex)) : f = g := by
  apply RM03.QuiverRepresentation.hom_ext
  intro i
  cases i
  · exact congrArg ModuleCat.Hom.hom h₀
  · exact congrArg ModuleCat.Hom.hom h₁

theorem shortExact : SingleArrowAlmostSplitSpec.ShortExact.{w, d} := by
  intro k _
  have : IsIso ((inclusion.{w, d} k).app (true : Vertex)) :=
    inclusion_app_true (k := k) ▸ inferInstanceAs (IsIso (eqToHom (targetVertex.{w, d} k)))
  have : IsIso ((projection.{w, d} k).app (false : Vertex)) :=
    projection_app_false (k := k) ▸ inferInstanceAs (IsIso (eqToHom (sourceVertex.{w, d} k)))
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply ((sequence k).exact_iff_kernel_ι_comp_cokernel_π_zero).2
    apply hom_ext
    · have h : (kernel.ι (projection k)).app (false : Vertex) ≫
          (projection k).app (false : Vertex) = 0 :=
        congrArg (fun f => f.app (false : Vertex)) (kernel.condition (projection k))
      have hz : (kernel.ι (projection k)).app (false : Vertex) = 0 :=
        (cancel_mono ((projection k).app (false : Vertex))).1 (by simpa only [zero_comp] using h)
      change (kernel.ι (projection k)).app (false : Vertex) ≫
        (cokernel.π (inclusion k)).app (false : Vertex) = 0
      rw [hz, zero_comp]
    · have h : (inclusion k).app (true : Vertex) ≫
          (cokernel.π (inclusion k)).app (true : Vertex) = 0 :=
        congrArg (fun f => f.app (true : Vertex)) (cokernel.condition (inclusion k))
      have hz : (cokernel.π (inclusion k)).app (true : Vertex) = 0 :=
        (cancel_epi ((inclusion k).app (true : Vertex))).1 (by simpa only [comp_zero] using h)
      change (kernel.ι (projection k)).app (true : Vertex) ≫
        (cokernel.π (inclusion k)).app (true : Vertex) = 0
      rw [hz, comp_zero]
  · change Mono (inclusion k)
    apply (NatTrans.mono_iff_mono_app _).2
    intro i
    cases i
    · exact source_zero.mono _
    · infer_instance
  · change Epi (projection k)
    apply (NatTrans.epi_iff_epi_app _).2
    intro i
    cases i
    · infer_instance
    · exact target_zero.epi _

private theorem from_source_to_projective_zero (f : S₁.{w, d} k ⟶ P₁.{w, d} k) : f = 0 := by
  apply hom_ext
  · apply ModuleCat.hom_ext
    have h := RM03.QuiverRepresentation.naturality f edge.toPath
    change (component f true).comp (arrow (S₁ k) edge) =
      (arrow (P₁ k) edge).comp (component f false) at h
    rw [source_arrow, arrow_identity, LinearMap.comp_zero] at h
    change 0 = component f false at h
    exact h.symm
  · exact target_zero.eq_of_src _ _

private theorem from_projective_to_target_zero (f : P₁.{w, d} k ⟶ S₂.{w, d} k) : f = 0 := by
  apply hom_ext
  · exact source_zero.eq_of_tgt _ _
  · apply ModuleCat.hom_ext
    have h := RM03.QuiverRepresentation.naturality f edge.toPath
    change (component f true).comp (arrow (P₁ k) edge) =
      (arrow (S₂ k) edge).comp (component f false) at h
    rw [target_arrow, arrow_identity, LinearMap.zero_comp] at h
    change component f true = 0 at h
    exact h

theorem nonsplit : SingleArrowAlmostSplitSpec.Nonsplit.{w, d} := by
  intro k _
  have : Simple (S₁.{w, d} k) := Forms.vertexSimple_isSimple k false
  have : Simple (S₂.{w, d} k) := Forms.vertexSimple_isSimple k true
  constructor
  · rintro ⟨⟨r, hr⟩⟩
    rw [from_projective_to_target_zero r, comp_zero] at hr
    exact id_nonzero _ hr.symm
  · rintro ⟨⟨s, hs⟩⟩
    rw [from_source_to_projective_zero s, zero_comp] at hs
    exact id_nonzero _ hs.symm

private theorem field_endomorphism (f : ModuleCat.of k (ULift.{d} k) ⟶ ModuleCat.of k (ULift.{d} k)) :
    ∃ a : k, f = a • 𝟙 _ := by
  refine ⟨(f (ULift.up 1)).down, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change f x = (f (ULift.up 1)).down • x
  have hx : x.down • (ULift.up (1 : k) : ULift.{d} k) = x := by
    apply ULift.ext
    simp
  calc
    f x = f (x.down • ULift.up 1) := congrArg (fun y => f y) hx.symm
    _ = x.down • f (ULift.up 1) := f.hom.map_smul _ _
    _ = (f (ULift.up 1)).down • x := by
      apply ULift.ext
      exact mul_comm _ _

private theorem scalar_projection (f : P₁.{w, d} k ⟶ S₁.{w, d} k) :
    ∃ a : k, f = a • projection.{w, d} k := by
  let e := eqToIso (sourceVertex.{w, d} k)
  obtain ⟨a, ha⟩ := field_endomorphism (f.app (false : Vertex) ≫ e.inv)
  refine ⟨a, hom_ext ?_ (target_zero.eq_of_tgt _ _)⟩
  change f.app (false : Vertex) = a • e.hom
  calc
    _ = (f.app (false : Vertex) ≫ e.inv) ≫ e.hom := by simp
    _ = (a • 𝟙 _) ≫ e.hom := congrArg (fun u => u ≫ e.hom) ha
    _ = _ := by
      exact (Linear.smul_comp _ _ _ a (𝟙 _) e.hom).trans
        (congrArg (fun f => a • f) (Category.id_comp e.hom))

private theorem scalar_inclusion (f : S₂.{w, d} k ⟶ P₁.{w, d} k) :
    ∃ a : k, f = a • inclusion.{w, d} k := by
  let e := eqToIso (targetVertex.{w, d} k)
  obtain ⟨a, ha⟩ := field_endomorphism (e.inv ≫ f.app (true : Vertex))
  refine ⟨a, hom_ext (source_zero.eq_of_src _ _) ?_⟩
  change f.app (true : Vertex) = a • e.hom
  calc
    _ = e.hom ≫ (e.inv ≫ f.app (true : Vertex)) := by simp
    _ = e.hom ≫ (a • 𝟙 _) := congrArg (fun u => e.hom ≫ u) ha
    _ = _ := by
      exact (Linear.comp_smul _ _ _ e.hom a (𝟙 _)).trans
        (congrArg (fun f => a • f) (Category.comp_id e.hom))

private theorem factor_from_summand (j : Kind) (f : representative.{w, d} k j ⟶ S₁.{w, d} k)
    (hf : ¬ IsSplitEpi f) : ∃ g : representative.{w, d} k j ⟶ P₁.{w, d} k, g ≫ projection k = f := by
  cases j with
  | source =>
    have : Simple (S₁.{w, d} k) := Forms.vertexSimple_isSimple k false
    change S₁.{w, d} k ⟶ S₁.{w, d} k at f
    change ¬ IsSplitEpi f at hf
    have h : f = 0 := by
      by_contra hn
      have := isIso_of_hom_simple hn
      exact hf inferInstance
    refine ⟨0, ?_⟩
    change (0 : S₁.{w, d} k ⟶ P₁.{w, d} k) ≫ projection k = f
    rw [zero_comp]
    exact h.symm
  | target =>
    have h : f = 0 := hom_ext (source_zero.eq_of_src _ _) (target_zero.eq_of_tgt _ _)
    exact ⟨0, by simpa only [zero_comp] using h.symm⟩
  | identity =>
    obtain ⟨a, ha⟩ := scalar_projection f
    refine ⟨a • (𝟙 (P₁.{w, d} k)), ?_⟩
    change (a • 𝟙 (P₁.{w, d} k)) ≫ projection k = f
    rw [Linear.smul_comp, Category.id_comp, ← ha]

private theorem factor_to_summand (j : Kind) (f : S₂.{w, d} k ⟶ representative.{w, d} k j)
    (hf : ¬ IsSplitMono f) : ∃ g : P₁.{w, d} k ⟶ representative.{w, d} k j, inclusion k ≫ g = f := by
  cases j with
  | source =>
    have h : f = 0 := hom_ext (source_zero.eq_of_src _ _) (target_zero.eq_of_tgt _ _)
    exact ⟨0, by simpa only [comp_zero] using h.symm⟩
  | target =>
    have : Simple (S₂.{w, d} k) := Forms.vertexSimple_isSimple k true
    change S₂.{w, d} k ⟶ S₂.{w, d} k at f
    change ¬ IsSplitMono f at hf
    have h : f = 0 := by
      by_contra hn
      have := isIso_of_hom_simple hn
      exact hf inferInstance
    refine ⟨0, ?_⟩
    change inclusion k ≫ (0 : P₁.{w, d} k ⟶ S₂.{w, d} k) = f
    rw [comp_zero]
    exact h.symm
  | identity =>
    obtain ⟨a, ha⟩ := scalar_inclusion f
    refine ⟨a • (𝟙 (P₁.{w, d} k)), ?_⟩
    change inclusion k ≫ (a • 𝟙 (P₁.{w, d} k)) = f
    rw [Linear.comp_smul, Category.comp_id, ← ha]

section Factorizations

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

theorem right_factorization : SingleArrowAlmostSplitSpec.RightFactorization.{w, d} := by
  intro k _ V f hf
  obtain ⟨n, ⟨e⟩⟩ := SingleArrowObjects.decomposition.{w, d} k V
  let J := Σ j : Kind, Fin (n j)
  let F : J → Rep.{w, d} k := fun j => representative k j.1
  let f' : (⨁ F) ⟶ S₁.{w, d} k := e.inv ≫ f
  have hn (j : J) : ¬ IsSplitEpi (biproduct.ι F j ≫ f') := by
    rintro ⟨⟨s, hs⟩⟩
    exact hf (IsSplitEpi.mk' ⟨s ≫ biproduct.ι F j ≫ e.inv, by
      simpa only [Category.assoc, f'] using hs⟩)
  choose g hg using fun j : J => factor_from_summand j.1 _ (hn j)
  have h : biproduct.desc g ≫ projection k = f' := by
    apply biproduct.hom_ext'
    intro j
    rw [biproduct.ι_desc_assoc, hg]
  refine ⟨e.hom ≫ biproduct.desc g, ?_⟩
  change (e.hom ≫ biproduct.desc g) ≫ projection k = f
  rw [Category.assoc, h]
  change e.hom ≫ e.inv ≫ f = f
  rw [Iso.hom_inv_id_assoc]

theorem left_factorization : SingleArrowAlmostSplitSpec.LeftFactorization.{w, d} := by
  intro k _ V f hf
  obtain ⟨n, ⟨e⟩⟩ := SingleArrowObjects.decomposition.{w, d} k V
  let J := Σ j : Kind, Fin (n j)
  let F : J → Rep.{w, d} k := fun j => representative k j.1
  let f' : S₂.{w, d} k ⟶ (⨁ F) := f ≫ e.hom
  have hn (j : J) : ¬ IsSplitMono (f' ≫ biproduct.π F j) := by
    rintro ⟨⟨r, hr⟩⟩
    exact hf (IsSplitMono.mk' ⟨e.hom ≫ biproduct.π F j ≫ r, by
      simpa only [Category.assoc, f'] using hr⟩)
  choose g hg using fun j : J => factor_to_summand j.1 _ (hn j)
  have h : inclusion k ≫ biproduct.lift g = f' := by
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, biproduct.lift_π, hg]
  refine ⟨biproduct.lift g ≫ e.inv, ?_⟩
  change inclusion k ≫ biproduct.lift g ≫ e.inv = f
  rw [← Category.assoc, h]
  change (f ≫ e.hom) ≫ e.inv = f
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Factorizations

-- The kernel and cokernel in the ambient category belong to the full
-- subcategory in this example. They give homology zero there as well.
private theorem shortExact_of_full_embedding {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [Preadditive D] [Balanced D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.PreservesZeroMorphisms] (S : ShortComplex C)
    (h : (S.map F).ShortExact) {Z : C} (hz : IsZero Z) : S.ShortExact := by
  have hk : IsLimit (KernelFork.ofι S.f S.zero) := by
    apply isLimitOfReflects F
    exact (isLimitMapConeForkEquiv' F S.zero).symm.toFun
      (ShortComplex.ShortExact.fIsKernel (S := S.map F) h)
  have hc : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    apply isColimitOfReflects F
    exact (isColimitMapCoconeCoforkEquiv' F S.zero).symm.toFun
      (ShortComplex.ShortExact.gIsCokernel (S := S.map F) h)
  have hm : Mono S.f := mono_of_isLimit_fork hk
  have he : Epi S.g := epi_of_isColimit_cofork hc
  have h₁ : hk.lift (KernelFork.ofι S.f S.zero) = 𝟙 _ := by
    apply (cancel_mono S.f).1
    rw [Category.id_comp]
    exact Fork.IsLimit.lift_ι hk
  have h₂ : hc.desc (CokernelCofork.ofπ S.g S.zero) = 𝟙 _ := by
    apply (cancel_epi S.g).1
    exact (Cofork.IsColimit.π_desc hc).trans (Category.comp_id S.g).symm
  let H : S.HomologyData :=
    { left :=
        { K := S.X₁
          H := Z
          i := S.f
          π := 0
          wi := S.zero
          hi := hk
          wπ := comp_zero
          hπ := CokernelCofork.IsColimit.ofEpiOfIsZero _ (by rw [h₁]; infer_instance) hz }
      right :=
        { Q := S.X₃
          H := Z
          p := S.g
          ι := 0
          wp := S.zero
          hp := hc
          wι := zero_comp
          hι := KernelFork.IsLimit.ofMonoOfIsZero _ (by
            rw [h₂]
            change Mono (𝟙 S.X₃)
            infer_instance) hz }
      iso := Iso.refl Z
      comm := by simp [S.zero] }
  exact ShortComplex.ShortExact.mk' ⟨⟨H, hz⟩⟩ hm he

theorem almost_split : SingleArrowAlmostSplitSpec.AlmostSplit.{w, d} := by
  intro k _
  let P := RM03.QuiverModuleEquivalenceSpec.finiteRepresentations.{0, 0, w, max w d}
    (k := k) (Q := Vertex)
  let X₁ : P.FullSubcategory := ⟨S₂ k, SingleArrowObjects.finite_representatives k .target⟩
  let X₂ : P.FullSubcategory := ⟨P₁ k, SingleArrowObjects.finite_representatives k .identity⟩
  let X₃ : P.FullSubcategory := ⟨S₁ k, SingleArrowObjects.finite_representatives k .source⟩
  let i : X₁ ⟶ X₂ := ObjectProperty.homMk (inclusion k)
  let p : X₂ ⟶ X₃ := ObjectProperty.homMk (projection k)
  let S := ShortComplex.mk i p (P.ι.map_injective (sequence k).zero)
  have hS : S.map P.ι = sequence k := rfl
  refine ⟨S, hS, ?_, ?_, ?_, ?_, ?_⟩
  · let Z : P.FullSubcategory := ⟨0, by
      intro j
      have : Subsingleton (vertex (0 : Rep.{w, d} k) j) :=
        ModuleCat.subsingleton_of_isZero ((isZero_zero (Rep.{w, d} k)).obj j)
      change Module.Finite k (vertex (0 : Rep.{w, d} k) j)
      exact Module.finite_def.mpr ⟨∅, by
        rw [Finset.coe_empty, Submodule.span_empty]
        exact (Submodule.eq_bot_of_subsingleton (p := ⊤)).symm⟩⟩
    have hz : IsZero Z :=
      IsZero.of_full_of_faithful_of_isZero P.ι Z (isZero_zero (Rep.{w, d} k))
    exact shortExact_of_full_embedding P.ι S (hS.symm ▸ shortExact k) hz
  · exact fun h => (nonsplit k).1 ((P.ι.isSplitMono_iff i).2 h)
  · exact fun h => (nonsplit k).2 ((P.ι.isSplitEpi_iff p).2 h)
  · intro V f hf
    obtain ⟨g, hg⟩ := right_factorization k V (P.ι.map f)
      (fun h => hf ((P.ι.isSplitEpi_iff f).1 h))
    exact ⟨ObjectProperty.homMk g, P.ι.map_injective hg⟩
  · intro V f hf
    obtain ⟨g, hg⟩ := left_factorization k V (P.ι.map f)
      (fun h => hf ((P.ι.isSplitMono_iff f).1 h))
    exact ⟨ObjectProperty.homMk g, P.ι.map_injective hg⟩

end RepTheorySurvey.Quiver.SingleArrowAlmostSplit
