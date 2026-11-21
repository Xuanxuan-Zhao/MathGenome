import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.NonstabilizingBoundaryExample
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ExhaustiveChainConvergence

set_option maxHeartbeats 600000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe u
namespace AdvancedHomologicalAlgebra.NonstabilizingBoundary
variable (k : Type u) [Field k]

@[simp] lemma differential_zero_neg_one : (differential k 0 (-1)).hom = LinearMap.id := rfl

lemma head_neg (a : ℤ) (ha : a < 1) : head k a = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply (Submodule.mem_bot k).mpr
  ext i
  apply (Finsupp.mem_supported' k x).mp hx
  change ¬ (i : ℤ) ≤ a
  have := i.pos
  omega

lemma acyclic (n : ℤ) :
    LinearMap.ker ((complex k).d n (n-1)).hom =
      LinearMap.range ((complex k).d (n+1) n).hom := by
  by_cases hn : n = 0
  · subst n
    change LinearMap.ker (differential k 0 (-1)).hom =
      LinearMap.range (differential k 1 0).hom
    simp [differential]
  · by_cases hn' : n = -1
    · subst n
      change LinearMap.ker (differential k (-1) (-2)).hom =
        LinearMap.range (differential k 0 (-1)).hom
      simp [differential]
    · haveI : Subsingleton ((complex k).X n) := by
        change Subsingleton (term k n)
        dsimp [term]
        rw [ite_eq_right (not_or.mpr ⟨hn, hn'⟩)]
        infer_instance
      exact Subsingleton.elim _ _

lemma boundedBelow : (filtration k).BoundedBelow := by
  intro n
  by_cases hn : n = 0
  · subst n
    exact ⟨1, fun a ha => head_neg k a ha⟩
  · by_cases hn' : n = -1
    · subst n
      refine ⟨0, ?_⟩
      intro a ha
      change piece k a (-1) = ⊥
      simp [ha.not_ge]
    · refine ⟨0, fun a _ => ?_⟩
      haveI : Subsingleton ((complex k).X n) := by
        change Subsingleton (term k n)
        dsimp [term]
        rw [ite_eq_right (not_or.mpr ⟨hn, hn'⟩)]
        infer_instance
      exact Subsingleton.elim _ _

lemma exhaustive : (filtration k).Exhaustive := by
  intro n x
  by_cases hn : n = 0
  · subst n
    change ∃ a : ℤ, x ∈ head k a
    refine ⟨((x.support.sup (fun i : ℕ+ => (i : ℕ)) : ℕ) : ℤ), ?_⟩
    intro i hi
    exact_mod_cast Finset.le_sup (f := fun i : ℕ+ => (i : ℕ)) hi
  · by_cases hn' : n = -1
    · subst n
      exact ⟨0, by change x ∈ piece k 0 (-1); simp⟩
    · exact ⟨0, by change x ∈ piece k 0 n; simp [piece, hn, hn']⟩

lemma lower_bot : (filtration k).lower 0 (-1) = ⊥ := by
  change (piece k (-1) (-1)).comap (piece k 0 (-1)).subtype = ⊥
  have h : piece k (-1) (-1) = ⊥ := by simp
  rw [h, Submodule.comap_bot, Submodule.ker_subtype]

/-- The associated graded in question is the whole copy spanned by the f_i. -/
def gradedEquiv : (filtration k).graded 0 (-1) ≃ₗ[k] V k :=
  ((filtration k).lower 0 (-1)).quotEquivOfEqBot (lower_bot k) ≪≫ₗ
    Submodule.topEquiv

@[simp] lemma gradedEquiv_projection (x : (filtration k).piece 0 (-1)) :
    gradedEquiv k ((filtration k).gradedProjection 0 (-1) x) = x.1 := rfl

lemma almost_eq (r : ℕ) : (filtration k).almost r 0 (-1) = ⊤ := by
  change piece k 0 (-1) ⊓ (piece k (0-(r:ℤ)) (-2)).comap
    (differential k (-1) (-2)).hom = ⊤
  simp [differential]

lemma cycles_eq_top (r : ℕ) : (filtration k).pageCycles r 0 (-1) = ⊤ := by
  change (filtration k).gradedImage 0 (-1) ((filtration k).almost r 0 (-1)) = ⊤
  rw [almost_eq]
  change ((⊤ : Submodule k ((complex k).X (-1))).comap _).map _ = ⊤
  rw [Submodule.comap_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

lemma boundarySource_eq (r : ℕ) : (filtration k).boundarySource r 0 (-1) = head k ((r:ℤ)-1) := by
  simp only [ExhaustiveChain.Filtration.boundarySource, zero_add]
  change piece k 0 (-1) ⊓ (piece k ((r:ℤ)-1) 0).map
    (differential k 0 (-1)).hom = _
  rw [piece_neg_one, ite_eq_left (by omega), piece_zero, differential_zero_neg_one,
    Submodule.map_id, top_inf_eq]

lemma boundaries_map (r : ℕ) :
    ((filtration k).pageBoundaries r 0 (-1)).map (gradedEquiv k).toLinearMap =
      head k ((r:ℤ)-1) := by
  change (((filtration k).boundarySource r 0 (-1)).comap
    ((filtration k).piece 0 (-1)).subtype |>.map
    ((filtration k).gradedProjection 0 (-1))).map _ = _
  rw [boundarySource_eq, ← Submodule.map_comp]
  change ((head k ((r:ℤ)-1)).comap (⊤ : Submodule k (V k)).subtype).map
    (⊤ : Submodule k (V k)).subtype = _
  rw [Submodule.map_comap_eq, Submodule.range_subtype, top_inf_eq]

lemma limitCycles_top : (filtration k).limitCycles 0 (-1) = ⊤ := by
  have h : (filtration k).filteredCycles 0 (-1) = ⊤ := by
    change piece k 0 (-1) ⊓ LinearMap.ker (differential k (-1) (-2)).hom = ⊤
    simp [differential]
  change (filtration k).gradedImage 0 (-1) _ = ⊤
  rw [h, ← almost_eq k 0]
  exact cycles_eq_top k 0

lemma mem_boundaries_iff (r : ℕ) (x : (filtration k).graded 0 (-1)) :
    x ∈ (filtration k).pageBoundaries r 0 (-1) ↔
      gradedEquiv k x ∈ head k ((r:ℤ)-1) := by
  rw [← boundaries_map k r, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

/-- An explicit identification of the numerator with the full f_i space. -/
def cyclesEquiv (r : ℕ) : (filtration k).pageCycles r 0 (-1) ≃ₗ[k] V k :=
  LinearEquiv.ofEq _ _ (cycles_eq_top k r) ≪≫ₗ Submodule.topEquiv ≪≫ₗ gradedEquiv k

@[simp] lemma cyclesEquiv_apply (r : ℕ) (x : (filtration k).pageCycles r 0 (-1)) :
    cyclesEquiv k r x = gradedEquiv k x.1 := rfl

lemma restrict_tail_ker (r : ℕ) :
    LinearMap.ker (Finsupp.restrictDom k k {i : ℕ+ | r ≤ (i : ℕ)}) =
      head k ((r:ℤ)-1) := by
  ext x
  rw [LinearMap.mem_ker, Subtype.ext_iff]
  change Finsupp.filter (fun i : ℕ+ => r ≤ (i : ℕ)) x = 0 ↔ _
  rw [head, Finsupp.mem_supported']
  constructor
  · intro h i hi
    have hi' : r ≤ (i : ℕ) := by
      change ¬ (i : ℤ) ≤ (r:ℤ)-1 at hi
      omega
    have hh := DFunLike.congr_fun h i
    simpa [Finsupp.filter_apply, hi'] using hh
  · intro h
    ext i
    by_cases hi : r ≤ (i : ℕ)
    · simp only [Finsupp.filter_apply, ite_eq_left hi, Finsupp.zero_apply]
      exact h i (by change ¬ (i : ℤ) ≤ (r:ℤ)-1; omega)
    · simp [hi]

/-- Remove the finitely many f_i already hit by boundaries. -/
def tailProjection (r : ℕ) : (filtration k).pageCycles r 0 (-1) →ₗ[k] tail k r :=
  (Finsupp.restrictDom k k {i : ℕ+ | r ≤ (i : ℕ)}).comp (cyclesEquiv k r).toLinearMap

lemma tailProjection_surjective (r : ℕ) : Function.Surjective (tailProjection k r) := by
  exact (LinearMap.range_eq_top.mp (Finsupp.range_restrictDom
    {i : ℕ+ | r ≤ (i:ℕ)})).comp (cyclesEquiv k r).surjective

lemma tailProjection_ker (r : ℕ) :
    LinearMap.ker (tailProjection k r) =
      ((filtration k).pageBoundaries r 0 (-1)).comap
        ((filtration k).pageCycles r 0 (-1)).subtype := by
  rw [tailProjection, LinearMap.ker_comp, restrict_tail_ker]
  ext x
  exact (mem_boundaries_iff k r x.1).symm

/-- The elementary first isomorphism theorem, with a named denominator. -/
def quotientByKernelEquiv {M N : Type u} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (B : Submodule k M) (f : M →ₗ[k] N)
    (h : B = LinearMap.ker f) (hf : Function.Surjective f) : (M ⧸ B) ≃ₗ[k] N :=
  Submodule.quotEquivOfEq B (LinearMap.ker f) h ≪≫ₗ f.quotKerEquivOfSurjective hf

/-- Every page is the tail with the original f_i representatives. -/
def pageEquiv (r : ℕ) : page k r ≃ₗ[k] tail k r :=
  quotientByKernelEquiv k (M := (filtration k).pageCycles r 0 (-1)) (N := tail k r)
    (((filtration k).pageBoundaries r 0 (-1)).comap
      ((filtration k).pageCycles r 0 (-1)).subtype)
    (tailProjection k r) (tailProjection_ker k r).symm (tailProjection_surjective k r)


lemma tail_nontrivial (r : ℕ) (hr : 1 ≤ r) : Nontrivial (tail k r) := by
  let i : ℕ+ := ⟨r, by omega⟩
  let x : tail k r := ⟨Finsupp.single i 1, Finsupp.single_mem_supported k 1 (show r ≤ (i:ℕ) from le_rfl)⟩
  refine ⟨⟨x, 0, ?_⟩⟩
  intro h
  have hh := congrArg (fun y : tail k r => y.1 i) h
  simp [x] at hh

lemma page_nontrivial (r : ℕ) (hr : 1 ≤ r) : Nontrivial (page k r) := by
  haveI := tail_nontrivial k r hr
  exact (pageEquiv k r).toEquiv.nontrivial

lemma boundaries_strict (r : ℕ) (hr : 1 ≤ r) :
    (filtration k).pageBoundaries r 0 (-1) <
      (filtration k).pageBoundaries (r+1) 0 (-1) := by
  apply lt_of_le_of_ne ((filtration k).pageBoundaries_mono 0 (-1) (by omega))
  intro h
  have hh := congrArg (fun S => S.map (gradedEquiv k).toLinearMap) h
  rw [boundaries_map, boundaries_map] at hh
  let i : ℕ+ := ⟨r, by omega⟩
  have hx : Finsupp.single i (1:k) ∈ head k (((r+1:ℕ):ℤ)-1) :=
    Finsupp.single_mem_supported k 1 (by change (i:ℤ) ≤ _; simp [i])
  rw [← hh] at hx
  have hz := (Finsupp.mem_supported' k _).mp hx i (by change ¬ (i:ℤ) ≤ _; dsimp [i]; omega)
  simp at hz

lemma boundary_union : (⨆ r : ℕ, (filtration k).pageBoundaries r 0 (-1)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha⟩ := exhaustive k 0 (gradedEquiv k x)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, a+1 ≤ (r:ℤ) := exists_nat_ge (a+1)
  apply (le_iSup (fun r : ℕ => (filtration k).pageBoundaries r 0 (-1)) r)
  rw [mem_boundaries_iff]
  change gradedEquiv k x ∈ head k a at ha
  exact Finsupp.supported_mono (s := {i : ℕ+ | (i:ℤ) ≤ a})
    (t := {i : ℕ+ | (i:ℤ) ≤ (r:ℤ)-1}) (by
      intro i hi
      change (i:ℤ) ≤ a at hi
      change (i:ℤ) ≤ (r:ℤ)-1
      omega) ha

lemma infinity_zero : Subsingleton ((filtration k).infinity 0 (-1)) := by
  have h : ((filtration k).limitBoundaries 0 (-1)).comap
      ((filtration k).limitCycles 0 (-1)).subtype = ⊤ := by
    rw [show (filtration k).limitBoundaries 0 (-1) = ⊤ from boundary_union k,
      Submodule.comap_top]
  change Subsingleton (_ ⧸ _)
  rw [h]
  infer_instance

lemma homology_zero : Subsingleton ((filtration k).homology (-1)) := by
  have h : (filtration k).boundaries (-1) = ⊤ := by
    change LinearMap.range (differential k 0 (-1)).hom = ⊤
    simp
  have h' : (filtration k).cycleBoundary (-1) = ⊤ := by
    change ((filtration k).boundaries (-1)).comap _ = ⊤
    rw [h, Submodule.comap_top]
  change Subsingleton (_ ⧸ _)
  rw [h']
  infer_instance

lemma pageEquiv_representative (r : ℕ) (x : V k) :
    pageEquiv k r (classMap k r x) =
      Finsupp.restrictDom k k {i : ℕ+ | r ≤ (i:ℕ)} x := by
  rfl

lemma page_spanned (r : ℕ) : Submodule.span k
    ((fun i : ℕ+ => classMap k r (Finsupp.single i 1)) '' {i | r ≤ (i:ℕ)}) = ⊤ := by
  apply top_unique
  intro y _
  have hle : tail k r ≤ (Submodule.span k
      ((fun i : ℕ+ => classMap k r (Finsupp.single i 1)) '' {i | r ≤ (i:ℕ)})).comap
        (classMap k r) := by
    rw [tail, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  have hclass : classMap k r (pageEquiv k r y).1 = y := by
    apply (pageEquiv k r).injective
    rw [pageEquiv_representative]
    exact LinearMap.congr_fun (Finsupp.restrictDom_comp_subtype _) (pageEquiv k r y)
  rw [← hclass]
  exact hle (pageEquiv k r y).2


/-- Convert categorical subobjects and their cokernel quotient to the
ordinary submodule quotient. This uses the actual inclusion map. -/
def subobjectEquiv {M : ModuleCat.{u} k} (Z : Subobject M) :
    (Z : ModuleCat k) ≃ₗ[k] ModuleCat.subobjectModule M Z :=
  LinearEquiv.ofInjective Z.arrow.hom ((ModuleCat.mono_iff_injective _).mp inferInstance)

lemma inclusion_range_map {M : ModuleCat.{u} k} (Z B : Subobject M) (h : B ≤ Z) :
    (LinearMap.range (Subobject.ofLE B Z h).hom).map (subobjectEquiv k Z).toLinearMap =
      (ModuleCat.subobjectModule M B).comap (ModuleCat.subobjectModule M Z).subtype := by
  ext x
  constructor
  · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
    refine ⟨b, ?_⟩
    exact (congrArg (fun f : (B : ModuleCat k) ⟶ M => f.hom b)
      (Subobject.ofLE_arrow h)).symm
  · rintro ⟨b, hb⟩
    refine ⟨(Subobject.ofLE B Z h).hom b, ⟨b, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun f : (B : ModuleCat k) ⟶ M => f.hom b)
      (Subobject.ofLE_arrow h)).trans hb

def subobjectQuotientEquiv {M : ModuleCat.{u} k} (Z B : Subobject M) (h : B ≤ Z) :
    (cokernel (Subobject.ofLE B Z h) : ModuleCat k) ≃ₗ[k]
      (ModuleCat.subobjectModule M Z ⧸
        (ModuleCat.subobjectModule M B).comap (ModuleCat.subobjectModule M Z).subtype) :=
  (ModuleCat.cokernelIsoRangeQuotient (Subobject.ofLE B Z h)).toLinearEquiv ≪≫ₗ
    Submodule.Quotient.equiv _ _ (subobjectEquiv k Z) (inclusion_range_map k Z B h)

/-- The concrete page quotient agrees with every choice of the upstream
spectral sequence structure, whose underlying page objects are fixed. -/
def categoricalPageEquiv (S : (filtration k).SpectralSequence) (r : ℕ) :
    (S.page r 0 (-1)) ≃ₗ[k] page k r := by
  let F := filtration k
  let M := (F.cochainFiltration.graded 0).X 1
  let Z := FilteredPage.cycles F.cochainFiltration (r:ℤ) 0 1
  let B := FilteredPage.boundaries F.cochainFiltration (r:ℤ) 0 1
  let g : F.graded 0 (-1) ≃ₗ[k] M := (S.gradedIso 0 1).toLinearEquiv
  have hz : (F.pageCycles r 0 (-1)).map g.toLinearMap = ModuleCat.subobjectModule M Z := by
    exact S.cycles_formula r 0 1
  have hb : (F.pageBoundaries r 0 (-1)).map g.toLinearMap = ModuleCat.subobjectModule M B := by
    exact S.boundaries_formula r 0 1
  let e : F.pageCycles r 0 (-1) ≃ₗ[k] ModuleCat.subobjectModule M Z :=
    g.ofSubmodules _ _ hz
  have hden :
      (((F.pageBoundaries r 0 (-1)).comap (F.pageCycles r 0 (-1)).subtype).map e.toLinearMap) =
        (ModuleCat.subobjectModule M B).comap (ModuleCat.subobjectModule M Z).subtype := by
    ext x
    rw [Submodule.mem_map_equiv]
    change (e.symm x).1 ∈ F.pageBoundaries r 0 (-1) ↔ x.1 ∈ ModuleCat.subobjectModule M B
    rw [← hb, Submodule.mem_map_equiv]
    change (e.symm x).1 ∈ F.pageBoundaries r 0 (-1) ↔ g.symm x.1 ∈ F.pageBoundaries r 0 (-1)
    rw [LinearEquiv.ofSubmodules_symm_apply]
  let q : page k r ≃ₗ[k]
      (ModuleCat.subobjectModule M Z ⧸
        (ModuleCat.subobjectModule M B).comap (ModuleCat.subobjectModule M Z).subtype) :=
    Submodule.Quotient.equiv _ _ e hden
  exact (subobjectQuotientEquiv k Z B (S.pages.containment (r:ℤ) 0 1)) ≪≫ₗ q.symm

theorem nonstabilizing_boundary_example : Specs.FullStatement.{u} := by
  intro k _
  refine ⟨acyclic k, boundedBelow k, exhaustive k, ?_, page_nontrivial k,
    boundaries_strict k, ?_, boundary_union k, infinity_zero k, homology_zero k,
    exhaustive_chain_pages (filtration k), ?_⟩
  · intro r _
    exact ⟨⟨pageEquiv k r, pageEquiv_representative k r, page_spanned k r⟩⟩
  · intro r
    rw [cycles_eq_top, limitCycles_top]
  · intro S r
    exact ⟨categoricalPageEquiv k S r⟩

end AdvancedHomologicalAlgebra.NonstabilizingBoundary
