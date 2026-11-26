import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.AffineAcyclicity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.OrderedCechComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteChartPresentations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.ProjectiveTwistChartModules
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.ProjectiveSpaces
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules

universe u

noncomputable section

namespace LinearAlgebraicGroups.ProjectiveFiniteness

open Specs.OrderedCechComparison

section FiniteCover

open private res res_res app_res exists_gluing₂ restrict_surjective_of_injective comp_app_zero abSheaf
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.AffineAcyclicity

variable {X : Scheme.{u}} (C : CochainComplex X.Modules ℕ)

/-- Exactness of the section complex at the positive degree `q + 1`. -/
private def SectionsExactAt (U : X.Opens) (q : ℕ) : Prop :=
  ∀ s : Γ(C.X (q + 1), U), (C.d (q + 1) (q + 2)).app U s = 0 →
    ∃ t : Γ(C.X q, U), (C.d q (q + 1)).app U t = s

private theorem sectionsSubsingleton_bot (M : X.Modules) :
    Subsingleton Γ(M, (⊥ : X.Opens)) := by
  let h := (abSheaf M).isTerminalOfEmpty
  have hz := (isZero_zero Ab).of_iso (h.uniqueUpToIso (isZero_zero Ab).isTerminal)
  have hm := hz.eq_of_src (𝟙 _) 0
  refine ⟨fun x y => ?_⟩
  exact (ConcreteCategory.congr_hom hm x).trans (ConcreteCategory.congr_hom hm y).symm

private theorem sectionsExactAt_bot (q : ℕ) : SectionsExactAt C ⊥ q := by
  intro s _
  exact ⟨0, (sectionsSubsingleton_bot (C.X (q + 1))).elim _ _⟩

private theorem sectionsExactAt_sup {U V : X.Opens} {q : ℕ}
    [∀ n, Injective (C.X n)] (hU : SectionsExactAt C U (q + 1))
    (hV : SectionsExactAt C V (q + 1)) (hUV : SectionsExactAt C (U ⊓ V) q) :
    SectionsExactAt C (U ⊔ V) (q + 1) := by
  intro s hs
  obtain ⟨a, ha⟩ := hU (res (C.X (q + 2)) le_sup_left s) (by rw [app_res, hs, map_zero])
  obtain ⟨b, hb⟩ := hV (res (C.X (q + 2)) le_sup_right s) (by rw [app_res, hs, map_zero])
  let c := res (C.X (q + 1)) inf_le_left a - res (C.X (q + 1)) inf_le_right b
  have hc : (C.d (q + 1) (q + 2)).app (U ⊓ V) c = 0 := by
    dsimp only [c]
    rw [map_sub, app_res, app_res, ha, hb, res_res, res_res, sub_self]
  obtain ⟨d, hd⟩ := hUV c hc
  obtain ⟨d', hd'⟩ := restrict_surjective_of_injective (C.X q) inf_le_left d
  let a' := a - (C.d q (q + 1)).app U d'
  have hglue : res (C.X (q + 1)) inf_le_left a' = res (C.X (q + 1)) inf_le_right b := by
    dsimp only [a']
    rw [map_sub, ← app_res, hd', hd]
    dsimp only [c]
    abel
  obtain ⟨t, hta, htb⟩ := exists_gluing₂ (C.X (q + 1)) le_sup_left le_sup_right le_rfl a' b hglue
  refine ⟨t, (abSheaf (C.X (q + 2))).eq_of_locally_eq₂
    (homOfLE le_sup_left) (homOfLE le_sup_right) le_rfl _ _ ?_ ?_⟩
  · change res (C.X (q + 2)) le_sup_left ((C.d (q + 1) (q + 2)).app (U ⊔ V) t) =
        res (C.X (q + 2)) le_sup_left s
    rw [← app_res, hta]
    dsimp only [a']
    rw [map_sub, ha, comp_app_zero (C.d_comp_d q (q + 1) (q + 2)), sub_zero]
  · change res (C.X (q + 2)) le_sup_right ((C.d (q + 1) (q + 2)).app (U ⊔ V) t) =
        res (C.X (q + 2)) le_sup_right s
    rw [← app_res, htb, hb]

private theorem sectionsExactAt_finset_sup {ι : Type*} (P : X.Opens → Prop)
    (hP : ∀ U V, P U → P V → P (U ⊓ V)) [∀ n, Injective (C.X n)]
    (hC : ∀ U, P U → ∀ q, SectionsExactAt C U q)
    (s : Finset ι) (U : ι → X.Opens) (hU : ∀ i ∈ s, P (U i))
    (q : ℕ) (hq : s.card ≤ q + 1) :
    SectionsExactAt C (s.sup U) q := by
  classical
  induction s using Finset.induction_on generalizing U q with
  | empty => simpa using sectionsExactAt_bot C q
  | @insert j s hj ih =>
    rw [Finset.card_insert_of_notMem hj] at hq
    rw [Finset.sup_insert]
    have h₁ : P (U j) := hU j (Finset.mem_insert_self _ _)
    have h₂ : ∀ i ∈ s, P (U i) := fun i hi => hU i (Finset.mem_insert_of_mem hi)
    cases q with
    | zero =>
      have hs : s = ∅ := Finset.card_eq_zero.mp (by omega)
      simpa [hs] using hC (U j) h₁ 0
    | succ q =>
      apply sectionsExactAt_sup C (hC (U j) h₁ _) (ih U h₂ _ (by omega))
      rw [Finset.sup_inf_distrib_left]
      exact ih _ (fun i hi => hP _ _ h₁ (h₂ i hi)) q (by omega)

private theorem resolutionSectionsExactAt_affine {F : X.Modules} [F.IsQuasicoherent]
    (I : InjectiveResolution F) {U : X.Opens} (hU : IsAffineOpen U) (q : ℕ) :
    SectionsExactAt I.cocomplex U q := by
  let E := openEvaluation U
  let K := (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have h := LinearAlgebraicGroups.Cohomology.isZero_rightDerived_evaluation_of_isAffineOpen
    hU F (q + 1) (Nat.succ_pos q)
  have hz : IsZero (K.homology (q + 1)) :=
    h.of_iso (I.isoRightDerivedObj E (q + 1)).symm
  have hex : K.ExactAt (q + 1) := (K.exactAt_iff_isZero_homology _).mpr hz
  have hex' := (K.exactAt_iff' q (q + 1) (q + 2) (by simp) (by
    simp only [CochainComplex.next]
    rfl)).mp hex
  exact (ShortComplex.moduleCat_exact_iff _).mp hex'

/-- A finite affine cover of a separated scheme bounds the degrees of nonzero
quasi-coherent cohomology. -/
theorem isZero_cohomology_of_affine_cover {k : Type u} [CommRing k]
    (Y : SchemeOverRing k) [Y.left.IsSeparated] {ι : Type*} [Fintype ι]
    (U : ι → Y.left.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (F : Y.left.Modules) [F.IsQuasicoherent] (q : ℕ) (hq : Fintype.card ι ≤ q + 1) :
    IsZero ((cohomology Y (q + 1)).obj F) := by
  classical
  let I := injectiveResolution F
  have (n : ℕ) : Injective (I.cocomplex.X n) := I.injective n
  have htop : (Finset.univ : Finset ι).sup U = ⊤ := by
    rw [← hcover]
    exact le_antisymm (Finset.sup_le fun i _ => le_iSup U i)
      (iSup_le fun i => Finset.le_sup (Finset.mem_univ i))
  have hex := sectionsExactAt_finset_sup I.cocomplex IsAffineOpen
    (fun _ _ hV hW => hV.inf hW) (fun V hV n => resolutionSectionsExactAt_affine I hV n)
    Finset.univ U (fun i _ => hU i) q (by simpa using hq)
  rw [htop] at hex
  let K := ((sectionsFunctor Y).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hk : K.ExactAt (q + 1) := by
    apply (K.exactAt_iff' q (q + 1) (q + 2) (by simp) (by
      simp only [CochainComplex.next]
      rfl)).mpr
    exact (ShortComplex.moduleCat_exact_iff _).mpr hex
  exact hk.isZero_homology.of_iso (I.isoRightDerivedObj (sectionsFunctor Y) (q + 1))

/-- Every derived global section module is zero on an empty scheme. -/
theorem isZero_cohomology_of_isEmpty {k : Type u} [CommRing k]
    (Y : SchemeOverRing k) [IsEmpty Y.left] (F : Y.left.Modules) (n : ℕ) :
    IsZero ((cohomology Y n).obj F) := by
  have htop : (⊤ : Y.left.Opens) = ⊥ := Subsingleton.elim _ _
  let I := injectiveResolution F
  let K := ((sectionsFunctor Y).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hK : IsZero (K.X n) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    change Subsingleton Γ(I.cocomplex.X n, (⊤ : Y.left.Opens))
    rw [htop]
    exact sectionsSubsingleton_bot _
  have hex : K.ExactAt n := (K.sc n).exact_of_isZero_X₂ hK
  exact hex.isZero_homology.of_iso (I.isoRightDerivedObj (sectionsFunctor Y) n)

end FiniteCover

section ClosedPushforward

open private res locally_surjective_of_epi from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.AffineAcyclicity

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward of module sheaves along a closed embedding preserves epimorphisms. -/
theorem pushforward_preservesEpimorphisms_of_isClosedEmbedding {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f) :
    (pushforward f).PreservesEpimorphisms where
  preserves {M N} α hα := by
    let T := SheafOfModules.toSheaf.{u} Y.ringCatSheaf
    have hlift := (TopCat.Presheaf.isLocallySurjective_iff α.mapPresheaf).mp
      (locally_surjective_of_epi α)
    apply T.epi_of_epi_map
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    change Γ(N, f ⁻¹ᵁ U) at t
    by_cases hn : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hn
      obtain ⟨V, hV, ⟨s, hs⟩, hx⟩ := hlift (f ⁻¹ᵁ U) t x hy
      obtain ⟨B, hB, hpre⟩ := hf.isEmbedding.isInducing.isOpen_iff.mp V.2
      let W : Y.Opens := ⟨B, hB⟩ ⊓ U
      have hpre' : f ⁻¹ᵁ (⟨B, hB⟩ : Y.Opens) = V := by
        ext x
        change f x ∈ B ↔ x ∈ V
        exact Set.ext_iff.mp hpre x
      have hw : f ⁻¹ᵁ W = V := by
        rw [Scheme.Hom.preimage_inf, hpre', inf_eq_left.mpr hV]
      have hxW : f x ∈ W := by
        change x ∈ f ⁻¹ᵁ W
        rwa [hw]
      refine ⟨W, inf_le_right, ?_, hxW⟩
      have hs' : ∃ s : Γ(M, f ⁻¹ᵁ W), α.app (f ⁻¹ᵁ W) s =
          res N (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ U from fun _ hx => hx.2) t := by
        exact (show ∀ (V' : X.Opens) (hle : V' ≤ f ⁻¹ᵁ U), V' = V →
          ∃ s : Γ(M, V'), α.app V' s = res N hle t from
            fun V' hle he => by subst V'; exact ⟨s, hs⟩) _ _ hw
      exact hs'
    · let W : Y.Opens := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩ ⊓ U
      have hw : f ⁻¹ᵁ W = ⊥ := by
        apply le_antisymm _ bot_le
        exact fun x hx => False.elim (hx.1 ⟨x, rfl⟩)
      refine ⟨W, inf_le_right, ⟨0, ?_⟩, hn, hy⟩
      have hzero : Subsingleton Γ(N, f ⁻¹ᵁ W) := by
        rw [hw]
        exact sectionsSubsingleton_bot N
      exact hzero.elim _ _

/-- Closed pushforward is exact in the abelian categories of module sheaves. -/
theorem pushforward_preservesHomology_of_isClosedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] : (pushforward f).PreservesHomology := by
  have := pushforward_preservesEpimorphisms_of_isClosedEmbedding f f.isClosedEmbedding
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

end ClosedPushforward

section Flasque

open private abSheaf restrict_surjective_of_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Cohomology.AffineAcyclicity

open HomologicalComplex

private theorem flasque_of_iso {X : TopCat.{u}} {F G : TopCat.Sheaf Ab X}
    (e : F ≅ G) [F.IsFlasque] : G.IsFlasque where
  epi {U V} i := by
    have he := e.hom.hom.naturality i
    have : IsIso (e.hom.hom.app V) := by
      change IsIso (((sheafToPresheaf _ _).mapIso e).hom.app V)
      infer_instance
    have h : Epi (e.hom.hom.app U ≫ G.obj.map i) := by
      rw [← he]
      infer_instance
    exact epi_of_epi (e.hom.hom.app U) (G.obj.map i)

private theorem injective_isFlasque {X : Scheme.{u}} (F : X.Modules) [Injective F] :
    (abSheaf F).IsFlasque where
  epi {_U _V} i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (restrict_surjective_of_injective F (leOfHom i.unop))

private theorem shortExact_cycles {D : Type*} [Category D] [Abelian D]
    (K : CochainComplex D ℕ) (n : ℕ) (hex : K.ExactAt (n + 1)) :
    (ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1))
      (by rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, toCycles_i, iCycles_d, zero_comp])).ShortExact := by
  let T := ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1))
    (by rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, toCycles_i, iCycles_d, zero_comp])
  have he : T.Exact := by
    apply T.exact_of_f_is_kernel
    let hk := K.cyclesIsKernel (i := n) (j := n + 1) (CochainComplex.next ℕ n)
    exact isKernelOfComp _ _ hk T.zero (K.toCycles_i _ _)
  have hi : (ComplexShape.up ℕ).prev (n + 1) = n := by simp
  have hj : (ComplexShape.up ℕ).next (n + 1) = n + 2 := CochainComplex.next ℕ (n + 1)
  have hp : Epi (K.sc' n (n + 1) (n + 2)).toCycles :=
    (ShortComplex.exact_iff_epi_toCycles _).mp ((K.exactAt_iff' n (n + 1) (n + 2) hi hj).mp hex)
  let e := K.cyclesIsoSc' n (n + 1) (n + 2) hi hj
  have hg : Epi T.g := by
    have he : T.g = (K.sc' n (n + 1) (n + 2)).toCycles ≫ e.inv := by
      rw [← K.toCycles_cyclesIsoSc'_hom n (n + 1) (n + 2) hi hj, Category.assoc]
      simp [e, T]
    rw [he]
    infer_instance
  exact ShortComplex.ShortExact.mk he

set_option backward.isDefEq.respectTransparency false in
private theorem flasque_cycles {X : Scheme.{u}} (K : CochainComplex X.Modules ℕ) (n : ℕ)
    (hK : ∀ j, K.ExactAt (j + 1)) (hF : ∀ j, (abSheaf (K.X j)).IsFlasque)
    (h0 : (abSheaf (K.cycles 0)).IsFlasque) :
    (abSheaf (K.cycles n)).IsFlasque := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    let A := SheafOfModules.toSheaf.{u} X.ringCatSheaf
    have Azero : A.PreservesZeroMorphisms :=
      inferInstanceAs ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).PreservesZeroMorphisms)
    have Alimits : PreservesFiniteLimits A :=
      inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
    have Acolimits : PreservesFiniteColimits A :=
      inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf))
    let S := ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1))
      (by rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, toCycles_i, iCycles_d, zero_comp])
    have h₁ : TopCat.Sheaf.IsFlasque (X := _) (C := Ab) (S.map A).X₁ := ih
    have h₂ : TopCat.Sheaf.IsFlasque (X := _) (C := Ab) (S.map A).X₂ := hF n
    exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
      ((shortExact_cycles K n (hK n)).map_of_exact A)

set_option backward.isDefEq.respectTransparency false in
/-- Positive derived global sections vanish on flasque coefficients. -/
theorem isZero_cohomology_of_isFlasque {k : Type u} [CommRing k]
    (Y : SchemeOverRing k) (F : Y.left.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.left.ringCatSheaf).obj F)] (q : ℕ) :
    IsZero ((cohomology Y (q + 1)).obj F) := by
  let I := injectiveResolution F
  let K := I.cocomplex
  let A := SheafOfModules.toSheaf.{u} Y.left.ringCatSheaf
  have Azero : A.PreservesZeroMorphisms :=
    inferInstanceAs ((SheafOfModules.toSheaf.{u} Y.left.ringCatSheaf).PreservesZeroMorphisms)
  have Alimits : PreservesFiniteLimits A :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} Y.left.ringCatSheaf))
  have Acolimits : PreservesFiniteColimits A :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} Y.left.ringCatSheaf))
  have hK (n : ℕ) : K.ExactAt (n + 1) :=
    (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (CochainComplex.next ℕ (n + 1))).mpr
      (I.exact_succ n)
  let e₀ : F ≅ K.cycles 0 :=
    I.isLimitKernelFork.conePointUniqueUpToIso (K.cyclesIsKernel 0 1 (CochainComplex.next ℕ 0))
  have hF (n : ℕ) : (abSheaf (K.X n)).IsFlasque :=
    have := I.injective n
    injective_isFlasque _
  have h₀ : (abSheaf (K.cycles 0)).IsFlasque := flasque_of_iso (A.mapIso e₀)
  let S := ShortComplex.mk (K.iCycles q) (K.toCycles q (q + 1))
    (by rw [← cancel_mono (K.iCycles (q + 1)), Category.assoc, toCycles_i, iCycles_d, zero_comp])
  have h₁ : TopCat.Sheaf.IsFlasque (X := _) (C := Ab) (S.map A).X₁ := flasque_cycles K q hK hF h₀
  let T := ShortComplex.mk (K.iCycles (q + 1)) (K.d (q + 1) (q + 2)) (K.iCycles_d _ _)
  have hT : T.Exact := T.exact_of_f_is_kernel (K.cyclesIsKernel (q + 1) (q + 2) (CochainComplex.next ℕ (q + 1)))
  let G := ((sectionsFunctor Y).mapHomologicalComplex (.up ℕ)).obj K
  have hG : G.ExactAt (q + 1) := by
    apply (G.exactAt_iff' q (q + 1) (q + 2) (by simp) (CochainComplex.next ℕ (q + 1))).mpr
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro s hs
    have hm : Mono (A.map T.f) := by
      change Mono ((SheafOfModules.toSheaf.{u} Y.left.ringCatSheaf).map (K.iCycles (q + 1)))
      have hm' : Mono (K.iCycles (q + 1)) :=
        mono_of_isLimit_fork (K.cyclesIsKernel (q + 1) (q + 2) (CochainComplex.next ℕ (q + 1)))
      exact Functor.map_mono _ _
    obtain ⟨z, hz⟩ := TopCat.Sheaf.sections_exact_of_left_exact
      (hT.map A) hm (U := ⊤) s hs
    have he : Epi ((A.map (K.toCycles q (q + 1))).hom.app (op ⊤)) :=
      TopCat.Sheaf.IsFlasque.epi_of_shortExact ((shortExact_cycles K q (hK q)).map_of_exact A)
    obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).mp he z
    refine ⟨t, ?_⟩
    change (K.d q (q + 1)).app ⊤ t = s
    change (K.toCycles q (q + 1)).app ⊤ t = z at ht
    change (K.iCycles (q + 1)).app ⊤ z = s at hz
    rw [← K.toCycles_i, Hom.comp_app, ConcreteCategory.comp_apply, ht, hz]
  exact hG.isZero_homology.of_iso (I.isoRightDerivedObj (sectionsFunctor Y) (q + 1))

/-- Closed pushforward of an injective module sheaf is flasque, as is its
pushforward along any scheme morphism. -/
theorem isFlasque_pushforward_of_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) [Injective F] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) := by
  have := injective_isFlasque F
  exact TopCat.Sheaf.IsFlasque.pushforward_isFlasque (abSheaf F) f.base

end Flasque

section LocallyFree

private def freeSingletonIso {C : Type u} [Category* C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    SheafOfModules.free (R := R) (PUnit.{u + 1}) ≅ SheafOfModules.unit R where
  hom := Sigma.desc (fun _ : PUnit.{u + 1} => 𝟙 (SheafOfModules.unit R))
  inv := SheafOfModules.ιFree PUnit.unit
  hom_inv_id := by
    apply Sigma.hom_ext
    intro j
    cases j
    simp [SheafOfModules.ιFree, SheafOfModules.free]
  inv_hom_id := by simp [SheafOfModules.ιFree, SheafOfModules.free]

set_option backward.isDefEq.respectTransparency false in
private def generatorsOfFreeIso {C : Type u} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {F : SheafOfModules R}
    (e : SheafOfModules.free (PUnit.{u + 1}) ≅ F) : F.GeneratingSections where
  I := PUnit.{u + 1}
  s := F.freeHomEquiv e.hom
  epi := by rw [Equiv.symm_apply_apply]; infer_instance

private theorem generatorsOfFreeIso_isIso {C : Type u} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {F : SheafOfModules R}
    (e : SheafOfModules.free (PUnit.{u + 1}) ≅ F) : IsIso (generatorsOfFreeIso e).π := by
  change IsIso (F.freeHomEquiv.symm (F.freeHomEquiv e.hom))
  rw [Equiv.symm_apply_apply]
  infer_instance

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency false in
/-- A sheaf that is locally isomorphic to the structure sheaf is finitely presented. -/
theorem isFinitePresentation_of_local_rank_one {X : Scheme.{u}} (F : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, SheafOfModules.unit (X.ringCatSheaf.over (U j)) ≅ F.over (U j)) :
    F.IsFinitePresentation := by
  let e' (j : ι) :
      SheafOfModules.free (R := X.ringCatSheaf.over (U j)) (PUnit.{u + 1}) ≅ F.over (U j) :=
    freeSingletonIso (X.ringCatSheaf.over (U j)) ≪≫ e j
  let gen (j : ι) : (F.over (U j)).GeneratingSections := generatorsOfFreeIso (e' j)
  have hgen (j : ι) : IsIso (gen j).π := generatorsOfFreeIso_isIso (e' j)
  let q : F.LocalGeneratorsData :=
    { I := ι
      X := U
      coversTop := (Opens.coversTop_iff _ U).mpr hU
      generators := gen }
  have : q.IsLocallyFreeData :=
    SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.mk (q := q) hgen
  refine { exists_quasicoherentData := ?_ }
  refine ⟨q.quasiCoherentData, ?_⟩
  exact SheafOfModules.QuasicoherentData.IsFinitePresentation.mk
    (q := q.quasiCoherentData) fun j => by
      constructor
      · exact ⟨(show Finite PUnit.{u + 1} by infer_instance)⟩
      · exact ⟨(show Finite (ULift.{u} Empty) by infer_instance)⟩



set_option backward.isDefEq.respectTransparency false in
/-- Finite presentation from rank-one trivializations on the actual open subschemes. -/
theorem isFinitePresentation_of_local_rank_one_restrict {X : Scheme.{u}} (F : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, SheafOfModules.unit (U j).toScheme.ringCatSheaf ≅ F.restrict (U j).ι) :
    F.IsFinitePresentation := by
  apply isFinitePresentation_of_local_rank_one F U hU
  intro j
  let E := (Scheme.Modules.overEquiv (U j)).functor
  exact E.preimageIso ((U j).sheafOfModulesEquivOverUnit X.ringCatSheaf ≪≫
    e j ≪≫ ((Scheme.Modules.overFunctorEquiv (U j)).app F).symm)

end LocallyFree

section ProjectiveCover

attribute [local instance] MvPolynomial.gradedAlgebra

open Specs.ProjectiveSpaces (projectiveSpace coordinateOpen coordinate_mem_degree_one grading)

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    {X : SchemeOverRing k}

/-- The pullbacks of the standard affine charts give the projective bound
on the cohomology of a closed subscheme. -/
theorem isZero_cohomology_above_projective_bound
    (i : X ⟶ projectiveSpace k W) [IsClosedImmersion i.left]
    (F : X.left.Modules) [F.IsQuasicoherent]
    (q : ℕ) (hq : Module.finrank k W ≤ q + 1) :
    IsZero ((cohomology X (q + 1)).obj F) := by
  let P := projectiveSpace k W
  let I := ULift.{u} (Fin (Module.finrank k W))
  let U : I → P.left.Opens := coordinateOpen k I
  have hU : ∀ j : I, IsAffineOpen (U j) := fun j =>
    Proj.isAffineOpen_basicOpen (grading k I) (MvPolynomial.X j)
      (coordinate_mem_degree_one k I j) Nat.one_pos
  have hP : IsProper P.hom :=
    LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper k W
  have hX : IsProper X.hom := by
    rw [← i.w]
    infer_instance
  have : X.left.IsSeparated := ⟨by
    rw [← terminal.comp_from X.hom]
    infer_instance⟩
  apply isZero_cohomology_of_affine_cover X (fun j => i.left ⁻¹ᵁ U j)
    (fun j => (hU j).preimage i.left)
    (i.left.iSup_preimage_eq_top
      (LinearAlgebraicGroups.ProjectiveSpaces.coordinateOpenCover k I)) F q
  simpa [I] using hq

/-- With no homogeneous coordinates the closed subscheme is empty. -/
theorem isEmpty_of_projective_finrank_zero (i : X ⟶ projectiveSpace k W)
    (h : Module.finrank k W = 0) : IsEmpty X.left := by
  let I := ULift.{u} (Fin (Module.finrank k W))
  let U : I → (projectiveSpace k W).left.Opens := coordinateOpen k I
  have : IsEmpty I := by
    dsimp [I]
    rw [h]
    infer_instance
  have hu := LinearAlgebraicGroups.ProjectiveSpaces.coordinateOpenCover k I
  have hb : (⊤ : (projectiveSpace k W).left.Opens) = ⊥ :=
    hu.symm.trans (iSup_of_empty U)
  refine ⟨fun x => ?_⟩
  have hx : i.left x ∈ (⊤ : (projectiveSpace k W).left.Opens) := by simp
  rw [hb] at hx
  exact hx

/-- The finiteness conclusion for projective space on the zero vector space. -/
theorem finiteDimensional_cohomology_of_projective_finrank_zero
    (i : X ⟶ projectiveSpace k W) (h : Module.finrank k W = 0)
    (F : X.left.Modules) (n : ℕ) : FiniteDimensional k ((cohomology X n).obj F) := by
  have := isEmpty_of_projective_finrank_zero i h
  have := ModuleCat.isZero_iff_subsingleton.mp (isZero_cohomology_of_isEmpty X F n)
  exact Module.Finite.of_surjective (0 : k →ₗ[k] (cohomology X n).obj F)
    (fun x => ⟨0, Subsingleton.elim _ x⟩)

end ProjectiveCover

open scoped BigOperators Simplicial

section MonomialComplex

variable {ι K : Type*} [LinearOrder ι] [CommRing K]

/-- Sign of deletion of a coordinate from the increasing enumeration of a finite set. -/
def deletionSign (s : Finset ι) (j : ι) : K :=
  (-1 : K) ^ (s.filter (· < j)).card

private theorem deletionSign_self_mul (s : Finset ι) (j : ι) :
    (deletionSign s j : K) * deletionSign s j = 1 := by
  unfold deletionSign
  rw [← mul_pow]
  simp

private theorem deletionSign_insert_of_not_lt (s : Finset ι) {i j : ι} (h : ¬ i < j) :
    (deletionSign (insert i s) j : K) = deletionSign s j := by
  simp [deletionSign, Finset.filter_insert, h]

private theorem deletionSign_insert_of_lt (s : Finset ι) {i j : ι}
    (hi : i ∉ s) (h : i < j) :
    (deletionSign (insert i s) j : K) = -deletionSign s j := by
  rw [deletionSign, Finset.filter_insert, ite_eq_left h, Finset.card_insert_of_notMem
    (fun hm => hi (Finset.mem_filter.mp hm).1), pow_succ, mul_neg, mul_one, deletionSign]

/-- Alternating deletion on families indexed by finite sets. On families
supported in one cardinality, it raises the cardinality by one. -/
def deletionDifferential (z : Finset ι → K) (s : Finset ι) : K :=
  ∑ j ∈ s, deletionSign s j * z (s.erase j)

/-- Insert the pivot in the argument of a cochain, with the sign of its position. -/
def insertionHomotopy (p : ι) (z : Finset ι → K) (s : Finset ι) : K :=
  if p ∈ s then 0 else deletionSign s p * z (insert p s)

private theorem deletionSign_cancel (s : Finset ι) {p j : ι}
    (hp : p ∉ s) (hj : j ∈ s) :
    (deletionSign s j : K) * deletionSign (s.erase j) p =
      -(deletionSign s p * deletionSign (insert p s) j) := by
  have hne : p ≠ j := fun h => hp (h ▸ hj)
  rcases lt_or_gt_of_ne hne with hpj | hjp
  · rw [deletionSign_insert_of_lt s hp hpj]
    conv_lhs =>
      rhs
      rw [← deletionSign_insert_of_not_lt (s.erase j) (not_lt_of_ge hpj.le),
        Finset.insert_erase hj]
    rw [mul_neg, neg_neg, mul_comm]
  · rw [deletionSign_insert_of_not_lt s (not_lt_of_ge hjp.le)]
    have he : (deletionSign s p : K) = -deletionSign (s.erase j) p := by
      rw [← deletionSign_insert_of_lt (s.erase j) (Finset.notMem_erase j s) hjp,
        Finset.insert_erase hj]
    rw [he, neg_mul, neg_neg, mul_comm]

/-- The signed insertion of a fixed coordinate contracts the augmented
alternating deletion complex. -/
theorem deletionDifferential_insertionHomotopy (p : ι) (z : Finset ι → K)
    (s : Finset ι) :
    deletionDifferential (insertionHomotopy p z) s +
      insertionHomotopy p (deletionDifferential z) s = z s := by
  by_cases hp : p ∈ s
  · rw [insertionHomotopy, ite_eq_left hp, add_zero, deletionDifferential]
    rw [Finset.sum_eq_single p]
    · rw [insertionHomotopy, ite_eq_right (Finset.notMem_erase _ _), Finset.insert_erase hp]
      have he : (deletionSign (s.erase p) p : K) = deletionSign s p := by
        rw [← deletionSign_insert_of_not_lt (s.erase p) (lt_irrefl p), Finset.insert_erase hp]
      rw [he, ← mul_assoc, deletionSign_self_mul, one_mul]
    · intro j _ hne
      rw [insertionHomotopy, ite_eq_left (Finset.mem_erase.mpr ⟨Ne.symm hne, hp⟩), mul_zero]
    · exact fun h => (h hp).elim
  · rw [insertionHomotopy, ite_eq_right hp, deletionDifferential, deletionDifferential,
      Finset.sum_insert hp, mul_add, ← mul_assoc, ← deletionSign_insert_of_not_lt s (lt_irrefl p)
        (K := K), deletionSign_self_mul, Finset.erase_insert hp]
    simp only [one_mul]
    rw [Finset.mul_sum, ← add_assoc, add_comm _ (z s), add_assoc]
    suffices h : (∑ j ∈ s, deletionSign s j * insertionHomotopy p z (s.erase j)) =
        -(∑ j ∈ s, deletionSign (insert p s) p * (deletionSign (insert p s) j *
          z ((insert p s).erase j))) by rw [h, neg_add_cancel, add_zero]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hne : j ≠ p := fun h => hp (h ▸ hj)
    rw [insertionHomotopy, ite_eq_right (fun h => hp (Finset.mem_of_mem_erase h)),
      Finset.erase_insert_of_ne hne.symm, ← mul_assoc, ← mul_assoc,
      deletionSign_insert_of_not_lt s (lt_irrefl p), deletionSign_cancel s hp hj, neg_mul]

/-- The insertion homotopy stays in the summand whose allowed finite sets
contain the prescribed negative support, provided the pivot is outside it. -/
theorem insertionHomotopy_eq_zero_of_not_subset (p : ι) (z : Finset ι → K)
    (t s : Finset ι) (hp : p ∉ t)
    (hz : ∀ a, ¬ t ⊆ a → z a = 0) (hs : ¬ t ⊆ s) :
    insertionHomotopy p z s = 0 := by
  by_cases hp' : p ∈ s
  · simp [insertionHomotopy, hp']
  · rw [insertionHomotopy, ite_eq_right hp', hz (insert p s), mul_zero]
    intro h
    apply hs
    intro x hx
    rcases Finset.mem_insert.mp (h hx) with rfl | hxs
    · exact (hp hx).elim
    · exact hxs

/-- The only possible nonzero entries in the primitive are one cardinality below
the cochain, since inserting a missing pivot increases cardinality. -/
theorem insertionHomotopy_eq_zero_of_card (p : ι) (z : Finset ι → K)
    (n : ℕ) (hz : ∀ a, a.card ≠ n + 1 → z a = 0)
    (s : Finset ι) (hs : s.card ≠ n) :
    insertionHomotopy p z s = 0 := by
  by_cases hp : p ∈ s
  · simp [insertionHomotopy, hp]
  · rw [insertionHomotopy, ite_eq_right hp, hz (insert p s), mul_zero]
    simpa [Finset.card_insert_of_notMem hp] using hs

section FinitelySupportedFamilies

variable {A : Type*} [Fintype ι]

/-- Restrict the insertion homotopy for a coefficient to its chosen pivot.
A missing pivot leaves that coefficient unchanged in the projected complex. -/
noncomputable def finiteSupportInsertion (pivot : A → Option ι)
    (z : Finset ι → A →₀ K) (s : Finset ι) : A →₀ K := by
  classical
  exact ∑ p : ι, if p ∈ s then 0 else
    (deletionSign s p : K) • (z (insert p s)).filter (fun a => pivot a = some p)

theorem finiteSupportInsertion_apply (pivot : A → Option ι)
    (z : Finset ι → A →₀ K) (s : Finset ι) (a : A) :
    finiteSupportInsertion pivot z s a =
      match pivot a with
      | none => 0
      | some p => insertionHomotopy p (fun t => z t a) s := by
  classical
  rw [finiteSupportInsertion, Finsupp.finsetSum_apply]
  cases ha : pivot a with
  | none =>
    apply Finset.sum_eq_zero
    intro p _
    by_cases hs : p ∈ s <;> simp [hs, ha]
  | some p =>
    rw [Finset.sum_eq_single p]
    · by_cases hs : p ∈ s <;> simp [insertionHomotopy, hs, ha]
    · intro j _ hj
      by_cases hs : j ∈ s <;> simp [hs, ha, Ne.symm hj]
    · simp

/-- A cochain with finite monomial support can be reduced to its coefficients
with no chosen pivot, using a primitive of finite monomial support. -/
theorem exists_primitive_off_exceptional_exponents (ν : A → Finset ι) (E : A → Prop)
    (hE : ∀ a, ¬ E a → ∃ p, p ∉ ν a) (z : Finset ι → A →₀ K) (n : ℕ)
    (hz : ∀ s a, s.card ≠ n + 1 ∨ ¬ ν a ⊆ s → z s a = 0)
    (hclosed : ∀ s a, deletionDifferential (fun t => z t a) s = 0) :
    ∃ w : Finset ι → A →₀ K,
      (∀ s a, s.card ≠ n ∨ ¬ ν a ⊆ s → w s a = 0) ∧
      (∀ s a, ¬ E a → deletionDifferential (fun t => w t a) s = z s a) ∧
      (∀ s a, E a → w s a = 0) := by
  classical
  let pivot (a : A) : Option ι := if he : E a then none else some (hE a he).choose
  refine ⟨finiteSupportInsertion pivot z, ?_, ?_, ?_⟩
  · intro s a hs
    rw [finiteSupportInsertion_apply]
    by_cases ha : E a
    · simp [pivot, ha]
    · simp only [pivot, dite_eq_right ha]
      rcases hs with hcard | hsubset
      · apply insertionHomotopy_eq_zero_of_card _ _ n
          (fun t ht => hz t a (Or.inl ht)) _ hcard
      · exact insertionHomotopy_eq_zero_of_not_subset _ _ _ _
          (hE a ha).choose_spec (fun t ht => hz t a (Or.inr ht)) hsubset
  · intro s a ha
    have hw (t : Finset ι) : finiteSupportInsertion pivot z t a =
        insertionHomotopy (hE a ha).choose (fun b => z b a) t := by
      simp [finiteSupportInsertion_apply, pivot, ha]
    simp only [hw]
    have hh := deletionDifferential_insertionHomotopy (hE a ha).choose (fun t => z t a) s
    have hz' : insertionHomotopy (hE a ha).choose
        (deletionDifferential fun t => z t a) s = 0 := by
      simp [insertionHomotopy, hclosed]
    rwa [hz', add_zero] at hh
  · intro s a ha
    simp [finiteSupportInsertion_apply, pivot, ha]

end FinitelySupportedFamilies

end MonomialComplex

/-- At fixed total degree, there are finitely many nonnegative exponent
vectors in finitely many coordinates. -/
theorem finite_nonnegative_exponents {ι : Type*} [Fintype ι] (d : ℤ) :
    Finite {a : ι → ℤ // (∑ j, a j) = d ∧ ∀ j, 0 ≤ a j} := by
  classical
  let : Fintype (Set.Icc (0 : ℤ) d) := (Set.finite_Icc _ _).fintype
  let bound (a : {a : ι → ℤ // (∑ j, a j) = d ∧ ∀ j, 0 ≤ a j}) (j : ι) :
      Set.Icc (0 : ℤ) d :=
    ⟨a.1 j, a.2.2 j, (Finset.single_le_sum (fun i _ => a.2.2 i) (Finset.mem_univ j)).trans a.2.1.le⟩
  exact Finite.of_injective bound (fun a b h =>
    Subtype.ext (funext fun i => congrArg Subtype.val (congrFun h i)))

/-- At fixed total degree, there are finitely many exponent vectors
which are strictly negative in every coordinate. -/
theorem finite_negative_exponents {ι : Type*} [Fintype ι] (d : ℤ) :
    Finite {a : ι → ℤ // (∑ j, a j) = d ∧ ∀ j, a j < 0} := by
  classical
  have := finite_nonnegative_exponents (ι := ι) (-d)
  let negate (a : {a : ι → ℤ // (∑ j, a j) = d ∧ ∀ j, a j < 0}) :
      {a : ι → ℤ // (∑ j, a j) = -d ∧ ∀ j, 0 ≤ a j} :=
    ⟨fun j => -a.1 j, by rw [Finset.sum_neg_distrib, a.2.1], fun j => neg_nonneg.mpr (a.2.2 j).le⟩
  exact Finite.of_injective negate (fun a b h => Subtype.ext (funext fun i =>
    neg_injective (congrFun (congrArg Subtype.val h) i)))

section FixedDegree

variable {ι K : Type*} [LinearOrder ι] [Fintype ι] [CommRing K]

/-- Integer exponents of Laurent monomials with one fixed total degree. -/
abbrev Exponents (ι : Type*) [Fintype ι] (d : ℤ) := {a : ι → ℤ // (∑ j, a j) = d}

/-- The coordinates that must be inverted to make a monomial available. -/
def negativeSupport {d : ℤ} (a : Exponents ι d) : Finset ι :=
  Finset.univ.filter (fun j => a.1 j < 0)

/-- Exponents with empty or full negative support. -/
def uniformSign {d : ℤ} (a : Exponents ι d) : Prop :=
  (∀ j, 0 ≤ a.1 j) ∨ (∀ j, a.1 j < 0)

omit [LinearOrder ι] in
theorem finite_uniformSign_exponents (d : ℤ) :
    Finite {a : Exponents ι d // uniformSign a} := by
  classical
  have := finite_nonnegative_exponents (ι := ι) d
  have := finite_negative_exponents (ι := ι) d
  let classify (a : {a : Exponents ι d // uniformSign a}) :
      {a : ι → ℤ // (∑ j, a j) = d ∧ ∀ j, 0 ≤ a j} ⊕
        {a : ι → ℤ // (∑ j, a j) = d ∧ ∀ j, a j < 0} :=
    if h : ∀ j, 0 ≤ a.1.1 j
    then .inl ⟨a.1.1, a.1.2, h⟩
    else .inr ⟨a.1.1, a.1.2, a.2.resolve_left h⟩
  let forgetSign : ( {a : ι → ℤ // (∑ j, a j) = d ∧ ∀ j, 0 ≤ a j} ⊕
        {a : ι → ℤ // (∑ j, a j) = d ∧ ∀ j, a j < 0}) → (ι → ℤ) :=
    Sum.elim Subtype.val Subtype.val
  have hforget (a : {a : Exponents ι d // uniformSign a}) :
      forgetSign (classify a) = a.1.1 := by
    by_cases h : ∀ j, 0 ≤ a.1.1 j <;> simp [forgetSign, classify, h]
  apply Finite.of_injective classify
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  simpa only [hforget] using congrArg forgetSign h

/-- In the alternating Laurent-monomial calculation, any cycle differs from a
boundary by a cochain with finitely many possible exponent vectors. -/
theorem exists_primitive_off_uniformSign (d : ℤ) (n : ℕ)
    (z : Finset ι → Exponents ι d →₀ K)
    (hz : ∀ s a, s.card ≠ n + 1 ∨ ¬ negativeSupport a ⊆ s → z s a = 0)
    (hclosed : ∀ s a, deletionDifferential (fun t => z t a) s = 0) :
    ∃ w : Finset ι → Exponents ι d →₀ K,
      (∀ s a, s.card ≠ n ∨ ¬ negativeSupport a ⊆ s → w s a = 0) ∧
      (∀ s a, ¬ uniformSign a → deletionDifferential (fun t => w t a) s = z s a) ∧
      (∀ s a, uniformSign a → w s a = 0) ∧
      w ∅ = 0 := by
  have hE (a : Exponents ι d) (ha : ¬ uniformSign a) : ∃ p, p ∉ negativeSupport a := by
    have hn : ¬ ∀ j, a.1 j < 0 := fun hn => ha (Or.inr hn)
    push Not at hn
    obtain ⟨j, hj⟩ := hn
    exact ⟨j, by simp [negativeSupport, not_lt_of_ge hj]⟩
  obtain ⟨w, hcard, hd, hzero⟩ :=
    exists_primitive_off_exceptional_exponents negativeSupport uniformSign hE z n hz hclosed
  refine ⟨w, hcard, hd, hzero, Finsupp.ext fun a => ?_⟩
  by_cases ha : uniformSign a
  · exact hzero ∅ a ha
  · apply hcard ∅ a
    apply Or.inr
    have hn : ¬ ∀ j, 0 ≤ a.1 j := fun hn => ha (Or.inl hn)
    push Not at hn
    obtain ⟨j, hj⟩ := hn
    intro hs
    simpa using hs (show j ∈ negativeSupport a by simp [negativeSupport, hj])

end FixedDegree

open HomologicalComplex

section MonomialCech

variable {ι k : Type u} [LinearOrder ι] [Field k]

private def tupleFinset {r : ℕ} (e : Fin r ↪o ι) : Finset ι :=
  Finset.univ.map e.toEmbedding

@[simp]
private theorem card_tupleFinset {r : ℕ} (e : Fin r ↪o ι) : (tupleFinset e).card = r := by
  simp [tupleFinset]

private theorem tupleFinset_orderEmbOfFin (s : Finset ι) {r : ℕ} (hs : s.card = r) :
    tupleFinset (s.orderEmbOfFin hs) = s :=
  s.map_orderEmbOfFin_univ hs

private theorem orderEmbOfFin_tupleFinset {r : ℕ} (e : Fin r ↪o ι) :
    (tupleFinset e).orderEmbOfFin (card_tupleFinset e) = e :=
  (Finset.orderEmbOfFin_unique' _ (fun j => Finset.mem_map.mpr ⟨j, by simp, rfl⟩)).symm

private theorem tupleFinset_delete {r : ℕ} (e : Fin (r + 1) ↪o ι) (j : Fin (r + 1)) :
    tupleFinset (j.succAboveOrderEmb.trans e) = (tupleFinset e).erase (e j) := by
  classical
  ext a
  simp only [tupleFinset, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨fun h => j.succAbove_ne i (e.injective h), ⟨j.succAbove i, rfl⟩⟩
  · rintro ⟨hne, i, rfl⟩
    obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq (x := i) (y := j) (ne_of_apply_ne e hne)
    exact ⟨a, rfl⟩

private theorem card_tupleFinset_lt {r : ℕ} (e : Fin r ↪o ι) (j : Fin r) :
    ((tupleFinset e).filter (· < e j)).card = j.val := by
  rw [tupleFinset, Finset.filter_map, Finset.card_map, ← Fin.card_Iio j]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Function.comp_apply]
  exact e.lt_iff_lt

private abbrev singletonCoordinates (i : ι) : (Set ι)ᵒᵈ :=
  Specs.ProjectiveTwistChartModules.singletonCoordinates i

private theorem tupleOpen_singleton {n : ℕ} (e : Fin (n + 1) ↪o ι) :
    OrderDual.ofDual (tupleOpen singletonCoordinates e) = (tupleFinset e : Set ι) := by
  ext i
  change i ∈ (⋃ j, ({e j} : Set ι)) ↔ _
  simp [tupleFinset, eq_comm]

end MonomialCech

section MonomialCech

set_option backward.isDefEq.respectTransparency false

variable {ι k : Type u} [LinearOrder ι] [Fintype ι] [Field k]

/-- Degree-d Laurent polynomials whose denominators use only coordinates in S. -/
private abbrev monomials (d : ℤ) (S : Set ι) :=
  Finsupp.supported k k {a : Exponents ι d | (negativeSupport a : Set ι) ⊆ S}

private abbrev monomialPresheaf (d : ℤ) : ((Set ι)ᵒᵈ)ᵒᵖ ⥤ ModuleCat.{u} k :=
  Specs.ProjectiveTwistChartModules.monomialPresheaf k d

private abbrev monomialComplex (d : ℤ) :=
  cechComplex singletonCoordinates (monomialPresheaf (k := k) (ι := ι) d)

private abbrev monomialComponent (d : ℤ) {n : ℕ} (e : Fin (n + 1) ↪o ι) :=
  ↥(monomials (k := k) d (OrderDual.ofDual (tupleOpen singletonCoordinates e)))

private def monomialComponentAt {d : ℤ} {n : ℕ}
    (z : (monomialComplex (k := k) (ι := ι) d).X n) (e : Fin (n + 1) ↪o ι) :
    monomialComponent (k := k) d e := z e

private def extendMonomialCochain {d : ℤ} {n : ℕ}
    (z : (monomialComplex (k := k) (ι := ι) d).X n) (s : Finset ι) : Exponents ι d →₀ k :=
  if hs : s.card = n + 1 then (monomialComponentAt z (s.orderEmbOfFin hs)).val else 0

private theorem extendMonomialCochain_tuple {d : ℤ} {n : ℕ}
    (z : (monomialComplex (k := k) (ι := ι) d).X n) (e : Fin (n + 1) ↪o ι) :
    extendMonomialCochain z (tupleFinset e) = (monomialComponentAt z e).val := by
  rw [extendMonomialCochain, dite_eq_left (card_tupleFinset e), orderEmbOfFin_tupleFinset]

private theorem extendMonomialCochain_support {d : ℤ} {n : ℕ}
    (z : (monomialComplex (k := k) (ι := ι) d).X n) (s : Finset ι) (a : Exponents ι d)
    (h : s.card ≠ n + 1 ∨ ¬ negativeSupport a ⊆ s) :
    extendMonomialCochain z s a = 0 := by
  by_cases hs : s.card = n + 1
  · rw [extendMonomialCochain, dite_eq_left hs]
    apply (Finsupp.mem_supported' k _).mp (monomialComponentAt z (s.orderEmbOfFin hs)).prop
    change ¬ (negativeSupport a : Set ι) ⊆ OrderDual.ofDual (tupleOpen singletonCoordinates _)
    rw [tupleOpen_singleton, tupleFinset_orderEmbOfFin]
    exact h.resolve_left (not_not_intro hs)
  · rw [extendMonomialCochain, dite_eq_right hs, Finsupp.zero_apply]

private def monomialCochainOfFamily {d : ℤ} {n : ℕ}
    (z : Finset ι → Exponents ι d →₀ k)
    (hz : ∀ s a, s.card = n + 1 → ¬ negativeSupport a ⊆ s → z s a = 0) :
    (monomialComplex (k := k) (ι := ι) d).X n := fun e =>
  show monomialComponent (k := k) d e from
    ⟨z (tupleFinset e), (Finsupp.mem_supported' k _).mpr fun a ha => by
      change ¬ (negativeSupport a : Set ι) ⊆ _ at ha
      rw [tupleOpen_singleton] at ha
      exact hz _ _ (card_tupleFinset _) ha⟩

private theorem extendMonomialCochain_ofFamily {d : ℤ} {n : ℕ}
    (z : Finset ι → Exponents ι d →₀ k)
    (hz : ∀ s a, s.card = n + 1 → ¬ negativeSupport a ⊆ s → z s a = 0)
    {s : Finset ι} (hs : s.card = n + 1) :
    extendMonomialCochain (monomialCochainOfFamily z hz) s = z s := by
  simp only [extendMonomialCochain, dite_eq_left hs, monomialComponentAt, monomialCochainOfFamily, tupleFinset_orderEmbOfFin]

set_option backward.isDefEq.respectTransparency false in
private theorem monomialComplex_d_apply {d : ℤ} {n : ℕ}
    (z : (monomialComplex (k := k) (ι := ι) d).X n) (e : Fin (n + 2) ↪o ι)
    (a : Exponents ι d) :
    (monomialComponentAt ((monomialComplex d).d n (n + 1) z) e).val a =
      deletionDifferential (fun t => extendMonomialCochain z t a) (tupleFinset e) := by
  rw [deletionDifferential, tupleFinset, Finset.sum_map]
  rw [show (monomialComplex (k := k) (ι := ι) d).d n (n + 1) =
      differential singletonCoordinates (monomialPresheaf d) n from
    CochainComplex.of_d (fun n => (orderedCochains singletonCoordinates
      (monomialPresheaf d)).obj (SemiSimplexCategory.mk n)) _ n]
  change ((show monomialComponent (k := k) d e from
    (differential singletonCoordinates (monomialPresheaf d) n).hom z e).val) a = _
  unfold differential
  erw [ModuleCat.hom_sum, LinearMap.sum_apply, Finset.sum_apply]
  rw [Submodule.coe_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j _
  erw [ModuleCat.hom_zsmul, LinearMap.smul_apply, Pi.smul_apply]
  change (-1 : ℤ) ^ (j : ℕ) • ((monomialComponentAt z (j.succAboveOrderEmb.trans e)).val a) =
    deletionSign (tupleFinset e) (e j) * extendMonomialCochain z ((tupleFinset e).erase (e j)) a
  rw [deletionSign, card_tupleFinset_lt, ← tupleFinset_delete, extendMonomialCochain_tuple]
  simp [zsmul_eq_mul]

private theorem deletionDifferential_extend_of_cycle {d : ℤ} {n : ℕ}
    (z : (monomialComplex (k := k) (ι := ι) d).X n)
    (hz : (monomialComplex d).d n (n + 1) z = 0)
    (s : Finset ι) (a : Exponents ι d) :
    deletionDifferential (fun t => extendMonomialCochain z t a) s = 0 := by
  classical
  by_cases hs : s.card = n + 2
  · rw [← tupleFinset_orderEmbOfFin s hs, ← monomialComplex_d_apply, hz]
    rfl
  · apply Finset.sum_eq_zero
    intro j hj
    change deletionSign s j * extendMonomialCochain z (s.erase j) a = 0
    rw [extendMonomialCochain_support z _ _ (Or.inl ?_), mul_zero]
    rw [Finset.card_erase_of_mem hj]
    have := Finset.card_pos.mpr (⟨j, hj⟩)
    omega

private abbrev uniformCochains (k : Type u) [Field k] (ι : Type u)
    [LinearOrder ι] [Fintype ι] (d : ℤ) (n : ℕ) :=
  ∀ _ : Fin (n + 1) ↪o ι, Finsupp.supported k k {a : Exponents ι d | uniformSign a}

private theorem noetherian_uniformCochains (d : ℤ) (n : ℕ) :
    IsNoetherian k (uniformCochains k ι d n) := by
  classical
  let _ : Fintype (Fin (n + 1) ↪o ι) := Fintype.ofFinite _
  have : Finite {a : Exponents ι d | uniformSign a} := finite_uniformSign_exponents d
  let _ : Fintype {a : Exponents ι d | uniformSign a} := Fintype.ofFinite _
  have : IsNoetherian k (Finsupp.supported k k {a : Exponents ι d | uniformSign a}) :=
    isNoetherian_of_linearEquiv (Finsupp.supportedEquivFinsupp (R := k)
      (M := k) {a : Exponents ι d | uniformSign a}).symm
  exact @isNoetherian_pi' k (Finsupp.supported k k {a : Exponents ι d | uniformSign a})
    _ _ _ (Fin (n + 1) ↪o ι) (by infer_instance) this

private def uniformCycles {d : ℤ} {n : ℕ} :
    Submodule k ((monomialComplex (k := k) (ι := ι) d).X n) :=
  LinearMap.ker ((monomialComplex d).d n (n + 1)).hom ⊓
    { carrier := {z | ∀ e, (monomialComponentAt z e).val ∈ Finsupp.supported k k {a : Exponents ι d | uniformSign a}}
      zero_mem' := fun _ => Submodule.zero_mem _
      add_mem' := fun h h' e => Submodule.add_mem _ (h e) (h' e)
      smul_mem' := fun c _ h e => Submodule.smul_mem _ c (h e) }

private def uniformCyclesInclusion {d : ℤ} {n : ℕ} :
    (uniformCycles (k := k) (ι := ι) (d := d) (n := n)) →ₗ[k] uniformCochains k ι d n where
  toFun z e := ⟨(monomialComponentAt z.val e).val, (show _ ∧ _ from z.prop).2 e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency true in
private theorem finite_uniformCycles {d : ℤ} {n : ℕ} :
    Module.Finite k (uniformCycles (k := k) (ι := ι) (d := d) (n := n)) := by
  let _ : IsNoetherian k (uniformCochains k ι d n) := noetherian_uniformCochains d n
  apply Module.Finite.of_injective uniformCyclesInclusion
  intro z z' h
  apply Subtype.ext
  funext e
  exact Subtype.ext (congrArg (fun f : uniformCochains k ι d n => (f e).val) h)

private theorem exists_uniform_cycle_representative {d : ℤ} {n : ℕ}
    (z : (monomialComplex (k := k) (ι := ι) d).X n)
    (hz : (monomialComplex d).d n (n + 1) z = 0) :
    ∃ w : (monomialComplex d).X ((ComplexShape.up ℕ).prev n),
      z - (monomialComplex d).d ((ComplexShape.up ℕ).prev n) n w ∈
        uniformCycles (d := d) (n := n) := by
  classical
  obtain ⟨w, hsupport, hprimitive, _, hempty⟩ := exists_primitive_off_uniformSign d n
    (extendMonomialCochain z) (extendMonomialCochain_support z)
    (deletionDifferential_extend_of_cycle z hz)
  cases n with
  | zero =>
    refine ⟨0, ?_⟩
    change _ ∧ _
    constructor
    · change ((monomialComplex d).d 0 1).hom _ = 0
      simpa using hz
    · intro e
      apply (Finsupp.mem_supported' k _).mpr
      intro a ha
      have h := hprimitive (tupleFinset e) a ha
      rw [extendMonomialCochain_tuple, deletionDifferential, Finset.sum_eq_zero] at h
      · simpa using h.symm
      · intro j hj
        have hcard : ((tupleFinset e).erase j).card = 0 := by
          rw [Finset.card_erase_of_mem hj, card_tupleFinset]
        rw [Finset.card_eq_zero.mp hcard, hempty, Finsupp.zero_apply, mul_zero]
  | succ n =>
    rw [CochainComplex.prev_nat_succ]
    have hw (s : Finset ι) (a : Exponents ι d)
        (_ : s.card = n + 1) (ha : ¬ negativeSupport a ⊆ s) : w s a = 0 :=
      hsupport s a (Or.inr ha)
    let w' := monomialCochainOfFamily w hw
    refine ⟨w', ?_⟩
    change _ ∧ _
    constructor
    · change (monomialComplex d).d (n + 1) (n + 2)
        (z - (monomialComplex d).d n (n + 1) w') = 0
      have hd : (monomialComplex d).d (n + 1) (n + 2)
          ((monomialComplex d).d n (n + 1) w') = 0 := by
        change (((monomialComplex d).d n (n + 1) ≫
          (monomialComplex d).d (n + 1) (n + 2)).hom) w' = 0
        rw [HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [map_sub, hz, hd, sub_zero]
    · intro e
      apply (Finsupp.mem_supported' k _).mpr
      intro a ha
      change ((monomialComponentAt z e).val) a - (monomialComponentAt ((monomialComplex d).d n (n + 1) w') e).val a = 0
      rw [monomialComplex_d_apply, sub_eq_zero,
        ← extendMonomialCochain_tuple z e, ← hprimitive (tupleFinset e) a ha]
      apply Finset.sum_congr rfl
      intro j hj
      have hs : ((tupleFinset e).erase j).card = n + 1 := by
        rw [Finset.card_erase_of_mem hj, card_tupleFinset]
        omega
      change _ * w ((tupleFinset e).erase j) a = _ * extendMonomialCochain w' _ a
      rw [extendMonomialCochain_ofFamily w hw hs]

/-- Every degree of the ordered Laurent-monomial complex has finite-dimensional homology. -/
private theorem finite_monomial_homology (d : ℤ) (n : ℕ) :
    Module.Finite k ((monomialComplex (k := k) (ι := ι) d).homology n) := by
  let C := monomialComplex (k := k) (ι := ι) d
  let S := C.sc' ((ComplexShape.up ℕ).prev n) n (n + 1)
  have := finite_uniformCycles (k := k) (ι := ι) (d := d) (n := n)
  let map : (uniformCycles (k := k) (ι := ι) (d := d) (n := n)) →ₗ[k] S.g.hom.ker :=
    Submodule.inclusion (by
      change (_ ⊓ _) ≤ LinearMap.ker (C.d n (n + 1)).hom
      exact inf_le_left)
  have hnext : (ComplexShape.up ℕ).next n = n + 1 := by simp [CochainComplex.next]
  let e : C.homology n ≅ S.homology :=
    (ShortComplex.homologyFunctor _).mapIso (C.isoSc' (i := (ComplexShape.up ℕ).prev n)
      (j := n) (k := n + 1) rfl hnext)
  apply Module.Finite.of_surjective
    (((S.moduleCatHomologyIso.inv ≫ e.inv).hom).comp ((LinearMap.range S.moduleCatToCycles).mkQ.comp map))
  intro y
  obtain ⟨z, hz⟩ := (Submodule.mkQ_surjective (LinearMap.range S.moduleCatToCycles))
    (S.moduleCatHomologyIso.hom (e.hom y))
  obtain ⟨w, hw⟩ := exists_uniform_cycle_representative z.val z.prop
  refine ⟨⟨z.val - S.f w, hw⟩, ?_⟩
  have he : map ⟨z.val - S.f w, hw⟩ = z - S.moduleCatToCycles w := rfl
  change e.inv (S.moduleCatHomologyIso.inv ((LinearMap.range S.moduleCatToCycles).mkQ _)) = y
  have hzero : (LinearMap.range S.moduleCatToCycles).mkQ (S.moduleCatToCycles w) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self S.moduleCatToCycles w)
  rw [he, map_sub, hz, hzero, sub_zero]
  simp
end MonomialCech

section FiniteExact

variable {k : Type u} [Field k]

private theorem finite_middle_of_exact (S : ShortComplex (ModuleCat.{u} k)) (hS : S.Exact)
    [Module.Finite k S.X₁] [Module.Finite k S.X₃] : Module.Finite k S.X₂ := by
  let g := S.g.hom.rangeRestrict
  have hg : Function.Surjective g := by
    rintro ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  apply Module.Finite.of_exact (f := S.f.hom) (g := g) ?_ hg
  apply LinearMap.exact_iff.mpr
  rw [hS.moduleCat_range_eq_ker]
  ext x
  change g x = 0 ↔ S.g.hom x = 0
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

private theorem finite_homology_of_shortExact
    {S : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)} (hS : S.ShortExact)
    (n : ℕ) [Module.Finite k (S.X₂.homology n)]
    [Module.Finite k (S.X₁.homology (n + 1))] : Module.Finite k (S.X₃.homology n) :=
  finite_middle_of_exact _ (hS.homology_exact₃ n (n + 1) rfl)

end FiniteExact


open scoped ModuleCat.Algebra

section AffineLocalization

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (M : X.Modules)

private abbrev restrictRing {V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

private abbrev affineSections {V : X.Opens} (h : V ≤ U) : ModuleCat.{u} Γ(X, U) :=
  (ModuleCat.restrictScalars (restrictRing h)).obj (M.val.obj (op V))

private def affineSectionRestriction {V : X.Opens} (h : V ≤ U) :
    Γ(M, U) →ₗ[Γ(X, U)] affineSections M h where
  toFun := fun x => M.presheaf.map (homOfLE h).op x
  map_add' := fun x y => map_add (M.presheaf.map (homOfLE h).op).hom x y
  map_smul' := fun r x => M.val.map_smul (homOfLE h).op r x

set_option backward.isDefEq.respectTransparency false in
private def fromSpecSectionIso (W : (Spec Γ(X, U)).Opens) {V : X.Opens}
    (e : hU.fromSpec ''ᵁ W = V) (hV : V ≤ U) :
    ((modulesSpecToSheaf.obj (M.restrict hU.fromSpec)).obj.obj (op W)) ≃ₗ[Γ(X, U)]
      affineSections M hV := by
  let R := Γ(X, U)
  let f := hU.fromSpec
  let eM := M.restrictAppIso f W ≪≫ M.presheaf.mapIso (eqToIso e).op.symm
  let hW : W ≤ f ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]; exact le_top
  have hf : f.appLE U W hW = (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map W.leTop.op := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rfl
  have hf' : (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map W.leTop.op ≫
        (f.appIso W).inv ≫ X.presheaf.map (eqToIso e).op.symm.hom =
      X.presheaf.map (homOfLE hV).op := by
    calc
      _ = ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map W.leTop.op) ≫
          (f.appIso W).inv ≫ X.presheaf.map (eqToIso e).op.symm.hom := by rw [Category.assoc]
      _ = _ := by
        rw [← hf, f.appLE_appIso_inv_assoc hW, ← Functor.map_comp]
        congr 1
  let l : ((modulesSpecToSheaf.obj (M.restrict f)).obj.obj (op W)) →ₗ[R] affineSections M hV :=
    { toFun := fun x => eM.hom x
      map_add' := fun x y => map_add eM.hom.hom x y
      map_smul' := by
        intro r x
        let x' : Γ(M.restrict f, W) := x
        change eM.hom (r • x') = restrictRing hV r • eM.hom x'
        let z : Γ(Spec R, W) := (Spec R).presheaf.map W.leTop.op ((Scheme.ΓSpecIso R).inv r)
        have hs : r • x' = z • x' := rfl
        rw [hs]
        change (M.presheaf.map (eqToIso e).op.symm.hom)
          ((M.restrictAppIso f W).hom (z • x')) = _
        rw [smul_restrictAppIso_hom_apply]
        change M.val.map _ (_ • _) = _
        rw [M.val.map_smul]
        exact congrArg (fun t : Γ(X, V) => t • eM.hom x')
          (ConcreteCategory.congr_hom hf' r) }
  exact LinearEquiv.ofBijective l (ConcreteCategory.bijective_of_isIso eM.hom)

set_option backward.isDefEq.respectTransparency false in
private def fromSpecSectionTopIso :
    ((modulesSpecToSheaf.obj (M.restrict hU.fromSpec)).obj.obj (op ⊤)) ≃ₗ[Γ(X, U)] Γ(M, U) := by
  let f := hU.fromSpec
  let e : f ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let l := fromSpecSectionIso hU M ⊤ e (le_refl U)
  have hid : restrictRing (le_refl U) = RingHom.id Γ(X, U) := by
    dsimp only [restrictRing]
    rw [show (homOfLE (le_refl U)).op = 𝟙 _ from Subsingleton.elim _ _, X.presheaf.map_id]
    rfl
  let idIso := ModuleCat.restrictScalarsId'App (f := restrictRing (le_refl U)) hid (M.val.obj (op U))
  exact l.trans idIso.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
include hU in
/-- Restricting a quasi-coherent module from an affine open to a principal
open is localization at the defining section of the structure sheaf. -/
theorem isLocalizedModule_affineSectionRestriction [M.IsQuasicoherent] (r : Γ(X, U)) :
    IsLocalizedModule.Away r (affineSectionRestriction M (X.basicOpen_le r)) := by
  let f := hU.fromSpec
  let R := Γ(X, U)
  let G := M.restrict f
  let D := PrimeSpectrum.basicOpen r
  let h := X.basicOpen_le r
  let e := hU.fromSpec_image_basicOpen r
  let e₁ := fromSpecSectionTopIso hU M
  let e₂ := fromSpecSectionIso hU M D e h
  let p := ((modulesSpecToSheaf.obj G).obj.map D.leTop.op).hom
  have hp : IsLocalizedModule.Away r p :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance r
  have hcomm : affineSectionRestriction M h =
      e₂.toLinearMap.comp (p.comp e₁.symm.toLinearMap) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e₁.surjective x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change affineSectionRestriction M h (e₁ y) = e₂ (p (e₁.symm (e₁ y)))
    rw [LinearEquiv.symm_apply_apply]
    let eTop : f ''ᵁ (⊤ : (Spec R).Opens) = U :=
      (f.image_top_eq_opensRange).trans hU.opensRange_fromSpec
    let a := M.restrictAppIso f ⊤
    let b := M.restrictAppIso f D
    let h₁ := (eqToIso eTop).op.symm.hom
    let h₂ := (eqToIso e).op.symm.hom
    let h₃ := (homOfLE h).op
    let h₄ := (homOfLE (f.image_mono (D.leTop.le))).op
    change M.presheaf.map h₃ (M.presheaf.map h₁ (a.hom y)) =
      M.presheaf.map h₂ (b.hom (G.presheaf.map D.leTop.op y))
    rw [map_restrictAppIso_hom_apply]
    change M.presheaf.map h₃ (M.presheaf.map h₁ (a.hom y)) =
      M.presheaf.map h₂ (M.presheaf.map h₄ (a.hom y))
    have hm : M.presheaf.map h₁ ≫ M.presheaf.map h₃ =
        M.presheaf.map h₄ ≫ M.presheaf.map h₂ := by
      rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
      exact congrArg M.presheaf.map (Subsingleton.elim _ _)
    exact ConcreteCategory.congr_hom hm (a.hom y)
  rw [hcomm]
  let _ : IsLocalizedModule.Away r (p.comp e₁.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers r) p e₁.symm
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem isLocalizedModule_affineSectionRestriction_of_eq_basicOpen {X : Scheme.{u}}
    {U V : X.Opens} (hU : IsAffineOpen U) (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X, U)) (h : V ≤ U) (e : V = X.basicOpen r) :
    IsLocalizedModule.Away r (affineSectionRestriction M h) := by
  subst V
  exact isLocalizedModule_affineSectionRestriction hU M r

set_option backward.isDefEq.respectTransparency false in
/-- On an affine chart followed by a principal restriction, the sections of an
affine pushforward of a quasi-coherent sheaf localize at the ambient element. -/
theorem isLocalizedModule_pushforward_affineSectionRestriction {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules) [M.IsQuasicoherent]
    {U : Y.Opens} (hU : IsAffineOpen U) (r : Γ(Y, U)) :
    IsLocalizedModule.Away r
      (affineSectionRestriction ((pushforward f).obj M) (Y.basicOpen_le r)) := by
  let V := Y.basicOpen r
  let U' := f ⁻¹ᵁ U
  let V' := f ⁻¹ᵁ V
  let N := (pushforward f).obj M
  let R := Γ(Y, U)
  let A := Γ(X, U')
  let r' := f.app U r
  let h : V ≤ U := Y.basicOpen_le r
  let h' : V' ≤ U' := fun _ hx => h hx
  let p := affineSectionRestriction M h'
  let _ : Algebra R A := (f.app U).hom.toAlgebra
  let _ : IsLocalizedModule.Away (algebraMap R A r) p :=
    isLocalizedModule_affineSectionRestriction_of_eq_basicOpen (hU.preimage f) M r' h'
      (Scheme.preimage_basicOpen f r)
  let _ : Module R Γ(M, U') := Module.compHom Γ(M, U') (f.app U).hom
  let _ : IsScalarTower R A Γ(M, U') := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let _ : Module R (affineSections M h') :=
    Module.compHom Γ(M, V') ((f.app V).hom.comp (restrictRing h))
  let _ : IsScalarTower R A (affineSections M h') :=
    IsScalarTower.of_algebraMap_smul fun t x => by
      change (X.presheaf.map (homOfLE h').op (f.app U t)) • x =
        (f.app V (Y.presheaf.map (homOfLE h).op t)) • x
      exact congrArg (fun a : Γ(X, V') => a • x)
        (ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) t).symm
  have he : p.restrictScalars R = affineSectionRestriction N h := by
    apply LinearMap.ext
    intro x
    rfl
  rw [← he]
  exact IsLocalizedModule.restrictScalars_powers r p

end AffineLocalization


section AffineSections

set_option backward.isDefEq.respectTransparency false in
private theorem finite_spec_sections_of_presentation {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (P : M.Presentation) [P.IsFinite] :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M) := by
  let N := (moduleSpecΓFunctor (R := R)).obj M
  let L := ModuleCat.of R (P.generators.I →₀ R)
  have hM : M.IsQuasicoherent := P.isQuasicoherent
  let f := (tilde.functor R).preimage
    ((tildeFinsupp P.generators.I).hom ≫ P.generators.π ≫ inv M.fromTildeΓ)
  have hmap : Epi ((tilde.functor R).map f) := by
    have : Epi P.generators.π := P.generators.epi
    rw [Functor.map_preimage]
    exact epi_comp _ _
  have hf : Epi f := (tilde.functor R).epi_of_epi_map hmap
  have hI : Finite P.generators.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  let _ : Fintype P.generators.I := Fintype.ofFinite _
  exact Module.Finite.of_surjective (f : L ⟶ N).hom ((ModuleCat.epi_iff_surjective f).1 hf)

set_option backward.isDefEq.respectTransparency false in
private theorem presentationRestrict_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (P : M.Presentation) [P.IsFinite] :
    (presentationRestrict f P).IsFinite := by
  exact ⟨⟨(show Finite P.generators.I from SheafOfModules.GeneratingSections.IsFiniteType.finite)⟩,
    ⟨(show Finite P.relations.I from SheafOfModules.GeneratingSections.IsFiniteType.finite)⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finite_restricted_sections_of_presentation {X : Scheme.{u}} (M : X.Modules)
    (P : M.Presentation) [P.IsFinite] {R : CommRingCat.{u}} (f : Spec R ⟶ X)
    [IsOpenImmersion f] :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (M.restrict f)) := by
  let Q := presentationRestrict f P
  have : Q.IsFinite := presentationRestrict_isFinite f M P
  exact finite_spec_sections_of_presentation _ Q

set_option backward.isDefEq.respectTransparency false in
private theorem finite_affine_open_sections_of_fromSpec {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U)
    (hm : Module.Finite Γ(X, U)
      ((moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict hU.fromSpec))) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  let _ : Module.Finite Γ(X, U)
      ((modulesSpecToSheaf.obj (M.restrict hU.fromSpec)).obj.obj (op ⊤)) := hm
  exact Module.Finite.equiv (fromSpecSectionTopIso hU M)

private theorem finite_affine_open_sections_of_presentation {X : Scheme.{u}} (M : X.Modules)
    (P : M.Presentation) [P.IsFinite] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(M, U) :=
  finite_affine_open_sections_of_fromSpec M hU
    (finite_restricted_sections_of_presentation M P hU.fromSpec)

set_option backward.isDefEq.respectTransparency false in
private theorem finite_sections_image_of_isOpenImmersion {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules) (V : Y.Opens)
    (h : Module.Finite Γ(Y, V) Γ(M.restrict f, V)) :
    Module.Finite Γ(X, f ''ᵁ V) Γ(M, f ''ᵁ V) := by
  let E := M.restrictAppIso f V
  let l : Γ(M.restrict f, V) →ₛₗ[(f.appIso V).inv.hom] Γ(M, f ''ᵁ V) :=
    { toFun := E.hom
      map_add' := fun x y => map_add E.hom.hom x y
      map_smul' := fun r x => smul_restrictAppIso_hom_apply f M V r x }
  apply Module.Finite.of_surjective l
  exact (ConcreteCategory.bijective_of_isIso E.hom).2

set_option backward.isDefEq.respectTransparency false in
private theorem finite_spec_sections_of_basic_cover {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (T : Set R) (hT : Ideal.span T = ⊤)
    (hM : ∀ t : T, Module.Finite Γ(Spec R, PrimeSpectrum.basicOpen t.val)
      Γ(M, PrimeSpectrum.basicOpen t.val)) :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M) := by
  let b (t : T) := PrimeSpectrum.basicOpen t.val
  let f (t : T) := ((modulesSpecToSheaf.obj M).obj.map (b t).leTop.op).hom
  have hloc : IsLocalizing (modulesSpecToSheaf.obj M) :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance
  have h (t : T) : IsLocalizedModule.Away t.val (f t) := hloc t.val
  exact Module.Finite.of_localizationSpan' T hT (Mₚ := fun t => Γ(M, b t))
    (Rₚ := fun t => Γ(Spec R, b t)) f hM

set_option backward.isDefEq.respectTransparency false in
private theorem finite_spec_sections_of_cover {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → (Spec R).Opens) (hU : IsOpenCover U)
    (P : ∀ i, (M.restrict (U i).ι).Presentation) (hP : ∀ i, (P i).IsFinite) :
    Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M) := by
  let T : Set R := {r | ∃ i, PrimeSpectrum.basicOpen r ≤ U i}
  have hT : Ideal.span T = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ ⨆ i, U i := by
      rw [hU.iSup_eq_top]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hr, hle⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hi (U i).isOpen
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr ⟨⟨i, hle⟩, hr⟩⟩
  apply finite_spec_sections_of_basic_cover M T hT
  intro t
  obtain ⟨i, hi⟩ := t.prop
  let W : (Spec R).Opens := PrimeSpectrum.basicOpen t.val
  let g : W.toScheme ⟶ (U i).toScheme := (Spec R).homOfLE hi
  let P' := presentationRestrict g (P i)
  have hp := hP i
  have : P'.IsFinite := presentationRestrict_isFinite g _ (P i)
  let e : (M.restrict (U i).ι).restrict g ≅ M.restrict W.ι :=
    ((restrictFunctorComp g (U i).ι).app M).symm ≪≫
      (restrictFunctorCongr (by simp [g])).app M
  let Q := P'.ofIsIso e.hom
  have : Q.IsFinite := inferInstanceAs ((P'.ofIsIso e.hom).IsFinite)
  have hW : IsAffine W.toScheme := IsAffineOpen.Spec_basicOpen t.val
  have hF := finite_affine_open_sections_of_presentation (M.restrict W.ι) Q
    (isAffineOpen_top W.toScheme)
  have h := finite_sections_image_of_isOpenImmersion W.ι M ⊤ hF
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem exists_finitePresentation_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (V : Y.Opens)
    (P : (M.over V).Presentation) [P.IsFinite] :
    ∃ Q : ((M.restrict f).restrict (f ⁻¹ᵁ V).ι).Presentation, Q.IsFinite := by
  let E := (overEquiv V).functor
  let P' := P.map E (V.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm
  have : P'.IsFinite := by
    exact ⟨⟨(show Finite P.generators.I from SheafOfModules.GeneratingSections.IsFiniteType.finite)⟩,
      ⟨(show Finite P.relations.I from SheafOfModules.GeneratingSections.IsFiniteType.finite)⟩⟩
  let P'' := P'.ofIsIso ((overFunctorEquiv V).app M).hom
  have : P''.IsFinite := inferInstanceAs ((P'.ofIsIso ((overFunctorEquiv V).app M).hom).IsFinite)
  let g := f ∣_ V
  let Q := presentationRestrict g P''
  have := presentationRestrict_isFinite g _ P''
  let e : (M.restrict V.ι).restrict g ≅ (M.restrict f).restrict (f ⁻¹ᵁ V).ι :=
    ((restrictFunctorComp g V.ι).app M).symm ≪≫
      (restrictFunctorCongr (morphismRestrict_ι f V)).app M ≪≫
        (restrictFunctorComp (f ⁻¹ᵁ V).ι f).app M
  exact ⟨Q.ofIsIso e.hom, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-- Sections of a finitely presented module sheaf on any affine open are finite
over its structure ring. -/
theorem finite_sections_of_isAffineOpen {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  apply finite_affine_open_sections_of_fromSpec M hU
  let f := hU.fromSpec
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hc : (⨆ i, q.X i) = ⊤ := ((Opens.coversTop_iff _ q.X).mp q.coversTop).iSup_eq_top
  let V := fun i => f ⁻¹ᵁ q.X i
  have hV : IsOpenCover V := f.iSup_preimage_eq_top hc
  choose P hP using fun i => exists_finitePresentation_restrict f M (q.X i) (q.presentation i)
  exact finite_spec_sections_of_cover (M.restrict f) V hV P hP

end AffineSections

section ClosedAffineSections

open LinearAlgebraicGroups.Specs.OrderedCechComparison

private theorem finite_restrictScalars_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (N : ModuleCat.{u} S) [Module.Finite S N] :
    Module.Finite R ((ModuleCat.restrictScalars f).obj N) := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module.Finite R S := RingHom.Finite.of_surjective f hf
  let T := (ModuleCat.restrictScalars f).obj N
  let _ : Module S T := inferInstanceAs (Module S N)
  let _ : Module.Finite S T := inferInstanceAs (Module.Finite S N)
  let _ : IsScalarTower R S T := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Finite.trans S T

set_option backward.isDefEq.respectTransparency false in
/-- On any affine chart of the ambient scheme, sections of the closed
pushforward are finite over the ambient chart ring. -/
theorem finite_closed_pushforward_sections {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) [M.IsFinitePresentation] {U : Y.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(Y, U) Γ((pushforward f).obj M, U) := by
  let V := f ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f
  let _ : Module.Finite Γ(X, V) (M.val.obj (op V)) := finite_sections_of_isAffineOpen M hV
  exact finite_restrictScalars_of_surjective (f.app U).hom (f.app_surjective U hU) (M.val.obj (op V))

open LinearAlgebraicGroups.Specs.ProjectiveSpaces (projectiveSpace)

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
  {X : SchemeOverRing k}

set_option backward.isDefEq.respectTransparency false in
/-- With exactly one homogeneous coordinate, all cohomology modules of a
coherent sheaf on the closed subscheme are finite over the base field. -/
theorem finiteDimensional_cohomology_of_projective_finrank_one
    (i : X ⟶ projectiveSpace k W) [IsClosedImmersion i.left] (h : Module.finrank k W = 1)
    (F : X.left.Modules) [F.IsFinitePresentation] (n : ℕ) :
    FiniteDimensional k ((cohomology X n).obj F) := by
  cases n with
  | zero =>
    have : IsIso (projectiveSpace k W).hom :=
      (LinearAlgebraicGroups.ProjectiveSpaces.oneDimensionalProjectiveSpace k W h).2
    have : IsClosedImmersion X.hom := by
      rw [← i.w]
      infer_instance
    obtain ⟨hX, hΓ⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (f := X.hom)
    have hsurj : Function.Surjective (groundRingHom X) :=
      hΓ.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
    let _ : Module.Finite Γ(X.left, ⊤) (F.val.obj (op ⊤)) :=
      finite_sections_of_isAffineOpen F (isAffineOpen_top X.left)
    have : Module.Finite k ((sectionsFunctor X).obj F) :=
      finite_restrictScalars_of_surjective _ hsurj (F.val.obj (op ⊤))
    exact Module.Finite.of_surjective ((cohomologyZero X).app F).inv.hom
      (ConcreteCategory.bijective_of_isIso _).2
  | succ n =>
    have hz := isZero_cohomology_above_projective_bound i F n (by omega)
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Module.Finite.of_surjective (0 : k →ₗ[k] (cohomology X (n + 1)).obj F)
      (fun x => ⟨0, Subsingleton.elim _ x⟩)

end ClosedAffineSections



open Specs.ProjectiveSpaces (coordinateProjectiveSpace projectiveSpace coordinateOpen
  coordinate_mem_degree_one grading)

attribute [local instance] MvPolynomial.gradedAlgebra

section ProjectiveNoetherian

open LinearAlgebraicGroups.Specs.ProjectiveSpaces (projectiveSpace)

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]

/-- A closed subscheme of finite-dimensional projective space over a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_projectiveEmbedding
    {X : SchemeOverRing k} (i : X ⟶ projectiveSpace k W) [IsClosedImmersion i.left] :
    IsLocallyNoetherian X.left := by
  let P := projectiveSpace k W
  have : IsProper P.hom := LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper k W
  have : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
  exact LocallyOfFiniteType.isLocallyNoetherian i.left

end ProjectiveNoetherian


section FiniteResolution

variable {k : Type u} [Field k]

private theorem finite_homology_finite_product
    {J : Type} [Finite J] (C : J → CochainComplex (ModuleCat.{u} k) ℕ) (n : ℕ)
    (h : ∀ j, Module.Finite k ((C j).homology n)) :
    Module.Finite k ((∏ᶜ C).homology n) := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  let H := homologyFunctor (ModuleCat.{u} k) (.up ℕ) n
  let e := PreservesProduct.iso H C ≪≫ ModuleCat.piIsoPi (fun j => H.obj (C j))
  let _ (j : J) : Module.Finite k (H.obj (C j)) := h j
  have hf : Module.Finite k (∀ j, H.obj (C j)) := inferInstance
  exact Module.Finite.of_surjective e.inv.hom (ConcreteCategory.bijective_of_isIso e.inv).2

/-- Dimension shifting for a collection of cochain complexes with a common
cohomological bound and finite-homology presentations. -/
private theorem finite_homology_of_resolution_steps
    (P : CochainComplex (ModuleCat.{u} k) ℕ → Prop) (bound : ℕ)
    (cutoff : ∀ C, P C → ∀ n, bound ≤ n → IsZero (C.homology n))
    (resolve : ∀ C, P C → ∃ S : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ),
      S.X₃ = C ∧ S.ShortExact ∧ P S.X₁ ∧ ∀ n, Module.Finite k (S.X₂.homology n))
    (C : CochainComplex (ModuleCat.{u} k) ℕ) (hC : P C) (n : ℕ) :
    Module.Finite k (C.homology n) := by
  suffices h : ∀ t C, P C → ∀ i, bound ≤ i + t → Module.Finite k (C.homology i) from
    h bound C hC n (by omega)
  intro t
  induction t with
  | zero =>
    intro C hC n hn
    have h := ModuleCat.isZero_iff_subsingleton.mp (cutoff C hC n (by omega))
    exact Module.Finite.of_surjective (0 : k →ₗ[k] C.homology n)
      (fun x => ⟨0, Subsingleton.elim _ x⟩)
  | succ t ih =>
    intro C hC n hn
    obtain ⟨S, rfl, hS, hker, hmid⟩ := resolve C hC
    have := ih S.X₁ hker (n + 1) (by omega)
    have := hmid n
    exact finite_homology_of_shortExact hS n

end FiniteResolution

section ProjectiveComparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    {X : SchemeOverRing k}

private abbrev standardCover (i : X ⟶ projectiveSpace k W) :
    ULift.{u} (Fin (Module.finrank k W)) → X.left.Opens :=
  pullbackCover i.left (coordinateOpen k (ULift.{u} (Fin (Module.finrank k W))))

private theorem standardCover_covers (i : X ⟶ projectiveSpace k W) :
    (⨆ j, standardCover i j) = ⊤ :=
  i.left.iSup_preimage_eq_top
    (LinearAlgebraicGroups.ProjectiveSpaces.coordinateOpenCover k _)

private theorem standardCover_isAffine (i : X ⟶ projectiveSpace k W) [IsClosedImmersion i.left]
    (j : ULift.{u} (Fin (Module.finrank k W))) : IsAffineOpen (standardCover i j) :=
  (Proj.isAffineOpen_basicOpen (grading k _) (MvPolynomial.X j)
    (coordinate_mem_degree_one k _ j) Nat.one_pos).preimage i.left

/-- The standard ordered cover of a projectively embedded scheme computes the
actual cohomology of each quasi-coherent module sheaf over the base field. -/
private def cohomologyIso_standardCover (i : X ⟶ projectiveSpace k W) [IsClosedImmersion i.left]
    (F : X.left.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (cohomology X n).obj F ≅ (SheafCech (standardCover i) F).homology n := by
  let P := projectiveSpace k W
  have : IsProper P.hom := LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper k W
  have : IsProper X.hom := by
    rw [← i.w]
    infer_instance
  have : X.left.IsSeparated := ⟨by rw [← terminal.comp_from X.hom]; infer_instance⟩
  refine LinearAlgebraicGroups.OrderedCechComparison.orderedCechComparisonIso X (standardCover i)
    (standardCover_covers i) F ?_ n
  intro p e q hq
  apply LinearAlgebraicGroups.Cohomology.isZero_rightDerived_evaluation_of_isAffineOpen _ F q hq
  exact IsAffineOpen.iInf fun j => standardCover_isAffine i (e j)

end ProjectiveComparison


open CategoryTheory.Preadditive

section CechChangeOfIndex

variable {k ι : Type u} [Field k] [Preorder ι]
    {D : Type v} {E : Type w} [CompleteLattice D] [CompleteLattice E]
    (U : ι → D) (V : ι → E) (F : D ⥤ E) (P : Eᵒᵖ ⥤ ModuleCat.{u} k)
    (h : ∀ (n : ℕ) (e : Fin (n + 1) ↪o ι), F.obj (tupleOpen U e) = tupleOpen V e)

private def tupleComponentHom {n : ℕ} (e : Fin (n + 1) ↪o ι) :
    P.obj (op (F.obj (tupleOpen U e))) ⟶ P.obj (op (tupleOpen V e)) :=
  P.map (eqToHom (h n e).symm).op

set_option backward.isDefEq.respectTransparency false in
private def orderedCochainsChangeOfIndex :
    orderedCochains U (F.op ⋙ P) ⟶ orderedCochains V P where
  app n := ModuleCat.ofHom <| LinearMap.pi fun e =>
    (tupleComponentHom U V F P h e).hom ∘ₗ LinearMap.proj e
  naturality := by
    intro n m i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext e
    let e' := (SemiSimplexCategory.homEquiv i).trans e
    let j : tupleOpen U e ⟶ tupleOpen U e' := homOfLE (tupleOpen_le U e _)
    let j' : tupleOpen V e ⟶ tupleOpen V e' := homOfLE (tupleOpen_le V e _)
    let m₁ := tupleComponentHom U V F P h e
    let m₂ := P.map (F.map j).op
    let m₃ := tupleComponentHom U V F P h e'
    let m₄ := P.map j'.op
    change m₁ (m₂ (x e')) = m₄ (m₃ (x e'))
    have he : m₂ ≫ m₁ = m₃ ≫ m₄ := by
      simp only [m₁, m₂, m₃, m₄, tupleComponentHom, ← Functor.map_comp]
      exact congrArg P.map (Subsingleton.elim _ _)
    exact ConcreteCategory.congr_hom he (x e')

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing the intersections along a functor that identifies all the
tuple opens gives the same ordered Čech complex. -/
private def cechComplexChangeOfIndexIso :
    cechComplex U (F.op ⋙ P) ≅ cechComplex V P := by
  let α := orderedCochainsChangeOfIndex U V F P h
  let β : cechComplex U (F.op ⋙ P) ⟶ cechComplex V P :=
    CochainComplex.ofHom (fun n => α.app ⦋n⦌ₛ) fun n => by
      simp only [cechComplex, CochainComplex.of_d, differential, comp_sum, sum_comp,
        comp_zsmul, zsmul_comp]
      exact Finset.sum_congr rfl fun i _ => congrArg ((-1 : ℤ) ^ (i : ℕ) • ·)
        (α.naturality (coface i)).symm
  have hβ (n : ℕ) : IsIso (β.f n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hbij (e : Fin (n + 1) ↪o ι) : Function.Bijective (tupleComponentHom U V F P h e) := by
      unfold tupleComponentHom
      exact ConcreteCategory.bijective_of_isIso _
    constructor
    · intro x y he
      funext e
      exact (hbij e).1 (congrFun he e)
    · intro y
      choose x hx using fun e => (hbij e).2 (y e)
      exact ⟨x, funext hx⟩
  let _ : IsIso β := @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ β hβ
  exact asIso β

end CechChangeOfIndex

section CechCutoff

private theorem isZero_orderedCech_homology_of_card_le {k ι : Type u} [Field k]
    [LinearOrder ι] [Fintype ι] {D : Type v} [CompleteLattice D]
    (U : ι → D) (P : Dᵒᵖ ⥤ ModuleCat.{u} k) (n : ℕ) (hn : Fintype.card ι ≤ n) :
    IsZero ((cechComplex U P).homology n) := by
  let K := cechComplex U P
  let _ : IsEmpty (Fin (n + 1) ↪o ι) :=
    ⟨fun e => by
      have hc := Fintype.card_le_of_injective e e.injective
      simp only [Fintype.card_fin] at hc
      omega⟩
  have : Subsingleton (K.X n) := by
    change Subsingleton (term U P n)
    infer_instance
  have hex : K.ExactAt n :=
    (K.sc n).exact_of_isZero_X₂ (ModuleCat.isZero_iff_subsingleton.mpr this)
  exact hex.isZero_homology

end CechCutoff

section Coordinates

variable {k ι : Type u} [Field k] [LinearOrder ι] [Fintype ι]

private abbrev coordinateIntersections : (Set ι)ᵒᵈ ⥤ (coordinateProjectiveSpace k ι).left.Opens where
  obj s := Specs.ProjectiveTwistChartModules.chartOpen k (OrderDual.ofDual s).toFinite.toFinset
  map h := homOfLE (Specs.ProjectiveTwistChartModules.chartOpen_anti (by simpa using h.le))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private theorem coordinateIntersections_tupleOpen {n : ℕ} (e : Fin (n + 1) ↪o ι) :
    (coordinateIntersections (k := k) (ι := ι)).obj (tupleOpen singletonCoordinates e) =
      tupleOpen (coordinateOpen k ι) e := by
  change Specs.ProjectiveTwistChartModules.chartOpen k (OrderDual.ofDual
    (tupleOpen singletonCoordinates e)).toFinite.toFinset = _
  rw [tupleOpen_singleton]
  have h : ((tupleFinset e : Set ι)).toFinite.toFinset = tupleFinset e := by
    ext a
    simp
  rw [h, Specs.ProjectiveTwistChartModules.chartOpen_eq_inf, tupleFinset, Finset.inf_map, Finset.inf_univ_eq_iInf]
  rfl

end Coordinates

section ProjectiveCoefficientDiagram

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    {X : SchemeOverRing k}

private def projectiveCoefficientDiagram (i : X ⟶ projectiveSpace k W) (F : X.left.Modules) :
    ((Set (ULift.{u} (Fin (Module.finrank k W))))ᵒᵈ)ᵒᵖ ⥤ ModuleCat.{u} k :=
  ((coordinateIntersections (k := k)) ⋙ Opens.map i.left.base).op ⋙ coefficientPresheaf F

private def projectiveCoefficientCechIso (i : X ⟶ projectiveSpace k W) (F : X.left.Modules) :
    cechComplex singletonCoordinates (projectiveCoefficientDiagram i F) ≅
      SheafCech (standardCover i) F :=
  cechComplexChangeOfIndexIso _ _ _ _ fun _ e => by
    change i.left ⁻¹ᵁ (coordinateIntersections (k := k)).obj (tupleOpen singletonCoordinates e) = _
    rw [coordinateIntersections_tupleOpen]
    exact (tupleOpen_pullback _ _ e).symm

/-- The coefficient diagram on the finite coordinate subsets computes the
cohomology of the original sheaf with its structural field action. -/
private def cohomologyIso_projectiveCoefficientDiagram
    (i : X ⟶ projectiveSpace k W) [IsClosedImmersion i.left] (F : X.left.Modules)
    [F.IsQuasicoherent] (n : ℕ) :
    (cohomology X n).obj F ≅
      (cechComplex singletonCoordinates (projectiveCoefficientDiagram i F)).homology n :=
  cohomologyIso_standardCover i F n ≪≫
    (homologyFunctor _ _ n).mapIso (projectiveCoefficientCechIso i F).symm

end ProjectiveCoefficientDiagram

section ExactCech

variable {k ι : Type u} [Field k] [Preorder ι]
    {D : Type v} [CompleteLattice D] (U : ι → D)

set_option backward.isDefEq.respectTransparency false in
private def cechFunctor :
    (Dᵒᵖ ⥤ ModuleCat.{u} k) ⥤ CochainComplex (ModuleCat.{u} k) ℕ where
  obj P := cechComplex U P
  map f := cechMap U f
  map_id P := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

set_option backward.isDefEq.respectTransparency false in
private instance : (cechFunctor (k := k) U).Additive where
  map_add := by
    intros
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise short exactness on the nonempty tuple intersections gives a
short exact sequence of ordered cochain complexes. -/
private theorem shortExact_cechFunctor
    (S : ShortComplex (Dᵒᵖ ⥤ ModuleCat.{u} k))
    (h : ∀ (n : ℕ) (e : Fin (n + 1) ↪o ι),
      (S.map ((CategoryTheory.evaluation _ _).obj (op (tupleOpen U e)))).ShortExact) :
    (S.map (cechFunctor U)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let A := (S.map (cechFunctor U)).map (HomologicalComplex.eval _ _ n)
  have hf (x : A.X₁) (e : Fin (n + 1) ↪o ι) :
      A.f x e = S.f.app (op (tupleOpen U e)) (x e) := rfl
  have hg (x : A.X₂) (e : Fin (n + 1) ↪o ι) :
      A.g x e = S.g.app (op (tupleOpen U e)) (x e) := rfl
  change A.ShortExact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.moduleCat_exact_iff A).mpr
    intro x hx
    have hz (e : Fin (n + 1) ↪o ι) : S.g.app (op (tupleOpen U e)) (x e) = 0 := by
      rw [← hg x e, hx]
      rfl
    choose y hy using fun e =>
      (ShortComplex.moduleCat_exact_iff _).mp (h n e).exact (x e) (hz e)
    refine ⟨y, funext fun e => ?_⟩
    exact (hf y e).trans (hy e)
  · apply (ModuleCat.mono_iff_injective A.f).mpr
    intro x y hxy
    funext e
    exact (h n e).moduleCat_injective_f ((hf x e).symm.trans
      ((congrFun hxy e).trans (hf y e)))
  · apply (ModuleCat.epi_iff_surjective A.g).mpr
    intro y
    choose x hx using fun e => (h n e).moduleCat_surjective_g (y e)
    exact ⟨x, funext fun e => (hg x e).trans (hx e)⟩

end ExactCech

section ChartDiagrams

open Specs.ProjectiveFiniteChartPresentations (Chart ChartRings Twists)
open Specs.ProjectiveTwistChartModules
  (ChartGeometry chartOpen chartRings chartGround chartOpen_anti indexOf)
open Specs.ProjectiveSpaces (coordinateProjectiveSpace)

set_option backward.isDefEq.respectTransparency false

variable {k ι : Type u} [Field k] [Fintype ι] [DecidableEq ι]

/-- Equip the actual rings of the intersections with the chart presentation data. -/
private abbrev projectiveChartRings (G : ChartGeometry k ι)
    [IsLocallyNoetherian (coordinateProjectiveSpace k ι).left] : ChartRings k ι where
  rings := chartRings k ι
  scalars :=
    { app S := CommRingCat.ofHom (chartGround k (indexOf S))
      naturality {S T} f := by
        ext r
        exact DFunLike.congr_fun
          (localScalars_comp (X := coordinateProjectiveSpace k ι)
            (homOfLE (chartOpen_anti (Chart.subset f)))) r }
  noetherian i := IsLocallyNoetherian.component_noetherian
    ⟨_, G.affine (indexOf (Chart.single i))⟩
  ratio S i j hj := G.ratio (indexOf S) i j hj
  ratio_self S j hj := G.ratio_self _ j hj
  ratio_mul S i j l hj hl := G.ratio_mul _ i j l hj hl
  ratio_map f i j hj := G.ratio_restrict f i j hj
  localizes S i j hj := G.ring_localization (indexOf S) i j hj

private abbrev projectiveTwists (G : ChartGeometry k ι)
    [IsLocallyNoetherian (coordinateProjectiveSpace k ι).left] : Twists (projectiveChartRings G) where
  diagram d := (ProjectiveTwistChartModules.twistDiagram G d).modules
  basis d S i hi :=
    (ProjectiveTwistChartModules.twistDiagram G d).basis
      (indexOf S) i hi
  basis_map d {S T} f i hi := by
    let L := ProjectiveTwistChartModules.twistDiagram G d
    change L.modules.map f (L.basis (indexOf S) i hi 1) =
      L.basis (indexOf T) i (Chart.subset f hi) 1
    apply (L.coefficients (indexOf T)).injective
    apply Subtype.ext
    rw [L.restrict_coeff, L.basis_coeff, L.basis_coeff]
    simp only [map_one]
  basis_transition d S i j hi hj :=
    (ProjectiveTwistChartModules.twistDiagram G d).basis_transition
      (indexOf S) i j hi hj
  localizes d S i j hj :=
    (ProjectiveTwistChartModules.twistDiagram G d).localized
      (indexOf S) i j hj

/-- Restrict a module sheaf to the diagram of its sections on chart intersections. -/
private def sheafChartModules (G : ChartGeometry k ι)
    [IsLocallyNoetherian (coordinateProjectiveSpace k ι).left]
    (M : (coordinateProjectiveSpace k ι).left.Modules) : (projectiveChartRings G).Modules where
  obj S := M.val.obj (op (chartOpen k (Chart.indices S)))
  map h := M.val.map (homOfLE (chartOpen_anti (Chart.subset h))).op
  map_id _ := M.val.map_id _
  map_comp _ _ := M.val.map_comp _ _

private theorem finite_sheafChartModules_pushforward (G : ChartGeometry k ι)
    [IsLocallyNoetherian (coordinateProjectiveSpace k ι).left]
    {X : Scheme.{u}} (f : X ⟶ (coordinateProjectiveSpace k ι).left) [IsClosedImmersion f]
    (M : X.Modules) [M.IsFinitePresentation] :
    (projectiveChartRings G).FiniteOnSingletons
      (sheafChartModules G ((pushforward f).obj M)) := fun i =>
  finite_closed_pushforward_sections f M
    (G.affine (indexOf (Chart.single i)))

private theorem localizes_pushforward_on_basicOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules) [M.IsQuasicoherent]
    {U V : Y.Opens} (hU : IsAffineOpen U) (r : Γ(Y, U)) (hle : V ≤ U)
    (hV : V = Y.basicOpen r) :
    IsLocalizedModule.Away r (affineSectionRestriction ((pushforward f).obj M) hle) := by
  subst V
  exact isLocalizedModule_pushforward_affineSectionRestriction f M hU r

private theorem localizes_sheafChartModules_pushforward (G : ChartGeometry k ι)
    [IsLocallyNoetherian (coordinateProjectiveSpace k ι).left]
    {X : Scheme.{u}} (f : X ⟶ (coordinateProjectiveSpace k ι).left) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] :
    (projectiveChartRings G).Localizes (sheafChartModules G ((pushforward f).obj M)) := by
  intro S i j hj
  exact localizes_pushforward_on_basicOpen f M (G.affine (indexOf S))
    (G.ratio (indexOf S) i j hj)
    (chartOpen_anti (Chart.subset (Chart.toAdjoin S i)))
    (G.insert_open (indexOf S) i j hj)

end ChartDiagrams

section ExtendChartDiagrams

open Specs.ProjectiveFiniteChartPresentations (Chart)
open Specs.ProjectiveTwistChartModules (chartSets)
open scoped Classical

variable {k ι : Type u} [Field k] [LinearOrder ι] [Fintype ι]

private abbrev CoordinateSets (ι : Type u) := ((Set ι)ᵒᵈ)ᵒᵖ

private abbrev coordinates (S : CoordinateSets ι) : Set ι := OrderDual.ofDual S.unop

private def nonemptyChart (S : CoordinateSets ι) (h : (coordinates S).Nonempty) : Chart ι :=
  Chart.ofFinset (coordinates S).toFinite.toFinset ((coordinates S).toFinite.toFinset_nonempty.mpr h)

omit [LinearOrder ι] in
private theorem coordinates_nonemptyChart (S : CoordinateSets ι) (h : (coordinates S).Nonempty) :
    (↑(nonemptyChart S h).indices : Set ι) = coordinates S :=
  (coordinates S).toFinite.coe_toFinset

private theorem nonemptyChart_eq (S : CoordinateSets ι) (h : (coordinates S).Nonempty) :
    (chartSets ι).obj (nonemptyChart S h) = S :=
  congrArg (fun s : Set ι => op (OrderDual.toDual s)) (coordinates_nonemptyChart S h)

omit [LinearOrder ι] [Fintype ι] in
private theorem coordinates_subset {S T : CoordinateSets ι} (f : S ⟶ T) :
    coordinates S ⊆ coordinates T := f.unop.le

private def nonemptyChartMap {S T : CoordinateSets ι} (f : S ⟶ T)
    (hs : (coordinates S).Nonempty) (ht : (coordinates T).Nonempty) :
    nonemptyChart S hs ⟶ nonemptyChart T ht :=
  Chart.hom (by
    intro a ha
    have h : a ∈ ((nonemptyChart S hs).indices : Set ι) := ha
    rw [coordinates_nonemptyChart] at h
    change a ∈ ((nonemptyChart T ht).indices : Set ι)
    rw [coordinates_nonemptyChart]
    exact coordinates_subset f h)

private abbrev chartExtensionObj (P : Chart ι ⥤ ModuleCat.{u} k) (S : CoordinateSets ι) :
    ModuleCat.{u} k :=
  ModuleCat.of k (∀ h : PLift (coordinates S).Nonempty, P.obj (nonemptyChart S h.down))

private def chartExtensionLinearMap (P : Chart ι ⥤ ModuleCat.{u} k)
    {S T : CoordinateSets ι} (f : S ⟶ T) (ht : PLift (coordinates T).Nonempty) :
    chartExtensionObj P S →ₗ[k] P.obj (nonemptyChart T ht.down) :=
  if hs : (coordinates S).Nonempty then
    (P.map (nonemptyChartMap f hs ht.down)).hom ∘ₗ LinearMap.proj (PLift.up hs)
  else 0

private def chartExtensionMap (P : Chart ι ⥤ ModuleCat.{u} k)
    {S T : CoordinateSets ι} (f : S ⟶ T) :
    chartExtensionObj P S ⟶ chartExtensionObj P T :=
  ModuleCat.ofHom (LinearMap.pi (chartExtensionLinearMap P f))

private theorem chartExtensionMap_apply_of_nonempty (P : Chart ι ⥤ ModuleCat.{u} k)
    {S T : CoordinateSets ι} (f : S ⟶ T) (hs : (coordinates S).Nonempty)
    (x : chartExtensionObj P S) (ht : PLift (coordinates T).Nonempty) :
    chartExtensionMap P f x ht = P.map (nonemptyChartMap f hs ht.down) (x (PLift.up hs)) := by
  change chartExtensionLinearMap P f ht x = _
  rw [chartExtensionLinearMap, dite_eq_left hs]
  rfl

private theorem chartExtensionMap_apply_of_empty (P : Chart ι ⥤ ModuleCat.{u} k)
    {S T : CoordinateSets ι} (f : S ⟶ T) (hs : ¬(coordinates S).Nonempty)
    (x : chartExtensionObj P S) (ht : PLift (coordinates T).Nonempty) :
    chartExtensionMap P f x ht = 0 := by
  change chartExtensionLinearMap P f ht x = _
  rw [chartExtensionLinearMap, dite_eq_right hs]
  rfl

/-- Extend the chart diagram by zero at the empty coordinate set. -/
private abbrev chartExtension (P : Chart ι ⥤ ModuleCat.{u} k) :
    CoordinateSets ι ⥤ ModuleCat.{u} k where
  obj := chartExtensionObj P
  map := chartExtensionMap P
  map_id S := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hs
    change chartExtensionMap P (𝟙 S) x hs = x hs
    rw [chartExtensionMap_apply_of_nonempty P _ hs.down,
      show nonemptyChartMap (𝟙 S) hs.down hs.down = 𝟙 _ from Subsingleton.elim _ _,
      P.map_id]
    cases hs
    rfl
  map_comp {S T V} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext hv
    change chartExtensionMap P (f ≫ g) x hv =
      chartExtensionMap P g (chartExtensionMap P f x) hv
    by_cases hs : (coordinates S).Nonempty
    · have ht := hs.mono (coordinates_subset f)
      rw [chartExtensionMap_apply_of_nonempty P _ hs,
        chartExtensionMap_apply_of_nonempty P _ ht, chartExtensionMap_apply_of_nonempty P _ hs]
      rw [← ConcreteCategory.comp_apply, ← P.map_comp]
      congr 2
    · rw [chartExtensionMap_apply_of_empty P _ hs]
      by_cases ht : (coordinates T).Nonempty
      · rw [chartExtensionMap_apply_of_nonempty P _ ht, chartExtensionMap_apply_of_empty P _ hs]
        exact (map_zero (P.map _).hom).symm
      · rw [chartExtensionMap_apply_of_empty P _ ht]

private def extendChartMap {P Q : Chart ι ⥤ ModuleCat.{u} k} (α : P ⟶ Q) :
    chartExtension P ⟶ chartExtension Q where
  app S := ModuleCat.ofHom <| LinearMap.pi fun h =>
    (α.app (nonemptyChart S h.down)).hom ∘ₗ LinearMap.proj h
  naturality {S T} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext ht
    change α.app (nonemptyChart T ht.down) (chartExtensionMap P f x ht) =
      chartExtensionMap Q f ((fun h => α.app (nonemptyChart S h.down) (x h)) :
        chartExtensionObj Q S) ht
    by_cases hs : (coordinates S).Nonempty
    · rw [chartExtensionMap_apply_of_nonempty P _ hs, chartExtensionMap_apply_of_nonempty Q _ hs]
      exact ConcreteCategory.congr_hom (α.naturality (nonemptyChartMap f hs ht.down)) (x (PLift.up hs))
    · rw [chartExtensionMap_apply_of_empty P _ hs, chartExtensionMap_apply_of_empty Q _ hs]
      exact map_zero (α.app _).hom

private def chartExtensionComparisonApp {P : Chart ι ⥤ ModuleCat.{u} k}
    {Q : CoordinateSets ι ⥤ ModuleCat.{u} k} (α : P ⟶ chartSets ι ⋙ Q) (S : CoordinateSets ι) :
    (chartExtension P).obj S ⟶ Q.obj S :=
  if h : (coordinates S).Nonempty then
    ModuleCat.ofHom (LinearMap.proj (PLift.up h)) ≫ α.app (nonemptyChart S h) ≫
      Q.map (eqToHom (nonemptyChart_eq S h))
  else 0

/-- A map on nonempty charts induces a map from the diagram extended by zero. -/
private def chartExtensionComparison {P : Chart ι ⥤ ModuleCat.{u} k}
    {Q : CoordinateSets ι ⥤ ModuleCat.{u} k} (α : P ⟶ chartSets ι ⋙ Q) :
    chartExtension P ⟶ Q where
  app := chartExtensionComparisonApp α
  naturality {S T} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    by_cases hs : (coordinates S).Nonempty
    · have ht := hs.mono (coordinates_subset f)
      dsimp only [chartExtensionComparisonApp]
      rw [dite_eq_left hs, dite_eq_left ht]
      simp only [ConcreteCategory.comp_apply]
      change Q.map (eqToHom (nonemptyChart_eq T ht))
          (α.app _ (chartExtensionMap P f x (PLift.up ht))) =
        Q.map f (Q.map (eqToHom (nonemptyChart_eq S hs)) (α.app _ (x (PLift.up hs))))
      rw [chartExtensionMap_apply_of_nonempty P _ hs]
      let a := nonemptyChartMap f hs ht
      rw [show α.app (nonemptyChart T ht) (P.map a (x (PLift.up hs))) =
          Q.map ((chartSets ι).map a) (α.app _ (x (PLift.up hs))) from
        ConcreteCategory.congr_hom (α.naturality a) (x (PLift.up hs))]
      have h : Q.map ((chartSets ι).map a) ≫ Q.map (eqToHom (nonemptyChart_eq T ht)) =
          Q.map (eqToHom (nonemptyChart_eq S hs)) ≫ Q.map f := by
        rw [← Q.map_comp, ← Q.map_comp]
        exact congrArg Q.map (Subsingleton.elim _ _)
      exact ConcreteCategory.congr_hom h _
    · dsimp only [chartExtensionComparisonApp]
      rw [dite_eq_right hs]
      by_cases ht : (coordinates T).Nonempty
      · rw [dite_eq_left ht]
        simp only [ConcreteCategory.comp_apply]
        change Q.map _ (α.app _ (chartExtensionMap P f x (PLift.up ht))) = Q.map f 0
        rw [chartExtensionMap_apply_of_empty P _ hs]
        change (Q.map _).hom ((α.app _).hom 0) = (Q.map f).hom 0
        simp only [map_zero]
      · rw [dite_eq_right ht]
        change (0 : Q.obj T) = (Q.map f).hom 0
        exact (map_zero (Q.map f).hom).symm

private theorem chartExtensionComparison_bijective {P : Chart ι ⥤ ModuleCat.{u} k}
    {Q : CoordinateSets ι ⥤ ModuleCat.{u} k} (α : P ≅ chartSets ι ⋙ Q)
    (S : CoordinateSets ι) (hs : (coordinates S).Nonempty) :
    Function.Bijective ((chartExtensionComparison α.hom).app S) := by
  dsimp only [chartExtensionComparison, chartExtensionComparisonApp]
  rw [dite_eq_left hs]
  refine (ConcreteCategory.bijective_of_isIso (Q.map (eqToHom (nonemptyChart_eq S hs)))).comp
    ((ConcreteCategory.bijective_of_isIso (α.hom.app (nonemptyChart S hs))).comp ⟨?_, ?_⟩)
  · intro x y hxy
    funext h
    have h₀ : h = PLift.up hs := Subsingleton.elim _ _
    subst h
    exact hxy
  · exact fun y => ⟨fun _ => y, rfl⟩

omit [Fintype ι] in
private theorem tupleCoordinates_nonempty {n : ℕ} (e : Fin (n + 1) ↪o ι) :
    (coordinates (op (tupleOpen singletonCoordinates e))).Nonempty := by
  rw [show coordinates (op (tupleOpen singletonCoordinates e)) =
    (tupleFinset e : Set ι) from tupleOpen_singleton e]
  exact ⟨e 0, Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

/-- All ordered Čech terms use nonempty coordinate sets. -/
private def cechIso_of_chartIso {P : Chart ι ⥤ ModuleCat.{u} k}
    {Q : CoordinateSets ι ⥤ ModuleCat.{u} k} (α : P ≅ chartSets ι ⋙ Q) :
    cechComplex singletonCoordinates (chartExtension P) ≅ cechComplex singletonCoordinates Q := by
  let β := cechMap singletonCoordinates (chartExtensionComparison α.hom)
  have hβ (n : ℕ) : IsIso (β.f n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have he (e : Fin (n + 1) ↪o ι) :
        Function.Bijective ((chartExtensionComparison α.hom).app (op (tupleOpen singletonCoordinates e))) :=
      chartExtensionComparison_bijective α _ (tupleCoordinates_nonempty e)
    exact ⟨fun x y h => funext fun e => (he e).1 (congrFun h e),
      fun y => ⟨fun e => (he e).2 (y e) |>.choose, funext fun e => (he e).2 (y e) |>.choose_spec⟩⟩
  let _ : IsIso β := @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ β hβ
  exact asIso β

end ExtendChartDiagrams

section ChartCohomology

open Specs.ProjectiveFiniteChartPresentations (Chart ChartRings product kernelι)
open Specs.ProjectiveTwistChartModules (chartGround groundDiagram chartSets)

set_option backward.isDefEq.respectTransparency false

variable {k ι : Type u} [Field k] [LinearOrder ι] [Fintype ι] [DecidableEq ι]
    {G : Specs.ProjectiveTwistChartModules.ChartGeometry k ι}
    [IsLocallyNoetherian (coordinateProjectiveSpace k ι).left]

private def groundChartMap {M N : (projectiveChartRings G).Modules} (f : M ⟶ N) :
    groundDiagram M ⟶ groundDiagram N where
  app S := (ModuleCat.restrictScalars
    (chartGround k (Specs.ProjectiveTwistChartModules.indexOf S))).map (f.app S)
  naturality {_ _} g := ModuleCat.hom_ext (LinearMap.ext fun x =>
    PresheafOfModules.naturality_apply f g x)

private abbrev chartCech (M : (projectiveChartRings G).Modules) :=
  cechComplex singletonCoordinates (chartExtension (groundDiagram M))

private def chartCechMap {M N : (projectiveChartRings G).Modules} (f : M ⟶ N) :
    chartCech M ⟶ chartCech N :=
  cechMap singletonCoordinates (extendChartMap (groundChartMap f))

private def groundKernelSequence {P M : (projectiveChartRings G).Modules} (q : P ⟶ M) :
    ShortComplex (CoordinateSets ι ⥤ ModuleCat.{u} k) :=
  ShortComplex.mk (extendChartMap (groundChartMap (kernelι q))) (extendChartMap (groundChartMap q))
    (by
      apply NatTrans.ext
      funext S
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext h
      exact (x h).2)

private theorem shortExact_groundKernelSequence {P M : (projectiveChartRings G).Modules}
    (q : P ⟶ M) (hq : ∀ S, Function.Surjective (q.app S)) :
    ((groundKernelSequence q).map (cechFunctor singletonCoordinates)).ShortExact := by
  apply shortExact_cechFunctor
  intro p e
  let S := op (tupleOpen singletonCoordinates e)
  let A := (groundKernelSequence q).map ((CategoryTheory.evaluation _ _).obj S)
  change A.ShortExact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.moduleCat_exact_iff A).mpr
    intro x hx
    let y : A.X₁ := fun h => ⟨x h, by
      have he := congrFun hx h
      change q.app (nonemptyChart S h.down) (x h) = 0 at he
      exact he⟩
    exact ⟨y, rfl⟩
  · apply (ModuleCat.mono_iff_injective A.f).mpr
    intro x y hxy
    funext h
    apply Subtype.ext
    have he := congrFun hxy h
    change (x h).val = (y h).val at he
    exact he
  · apply (ModuleCat.epi_iff_surjective A.g).mpr
    intro y
    let x : A.X₂ := fun h => (hq _ (y h)).choose
    refine ⟨x, funext fun h => ?_⟩
    change q.app (nonemptyChart S h.down) (x h) = y h
    exact (hq _ (y h)).choose_spec

private def productChartProjection {J : Type} (P : J → (projectiveChartRings G).Modules)
    (j : J) : product P ⟶ P j where
  app _ := ModuleCat.ofHom (LinearMap.proj j)
  naturality _ := ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

private def chartCechProductIso {J : Type} (P : J → (projectiveChartRings G).Modules) :
    chartCech (product P) ≅ ∏ᶜ (fun j => chartCech (P j)) := by
  let K := fun j => chartCech (P j)
  let β : chartCech (product P) ⟶ ∏ᶜ K :=
    Pi.lift (fun j => chartCechMap (productChartProjection P j))
  have hβ (n : ℕ) : IsIso (β.f n) := by
    let E := HomologicalComplex.eval (ModuleCat.{u} k) (.up ℕ) n
    let e := PreservesProduct.iso E K ≪≫ ModuleCat.piIsoPi (fun j => (K j).X n)
    have happ (x : (chartCech (product P)).X n) (j : J) :
        e.hom (β.f n x) j = fun t h => x t h j := by
      let π := ModuleCat.ofHom (R := k) (LinearMap.proj j :
        (∀ a, (K a).X n) →ₗ[k] (K j).X n)
      have he : e.hom ≫ π = (Pi.π K j).f n := by
        change e.hom ≫ π = E.map (Pi.π K j)
        simp only [e, π, Iso.trans_hom, Category.assoc, ModuleCat.piIsoPi_hom_ker_subtype,
          PreservesProduct.iso_hom]
        exact piComparison_comp_π E K j
      have hπ : β.f n ≫ (Pi.π K j).f n =
          (chartCechMap (productChartProjection P j)).f n :=
        congrArg (fun f : chartCech (product P) ⟶ K j => f.f n)
          (Pi.lift_comp_π (fun a => chartCechMap (productChartProjection P a)) j)
      exact (ConcreteCategory.congr_hom he (β.f n x)).trans (ConcreteCategory.congr_hom hπ x)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    apply ((ConcreteCategory.bijective_of_isIso e.hom).of_comp_iff' (β.f n)).mp
    constructor
    · intro x y hxy
      funext t h j
      exact congrFun (congrFun ((happ x j).symm.trans ((congrFun hxy j).trans (happ y j))) t) h
    · intro y
      exact ⟨fun t h j => y j t h, funext fun j => happ _ j⟩
  let _ : IsIso β := @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ β hβ
  exact asIso β

private theorem finite_chartCech_twist (G : Specs.ProjectiveTwistChartModules.ChartGeometry k ι)
    (d : ℤ) (n : ℕ) : Module.Finite k ((chartCech ((projectiveTwists G).diagram d)).homology n) := by
  let T := ProjectiveTwistChartModules.twistDiagram G d
  let e : chartCech ((projectiveTwists G).diagram d) ≅ monomialComplex (k := k) (ι := ι) d :=
    cechIso_of_chartIso (ProjectiveTwistChartModules.groundDiagramIso G d T) ≪≫
      (ProjectiveTwistChartModules.orderedLaurentComparison (k := k) (ι := ι) d).iso
  let H := homologyFunctor (ModuleCat.{u} k) (.up ℕ) n
  let _ : Module.Finite k (H.obj (monomialComplex (k := k) (ι := ι) d)) :=
    finite_monomial_homology (k := k) (ι := ι) d n
  let h := H.mapIso e
  exact Module.Finite.of_surjective h.inv.hom (ConcreteCategory.bijective_of_isIso h.inv).2

private theorem finite_chartCech_of_finite_localizing [Nonempty ι]
    (G : Specs.ProjectiveTwistChartModules.ChartGeometry k ι)
    (M : (projectiveChartRings G).Modules) (hM : (projectiveChartRings G).FiniteOnSingletons M)
    (hLoc : (projectiveChartRings G).Localizes M) (n : ℕ) : Module.Finite k ((chartCech M).homology n) := by
  let D := projectiveChartRings G
  let L := projectiveTwists G
  let Good (C : CochainComplex (ModuleCat.{u} k) ℕ) : Prop :=
    ∃ N : D.Modules, D.FiniteOnSingletons N ∧ D.Localizes N ∧ C = chartCech N
  refine finite_homology_of_resolution_steps Good (Fintype.card ι) ?_ ?_ _
    ⟨M, hM, hLoc, rfl⟩ n
  · intro C hC p hp
    obtain ⟨N, _, _, rfl⟩ := hC
    exact isZero_orderedCech_homology_of_card_le singletonCoordinates
      (chartExtension (groundDiagram N)) p hp
  · intro C hC
    obtain ⟨N, hN, hLocN, rfl⟩ := hC
    obtain ⟨r, d, q, hq, _, _, hker, hLocKer⟩ :=
      ProjectiveFiniteChartPresentations.finiteChartPresentations k ι D L N hN hLocN
    refine ⟨(groundKernelSequence q).map (cechFunctor singletonCoordinates), rfl,
      shortExact_groundKernelSequence q hq, ⟨Specs.ProjectiveFiniteChartPresentations.kernel q, hker, hLocKer, rfl⟩, ?_⟩
    intro p
    let K := fun a : Fin r => chartCech (L.diagram (d a))
    let H := homologyFunctor (ModuleCat.{u} k) (.up ℕ) p
    let _ : Module.Finite k (H.obj (∏ᶜ K)) :=
      finite_homology_finite_product K p (fun a => finite_chartCech_twist G (d a) p)
    let e := H.mapIso
      (chartCechProductIso (fun a => L.diagram (d a)))
    exact Module.Finite.of_surjective e.inv.hom (ConcreteCategory.bijective_of_isIso e.inv).2

end ChartCohomology

section ProjectiveFiniteness

open Specs.ProjectiveFiniteChartPresentations (Chart)
open Specs.ProjectiveTwistChartModules
  (ChartGeometry chartOpen chartOpen_anti chartSets groundDiagram)

set_option backward.isDefEq.respectTransparency false

private def chartOpens {k ι : Type u} [Field k] :
    Chart ι ⥤ (coordinateProjectiveSpace k ι).left.Opensᵒᵖ where
  obj S := op (chartOpen k (Chart.indices S))
  map f := (homOfLE (chartOpen_anti (Chart.subset f))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private def sheafChartGroundIso {k ι : Type u} [Field k] [LinearOrder ι] [Fintype ι] [DecidableEq ι]
    (G : ChartGeometry k ι) [IsLocallyNoetherian (coordinateProjectiveSpace k ι).left]
    (M : (coordinateProjectiveSpace k ι).left.Modules) :
    groundDiagram (sheafChartModules G M) ≅
      chartSets ι ⋙ (coordinateIntersections (k := k)).op ⋙ coefficientPresheaf M := by
  let e : chartOpens (k := k) (ι := ι) ≅ chartSets ι ⋙ (coordinateIntersections (k := k)).op :=
    NatIso.ofComponents (fun S => eqToIso (by
      change op (chartOpen k (Chart.indices S)) = op (chartOpen k (((Chart.indices S) : Set ι)).toFinite.toFinset)
      congr 2
      exact Finset.coe_injective (((Chart.indices S) : Set ι).toFinite.coe_toFinset).symm))
      (fun _ => Subsingleton.elim _ _)
  let b : groundDiagram (sheafChartModules G M) ≅ chartOpens ⋙ coefficientPresheaf M :=
    NatIso.ofComponents (fun _ => Iso.refl _)
      (fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))
  exact b ≪≫ Functor.isoWhiskerRight e (coefficientPresheaf M)

variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    {X : SchemeOverRing k}

private def closedPushforwardCoefficientIso (i : X ⟶ projectiveSpace k W) (F : X.left.Modules) :
    coefficientPresheaf ((pushforward i.left).obj F) ≅
      (Opens.map i.left.base).op ⋙ coefficientPresheaf F := by
  have hi : i.left ≫ (projectiveSpace k W).hom = X.hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id k)) := by
    simpa using i.w
  let b := coefficientPullback (RingHom.id k) i.left hi (𝟙 ((pushforward i.left).obj F))
  let _ (U : (projectiveSpace k W).left.Opensᵒᵖ) : IsIso (b.app U) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact Function.bijective_id
  let _ : IsIso b := NatIso.isIso_of_isIso_app b
  let P := (Opens.map i.left.base).op ⋙ coefficientPresheaf F
  exact asIso b ≪≫
    Functor.isoWhiskerLeft P (ModuleCat.restrictScalarsId k) ≪≫ Functor.rightUnitor P

private def cohomologyIso_chartCech (i : X ⟶ projectiveSpace k W) [IsClosedImmersion i.left]
    [IsLocallyNoetherian (projectiveSpace k W).left]
    (G : ChartGeometry k (ULift.{u} (Fin (Module.finrank k W))))
    (F : X.left.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (cohomology X n).obj F ≅
      (chartCech (sheafChartModules G ((pushforward i.left).obj F))).homology n := by
  let ι := ULift.{u} (Fin (Module.finrank k W))
  let charts := chartSets ι ⋙ (coordinateIntersections (k := k) (ι := ι)).op
  let e : groundDiagram (sheafChartModules G ((pushforward i.left).obj F)) ≅
      chartSets ι ⋙ projectiveCoefficientDiagram i F :=
    sheafChartGroundIso G _ ≪≫
      Functor.isoWhiskerLeft charts (closedPushforwardCoefficientIso i F)
  exact cohomologyIso_projectiveCoefficientDiagram i F n ≪≫
    (homologyFunctor (ModuleCat.{u} k) (.up ℕ) n).mapIso (cechIso_of_chartIso e).symm

/-- Every derived cohomology group of a coherent sheaf on a closed subscheme
of finite-dimensional projective space is finite-dimensional over the base field. -/
theorem projectiveCohomologyFiniteness : Specs.ProjectiveFiniteness.ProjectiveCohomologyFiniteness.{u} := by
  intro k W _ _ _ _ X i _ F _ n
  by_cases h : Module.finrank k W = 0
  · exact finiteDimensional_cohomology_of_projective_finrank_zero i h F n
  let ι := ULift.{u} (Fin (Module.finrank k W))
  let _ : Nonempty ι := ⟨⟨⟨0, Nat.pos_of_ne_zero h⟩⟩⟩
  let _ : IsProper (projectiveSpace k W).hom :=
    LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper k W
  let _ : IsLocallyNoetherian (projectiveSpace k W).left :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpace k W).hom
  let G := ProjectiveTwistChartModules.chartGeometry (k := k) (ι := ι)
  let M := sheafChartModules G ((pushforward i.left).obj F)
  let _ : Module.Finite k ((chartCech M).homology n) :=
    finite_chartCech_of_finite_localizing G M
      (finite_sheafChartModules_pushforward G i.left F)
      (localizes_sheafChartModules_pushforward G i.left F) n
  let e := cohomologyIso_chartCech i G F n
  exact Module.Finite.of_surjective e.inv.hom (ConcreteCategory.bijective_of_isIso e.inv).2

/-- A line bundle on a projectively embedded scheme has finite-dimensional cohomology. -/
theorem projectiveCohomologyFiniteness_of_local_rank_one
    (i : X ⟶ projectiveSpace k W) [IsClosedImmersion i.left] (F : X.left.Modules)
    {J : Type u} (U : J → X.left.Opens) (hU : IsOpenCover U)
    (e : ∀ j, SheafOfModules.unit (U j).toScheme.ringCatSheaf ≅ F.restrict (U j).ι)
    (n : ℕ) : FiniteDimensional k ((cohomology X n).obj F) := by
  let _ : F.IsFinitePresentation := isFinitePresentation_of_local_rank_one_restrict F U hU e
  exact projectiveCohomologyFiniteness k W X i F n

end ProjectiveFiniteness

end LinearAlgebraicGroups.ProjectiveFiniteness
