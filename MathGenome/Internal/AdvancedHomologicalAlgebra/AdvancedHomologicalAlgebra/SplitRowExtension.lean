import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.SplitRowExtension
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Abelian.Refinements

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u

namespace AdvancedHomologicalAlgebra.SplitRowExtension

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Split cycles give a generalized inverse for every differential. -/
lemma differential_has_generalized_inverse (L : CochainComplex C ℤ)
    [∀ p, Injective (L.X p)] [∀ p, Injective (L.cycles p)] (i j : ℤ) :
    ∃ s : L.X j ⟶ L.X i, L.d i j ≫ s ≫ L.d i j = L.d i j := by
  by_cases hij : (ComplexShape.up ℤ).Rel i j
  · let r := Injective.factorThru (𝟙 (L.cycles i)) (L.iCycles i)
    have hr : L.iCycles i ≫ r = 𝟙 _ := Injective.comp_factorThru _ _
    let S := ShortComplex.mk (L.iCycles i) (L.d i j) (L.iCycles_d i j)
    have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S
      (L.cyclesIsKernel i j ((ComplexShape.up ℤ).next_eq' hij))
    have hk : S.f ≫ (𝟙 (L.X i) - r ≫ L.iCycles i) = 0 := by
      dsimp [S]
      simp [Preadditive.comp_sub, ← Category.assoc, hr]
    refine ⟨hS.descToInjective _ hk, ?_⟩
    rw [← Category.assoc, hS.comp_descToInjective]
    simp [Preadditive.sub_comp, Category.assoc]
  · exact ⟨0, by simp [L.shape i j hij]⟩

/-- A map annihilating all differentials extends using just the quotient test. -/
lemma extend_cycle_valued_map {U V L : CochainComplex C ℤ}
    [∀ p, Injective (L.cycles p)] (i : U ⟶ V)
    (hi : ∀ p, Mono (opcyclesMap i p)) (f : U ⟶ L)
    (hf : ∀ p, f.f p ≫ L.d p (p + 1) = 0) :
    ∃ g : V ⟶ L, i ≫ g = f := by
  classical
  let a (p : ℤ) := L.liftCycles (f.f p) (p + 1) (by simp) (hf p)
  have ha (p : ℤ) : U.d (p - 1) p ≫ a p = 0 := by
    apply (cancel_mono (L.iCycles p)).1
    simp only [Category.assoc, a, liftCycles_i, zero_comp]
    rw [← f.comm]
    have hp := hf (p - 1)
    have hp' : (p - 1) + (1 : ℤ) = p := by omega
    rw [hp'] at hp
    exact hp
  let b (p : ℤ) := U.descOpcycles (a p) (p - 1) (by simp) (ha p)
  let e (p : ℤ) : V.opcycles p ⟶ L.cycles p :=
    @Injective.factorThru _ _ _ _ _ _ (b p) (opcyclesMap i p) (hi p)
  let g : V ⟶ L :=
    { f := fun p => V.pOpcycles p ≫ e p ≫ L.iCycles p
      comm' := fun p q hpq => by
        simp only [Category.assoc, iCycles_d, comp_zero]
        simp only [← Category.assoc, d_pOpcycles, zero_comp] }
  refine ⟨g, ?_⟩
  ext p
  change i.f p ≫ (V.pOpcycles p ≫ e p ≫ L.iCycles p) = f.f p
  rw [← Category.assoc, ← p_opcyclesMap, Category.assoc]
  have he : opcyclesMap i p ≫ e p = b p :=
    @Injective.comp_factorThru _ _ _ _ _ _ (b p) (opcyclesMap i p) (hi p)
  rw [← Category.assoc (opcyclesMap i p), he, ← Category.assoc]
  simp [b, a]

/-- Termwise injectivity and injective cycles suffice for admissible extension.
The proof separates a cycle-valued map from a null-homotopic map. -/
theorem extension_of_injective_terms_and_cycles (L : CochainComplex C ℤ)
    [∀ p, Injective (L.X p)] [∀ p, Injective (L.cycles p)] :
    HasExtensionProperty L := by
  classical
  intro U V i hi f
  choose s hs using differential_has_generalized_inverse L
  let h : ∀ p q, L.X p ⟶ L.X q := fun p q => s q p
  let N : L ⟶ L := Homotopy.nullHomotopicMap h
  let P : L ⟶ L := 𝟙 L - N
  have hP (p : ℤ) : P.f p ≫ L.d p (p + 1) = 0 := by
    have hN : N.f p = L.d p (p + 1) ≫ h (p + 1) p +
        h p (p - 1) ≫ L.d (p - 1) p :=
      Homotopy.nullHomotopicMap_f (by simp) (by simp) h
    simp only [P, sub_f_apply, id_f, Preadditive.sub_comp, id_comp, hN,
      Preadditive.add_comp, Category.assoc, d_comp_d, comp_zero, add_zero]
    exact sub_eq_zero.mpr (hs p (p + 1)).symm
  obtain ⟨g₀, hg₀⟩ := extend_cycle_valued_map i hi.2 (f ≫ P) (fun p => by
    simp only [comp_f, Category.assoc, hP, comp_zero])
  have he (p q : ℤ) : ∃ e : V.X p ⟶ L.X q, i.f p ≫ e = f.f p ≫ h p q := by
    have := hi.1 p
    exact Injective.factors _ _
  choose e he using he
  refine ⟨g₀ + Homotopy.nullHomotopicMap e, ?_⟩
  rw [Preadditive.comp_add, hg₀, Homotopy.comp_nullHomotopicMap]
  have hcomp : (fun p q => i.f p ≫ e p q) = (fun p q => f.f p ≫ h p q) := by
    funext p q
    exact he p q
  rw [hcomp, ← Homotopy.comp_nullHomotopicMap]
  dsimp [P, N]
  simp [Preadditive.comp_sub]

/-- Every nonnegative horizontal row of any Cartan–Eilenberg resolution
has the asserted extension property. -/
theorem rowExtension : Specs.RowExtension.{v, u} := by
  intro C _ _ K R q hq
  let L := R.bicomplex.flip.X q
  have ht : ∀ p, Injective (L.X p) := fun p => (R.terms p).injective q hq
  have hz : ∀ p, Injective (L.cycles p) := fun p => (R.cycles p).injective q hq
  change HasExtensionProperty L
  apply extension_of_injective_terms_and_cycles

open CartanEilenbergData

/-- The image inclusion of an incoming differential is killed by the quotient. -/
lemma boundary_ι_pOpcycles (L : CochainComplex C ℤ) (p : ℤ) :
    image.ι (L.d (p - 1) p) ≫ L.pOpcycles p = 0 := by
  apply (cancel_epi (factorThruImage (L.d (p - 1) p))).1
  simp

/-- Exactness of boundaries in an incoming/outgoing pair makes the kernel
of the outgoing map an admissible subcomplex. No injectivity is needed. -/
lemma kernel_admissible_of_exact_boundaries {U V W : CochainComplex C ℤ}
    (a : U ⟶ V) (b : V ⟶ W) (hab : a ≫ b = 0)
    (hex : ∀ p, (ShortComplex.mk ((boundariesFunctor p).map a)
      ((boundariesFunctor p).map b) (by
        rw [← Functor.map_comp, hab, Functor.map_zero])).Exact) :
    Admissible (kernel.ι b) := by
  let T := kernel b
  let t : T ⟶ V := kernel.ι b
  let k : U ⟶ T := kernel.lift b a hab
  have hkt : k ≫ t = a := kernel.lift_ι _ _ _
  have ht : Mono t := inferInstance
  refine ⟨fun p => inferInstanceAs (Mono (t.f p)), fun p => ?_⟩
  rw [Preadditive.mono_iff_cancel_zero]
  intro A z hz
  obtain ⟨A₁, π₁, _, x, hx⟩ := surjective_up_to_refinements_of_epi (T.pOpcycles p) z
  have hx₀ : (x ≫ t.f p) ≫ V.pOpcycles p = 0 := by
    rw [Category.assoc, ← p_opcyclesMap, ← Category.assoc, ← hx, Category.assoc, hz,
      comp_zero]
  let S := ShortComplex.mk (V.d (p - 1) p) (V.pOpcycles p) (V.d_pOpcycles _ _)
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S
    (V.opcyclesIsCokernel (i := p - 1) (j := p) (by simp))
  obtain ⟨A₂, π₂, _, v, hv⟩ := hS.exact_up_to_refinements _ hx₀
  let β := v ≫ factorThruImage (V.d (p - 1) p)
  have hβ : β ≫ image.ι (V.d (p - 1) p) = π₂ ≫ x ≫ t.f p := by
    simpa only [β, Category.assoc, image.fac] using hv.symm
  have hβ₀ : β ≫ (boundariesFunctor p).map b = 0 := by
    apply (cancel_mono (image.ι (W.d (p - 1) p))).1
    dsimp [boundariesFunctor]
    rw [Category.assoc, image.map_homMk'_ι, ← Category.assoc, hβ]
    have htb : t.f p ≫ b.f p = 0 := by
      change (t ≫ b).f p = 0
      simp [t]
    simp only [Category.assoc, htb, comp_zero, zero_comp]
  obtain ⟨A₃, π₃, _, y, hy⟩ := (hex p).exact_up_to_refinements β hβ₀
  have hxeq : π₃ ≫ π₂ ≫ x = y ≫ image.ι (U.d (p - 1) p) ≫ k.f p := by
    apply (cancel_mono (t.f p)).1
    have hktp : k.f p ≫ t.f p = a.f p := congrArg (fun f => f.f p) hkt
    calc
      (π₃ ≫ π₂ ≫ x) ≫ t.f p = π₃ ≫ β ≫ image.ι (V.d (p - 1) p) := by
        simp only [Category.assoc, hβ]
      _ = (y ≫ (boundariesFunctor p).map a) ≫ image.ι (V.d (p - 1) p) := by
        rw [← Category.assoc, hy]
      _ = (y ≫ image.ι (U.d (p - 1) p) ≫ k.f p) ≫ t.f p := by
        dsimp [boundariesFunctor]
        simp only [Category.assoc, image.map_homMk'_ι, hktp]
  have hk₀ : image.ι (U.d (p - 1) p) ≫ k.f p ≫ T.pOpcycles p = 0 := by
    rw [← p_opcyclesMap, ← Category.assoc, boundary_ι_pOpcycles, zero_comp]
  have hz₀ : π₃ ≫ π₂ ≫ π₁ ≫ z = 0 := by
    rw [hx]
    calc
      π₃ ≫ π₂ ≫ x ≫ T.pOpcycles p =
          (y ≫ image.ι (U.d (p - 1) p) ≫ k.f p) ≫ T.pOpcycles p := by
            rw [← hxeq, Category.assoc, Category.assoc]
      _ = 0 := by rw [Category.assoc, Category.assoc, hk₀, comp_zero]
  simpa only [← cancel_epi π₃, ← cancel_epi π₂, ← cancel_epi π₁, comp_zero] using hz₀

/-- Injection on cohomology and in the next degree gives the quotient test. -/
lemma mono_opcyclesMap_of_mono_homologyMap {U V : CochainComplex C ℤ}
    (i : U ⟶ V) (p : ℤ) [Mono (homologyMap i p)] [Mono (i.f (p + 1))] :
    Mono (opcyclesMap i p) := by
  let S (L : CochainComplex C ℤ) := ShortComplex.mk
    (L.homologyι p) (L.opcyclesToCycles p (p + 1)) (by simp)
  let φ : S U ⟶ S V :=
    { τ₁ := homologyMap i p
      τ₂ := opcyclesMap i p
      τ₃ := cyclesMap i (p + 1)
      comm₁₂ := homologyι_naturality i p
      comm₂₃ := opcyclesToCycles_naturality i p (p + 1) }
  have hS : (S U).Exact :=
    (HomologySequence.composableArrows₃_exact U p (p + 1) (by simp)).exact 0
  exact ShortComplex.mono_τ₂_of_exact_of_mono φ hS

/-- The degree-zero augmentation passes both admissibility tests. -/
theorem augmentationAdmissible : Specs.AugmentationAdmissible.{v, u} := by
  intro C _ _ K R
  have ht (p : ℤ) : Mono (R.augmentation.f p) := (R.terms p).mono
  have hh (p : ℤ) : Mono (homologyMap R.augmentation p) := (R.cohomology p).mono
  exact ⟨ht, fun p => mono_opcyclesMap_of_mono_homologyMap R.augmentation p⟩

/-- This applies to the kernels in every nonnegative vertical degree,
including the one identified with K by the augmentation. -/
theorem verticalKernelAdmissible : Specs.VerticalKernelAdmissible.{v, u} := by
  intro C _ _ K R q hq
  by_cases hq₀ : q = 0
  · subst q
    have haug : R.augmentation ≫ R.bicomplex.flip.d 0 (0 + 1) = 0 := by
      ext p
      exact R.augmentation_d p
    apply kernel_admissible_of_exact_boundaries R.augmentation _ haug
    intro p
    exact (R.boundaries p).exact_zero
  · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq₀)
    apply kernel_admissible_of_exact_boundaries
      (R.bicomplex.flip.d (q - 1) q) _ (R.bicomplex.flip.d_comp_d _ _ _)
    intro p
    let J := invariantColumn R.bicomplex (boundariesFunctor p)
    have hJ : J.ExactAt q := (R.boundaries p).exact_pos q hqpos
    exact (J.exactAt_iff' (q - 1) q (q + 1) (by simp) (by simp)).mp hJ

end AdvancedHomologicalAlgebra.SplitRowExtension
