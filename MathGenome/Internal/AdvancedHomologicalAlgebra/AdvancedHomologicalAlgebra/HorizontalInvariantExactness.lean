import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HorizontalInvariantExactness
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
open Specs.AdvancedHomologicalAlgebra.HorizontalInvariantExactness

namespace AdvancedHomologicalAlgebra.HorizontalInvariantExactness

universe v u
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Injectivity on quotients by boundaries implies injectivity on cohomology. -/
lemma mono_homologyMap_of_mono_opcyclesMap {U V : CochainComplex A ℤ}
    (i : U ⟶ V) (p : ℤ) [Mono (opcyclesMap i p)] : Mono (homologyMap i p) :=
  mono_of_mono_fac (homologyι_naturality i p)

lemma homology_shortExact (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (hi : ∀ p, Mono (opcyclesMap S.f p)) (p : ℤ) :
    (S.map (homologyFunctor A (ComplexShape.up ℤ) p)).ShortExact := by
  have := hi p
  have := hi (p + 1)
  have := mono_homologyMap_of_mono_opcyclesMap S.f p
  have := mono_homologyMap_of_mono_opcyclesMap S.f (p + 1)
  have hrel : (ComplexShape.up ℤ).Rel p (p + 1) := by simp
  have hδ : hS.δ p (p + 1) hrel = 0 := by
    apply (cancel_mono (homologyMap S.f (p + 1))).1
    simp
  refine { exact := hS.homology_exact₂ p
           mono_f := inferInstanceAs (Mono (homologyMap S.f p))
           epi_g := ?_ }
  exact ((ShortComplex.mk _ _ (hS.comp_δ p (p + 1) hrel)).exact_iff_epi hδ).1
    (hS.homology_exact₃ p (p + 1) hrel)

lemma opcycles_shortExact (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (hi : ∀ p, Mono (opcyclesMap S.f p)) (p : ℤ) :
    (S.map (opcyclesFunctor A (ComplexShape.up ℤ) p)).ShortExact := by
  have := hS.epi_g
  have := hi p
  exact { exact := opcycles_right_exact S hS.exact p
          mono_f := hi p
          epi_g := inferInstanceAs (Epi (opcyclesMap S.g p)) }

lemma cycles_shortExact (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (hi : ∀ p, Mono (opcyclesMap S.f p)) (p : ℤ) :
    (S.map (cyclesFunctor A (ComplexShape.up ℤ) p)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have : Epi (homologyMap S.g p) := (homology_shortExact S hS hi p).epi_g
  let R (K : CochainComplex A ℤ) := ShortComplex.mk
    (K.opcyclesToCycles (p - 1) p) (K.homologyπ p)
    (K.opcyclesToCycles_homologyπ (p - 1) p)
  have hex (K : CochainComplex A ℤ) : (R K).Exact :=
    (HomologySequence.composableArrows₃_exact K (p - 1) p (by simp)).exact 1
  let φ : R S.X₂ ⟶ R S.X₃ :=
    { τ₁ := opcyclesMap S.g (p - 1)
      τ₂ := cyclesMap S.g p
      τ₃ := homologyMap S.g p
      comm₁₂ := opcyclesToCycles_naturality S.g (p - 1) p
      comm₂₃ := (homologyπ_naturality S.g p).symm }
  refine { exact := cycles_left_exact S hS.exact p
           mono_f := inferInstanceAs (Mono (cyclesMap S.f p))
           epi_g := ?_ }
  exact ShortComplex.epi_of_epi_of_epi_of_epi φ (hex S.X₃)
    inferInstance inferInstance (homology_shortExact S hS hi p).epi_g

/-- The kernel of the quotient projection is the image of the incoming differential. -/
theorem boundaryImageComparison : boundaryImageComparisonType := by
  intro A _ _ K p
  let hc := K.opcyclesIsCokernel (i := p - 1) (j := p) (by simp)
  let e : cokernel (K.d (p - 1) p) ≅ K.opcycles p :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hc
  have he : cokernel.π (K.d (p - 1) p) ≫ e.hom = K.pOpcycles p := by
    simpa [e] using (IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (K.d (p - 1) p)) hc WalkingParallelPair.one)
  let b := kernel.mapIso (K.pOpcycles p) (cokernel.π (K.d (p - 1) p))
    (Iso.refl _) e.symm (by simp [← he])
  exact ⟨b, by simp [b]⟩

/-- Snake diagram for the kernels of the degreewise quotient projections. -/
private noncomputable def boundarySnake
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (hi : ∀ p, Mono (opcyclesMap S.f p)) (p : ℤ) : ShortComplex.SnakeInput A where
  L₀ := boundarySequence S p
  L₁ := S.map (eval A (ComplexShape.up ℤ) p)
  L₂ := S.map (opcyclesFunctor A (ComplexShape.up ℤ) p)
  L₃ := ShortComplex.mk (0 : (0 : A) ⟶ 0) (0 : (0 : A) ⟶ 0) (by simp)
  v₀₁ :=
    { τ₁ := kernel.ι (S.X₁.pOpcycles p)
      τ₂ := kernel.ι (S.X₂.pOpcycles p)
      τ₃ := kernel.ι (S.X₃.pOpcycles p)
      comm₁₂ := by simp [boundarySequence, boundariesMap]
      comm₂₃ := by simp [boundarySequence, boundariesMap] }
  v₁₂ :=
    { τ₁ := S.X₁.pOpcycles p
      τ₂ := S.X₂.pOpcycles p
      τ₃ := S.X₃.pOpcycles p
      comm₁₂ := p_opcyclesMap S.f p
      comm₂₃ := p_opcyclesMap S.g p }
  v₂₃ := 0
  w₀₂ := by ext <;> exact kernel.condition _
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    all_goals
      exact (KernelFork.isLimitMapConeEquiv _ _).symm (kernelIsKernel _)
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (CokernelCofork.IsColimit.ofEpiOfIsZero _
          (inferInstanceAs (Epi (S.X₁.pOpcycles p))) (isZero_zero A))
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (CokernelCofork.IsColimit.ofEpiOfIsZero _
          (inferInstanceAs (Epi (S.X₂.pOpcycles p))) (isZero_zero A))
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (CokernelCofork.IsColimit.ofEpiOfIsZero _
          (inferInstanceAs (Epi (S.X₃.pOpcycles p))) (isZero_zero A))
  L₁_exact := hS.exact.map (eval A (ComplexShape.up ℤ) p)
  epi_L₁_g := by
    have := hS.epi_g
    change Epi (S.g.f p)
    infer_instance
  L₂_exact := (opcycles_shortExact S hS hi p).exact
  mono_L₂_f := hi p

lemma boundaries_shortExact (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact)
    (hi : ∀ p, Mono (opcyclesMap S.f p)) (p : ℤ) :
    (boundarySequence S p).ShortExact := by
  let D := boundarySnake S hS hi p
  have := hS.mono_f
  have : Mono (D.L₁.f) := inferInstanceAs (Mono (S.f.f p))
  have hδ : D.δ = 0 := (isZero_zero A).eq_of_tgt _ _
  exact { exact := D.L₀_exact
          mono_f := D.mono_L₀_f
          epi_g := (D.L₁'.exact_iff_epi hδ).1 D.L₁'_exact }

/-- HA-G07 for a general short exact sequence of cochain complexes. -/
theorem shortExactInvariants : shortExactInvariantsType := by
  intro A _ _ S hS hi p
  exact ⟨boundaries_shortExact S hS hi p, cycles_shortExact S hS hi p,
    homology_shortExact S hS hi p, opcycles_shortExact S hS hi p⟩

/-- HA-G07 with W the cokernel complex of a degreewise admissible injection. -/
theorem horizontalInvariantExactness : horizontalInvariantExactnessType := by
  intro A _ _ U V i hi hq
  have : Mono i := mono_of_mono_f i hi
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel i)
      mono_f := inferInstanceAs (Mono i)
      epi_g := inferInstanceAs (Epi (cokernel.π i)) }
  exact ⟨hS, shortExactInvariants A S hS hq⟩

end AdvancedHomologicalAlgebra.HorizontalInvariantExactness
