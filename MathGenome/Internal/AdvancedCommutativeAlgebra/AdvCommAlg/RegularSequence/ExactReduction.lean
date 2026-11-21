import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.ExactReduction

/-! Reduction of exact complexes and closure of weak regularity under extensions,
paper.tex:2472–2493 (RK-12). -/

universe u v w
open scoped Pointwise
open CategoryTheory Function
open RingTheory.Sequence Submodule

namespace AdvCommAlg.RegularSequence
variable {R : Type u} [CommRing R]

/-- Reduction of a monomorphism stays injective when its cokernel has no a-torsion. -/
theorem injective_quotSMulTop_of_exact {L M N : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {f : L →ₗ[R] M} {g : M →ₗ[R] N}
    (hf : Injective f) (hfg : Exact f g) {a : R} (ha : IsSMulRegular N a) :
    Injective (QuotSMulTop.map a f) := by
  have h0 : Exact (0 : L →ₗ[R] L) f :=
    (LinearMap.exact_zero_iff_injective L f).mpr hf
  have h := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h0 hfg ha
  simpa only [map_zero, LinearMap.exact_zero_iff_injective] using h

/-- Weak regularity passes from the outer modules of a short exact sequence to its middle. -/
theorem weaklyRegular_extension {L M N : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (x : List R) (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hf : Injective f) (hfg : Exact f g) (hg : Surjective g)
    (hL : WeaklyRegular L x) (hN : WeaklyRegular N x) : WeaklyRegular M x := by
  induction x generalizing L M N with
  | nil => exact IsWeaklyRegular.nil R M
  | cons a x ih =>
    obtain ⟨haL, hxL⟩ := (isWeaklyRegular_cons_iff L a x).mp hL
    obtain ⟨haN, hxN⟩ := (isWeaklyRegular_cons_iff N a x).mp hN
    apply (isWeaklyRegular_cons_iff M a x).mpr
    refine ⟨isSMulRegular_of_range_eq_ker hf hfg.linearMap_ker_eq.symm haL haN, ?_⟩
    exact ih (QuotSMulTop.map a f) (QuotSMulTop.map a g)
      (injective_quotSMulTop_of_exact hf hfg haN)
      (QuotSMulTop.map_exact a hfg hg) (QuotSMulTop.map_surjective a hg) hxL hxN

private theorem exactAt_iff_function {ι : Type w} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i : ι) :
    K.ExactAt i ↔ Exact (K.d (c.prev i) i).hom (K.d i (c.next i)).hom :=
  CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (K.sc i)

/-- The intermediate complex after reducing by one element. -/
private def elementReduction {ι : Type w} {c : ComplexShape ι} (a : R)
    (K : HomologicalComplex (ModuleCat.{v} R) c) :
    HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (QuotSMulTop a (K.X i))
  d i j := ModuleCat.ofHom (QuotSMulTop.map a (K.d i j).hom)
  shape i j hij := by
    apply ModuleCat.hom_ext
    change QuotSMulTop.map a (K.d i j).hom = 0
    rw [K.shape i j hij]
    exact map_zero _
  d_comp_d' i j k _ _ := by
    apply ModuleCat.hom_ext
    change (QuotSMulTop.map a (K.d j k).hom).comp
      (QuotSMulTop.map a (K.d i j).hom) = 0
    rw [← QuotSMulTop.map_comp]
    have h : (K.d j k).hom.comp (K.d i j).hom = 0 :=
      congrArg ModuleCat.Hom.hom (K.d_comp_d i j k)
    rw [h, map_zero]

private theorem acyclic_elementReduction {ι : Type w} {c : ComplexShape ι}
    (a : R) (K : HomologicalComplex (ModuleCat.{v} R) c) (hK : K.Acyclic)
    (ha : ∀ i, IsSMulRegular (K.X i) a) : (elementReduction a K).Acyclic := by
  intro i
  apply (exactAt_iff_function _ i).mpr
  change Exact (QuotSMulTop.map a (K.d (c.prev i) i).hom)
    (QuotSMulTop.map a (K.d i (c.next i)).hom)
  have hi := (exactAt_iff_function K i).mp (hK i)
  by_cases hrel : c.Rel i (c.next i)
  · have hn := (exactAt_iff_function K (c.next i)).mp (hK (c.next i))
    rw [c.prev_eq' hrel] at hn
    exact QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
      hi hn (ha (c.next (c.next i)))
  · have hz : (K.d i (c.next i)).hom = 0 := by rw [K.shape _ _ hrel]; rfl
    rw [hz] at hi ⊢
    rw [map_zero]
    apply (LinearMap.exact_zero_iff_surjective (QuotSMulTop a (K.X (c.next i))) _).mpr
    exact QuotSMulTop.map_surjective a
      ((LinearMap.exact_zero_iff_surjective (K.X (c.next i)) _).mp hi)

/-- Quotienting every term of an exact complex by a weakly regular list preserves exactness. -/
theorem exact_reduction {ι : Type w} {c : ComplexShape ι} (x : List R)
    (K : HomologicalComplex (ModuleCat.{v} R) c) (hK : K.Acyclic)
    (hx : ∀ i, WeaklyRegular (K.X i) x) : (coefficientReduction x K).Acyclic := by
  induction x generalizing K with
  | nil =>
    intro i
    apply (exactAt_iff_function _ i).mpr
    let e (j : ι) := quotEquivOfEqBot
      (Ideal.ofList ([] : List R) • ⊤ : Submodule R (K.X j)) (by simp)
    apply (Exact.iff_of_ladder_linearEquiv
      (e₁ := e (c.prev i)) (e₂ := e i) (e₃ := e (c.next i)) ?_ ?_).mp
      ((exactAt_iff_function K i).mp (hK i))
    all_goals exact quot_hom_ext _ _ _ (fun _ => rfl)
  | cons a x ih =>
    have ha (i : ι) : IsSMulRegular (K.X i) a :=
      ((isWeaklyRegular_cons_iff (K.X i) a x).mp (hx i)).1
    have ht (i : ι) : WeaklyRegular ((elementReduction a K).X i) x :=
      ((isWeaklyRegular_cons_iff (K.X i) a x).mp (hx i)).2
    have hred := ih (elementReduction a K) (acyclic_elementReduction a K hK ha) ht
    intro i
    apply (exactAt_iff_function _ i).mpr
    have H₁ := quotOfListConsSMulTopEquivQuotSMulTopInner_naturality a x
      (K.d (c.prev i) i).hom
    have H₂ := quotOfListConsSMulTopEquivQuotSMulTopInner_naturality a x
      (K.d i (c.next i)).hom
    exact (Exact.iff_of_ladder_linearEquiv H₁.symm H₂.symm).mp
      ((exactAt_iff_function _ i).mp (hred i))

end AdvCommAlg.RegularSequence
