import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.RegularSequenceBound
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.TopHomologyAndRegularElement
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions

open CategoryTheory
open scoped Pointwise
noncomputable section
universe u v
namespace AdvCommAlg.Koszul.RegularSequenceBound
open TopHomology CoefficientSequences
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The range convention in RK-14 equals the usual scalar multiple submodule. -/
theorem scalarRange_eq_smul_top (a : R) :
    scalarRange M a = a • (⊤ : Submodule R M) := by
  ext m
  change (∃ n : M, a • n = m) ↔ _
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]

/-- Transport of Koszul homology along a coefficient equivalence. -/
def coefficientHomologyEquiv {N : Type v} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (x : List R) (q : ℕ) :
    homology M x q ≃ₗ[R] homology N x q :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R)
      (ComplexShape.down ℕ) q).mapIso
    ((coefficientChainFunctor x).mapIso e.toModuleIso)).toLinearEquiv

/-- A coefficient equivalence restricts to the annihilator of any fixed ideal. -/
def annihilatorEquiv {N : Type v} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (I : Ideal R) :
    idealAnnihilator M I ≃ₗ[R] idealAnnihilator N I :=
  e.ofSubmodules _ _ (by
    ext n
    constructor
    · rintro ⟨m, hm, rfl⟩ a ha
      rw [← map_smul, hm a ha, map_zero]
    · intro hn
      refine ⟨e.symm n, ?_, e.apply_symm_apply n⟩
      intro a ha
      rw [← map_smul, hn a ha, map_zero])

/-- The connecting map after reduction is surjective; it is an isomorphism
when the preceding homology group is zero. -/
theorem reduction_connecting (x : List R) (a : R) (ha : a ∈ listIdeal x)
    (hinj : Function.Injective (fun m : M => a • m)) (q : ℕ) :
    ∃ f : homology (QuotSMulTop a M) x (q+1) →ₗ[R] homology M x q,
      Function.Surjective f ∧
      (Subsingleton (homology M x (q+1)) → Function.Injective f) := by
  obtain ⟨h, hs, _⟩ := regularElement_shortExact M x a ha hinj
  let S := reductionHomologySequence M x a h q
  have hS : S.ShortExact := hs q
  let e := coefficientHomologyEquiv (M ⧸ scalarRange M a)
    (Submodule.quotEquivOfEq _ _ (scalarRange_eq_smul_top M a)) x (q+1)
  refine ⟨S.g.hom.comp e.symm.toLinearMap, ?_, ?_⟩
  · exact ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g).comp e.symm.surjective
  · intro hzero
    have hX : Limits.IsZero S.X₁ := ModuleCat.isZero_iff_subsingleton.mpr hzero
    have : IsIso S.g := hS.isIso_g_iff.mpr hX
    exact ((ModuleCat.mono_iff_injective S.g).mp inferInstance).comp e.symm.injective

/-- Iterating the surjective connecting maps gives a support bound even
without a properness or nonzero-quotient hypothesis. -/
theorem homology_vanish_of_weaklyRegular (x y : List R)
    (hy : RingTheory.Sequence.IsWeaklyRegular M y)
    (hI : ∀ a ∈ y, a ∈ listIdeal x) (q : ℕ) (hq : x.length < q + y.length) :
    Subsingleton (homology M x q) := by
  induction y generalizing M q with
  | nil => exact homology_bounded M x q (by simpa using hq)
  | cons a y ih =>
    obtain ⟨ha, hy⟩ := (RingTheory.Sequence.isWeaklyRegular_cons_iff M a y).mp hy
    have hQ : Subsingleton (homology (QuotSMulTop a M) x (q+1)) :=
      ih (QuotSMulTop a M) hy (fun b hb => hI b (List.mem_cons_of_mem a hb))
        (q+1) (by simp only [List.length_cons] at hq; omega)
    obtain ⟨f, hf, _⟩ := reduction_connecting M x a (hI a List.mem_cons_self) ha q
    exact hf.subsingleton

/-- At total degree r the inverse connecting maps identify the original
group with the top group after quotienting by the whole regular list. -/
theorem extremal_homology_equiv (x y : List R)
    (hy : RingTheory.Sequence.IsWeaklyRegular M y)
    (hI : ∀ a ∈ y, a ∈ listIdeal x) (q : ℕ) (hq : q + y.length = x.length) :
    Nonempty (homology M x q ≃ₗ[R]
      idealAnnihilator (M ⧸ (Ideal.ofList y • ⊤ : Submodule R M)) (listIdeal x)) := by
  induction y generalizing M q with
  | nil =>
    have hqr : q = x.length := by simpa using hq
    subst q
    let e : (M ⧸ (Ideal.ofList ([] : List R) • ⊤ : Submodule R M)) ≃ₗ[R] M :=
      Submodule.quotEquivOfEqBot _ (by simp)
    exact ⟨(topHomologyAnnihilatorEquiv M x).trans (annihilatorEquiv M e.symm _)⟩
  | cons a y ih =>
    obtain ⟨ha, hy'⟩ := (RingTheory.Sequence.isWeaklyRegular_cons_iff M a y).mp hy
    obtain ⟨e⟩ := ih (QuotSMulTop a M) hy'
      (fun b hb => hI b (List.mem_cons_of_mem a hb)) (q+1) (by
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq)
    obtain ⟨f, hf, hfinj⟩ := reduction_connecting M x a (hI a List.mem_cons_self) ha q
    have hz : Subsingleton (homology M x (q+1)) :=
      homology_vanish_of_weaklyRegular M x (a :: y) hy hI (q+1) (by omega)
    let ef := LinearEquiv.ofBijective f ⟨hfinj hz, hf⟩
    let eq := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a y
    exact ⟨ef.symm.trans (e.trans (annihilatorEquiv _ eq.symm _))⟩

/-- RK-14, including the length estimate, vanishing, and the induced extremal
annihilator identification, with arbitrary coefficient modules. -/
theorem regularSequence_bound :
    Specs.AdvCommAlg.Koszul.RegularSequenceBound.regularSequenceBound.{u,v} := by
  intro R _ M _ _ I x y hx hnonzero hI hy
  subst I
  have hvan := homology_vanish_of_weaklyRegular M x y hy.toIsWeaklyRegular hI
  have hlen : y.length ≤ x.length := by
    by_contra h
    have : Subsingleton (homology M x 0) := hvan 0 (by omega)
    have : Nontrivial (M ⧸ listSubmodule M x) := hnonzero
    have : Nontrivial (homology M x 0) :=
      (homologyZeroEquiv M x).toEquiv.nontrivial
    exact not_subsingleton (homology M x 0) inferInstance
  refine ⟨hlen, ?_, ?_⟩
  · intro q hq
    exact hvan q (by omega)
  · exact extremal_homology_equiv M x y hy.toIsWeaklyRegular hI _ (by omega)

end AdvCommAlg.Koszul.RegularSequenceBound
