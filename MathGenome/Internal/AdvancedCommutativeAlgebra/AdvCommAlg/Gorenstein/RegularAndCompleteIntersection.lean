import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.RegularReduction
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.RegularAndCompleteIntersection
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-! GC-07: regular local rings and complete intersections, including the
empty regular sequence. Gorenstein means finite self-injective dimension. -/

noncomputable section
universe u
open CategoryTheory

namespace AdvCommAlg.Gorenstein

/-- Finite self-injective dimension is invariant under ring isomorphisms. -/
lemma localGorenstein_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing S] [IsLocalRing S]
    (e : R ≃+* S) : LocalGorenstein R ↔ LocalGorenstein S := by
  change injectiveDimension (ModuleCat.of R R) ≠ ⊤ ↔
    injectiveDimension (ModuleCat.of S S) ≠ ⊤
  rw [ModuleCat.injectiveDimension_eq_of_semiLinearEquiv
    (M := ModuleCat.of R R) (N := ModuleCat.of S S) e e.toSemilinearEquiv]

/-- Fields are self-injective, hence Gorenstein. -/
lemma field_gorenstein (K : Type u) [Field K] : LocalGorenstein K := by
  letI : Module.Injective K K := Module.injective_of_isSemisimpleRing K K
  letI := Module.injective_object_of_injective_module K K
  exact (finiteInjectiveDimension_iff_exists_bound K K).mpr ⟨0, inferInstance⟩

/-- Identify the module quotient used by the sequence API with the ring quotient,
linearly over that quotient ring. -/
def principalRingModuleEquiv {R : Type u} [CommRing R] (a : R) :
    QuotSMulTop a R ≃ₗ[R ⧸ Ideal.span {a}] (R ⧸ Ideal.span {a}) where
  toAddEquiv := (Submodule.quotEquivOfEq _ _ (by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])).toAddEquiv
  map_smul' q r := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    induction r using Submodule.Quotient.induction_on with
    | _ t => rfl

private lemma regularSequence_reduction (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      (x : List R) (hm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R),
      x.length = n → RegularSequence.RingRegular x →
      letI := sequenceQuotientLocalRing R x hm
      LocalGorenstein R ↔ LocalGorenstein (R ⧸ Ideal.ofList x) := by
  induction n with
  | zero =>
    intro R _ _ _ x hm hn _
    have hx : x = [] := List.length_eq_zero_iff.mp hn
    subst x
    letI := sequenceQuotientLocalRing R [] hm
    let e : (R ⧸ Ideal.ofList ([] : List R)) ≃+* R :=
      (Ideal.quotEquivOfEq Ideal.ofList_nil).trans (RingEquiv.quotientBot R)
    exact (localGorenstein_ringEquiv e).symm
  | succ n ih =>
    intro R _ _ _ x hm hn hx
    cases x with
    | nil => simp at hn
    | cons a x =>
      have ha := hm a (by simp)
      let Q := R ⧸ Ideal.span {a}
      letI := RegularReduction.quotientLocalRing a ha
      let y : List Q := x.map (Ideal.Quotient.mk (Ideal.span {a}))
      have hpair := (RingTheory.Sequence.isRegular_cons_iff' R a x).mp hx
      have hy : RegularSequence.RingRegular y :=
        ((principalRingModuleEquiv a).isRegular_congr y).mp hpair.2
      have hmQ : ∀ b ∈ y, b ∈ IsLocalRing.maximalIdeal Q := by
        intro b hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        letI := IsLocalHom.of_surjective
          (Ideal.Quotient.mk (Ideal.span {a})) Ideal.Quotient.mk_surjective
        exact map_nonunit _ c (hm c (by simp [hc]))
      have hylen : y.length = n := by simpa [y] using Nat.succ.inj hn
      letI := sequenceQuotientLocalRing Q y hmQ
      letI := sequenceQuotientLocalRing R (a :: x) hm
      let e : (Q ⧸ Ideal.ofList y) ≃+* (R ⧸ Ideal.ofList (a :: x)) :=
        (Ideal.quotEquivOfEq (Ideal.map_ofList _ x).symm).trans
          ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {a}) (Ideal.ofList x)).trans
            (Ideal.quotEquivOfEq (Ideal.ofList_cons a x).symm))
      exact (RegularReduction.localGorenstein_quotient_iff R a ha hpair.1).trans
        ((ih Q y hmQ hylen hy).trans (localGorenstein_ringEquiv e))

/-- Reduction by a finite regular sequence preserves and detects Gorensteinness.
For the empty list this is the ring isomorphism R/(0) ≃ R. -/
theorem localGorenstein_regularSequence_quotient_iff (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (x : List R)
    (hm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) (hx : RegularSequence.RingRegular x) :
    letI := sequenceQuotientLocalRing R x hm
    LocalGorenstein R ↔ LocalGorenstein (R ⧸ Ideal.ofList x) :=
  regularSequence_reduction x.length R x hm rfl hx

/-- A regular local ring reduces along regular maximal-ideal generators to
its residue field, which has self-injective dimension zero. -/
theorem regularLocal_gorenstein (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    LocalGorenstein R := by
  obtain ⟨x, hgen, _, hx⟩ := CohenMacaulay.exists_regular_generators R
  have hm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R := by
    intro a ha
    rw [← hgen]
    exact Ideal.subset_span ha
  letI := sequenceQuotientLocalRing R x hm
  let e : (R ⧸ Ideal.ofList x) ≃+* IsLocalRing.ResidueField R :=
    Ideal.quotEquivOfEq hgen
  exact (localGorenstein_regularSequence_quotient_iff R x hm hx).mpr
    ((localGorenstein_ringEquiv e).mpr (field_gorenstein _))

/-- Every quotient presentation of a complete intersection is Gorenstein. -/
theorem completeIntersection_gorenstein (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (x : List R)
    (hm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) (hx : RegularSequence.RingRegular x) :
    letI := sequenceQuotientLocalRing R x hm
    LocalGorenstein (R ⧸ Ideal.ofList x) :=
  (localGorenstein_regularSequence_quotient_iff R x hm hx).mp (regularLocal_gorenstein R)

/-- Gorensteinness transfers from a complete-intersection quotient to any
isomorphic presented local ring. -/
theorem gorenstein_of_completeIntersection_presentation (S : Type u) [CommRing S]
    [IsNoetherianRing S] [IsLocalRing S] (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (x : List R)
    (hm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) (hx : RegularSequence.RingRegular x)
    (e : (R ⧸ Ideal.ofList x) ≃+* S) : LocalGorenstein S := by
  letI := sequenceQuotientLocalRing R x hm
  exact (localGorenstein_ringEquiv e).mp (completeIntersection_gorenstein R x hm hx)

end AdvCommAlg.Gorenstein
