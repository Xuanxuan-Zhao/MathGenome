import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.OpenRegularLocus
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DenseRegularOpen
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalLocalization
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

namespace CommutativeAlgebraNotes.Excellence

open PrimeSpectrum Set Topology TopologicalSpace RingTheory.Sequence
open AdvCommAlg.CohenMacaulay

universe u v

section LocalAlgebra

variable {A : Type v} [CommRing A]

private theorem isSMulRegular_quotient_iff (I : Ideal A) (x : A) :
    IsSMulRegular (A ⧸ I) (Ideal.Quotient.mk I x) ↔ I.colon {x} ≤ I := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  constructor
  · intro h y hy
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply h
    rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, mul_comm]
    exact Submodule.mem_colon_singleton.mp hy
  · intro h y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [smul_eq_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.Quotient.eq_zero_iff_mem, mul_comm]
    exact fun hy ↦ h (Submodule.mem_colon_singleton.mpr hy)

private theorem weaklyRegular_iff_colon (xs : List A) :
    IsWeaklyRegular A xs ↔
      ∀ (i : ℕ) (_ : i < xs.length), (Ideal.ofList (xs.take i)).colon {xs[i]} ≤
        Ideal.ofList (xs.take i) := by
  rw [isWeaklyRegular_iff]
  have hmul (I : Ideal A) : I • (⊤ : Submodule A A) = I := Ideal.mul_top I
  apply forall₂_congr
  intro i hi
  rw [hmul]
  exact isSMulRegular_quotient_iff _ _

/-- Regularity lifts across a quotient by a weakly regular list in the maximal ideal. -/
private theorem regularLocal_of_weaklyRegular_quotient [IsNoetherianRing A] [IsLocalRing A]
    (xs : List A) (hmem : Ideal.ofList xs ≤ IsLocalRing.maximalIdeal A)
    (hreg : IsWeaklyRegular A xs) (hquot : IsRegularLocalRing (A ⧸ Ideal.ofList xs)) :
    IsRegularLocalRing A := by
  induction xs using List.reverseRecOn with
  | nil =>
    have : IsRegularLocalRing (A ⧸ (⊥ : Ideal A)) := by
      rw [← Ideal.ofList_nil]
      exact hquot
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot A)
  | append_singleton xs x ih =>
    rw [Ideal.ofList_append, Ideal.ofList_singleton] at hmem hquot
    let I := Ideal.ofList xs
    let f := Ideal.Quotient.mk I
    have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top (sup_le_iff.mp hmem).1)
    have : IsLocalRing (A ⧸ I) := .of_surjective' f Ideal.Quotient.mk_surjective
    have : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
    have hx : x ∈ IsLocalRing.maximalIdeal A :=
      (sup_le_iff.mp hmem).2 (Ideal.subset_span (Set.mem_singleton x))
    have hx' : f x ∈ IsLocalRing.maximalIdeal (A ⧸ I) := by
      change x ∈ (IsLocalRing.maximalIdeal (A ⧸ I)).comap f
      rwa [IsLocalRing.maximalIdeal_comap]
    obtain ⟨hxs, hxreg⟩ := (isWeaklyRegular_append_iff A xs [x]).mp hreg
    have hmul : I • (⊤ : Submodule A A) = I := Ideal.mul_top I
    rw [isWeaklyRegular_singleton_iff, hmul] at hxreg
    have := hquot
    have : IsRegularLocalRing ((A ⧸ I) ⧸ Ideal.span {f x}) := by
      have e := (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {x})).symm
      rw [Ideal.map_span, Set.image_singleton] at e
      exact IsRegularLocalRing.of_ringEquiv e
    exact ih (sup_le_iff.mp hmem).1 hxs (regularLocal_of_regular_quotient (f x) hx' hxreg)

private theorem map_colon_singleton {M : Submonoid A} {B : Type*} [CommRing B]
    [Algebra A B] [IsLocalization M B] (I : Ideal A) (x : A) :
    (I.colon {x}).map (algebraMap A B) =
      (I.map (algebraMap A B)).colon {algebraMap A B x} := by
  ext y
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M y
  have hmul : IsLocalization.mk' B a s * algebraMap A B x = IsLocalization.mk' B (a * x) s := by
    rw [← IsLocalization.mk'_one (M := M) (S := B) x, ← IsLocalization.mk'_mul, mul_one]
  rw [Submodule.mem_colon_singleton, smul_eq_mul, hmul,
    IsLocalization.mk'_mem_map_algebraMap_iff M, IsLocalization.mk'_mem_map_algebraMap_iff M]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc]

/-- Generators of an extended ideal can be represented by numerators. -/
private theorem exists_list_numerators {M : Submonoid A} {B : Type*} [CommRing B]
    [Algebra A B] [IsLocalization M B] (ys : List B) :
    ∃ xs : List A, xs.length = ys.length ∧
      Ideal.ofList (xs.map (algebraMap A B)) = Ideal.ofList ys := by
  induction ys with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons y ys ih =>
    obtain ⟨xs, hlen, hspan⟩ := ih
    obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M y
    refine ⟨a :: xs, by simp [hlen], ?_⟩
    rw [List.map_cons, Ideal.ofList_cons, Ideal.ofList_cons, hspan]
    congr 1
    rw [← ha]
    exact Ideal.span_singleton_mul_right_unit (IsLocalization.map_units B s) y

end LocalAlgebra

section Spectrum

variable {A : Type v} [CommRing A]

private abbrev extendIdeal (q : PrimeSpectrum A) (I : Ideal A) :
    Ideal (Localization.AtPrime q.asIdeal) :=
  I.map (algebraMap A (Localization.AtPrime q.asIdeal))

private theorem isOpen_extendedIdeal_le [IsNoetherianRing A] (I J : Ideal A) :
    IsOpen {q : PrimeSpectrum A | extendIdeal q I ≤ extendIdeal q J} := by
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
  have hmem (a : A) :
      {q : PrimeSpectrum A | algebraMap A (Localization.AtPrime q.asIdeal) a ∈
        extendIdeal q J} = ⋃ b : {b : A // b * a ∈ J}, (basicOpen b.val : Set _) := by
    ext q
    simp only [mem_ofPred_eq, mem_iUnion, SetLike.mem_coe, mem_basicOpen, Subtype.exists, exists_prop]
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.asIdeal.primeCompl]
    simp only [Ideal.mem_primeCompl_iff]
    exact exists_congr fun _ ↦ and_comm
  have he : {q : PrimeSpectrum A | extendIdeal q I ≤ extendIdeal q J} =
      ⋂ a ∈ s, {q : PrimeSpectrum A | algebraMap A (Localization.AtPrime q.asIdeal) a ∈
        extendIdeal q J} := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter]
    rw [Ideal.map_le_iff_le_comap]
    rw [← hs, Submodule.span_le]
    rfl
  rw [he]
  exact isOpen_biInter_finset fun a _ ↦ (hmem a).symm ▸ isOpen_iUnion fun _ ↦ isOpen_basicOpen

private theorem isOpen_weaklyRegular [IsNoetherianRing A] (xs : List A) :
    IsOpen {q : PrimeSpectrum A |
      IsWeaklyRegular (Localization.AtPrime q.asIdeal)
        (xs.map (algebraMap A (Localization.AtPrime q.asIdeal)))} := by
  have he : {q : PrimeSpectrum A |
      IsWeaklyRegular (Localization.AtPrime q.asIdeal)
        (xs.map (algebraMap A (Localization.AtPrime q.asIdeal)))} =
      ⋂ i : Fin xs.length, {q : PrimeSpectrum A |
        extendIdeal q ((Ideal.ofList (xs.take i)).colon {xs[i.val]}) ≤
          extendIdeal q (Ideal.ofList (xs.take i))} := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter, weaklyRegular_iff_colon, Fin.forall_iff,
      extendIdeal, map_colon_singleton (M := q.asIdeal.primeCompl), ← List.map_take,
      Ideal.map_ofList, List.getElem_map, List.length_map]
  rw [he]
  exact isOpen_iInter_of_finite fun _ ↦ isOpen_extendedIdeal_le _ _

private theorem regularLocus_of_le {p q : PrimeSpectrum A} (hpq : p ≤ q)
    (hq : q ∈ regularLocus A) : p ∈ regularLocus A := by
  let B := Localization.AtPrime q.asIdeal
  let Q := extendIdeal q p.asIdeal
  have hd : Disjoint (q.asIdeal.primeCompl : Set A) (p.asIdeal : Set A) := by
    rw [Set.disjoint_left]
    exact fun _ ha hb ↦ ha (hpq hb)
  have : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.asIdeal.primeCompl B p.asIdeal p.isPrime hd
  have hQ : Q.comap (algebraMap A B) = p.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint q.asIdeal.primeCompl B p.isPrime hd
  have hM : (Q.comap (algebraMap A B)).primeCompl = p.asIdeal.primeCompl := by
    ext a
    simp only [Ideal.mem_primeCompl_iff, hQ]
  have : IsLocalization p.asIdeal.primeCompl (Localization.AtPrime Q) := by
    rw [← hM]
    exact IsLocalization.isLocalization_atPrime_localization_atPrime q.asIdeal.primeCompl Q
  have : IsRegularLocalRing B := hq
  have : IsRegularLocalRing (Localization.AtPrime Q) := regularLocal_localization_atPrime B Q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime Q)
      (Localization.AtPrime p.asIdeal)).toRingEquiv

private theorem regularLocal_quotient_atPrime (I : Ideal A) (q : PrimeSpectrum (A ⧸ I))
    (hq : q ∈ regularLocus (A ⧸ I)) :
    IsRegularLocalRing
      (Localization.AtPrime (comap (Ideal.Quotient.mk I) q).asIdeal ⧸
        extendIdeal (comap (Ideal.Quotient.mk I) q) I) := by
  let p := comap (Ideal.Quotient.mk I) q
  let B := Localization.AtPrime p.asIdeal ⧸ extendIdeal p I
  have hmon : Algebra.algebraMapSubmonoid (A ⧸ I) p.asIdeal.primeCompl = q.asIdeal.primeCompl :=
    q.asIdeal.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalization.AtPrime B q.asIdeal := by
    rw [IsLocalization.AtPrime, ← hmon]
    infer_instance
  have : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := hq
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) B).toRingEquiv

private theorem exists_regularOpen_on_closure [IsNoetherianRing A] (p : PrimeSpectrum A)
    (hp : p ∈ regularLocus A) (hquot : Specs.HasNonemptyRegularOpen (A ⧸ p.asIdeal)) :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧ p ∈ U ∧
      closure {p} ∩ U ⊆ regularLocus A := by
  let B := Localization.AtPrime p.asIdeal
  let f := Ideal.Quotient.mk p.asIdeal
  have : IsRegularLocalRing B := hp
  obtain ⟨ys, hgen, hdim, _⟩ := exists_regular_generators B
  obtain ⟨xs, hlen, hspan⟩ := exists_list_numerators (M := p.asIdeal.primeCompl) ys
  let J := Ideal.ofList xs
  have he : Ideal.ofList (xs.map (algebraMap A B)) = IsLocalRing.maximalIdeal B :=
    hspan.trans hgen
  have hpgen : extendIdeal p J = extendIdeal p p.asIdeal := by
    change (Ideal.ofList xs).map (algebraMap A B) = p.asIdeal.map (algebraMap A B)
    rw [Ideal.map_ofList, he, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have hJ : J ≤ p.asIdeal := by
    change Ideal.ofList xs ≤ p.asIdeal
    rw [← IsLocalization.AtPrime.under_maximalIdeal B p.asIdeal, ← he, ← Ideal.map_ofList]
    exact Ideal.le_comap_map
  let V := {q : PrimeSpectrum A | extendIdeal q p.asIdeal ≤ extendIdeal q J}
  let W := {q : PrimeSpectrum A | IsWeaklyRegular (Localization.AtPrime q.asIdeal)
    (xs.map (algebraMap A (Localization.AtPrime q.asIdeal)))}
  have hpV : p ∈ V := hpgen.ge
  have hpW : p ∈ W :=
    (regular_generatingList B ys.length _ hdim (by simpa using hlen) he).toIsWeaklyRegular
  obtain ⟨U, hU, hUne, hUreg⟩ := hquot
  have hInd := comap_isInducing_of_surjective (A ⧸ p.asIdeal) f Ideal.Quotient.mk_surjective
  obtain ⟨U', hU', hpre⟩ := hInd.isOpen_iff.mp hU
  let η : PrimeSpectrum (A ⧸ p.asIdeal) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : IsGenericPoint η univ := by
    rw [IsGenericPoint, PrimeSpectrum.closure_singleton]
    exact zeroLocus_bot
  have hηU : η ∈ U := (hη.mem_open_set_iff hU).mpr (by simpa using hUne)
  have hηp : comap f η = p := PrimeSpectrum.ext (Ideal.mk_ker)
  have hη' : η ∈ comap f ⁻¹' U' := hpre.symm ▸ hηU
  have hpU' : p ∈ U' := hηp ▸ hη'
  refine ⟨U' ∩ (V ∩ W), hU'.inter
    ((isOpen_extendedIdeal_le _ _).inter (isOpen_weaklyRegular xs)), ⟨hpU', hpV, hpW⟩, ?_⟩
  rintro q ⟨hqp, hqU', hqV, hqW⟩
  rw [PrimeSpectrum.closure_singleton, ← Ideal.mk_ker (I := p.asIdeal), ←
    range_comap_of_surjective _ f Ideal.Quotient.mk_surjective] at hqp
  obtain ⟨q', rfl⟩ := hqp
  have hq'U : q' ∈ U := hpre ▸ (show q' ∈ comap f ⁻¹' U' from hqU')
  let q := comap f q'
  let C := Localization.AtPrime q.asIdeal
  have hpq : p.asIdeal ≤ q.asIdeal := Ideal.mk_ker.symm.le.trans (Ideal.ker_le_comap f)
  have hEq : extendIdeal q J = extendIdeal q p.asIdeal :=
    (Ideal.map_mono hJ).antisymm hqV
  refine regularLocal_of_weaklyRegular_quotient (xs.map (algebraMap A C)) ?_ hqW ?_
  · rw [← Ideal.map_ofList]
    change extendIdeal q J ≤ IsLocalRing.maximalIdeal C
    rw [hEq, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hpq
  · rw [← Ideal.map_ofList]
    change IsRegularLocalRing (C ⧸ extendIdeal q J)
    rw [hEq]
    exact regularLocal_quotient_atPrime p.asIdeal q' (hUreg hq'U)

/-- The singular set is closed by induction on closed subsets of the spectrum. -/
private theorem isOpen_regularLocus_of_primeQuotients [IsNoetherianRing A]
    (hquot : ∀ p : PrimeSpectrum A, Specs.HasNonemptyRegularOpen (A ⧸ p.asIdeal)) :
    IsOpen (regularLocus A) := by
  classical
  let S := (regularLocus A)ᶜ
  have hclosed (C : Closeds (PrimeSpectrum A)) : IsClosed (S ∩ (C : Set (PrimeSpectrum A))) := by
    refine wellFounded_lt.induction (C := fun D : Closeds (PrimeSpectrum A) ↦
      IsClosed (S ∩ (D : Set (PrimeSpectrum A)))) C ?_
    clear C
    intro C ih
    by_cases hne : (C : Set (PrimeSpectrum A)).Nonempty
    · by_cases hirr : IsPreirreducible (C : Set (PrimeSpectrum A))
      · obtain ⟨p, hp⟩ := QuasiSober.sober ⟨hne, hirr⟩ C.isClosed
        by_cases hreg : p ∈ regularLocus A
        · obtain ⟨U, hU, hpU, hsub⟩ := exists_regularOpen_on_closure p hreg (hquot p)
          rw [hp.def] at hsub
          let C' : Closeds (PrimeSpectrum A) := ⟨(C : Set (PrimeSpectrum A)) ∩ Uᶜ, C.isClosed.inter hU.isClosed_compl⟩
          have hlt : C' < C := lt_of_le_not_ge inter_subset_left fun h ↦
            (h hp.mem).2 hpU
          convert ih C' hlt using 1
          ext q
          change (q ∈ S ∧ q ∈ C) ↔ q ∈ S ∧ q ∈ C ∧ q ∉ U
          exact ⟨fun ⟨hs, hc⟩ ↦ ⟨hs, hc, fun hu ↦ hs (hsub ⟨hc, hu⟩)⟩,
            fun ⟨hs, hc, _⟩ ↦ ⟨hs, hc⟩⟩
        · have hsub : (C : Set (PrimeSpectrum A)) ⊆ S := fun q hq hqreg ↦
            hreg (regularLocus_of_le ((le_iff_specializes _ _).mpr (hp.specializes hq)) hqreg)
          rw [inter_eq_right.mpr hsub]
          exact C.isClosed
      · rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
        push Not at hirr
        obtain ⟨Z₁, Z₂, hZ₁, hZ₂, hcover, hn₁, hn₂⟩ := hirr
        let C₁ : Closeds (PrimeSpectrum A) := ⟨(C : Set (PrimeSpectrum A)) ∩ Z₁, C.isClosed.inter hZ₁⟩
        let C₂ : Closeds (PrimeSpectrum A) := ⟨(C : Set (PrimeSpectrum A)) ∩ Z₂, C.isClosed.inter hZ₂⟩
        have hlt₁ : C₁ < C := lt_of_le_not_ge inter_subset_left fun h ↦
          hn₁ (fun q hq ↦ (h hq).2)
        have hlt₂ : C₂ < C := lt_of_le_not_ge inter_subset_left fun h ↦
          hn₂ (fun q hq ↦ (h hq).2)
        have hEq : (C : Set (PrimeSpectrum A)) = (C₁ : Set (PrimeSpectrum A)) ∪ (C₂ : Set (PrimeSpectrum A)) := by
          change (C : Set (PrimeSpectrum A)) = (C : Set (PrimeSpectrum A)) ∩ Z₁ ∪ (C : Set (PrimeSpectrum A)) ∩ Z₂
          rw [← inter_union_distrib_left, inter_eq_left.mpr hcover]
        rw [hEq, inter_union_distrib_left]
        exact (ih C₁ hlt₁).union (ih C₂ hlt₂)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, inter_empty]
      exact isClosed_empty
  exact isClosed_compl_iff.mp (by simpa [S] using hclosed ⊤)

end Spectrum

/-- The regular locus of a finite-type algebra over a field is open. -/
theorem isOpen_regularLocus_field : Specs.isOpen_regularLocus_fieldType.{u,v} := by
  intro k A _ _ _ _
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  exact isOpen_regularLocus_of_primeQuotients fun p ↦
    denseRegularOpen_field k (A ⧸ p.asIdeal)

/-- The regular locus of a finite-type algebra over the integers is open. -/
theorem isOpen_regularLocus_int : Specs.isOpen_regularLocus_intType.{v} := by
  intro A _ _
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  apply isOpen_regularLocus_of_primeQuotients
  intro p
  have hfinite : Algebra.FiniteType ℤ (A ⧸ p.asIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mk p.asIdeal).toIntAlgHom
      Ideal.Quotient.mk_surjective
  exact @denseRegularOpen_int (A ⧸ p.asIdeal) _ _ hfinite

/-- The regular locus of a finite-type algebra over a Noetherian complete local ring is open. -/
theorem isOpen_regularLocus_completeLocal : Specs.isOpen_regularLocus_completeLocalType.{u,v} := by
  intro R A _ _ _ _ _ _ _
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  exact isOpen_regularLocus_of_primeQuotients fun p ↦
    denseRegularOpen_completeLocal R (A ⧸ p.asIdeal)

end CommutativeAlgebraNotes.Excellence
