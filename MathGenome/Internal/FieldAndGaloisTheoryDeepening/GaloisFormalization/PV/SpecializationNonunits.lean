import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

namespace GaloisFormalization.PV

open Polynomial PrimeSpectrum

/-- An injective, finitely presented map of domains has image on spectra containing
a principal open neighborhood of the zero prime. -/
private theorem exists_basicOpen_subset_range_comap
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (f : R →+* S) (hf : f.FinitePresentation) (hinj : Function.Injective f) :
    ∃ d : R, d ≠ 0 ∧ (↑(basicOpen d) : Set (PrimeSpectrum R)) ⊆ Set.range (comap f) := by
  classical
  have hgeneric : (⊥ : PrimeSpectrum R) ∈ Set.range (comap f) := by
    refine ⟨⊥, PrimeSpectrum.ext ?_⟩
    simp only [comap_asIdeal, asIdeal_bot]
    exact (RingHom.injective_iff_ker_eq_bot f).mp hinj
  obtain ⟨data, hdata⟩ :=
    exists_constructibleSetData_iff.mpr (isConstructible_range_comap hf)
  rw [← hdata, ConstructibleSetData.toSet] at hgeneric
  simp only [Set.mem_iUnion] at hgeneric
  obtain ⟨piece, hpiece, hgeneric⟩ := hgeneric
  have hg : ∀ r ∈ Set.range piece.g, r = 0 := by
    intro r hr
    have h := hgeneric.1 hr
    simpa using h
  have hd : piece.f ≠ 0 := by
    simpa using hgeneric.2
  refine ⟨piece.f, hd, fun p hp ↦ ?_⟩
  rw [← hdata, ConstructibleSetData.toSet]
  refine Set.mem_iUnion₂.mpr ⟨piece, hpiece, ?_⟩
  rw [basicOpen_eq_zeroLocus_compl] at hp
  exact ⟨fun r hr ↦ (hg r hr).symm ▸ p.asIdeal.zero_mem, hp⟩

/-- Only finitely many base-field translates of a transcendental element are units. -/
theorem finite_unit_specializations
    {F : Type*} {B : Type*} [Field F] [Infinite F] [CommRing B] [IsDomain B]
    [Algebra F B] [Algebra.FiniteType F B] (t : B) (ht : Transcendental F t) :
    Set.Finite {a : F | IsUnit (t - algebraMap F B a)} := by
  let f : F[X] →+* B := (aeval t).toRingHom
  have hft : f.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := Polynomial.C)
    have heq : f.comp Polynomial.C = algebraMap F B := by
      ext a
      exact aeval_C t a
    rw [heq]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨d, hd, hopen⟩ := exists_basicOpen_subset_range_comap f
    (RingHom.FinitePresentation.of_finiteType.mp hft)
    (transcendental_iff_injective.mp ht)
  refine (finite_setOfPred_isRoot hd).subset ?_
  intro a ha
  by_contra hroot
  let p : PrimeSpectrum F[X] := ⟨RingHom.ker (evalRingHom a), RingHom.ker_isPrime _⟩
  have hp : p ∈ basicOpen d := hroot
  obtain ⟨q, hq⟩ := hopen hp
  have hmem : X - C a ∈ p.asIdeal := by
    change evalRingHom a (X - C a) = 0
    simp
  rw [← hq] at hmem
  have htmem : t - algebraMap F B a ∈ q.asIdeal := by
    change f (X - C a) ∈ q.asIdeal at hmem
    simpa [f] using hmem
  exact q.asIdeal.notMem_of_isUnit ha htmem

end GaloisFormalization.PV
