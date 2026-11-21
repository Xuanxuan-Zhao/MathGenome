import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.SpectrumFunctorQuotient

universe u v w

namespace P103.Ch04.SpectrumFunctorQuotient

theorem contraction_asIdeal :
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A) (q : PrimeSpectrum A),
    (PrimeSpectrum.comap g q).asIdeal = Ideal.comap g q.asIdeal := by
  intro R A _ _ g q
  rfl

theorem contraction_membership :
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A) (q : PrimeSpectrum A) (f : R),
    f ∈ (PrimeSpectrum.comap g q).asIdeal ↔ g f ∈ q.asIdeal := by
  intro R A _ _ g q f
  rfl

theorem contraction_continuous :
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), Continuous (PrimeSpectrum.comap g) := by
  intro R A _ _ g
  exact PrimeSpectrum.continuous_comap g

theorem principal_preimage :
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A) (f : R),
    PrimeSpectrum.comap g ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (g f) : Set (PrimeSpectrum A)) := by
  intro R A _ _ g f
  rfl

theorem contraction_identity :
  ∀ (R : Type u) [CommRing R],
    PrimeSpectrum.comap (RingHom.id R) = id := by
  intro R _
  rfl

theorem contraction_composition :
  ∀ (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B] (g : R →+* A) (h : A →+* B),
    PrimeSpectrum.comap (h.comp g) = PrimeSpectrum.comap g ∘ PrimeSpectrum.comap h := by
  intro R A B _ _ _ g h
  rfl

theorem quotient_range :
  ∀ (R : Type u) [CommRing R] (I : Ideal R),
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  intro R _ I
  simpa only [Ideal.mk_ker] using
    range_comap_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective

theorem quotient_homeomorphism :
  ∀ (R : Type u) [CommRing R] (I : Ideal R),
    ∃ e : PrimeSpectrum (R ⧸ I) ≃ₜ
        {p : PrimeSpectrum R // p ∈ PrimeSpectrum.zeroLocus (I : Set R)},
      (∀ q, (e q).val = PrimeSpectrum.comap (Ideal.Quotient.mk I) q) ∧
      (∀ p, (e.symm p).asIdeal = p.val.asIdeal.map (Ideal.Quotient.mk I)) := by
  intro R _ I
  -- The ideal correspondence has contraction as forward map and ideal image
  -- as inverse. The quotient map is surjective, including when I is the unit ideal.
  let e := I.primeSpectrumQuotientOrderIsoZeroLocus.toEquiv
  have he : Topology.IsInducing e := by
    apply Topology.IsInducing.subtypeVal.of_comp_iff.mp
    exact PrimeSpectrum.comap_isInducing_of_surjective (R ⧸ I)
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact ⟨e.toHomeomorphOfIsInducing he, (fun _ => rfl), (fun _ => rfl)⟩

end P103.Ch04.SpectrumFunctorQuotient
