import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.RadicalZariski

/-! Independent statements for the first two assertions of paper.tex,
Theorem 4.4 (and the principal-open inverse-image formula in its proof).
All rings are commutative and unital, all maps preserve one, and no
nontriviality or injectivity hypotheses are imposed. `zeroLocus I` is V(I)
and `basicOpen f` is D(f), as in the upstream Zariski interface. -/

universe u v w

namespace Specs.P103.Ch04.SpectrumFunctorQuotient

def contraction_asIdeal : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A) (q : PrimeSpectrum A),
    (PrimeSpectrum.comap g q).asIdeal = Ideal.comap g q.asIdeal

def contraction_membership : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A) (q : PrimeSpectrum A) (f : R),
    f ∈ (PrimeSpectrum.comap g q).asIdeal ↔ g f ∈ q.asIdeal

def contraction_continuous : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A), Continuous (PrimeSpectrum.comap g)

def principal_preimage : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (g : R →+* A) (f : R),
    PrimeSpectrum.comap g ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen (g f) : Set (PrimeSpectrum A))

def contraction_identity : Prop :=
  ∀ (R : Type u) [CommRing R],
    PrimeSpectrum.comap (RingHom.id R) = id

def contraction_composition : Prop :=
  ∀ (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B] (g : R →+* A) (h : A →+* B),
    PrimeSpectrum.comap (h.comp g) = PrimeSpectrum.comap g ∘ PrimeSpectrum.comap h

def quotient_range : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R),
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set R)

/-- The subspace topology is the inherited topology on this subtype.
The two formulas specify the forward map and inverse, not merely the existence
of some homeomorphism. Universality includes I = R and the zero ring. -/
def quotient_homeomorphism : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Ideal R),
    ∃ e : PrimeSpectrum (R ⧸ I) ≃ₜ
        {p : PrimeSpectrum R // p ∈ PrimeSpectrum.zeroLocus (I : Set R)},
      (∀ q, (e q).val = PrimeSpectrum.comap (Ideal.Quotient.mk I) q) ∧
      (∀ p, (e.symm p).asIdeal = p.val.asIdeal.map (Ideal.Quotient.mk I))

end Specs.P103.Ch04.SpectrumFunctorQuotient
