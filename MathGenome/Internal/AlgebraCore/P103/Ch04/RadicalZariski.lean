import MathGenome.Internal.AlgebraCore.Specs.P103.Ch04.RadicalZariski

universe u v

/-! The radical, nilradical and principal opens of an arbitrary commutative
unital ring, including the zero ring. No nontriviality assumption is used. -/

namespace P103.Ch04.RadicalZariski

theorem radical_membership_positive :
  ∀ (R : Type u) [CommRing R] (I : Ideal R) (a : R),
    a ∈ I.radical ↔ ∃ n : ℕ, 1 ≤ n ∧ a ^ n ∈ I := by
  intro R _ I a
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp h
    cases n with
    | zero =>
      have hI : I = ⊤ := (Ideal.eq_top_iff_one I).mpr (by simpa using hn)
      exact ⟨1, le_rfl, by simp [hI]⟩
    | succ n => exact ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hn⟩
  · rintro ⟨n, _, hn⟩
    exact Ideal.mem_radical_iff.mpr ⟨n, hn⟩

theorem radical_eq_prime_intersection :
  ∀ (R : Type u) [CommRing R] (I : Ideal R),
    I.radical = sInf {p : Ideal R | I ≤ p ∧ p.IsPrime} := by
  intro R _ I
  exact Ideal.radical_eq_sInf I

theorem prime_is_proper :
  ∀ (R : Type u) [CommRing R] (p : PrimeSpectrum R), p.asIdeal ≠ ⊤ := by
  intro R _ p
  exact p.isPrime.ne_top

theorem empty_ideal_intersection :
  ∀ (R : Type u) [CommRing R], sInf (∅ : Set (Ideal R)) = ⊤ := by
  intro R _
  exact sInf_empty

theorem nilradical_eq_radical_zero :
  ∀ (R : Type u) [CommRing R], nilradical R = (⊥ : Ideal R).radical := by
  intro R _
  rfl

theorem nilradical_membership :
  ∀ (R : Type u) [CommRing R] (a : R),
    a ∈ nilradical R ↔ IsNilpotent a := by
  intro R _ a
  exact mem_nilradical

theorem vanishing_membership :
  ∀ (R : Type u) [CommRing R] (I : Ideal R) (p : PrimeSpectrum R),
    p ∈ PrimeSpectrum.zeroLocus (I : Set R) ↔ I ≤ p.asIdeal := by
  intro R _ I p
  rfl

theorem principal_membership :
  ∀ (R : Type u) [CommRing R] (f : R) (p : PrimeSpectrum R),
    p ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ↔ f ∉ p.asIdeal := by
  intro R _ f p
  rfl

theorem vanishing_iSup :
  ∀ (R : Type u) [CommRing R] (ι : Sort v) (I : ι → Ideal R),
    (⋂ i, PrimeSpectrum.zeroLocus (I i : Set R)) =
      PrimeSpectrum.zeroLocus ((⨆ i, I i : Ideal R) : Set R) := by
  intro R _ ι I
  exact (PrimeSpectrum.zeroLocus_iSup I).symm

theorem vanishing_union :
  ∀ (R : Type u) [CommRing R] (I J : Ideal R),
    PrimeSpectrum.zeroLocus (I : Set R) ∪ PrimeSpectrum.zeroLocus (J : Set R) =
      PrimeSpectrum.zeroLocus ((I * J : Ideal R) : Set R) := by
  intro R _ I J
  exact (PrimeSpectrum.zeroLocus_mul I J).symm

theorem vanishing_zero :
  ∀ (R : Type u) [CommRing R],
    PrimeSpectrum.zeroLocus ((⊥ : Ideal R) : Set R) = Set.univ := by
  intro R _
  exact PrimeSpectrum.zeroLocus_bot

theorem vanishing_unit :
  ∀ (R : Type u) [CommRing R],
    PrimeSpectrum.zeroLocus ((⊤ : Ideal R) : Set R) = ∅ := by
  intro R _
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr rfl

theorem closed_iff_vanishing :
  ∀ (R : Type u) [CommRing R] (Z : Set (PrimeSpectrum R)),
    IsClosed Z ↔ ∃ I : Ideal R, Z = PrimeSpectrum.zeroLocus (I : Set R) := by
  intro R _ Z
  exact PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z

theorem principal_mul :
  ∀ (R : Type u) [CommRing R] (f g : R),
    (PrimeSpectrum.basicOpen (f * g) : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ∩
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) := by
  intro R _ f g
  exact congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) => (U : Set (PrimeSpectrum R)))
    (PrimeSpectrum.basicOpen_mul f g)

theorem principal_basis :
  ∀ (R : Type u) [CommRing R],
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : R => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R))) := by
  intro R _
  exact PrimeSpectrum.isTopologicalBasis_basic_opens

theorem principal_zero :
  ∀ (R : Type u) [CommRing R],
    (PrimeSpectrum.basicOpen (0 : R) : Set (PrimeSpectrum R)) = ∅ := by
  intro R _
  simp only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot]

theorem principal_one :
  ∀ (R : Type u) [CommRing R],
    (PrimeSpectrum.basicOpen (1 : R) : Set (PrimeSpectrum R)) = Set.univ := by
  intro R _
  simp only [PrimeSpectrum.basicOpen_one, TopologicalSpace.Opens.coe_top]

theorem spectrum_zero_ring :
  ∀ (R : Type u) [CommRing R] [Subsingleton R], IsEmpty (PrimeSpectrum R) := by
  intro R _ _
  infer_instance

end P103.Ch04.RadicalZariski
