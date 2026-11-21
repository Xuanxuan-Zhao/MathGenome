import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SupportAndParameters

/-! CM-04, paper.tex:3301–3334. The additive dimension equation includes the
necessary length bound, also for empty lists and modules of dimension zero. -/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def regular_iff_dimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M → ∀ x : List R,
    (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) →
    (RingTheory.Sequence.IsRegular M x ↔
      dimensionValue R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) + x.length =
        dimensionValue R M)

def regular_iff_dimension_subType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M → ∀ (d : ℕ), dimensionValue R M = d →
    ∀ x : List R, (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) →
    (RingTheory.Sequence.IsRegular M x ↔ x.length ≤ d ∧
      dimensionValue R (M ⧸ (Ideal.ofList x • (⊤ : Submodule R M))) =
        ((d - x.length : ℕ) : WithBot ℕ∞))

def regular_prefix_cohenMacaulayType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M → ∀ x : List R,
    (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) →
    RingTheory.Sequence.IsRegular M x → ∀ i : ℕ,
    Nontrivial (M ⧸ (Ideal.ofList (x.take i) • (⊤ : Submodule R M))) ∧
    LocalCohenMacaulayValue R
      (M ⧸ (Ideal.ofList (x.take i) • (⊤ : Submodule R M)))

def regular_extend_systemOfParametersType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M → ∀ x : List R,
    (∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) →
    RingTheory.Sequence.IsRegular M x →
    ∃ y : List R, IsSystemOfParametersValue R M (x ++ y)

def localCohenMacaulay_iff_exists_regular_systemOfParametersType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M ↔ ∃ x : List R,
    IsSystemOfParametersValue R M x ∧ RingTheory.Sequence.IsRegular M x

def localCohenMacaulay_iff_every_systemOfParameters_regularType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
  LocalCohenMacaulayValue R M ↔ ∀ x : List R,
    IsSystemOfParametersValue R M x → RingTheory.Sequence.IsRegular M x

end AdvCommAlg.CohenMacaulay.Specs
