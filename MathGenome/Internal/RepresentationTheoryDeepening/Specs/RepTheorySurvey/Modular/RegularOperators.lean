import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SplittingSystem
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Independent specifications for the operator assertions of MR02 and MR04. -/

namespace RepTheorySurvey.Modular.MR02Spec

universe uG uO uK uV

/-- All eigenvalues are `n`-th roots of unity, and the operator has a basis of
eigenvectors labeled by those roots. -/
def HasRootEigenbasis {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (n : ℕ) (T : Module.End F V) : Prop :=
  (∀ μ : F, T.HasEigenvalue μ → ∃ u : rootsOfUnity n F, u.val.val = μ) ∧
    ∃ (b : Module.Basis (Fin (Module.finrank F V)) F V)
      (eigenvalues : Fin (Module.finrank F V) → rootsOfUnity n F),
      ∀ i, T (b i) = (eigenvalues i).val.val • b i

set_option backward.isDefEq.respectTransparency false in
/-- The action of a `p`-regular element on a finite-dimensional residue-field module. -/
def residueEigenbasis :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K],
    MR01Spec.SplittingSystemData G p O K →
    ∀ (g : MR01Spec.pRegularValue G p) (M : Type uV) [AddCommGroup M]
      [Module (MonoidAlgebra (IsLocalRing.ResidueField O) G) M]
      [FiniteDimensional (IsLocalRing.ResidueField O)
        (RestrictScalars (IsLocalRing.ResidueField O)
          (MonoidAlgebra (IsLocalRing.ResidueField O) G) M)],
      HasRootEigenbasis (MR01Spec.primeToPartValue G p)
        (Representation.ofModule (k := IsLocalRing.ResidueField O) (G := G) M g.val)

set_option backward.isDefEq.respectTransparency false in
/-- The action of a `p`-regular element on a finite-dimensional fraction-field module. -/
def fractionEigenbasis :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K],
    MR01Spec.SplittingSystemData G p O K →
    ∀ (g : MR01Spec.pRegularValue G p) (M : Type uV) [AddCommGroup M]
      [Module (MonoidAlgebra K G) M] [FiniteDimensional K (RestrictScalars K (MonoidAlgebra K G) M)],
      HasRootEigenbasis (MR01Spec.primeToPartValue G p)
        (Representation.ofModule (k := K) (G := G) M g.val)

end RepTheorySurvey.Modular.MR02Spec
