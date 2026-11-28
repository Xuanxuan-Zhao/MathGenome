import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.Characters
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic

/-! The Brauer character basis and the count of simple modules in MR05. -/

namespace RepTheorySurvey.Modular.MR05Spec

universe uG uO uK uI uV

open IsLocalRing (ResidueField)

set_option backward.isDefEq.respectTransparency false in
private theorem finiteRestrictedScalarsOfSimple {F A M : Type*}
    [Field F] [Ring A] [Algebra F A] [Module.Finite F A]
    [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Module.Finite F (RestrictScalars F A M) := by
  let _ : Module A (RestrictScalars F A M) := RestrictScalars.moduleOrig F A M
  let _ : IsSimpleModule A (RestrictScalars F A M) := ‹IsSimpleModule A M›
  exact Module.Finite.trans A (RestrictScalars F A M)

set_option backward.isDefEq.respectTransparency false in
/-- The lifted Brauer characters of a complete, irredundant family of simple modules
form a basis of the fraction-field-valued functions on the regular classes.
The module universe contains the residue-field universe so it contains all simple types
up to isomorphism, including the columns of the split matrix factors. -/
def brauerCharacterBasisType : Prop :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (system : MR01Spec.SplittingSystemData G p O K)
    {ι : Type uI} (S : ι → ModuleCat.{max uO uV} (MonoidAlgebra (ResidueField O) G)),
    ∀ (hS : MR01Spec.SimpleRepresentativeFamily S),
    ∃ b : Module.Basis ι K (MR03Spec.pRegularConjClassesValue G p → K),
      ∀ i c,
        letI := hS.simple i
        letI := finiteRestrictedScalarsOfSimple (F := ResidueField O)
          (A := MonoidAlgebra (ResidueField O) G) (M := S i)
        b i c = algebraMap O K (MR03Spec.brauerClassCharacterValue system (S i) c)

/-- The number of simple labels equals the number of regular conjugacy classes. -/
def cardSimpleRepresentativesType : Prop :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (_ : MR01Spec.SplittingSystemData G p O K)
    {ι : Type uI} (S : ι → ModuleCat.{max uO uV} (MonoidAlgebra (ResidueField O) G)),
    MR01Spec.SimpleRepresentativeFamily S →
    Finite ι ∧ Nat.card ι = Nat.card (MR03Spec.pRegularConjClassesValue G p)

end RepTheorySurvey.Modular.MR05Spec
