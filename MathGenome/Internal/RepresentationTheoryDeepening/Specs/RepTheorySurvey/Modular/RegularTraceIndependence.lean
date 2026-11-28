import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.SplittingSystem
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Trace

/-! The residue-field trace independence used in Theorem MR05. -/

namespace RepTheorySurvey.Modular.MR05ModularTracesSpec

universe uG uO uK uI uV

/-- The traces of the simple modules, restricted to the `p`-regular elements, are
linearly independent over the residue field of the splitting system. -/
def regularTraceLinearIndependent :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K]
    (_ : MR01Spec.SplittingSystemData G p O K)
    {ι : Type uI} (S : ι → ModuleCat.{uV} (MonoidAlgebra (IsLocalRing.ResidueField O) G)),
    MR01Spec.SimpleRepresentativeFamily S →
    LinearIndependent (IsLocalRing.ResidueField O)
      (fun i (g : MR01Spec.pRegularValue G p) =>
        LinearMap.trace (IsLocalRing.ResidueField O) _
          (Representation.ofModule (k := IsLocalRing.ResidueField O) (S i) g.val))

end RepTheorySurvey.Modular.MR05ModularTracesSpec
