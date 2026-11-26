import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent

namespace LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedTorusTorsors

open MaximalUnramifiedBrauer
open LinearAlgebraicGroups.Descent.NonabelianCohomology
open LinearAlgebraicGroups.Specs.Fppf
open LinearAlgebraicGroups.Specs.CharacterDescent

universe u

/-- Every torus over the maximal unramified extension of a nonarchimedean local
field has trivial first Galois cohomology. -/
def TorusVanishing : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    let K := maximalUnramified F
    ∀ (S : Type u) [Field S] [Algebra K S] [IsSepClosure K S]
      (A : LinearAlgebraicGroups.HopfAlgebraCategory K), IsTorus A →
      ∀ x : groupH1 K (LinearAlgebraicGroups.specGroup A).X S,
        x = groupBasepoint K (LinearAlgebraicGroups.specGroup A).X S

/-- Every right fppf torsor under such a torus has a rational point. -/
def TorusTorsorsHavePoints : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F],
    let K := maximalUnramified F
    ∀ (A : LinearAlgebraicGroups.HopfAlgebraCategory K), IsTorus A →
      ∀ P : FppfTorsor (fieldBase K) (LinearAlgebraicGroups.specGroup A),
        Nonempty (P.val.Section (fieldTest K))

end LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedTorusTorsors
