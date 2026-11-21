import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ScalarObstruction

/-! Injectivity of the scalar obstruction in RM03-C04.13. -/

namespace Specs.RM03.Brauer.ScalarInjective

open _root_.RM03.Brauer.ScalarObstruction
open Specs.RM03.Brauer.ScalarObstruction

universe u v w

/-- For a finite Galois extension, the homomorphism on the relative Brauer
subgroup given by the scalar lift-defect formula is injective. -/
def ObstructionInjective : Prop :=
  ∀ (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (gk : AddCommGroup (BrauerGroup.{u, max u v w} k))
    (gK : AddCommGroup (BrauerGroup.{v, max u v w} K)),
    GroupLaws.{u, max v w} k gk → GroupLaws.{v, max u w} K gK →
    letI := gk
    letI := gK
    ∀ (f : BrauerGroup.{u, max u v w} k →+ BrauerGroup.{v, max u v w} K),
      IsScalarExtension k K f →
      ∀ (φ : relativeSubgroup f →+ Additive (H2 k K)),
        IsObstructionHom.{u,v,w} f φ → Function.Injective φ

end Specs.RM03.Brauer.ScalarInjective
