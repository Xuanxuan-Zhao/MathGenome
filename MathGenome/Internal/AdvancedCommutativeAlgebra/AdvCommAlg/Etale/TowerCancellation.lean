import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.TowerCancellation

/-! ET-05: cancellation in a compatible tower of commutative algebras.
The canonical cancellation theorem uses uniqueness of lifts on the
intermediate base to make the lift linear over that base. The accepted
FL-01 equivalences identify its cotangent predicates with square-zero
lifting. No finiteness is needed for this argument.
-/
namespace AdvCommAlg.Etale

universe u v w

/-- Formal cancellation without any finite type or presentation hypothesis. -/
theorem formal_etale_tower_cancellation :
    Specs.AdvCommAlg.Etale.TowerCancellation.formalEtaleCancellation.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ hB hC
  let : Algebra.FormallyUnramified A B :=
    (FormalLifting.formallyUnramified_iff A B).mp hB
  let : Algebra.FormallyEtale A C :=
    (FormalLifting.formallyEtale_iff A C).mp hC
  apply (FormalLifting.formallyEtale_iff B C).mpr
  exact Algebra.FormallyEtale.of_restrictScalars (R := A) (A := B) (B := C)

/-- Étale cancellation, including finite presentation over the intermediate
base. Mathlib's relative finite presentation theorem applies since B/A is
finite type and C/A is finitely presented, both consequences of étaleness. -/
theorem etale_tower_cancellation :
    Specs.AdvCommAlg.Etale.TowerCancellation.etaleCancellation.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ hB hC
  let : Algebra.Etale A B := hB
  let : Algebra.Etale A C := hC
  exact Algebra.Etale.of_restrictScalars A B C

end AdvCommAlg.Etale
