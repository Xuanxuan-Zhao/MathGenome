import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.DirectSum.Module

/-! LA-C06, source lines 1402–1445. The form and dual assertions in the
remainder of C06 are allocated to LA-C06-Forms. A summand with a standard
basis of size r+1 is L_r, by the upstream classification and equivalence
statements. Internal direct sums use the actual inclusions of invariant
subspaces; thus their canonical sum map is an isomorphism. -/

open scoped Classical
universe u v w
namespace Specs.LieAlgebrasAndRepresentations.ClebschGordan
open Module Sl2Model Sl2SimpleModules
open scoped TensorProduct

/-- Every finite-dimensional module is an internal finite sum of standard
modules. The indexing set may be empty, so this includes the zero module. -/
def finite_standard_decomposition_type : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (M : Type v) [AddCommGroup M] [Module k M]
    [LieRingModule (Model k) M] [LieModule k (Model k) M] [FiniteDimensional k M],
    ∃ S : Set (LieSubmodule k (Model k) M), S.Finite ∧
      DirectSum.IsInternal (fun W : S => W.val.toSubmodule) ∧
      ∀ W ∈ S, ∃ (n : ℕ) (b : Basis (Fin (n + 1)) k W), IsStandardBasis b

/-- The tensor product has exactly one summand of each highest weight
m+n-2j, for 0 ≤ j ≤ min(m,n). The quantification over arbitrary standard
bases makes the statement independent of a choice of model of L_m or L_n.
Both zero parameters are allowed. -/
def clebsch_gordan_type : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    (M : Type v) (N : Type w)
    [AddCommGroup M] [Module k M] [LieRingModule (Model k) M] [LieModule k (Model k) M]
    [AddCommGroup N] [Module k N] [LieRingModule (Model k) N] [LieModule k (Model k) N]
    (m n : ℕ) (b : Basis (Fin (m + 1)) k M) (c : Basis (Fin (n + 1)) k N),
    IsStandardBasis b → IsStandardBasis c →
    ∃ W : Fin (min m n + 1) → LieSubmodule k (Model k) (M ⊗[k] N),
      DirectSum.IsInternal (fun j => (W j).toSubmodule) ∧
      ∀ j, ∃ d : Basis (Fin (m + n - 2 * j.val + 1)) k (W j), IsStandardBasis d

end Specs.LieAlgebrasAndRepresentations.ClebschGordan
