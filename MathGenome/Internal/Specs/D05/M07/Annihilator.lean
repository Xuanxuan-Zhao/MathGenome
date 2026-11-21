import MathGenome.Internal.Specs.D05.M02.Subspace
import MathGenome.Internal.Specs.D05.M03.Kernel
import MathGenome.Internal.Specs.D05.M07.Dual

/-!
Independent specifications for K05.07.annihilator (paper.tex:1023–1027).

The annihilator of a subspace lives in the algebraic dual; the preannihilator
of an arbitrary set of functionals lives in the original space. For a set of
functionals we use the canonical coannihilator of its linear span, and require
the bridge to the paper's pointwise vanishing condition and intersection of
kernels. There are no dimension, topology, or conjugation assumptions.
-/

namespace Specs.D05.M07.Annihilator

universe u v

/-- Type of the annihilator construction in the algebraic dual. -/
def annihilator_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Submodule K V → Submodule K (Module.Dual K V)

/-- The canonical submodule of functionals vanishing on the given subspace. -/
def annihilator_value : annihilator_type.{u, v} :=
  fun _ _ _ _ _ U => U.dualAnnihilator

/-- The input is an arbitrary set of functionals, with output in V. -/
def preannihilator_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Set (Module.Dual K V) → Submodule K V

/-- Taking the span permits reuse of Mathlib's canonical coannihilator. -/
def preannihilator_value : preannihilator_type.{u, v} :=
  fun K _ _ _ _ F => (Submodule.span K F).dualCoannihilator

/-- The carrier is exactly the annihilator defined in the paper. -/
def annihilator_eq_set : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (U : Submodule K V),
    (U.dualAnnihilator : Set (Module.Dual K V)) =
      {f | ∀ u ∈ U, f u = 0}

/-- Vanishing on F is equivalent to vanishing on its span. -/
def preannihilator_eq_set : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Set (Module.Dual K V)),
    ((Submodule.span K F).dualCoannihilator : Set V) =
      {v | ∀ f ∈ F, f v = 0}

/-- Linear combinations of vanishing functionals still vanish on U. -/
def annihilator_linear_combination : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) (a b : K) (f g : Module.Dual K V),
    f ∈ U.dualAnnihilator → g ∈ U.dualAnnihilator →
      a • f + b • g ∈ U.dualAnnihilator

/-- Simultaneous kernels are closed under linear combinations in V. -/
def preannihilator_linear_combination : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Set (Module.Dual K V)) (a b : K) (u v : V),
    u ∈ (Submodule.span K F).dualCoannihilator →
    v ∈ (Submodule.span K F).dualCoannihilator →
      a • u + b • v ∈ (Submodule.span K F).dualCoannihilator

/-- The preannihilator is the intersection over precisely the members of F. -/
def preannihilator_eq_iInf : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F : Set (Module.Dual K V)),
    (Submodule.span K F).dualCoannihilator = ⨅ f ∈ F, LinearMap.ker f

/-- Annihilation reverses inclusion of subspaces of V. -/
def annihilator_antitone : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U W : Submodule K V),
    U ≤ W → W.dualAnnihilator ≤ U.dualAnnihilator

/-- Preannihilation reverses inclusion of arbitrary sets in the dual. -/
def preannihilator_antitone : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F G : Set (Module.Dual K V)),
    F ⊆ G → (Submodule.span K G).dualCoannihilator ≤
      (Submodule.span K F).dualCoannihilator

end Specs.D05.M07.Annihilator
