import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.ReflexiveWeakCompactness
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.CompactDirectMethod
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
Independent statements for paper.tex §v03-02, Theorem thm:direct-method,
part 3 and its weakly compact sublevel variant (1399–1444).
Sequences converge in σ(X,X′), with the original norm-continuous dual.
The liminf is taken in EReal so that divergence to minus infinity is represented
correctly, even though the objective itself never takes minus infinity.
-/
noncomputable section
open Set Filter
open scoped Topology
universe u
namespace VariationalNotes.Existence.Specs

def WeakSequentiallyClosedType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X], Set X → Prop

def WeakSequentiallyClosed {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) : Prop :=
  ∀ (a : ℕ → X) (x : X), (∀ n, a n ∈ C) →
    Tendsto (fun n => toWeakSpace ℝ X (a n)) atTop (𝓝 (toWeakSpace ℝ X x)) → x ∈ C

def WeakSequentialLowerSemicontinuousOnType :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X],
    (X → WithTop ℝ) → Set X → Prop

def WeakSequentialLowerSemicontinuousOn {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (J : X → WithTop ℝ) (C : Set X) : Prop :=
  ∀ (a : ℕ → X) (x : X), (∀ n, a n ∈ C) → x ∈ C →
    Tendsto (fun n => toWeakSpace ℝ X (a n)) atTop (𝓝 (toWeakSpace ℝ X x)) →
      ConvexAnalysis.Specs.toEReal (J x) ≤
        liminf (fun n => ConvexAnalysis.Specs.toEReal (J (a n))) atTop

def reflexive_direct_method : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    IsReflexive X → ∀ (J : X → WithTop ℝ) (C : Set X),
    C.Nonempty → WeakSequentiallyClosed C → ProperOn J C →
    (∃ b : ℝ, ∀ x ∈ C, (b : WithTop ℝ) ≤ J x) → CoerciveOn J C →
    WeakSequentialLowerSemicontinuousOn J C → AttainsFiniteMinimum J C

/-- This alternative has no reflexivity, completeness, coercivity, lower bound,
convexity, or closedness requirement. Nonemptiness of the real sublevel already
supplies properness on C. -/
def weaklyCompact_sublevel_direct_method : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (J : X → WithTop ℝ) (C : Set X) (α : ℝ),
    {x ∈ C | J x ≤ (α : WithTop ℝ)}.Nonempty →
    @IsCompact X (weakTopology X) {x ∈ C | J x ≤ (α : WithTop ℝ)} →
    @IsLowerSemicontinuousOn X (weakTopology X) J {x ∈ C | J x ≤ (α : WithTop ℝ)} →
    AttainsFiniteMinimum J C

/-- Each clause is separately universally quantified with its own hypotheses. -/
def three_forms_direct_method : Prop :=
  compact_direct_method.{u} ∧ compact_sublevel_direct_method.{u} ∧
  finiteDimensional_direct_method.{u} ∧ reflexive_direct_method.{u} ∧
  weaklyCompact_sublevel_direct_method.{u}

end VariationalNotes.Existence.Specs
