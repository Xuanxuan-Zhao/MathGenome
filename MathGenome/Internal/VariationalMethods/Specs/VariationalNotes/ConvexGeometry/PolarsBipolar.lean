import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Data.EReal.Basic

/-!
Independent specifications for paper.tex §1.5 (Definition and Theorem
`thm:cone-bipolar`), with the real Hausdorff locally convex convention
from the preface. The normal is the continuous-dual normal used in §1.10
and §2.6. Polars back in E use evaluation, not the whole bidual.
The conic hull contains zero even when the generators are empty.
-/
open Set
open scoped Pointwise
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry.Specs

def supportFunction {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (S : Set E) (l : E →L[ℝ] ℝ) : EReal :=
  ⨆ x ∈ S, (l x : EReal)

def supportFunctionType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E], Set E → (E →L[ℝ] ℝ) → EReal

def negativePolar {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (S : Set E) : Set (E →L[ℝ] ℝ) :=
  {l | ∀ x ∈ S, l x ≤ 0}

def negativePolarType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E], Set E → Set (E →L[ℝ] ℝ)

def primalPolar {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (T : Set (E →L[ℝ] ℝ)) : Set E :=
  {x | ∀ l ∈ T, l x ≤ 0}

def primalPolarType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E], Set (E →L[ℝ] ℝ) → Set E

def positiveDual {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (S : Set E) : Set (E →L[ℝ] ℝ) :=
  {l | ∀ x ∈ S, 0 ≤ l x}

def positiveDualType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E], Set E → Set (E →L[ℝ] ℝ)

def primalPositiveDual {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (T : Set (E →L[ℝ] ℝ)) : Set E :=
  {x | ∀ l ∈ T, 0 ≤ l x}

def primalPositiveDualType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E], Set (E →L[ℝ] ℝ) → Set E

def closedHalfspace {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (l : E →L[ℝ] ℝ) (a : ℝ) : Set E :=
  {x | l x ≤ a}

def closedHalfspaceType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E], (E →L[ℝ] ℝ) → ℝ → Set E

def closedConicHull {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (S : Set E) : Set E :=
  closure (conicHull S)

def closedConicHullType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E], Set E → Set E

def normalCone {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] (C : Set E) (x : E) : Set (E →L[ℝ] ℝ) :=
  {l | ∀ z ∈ C, l (z - x) ≤ 0}

def normalConeType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E], Set E → E → Set (E →L[ℝ] ℝ)

def supportFunction_empty : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
  ∀ l : E →L[ℝ] ℝ, supportFunction (∅ : Set E) l = ⊥

def negativePolar_supportFunction : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
  ∀ (S : Set E) (l : E →L[ℝ] ℝ), l ∈ negativePolar S ↔ supportFunction S l ≤ 0

def positiveDual_eq_neg_polar : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
  ∀ S : Set E, positiveDual S = -negativePolar S

def primalPositiveDual_eq_neg_polar : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
  ∀ T : Set (E →L[ℝ] ℝ), primalPositiveDual T = -primalPolar T

def empty_halfspace : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
  closedHalfspace (0 : E →L[ℝ] ℝ) (-1) = ∅

def normalCone_polar : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E],
  ∀ (C : Set E) (x : E), normalCone C x = negativePolar ((fun z => z - x) '' C)

def halfspace_properties : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E],
  ∀ (l : E →L[ℝ] ℝ) (a : ℝ), IsClosed (closedHalfspace l a) ∧
    Convex ℝ (closedHalfspace l a)

def closedConicHull_properties : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E],
  ∀ S : Set E, IsClosed (closedConicHull S) ∧ IsCone (closedConicHull S) ∧
    S ⊆ closedConicHull S ∧
    ∀ K : Set E, IsClosed K → IsCone K → S ⊆ K → closedConicHull S ⊆ K

def closedConicHull_empty : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E],
  closedConicHull (∅ : Set E) = {0}

def polar_closedConicHull : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E],
  ∀ S : Set E, negativePolar (closedConicHull S) = negativePolar S

def halfspace_representation : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E],
  ∀ C : Set E, IsClosed C → Convex ℝ C →
    C = ⋂ (l : E →L[ℝ] ℝ) (a : ℝ) (_ : C ⊆ closedHalfspace l a), closedHalfspace l a

def cone_bipolar : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E],
  ∀ S : Set E, primalPolar (negativePolar S) = closedConicHull S

def cone_bipolar_empty : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E],
  primalPolar (negativePolar (∅ : Set E)) = {0}

def positive_bipolar : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E],
  ∀ S : Set E, primalPositiveDual (positiveDual S) = closedConicHull S

def closed_cone_positive_bipolar : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E],
  ∀ K : Set E, IsClosed K → IsCone K → primalPositiveDual (positiveDual K) = K

end VariationalNotes.ConvexGeometry.Specs
