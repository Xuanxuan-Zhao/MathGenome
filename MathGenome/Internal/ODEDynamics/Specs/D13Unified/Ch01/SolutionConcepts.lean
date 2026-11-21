import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Basic

/-!
Shared objects for paper.tex, Chapter 1, Objects and domains and d13:01:solution.

The state space is an arbitrary real normed vector space. In particular one may use
`Fin n → ℝ`, including `n = 0`, with any normed-space structure, or any linearly
isomorphic finite-dimensional space. No Euclidean or sup norm is imposed.

Curves have ambient representatives `ℝ → E`, as in Mathlib's calculus on sets.
Their actual domains are recorded separately. Values outside those domains do
not enter any solution condition or comparison; `Solution.value` is the map on
that actual domain. In particular an ambient representative does not make a
solution global.
-/

noncomputable section

open Set

namespace D13Unified

/-- A nonempty real interval, with any of its endpoints included or excluded. -/
structure TimeInterval where
  carrier : Set ℝ
  nonempty : carrier.Nonempty
  ordConnected : OrdConnected carrier

/-- A nonempty open real interval, allowing infinite endpoints and all of `ℝ`. -/
structure OpenTimeInterval extends TimeInterval where
  isOpen : IsOpen carrier

/-- A continuous vector field on its specified open time-state domain.
There is no global-domain or Lipschitz hypothesis. -/
structure ODE (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  domain : Set (ℝ × E)
  isOpen_domain : IsOpen domain
  field : domain → E
  continuous_field : Continuous field

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Zero extension is only an evaluation convention. Solution predicates always
require the graph to lie in `domain`. It is not a global continuous extension. -/
def eval (F : ODE E) (t : ℝ) (x : E) : E := by
  classical
  exact if h : (t, x) ∈ F.domain then F.field ⟨(t, x), h⟩ else 0

/-- Change the normed realization of the state space through a continuous linear
bijection. The time coordinate is unchanged and the domain is transported too. -/
def transport {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : ODE E) (e : E ≃L[ℝ] G) : ODE G where
  domain := (fun p : ℝ × G => (p.1, e.symm p.2)) ⁻¹' F.domain
  isOpen_domain := F.isOpen_domain.preimage
    (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd))
  field := fun p => e (F.field ⟨(p.val.1, e.symm p.val.2), p.property⟩)
  continuous_field := e.continuous.comp (F.continuous_field.comp
    (((continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)).comp
      continuous_subtype_val).subtype_mk _))

end ODE
end D13Unified

namespace Specs.D13Unified.Ch01.SolutionConcepts

open _root_.D13Unified

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differential solution on an interval of any endpoint type. Within derivatives
at the endpoints of a nondegenerate closed interval are exactly the appropriate
one-sided derivatives. On a singleton the within-derivative condition is vacuous,
as is the integral condition; continuity and graph membership are still required. -/
def solutionOnValue (F : ODE E) (I : TimeInterval) (x : ℝ → E) : Prop :=
  ContinuousOn x I.carrier ∧
  (∀ t ∈ I.carrier, (t, x t) ∈ F.domain) ∧
  ∀ t ∈ I.carrier, HasDerivWithinAt x (F.eval t (x t)) I.carrier t

def solutionOnType : Type u := ODE E → TimeInterval → (ℝ → E) → Prop

/-- Classical solution on its nonempty open interval: C¹, graph in the domain,
and the ordinary derivative equation at every point of that interval. -/
def classicalSolutionOnValue (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E) : Prop :=
  ContDiffOn ℝ 1 x I.carrier ∧
  (∀ t ∈ I.carrier, (t, x t) ∈ F.domain) ∧
  ∀ t ∈ I.carrier, HasDerivAt x (F.eval t (x t)) t

def classicalSolutionOnType : Type u := ODE E → OpenTimeInterval → (ℝ → E) → Prop

def ivpOnValue (F : ODE E) (I : TimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E) : Prop :=
  solutionOnValue F I x ∧ s ∈ I.carrier ∧ x s = ξ

def ivpOnType : Type u := ODE E → TimeInterval → (ℝ → E) → ℝ → E → Prop

def classicalIVPOnValue (F : ODE E) (I : OpenTimeInterval)
    (x : ℝ → E) (s : ℝ) (ξ : E) : Prop :=
  classicalSolutionOnValue F I x ∧ s ∈ I.carrier ∧ x s = ξ

def classicalIVPOnType : Type u := ODE E → OpenTimeInterval → (ℝ → E) → ℝ → E → Prop

/-- Compact-interval solution, including the nonempty degenerate interval. -/
def compactSolutionOnValue (F : ODE E) (a b : ℝ) (x : ℝ → E) : Prop :=
  a ≤ b ∧ ContinuousOn x (Icc a b) ∧
  (∀ t ∈ Icc a b, (t, x t) ∈ F.domain) ∧
  ∀ t ∈ Icc a b, HasDerivWithinAt x (F.eval t (x t)) (Icc a b) t

def compactSolutionOnType : Type u := ODE E → ℝ → ℝ → (ℝ → E) → Prop

end Specs.D13Unified.Ch01.SolutionConcepts

namespace D13Unified

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A solution together with its actual nonempty open interval of definition. -/
structure Solution (F : ODE E) where
  interval : OpenTimeInterval
  representative : ℝ → E
  isSolution : Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue
    F interval representative

/-- A solution on an interval of arbitrary endpoint type. -/
structure IntervalSolution (F : ODE E) where
  interval : TimeInterval
  representative : ℝ → E
  isSolution : Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue
    F interval representative

/-- Evaluation has the actual solution domain as its source type. -/
def Solution.value {F : ODE E} (x : Solution F) : x.interval.carrier → E :=
  fun t => x.representative t

def IntervalSolution.value {F : ODE E} (x : IntervalSolution F) : x.interval.carrier → E :=
  fun t => x.representative t

end D13Unified

namespace Specs.D13Unified.Ch01.SolutionConcepts

open _root_.D13Unified

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `y` extends `x` precisely when its domain contains that of `x` and its
values agree on the entire original domain. Values of representatives elsewhere
are deliberately irrelevant. Both objects already carry their solution proofs. -/
def extensionValue {F : ODE E} (x y : Solution F) : Prop :=
  x.interval.carrier ⊆ y.interval.carrier ∧
  EqOn y.representative x.representative x.interval.carrier

def extensionType (F : ODE E) : Type u := Solution F → Solution F → Prop

/-- Maximality is absence of any extension to a strictly larger open interval.
No uniqueness, existence of maximal solutions, or choice of a solution is assumed. -/
def maximalValue {F : ODE E} (x : Solution F) : Prop :=
  ¬ ∃ y : Solution F, extensionValue x y ∧ x.interval.carrier ⊂ y.interval.carrier

def maximalType (F : ODE E) : Type u := Solution F → Prop

def globalValue {F : ODE E} (x : Solution F) : Prop := x.interval.carrier = univ

def globalType (F : ODE E) : Type u := Solution F → Prop

/-- Restriction keeps exactly the values on the specified smaller open interval. -/
def restrictValue {F : ODE E} (x : Solution F) (J : OpenTimeInterval)
    (hJ : J.carrier ⊆ x.interval.carrier) : Solution F where
  interval := J
  representative := x.representative
  isSolution := ⟨x.isSolution.1.mono hJ,
    fun t ht => x.isSolution.2.1 t (hJ ht),
    fun t ht => x.isSolution.2.2 t (hJ ht)⟩

def restrictType (F : ODE E) : Type u :=
  (x : Solution F) → (J : OpenTimeInterval) →
    J.carrier ⊆ x.interval.carrier → Solution F

def intervalRestrictValue {F : ODE E} (x : IntervalSolution F) (J : TimeInterval)
    (hJ : J.carrier ⊆ x.interval.carrier) : IntervalSolution F where
  interval := J
  representative := x.representative
  isSolution := ⟨x.isSolution.1.mono hJ,
    fun t ht => x.isSolution.2.1 t (hJ ht),
    fun t ht => (x.isSolution.2.2 t (hJ ht)).mono hJ⟩

def intervalRestrictType (F : ODE E) : Type u :=
  (x : IntervalSolution F) → (J : TimeInterval) →
    J.carrier ⊆ x.interval.carrier → IntervalSolution F

/-- Compatibility between ordinary C¹ solutions on open intervals and the
endpoint-aware differential predicate used on arbitrary intervals. -/
def classicalIffSolutionOn : Prop :=
  ∀ (F : ODE E) (I : OpenTimeInterval) (x : ℝ → E),
    classicalSolutionOnValue F I x ↔ solutionOnValue F I.toTimeInterval x

/-- A linear equivalence between finite-dimensional normed realizations needs no
isometry hypothesis. Applying this to the identity between two differently normed
copies gives continuity, C¹ regularity and differential-equation invariance under
changing the norm. The velocity `v` can be any prescribed right hand side. -/
def normIndependence : Prop :=
  ∀ {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
    (e : E ≃ₗ[ℝ] G) (I : Set ℝ) (x v : ℝ → E),
    (ContinuousOn (fun t => e (x t)) I ↔ ContinuousOn x I) ∧
    (ContDiffOn ℝ 1 (fun t => e (x t)) I ↔ ContDiffOn ℝ 1 x I) ∧
    ((∀ t ∈ I, HasDerivWithinAt (fun r => e (x r)) (e (v t)) I t) ↔
      ∀ t ∈ I, HasDerivWithinAt x (v t) I t) ∧
    ((∀ t ∈ I, HasDerivAt (fun r => e (x r)) (e (v t)) t) ↔
      ∀ t ∈ I, HasDerivAt x (v t) t)

/-- In particular existence of the IVP on the same interval is norm independent.
A linear equivalence between finite-dimensional real spaces is automatically
continuous in both norms; neither norm is required to be Euclidean. -/
def normIndependentSolutions : Prop :=
  ∀ {G : Type v} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
    (e : E ≃ₗ[ℝ] G) (F : ODE E) (I : OpenTimeInterval) (s : ℝ) (ξ : E),
    (∀ x : ℝ → E,
      classicalIVPOnValue (F.transport e.toContinuousLinearEquiv) I
        (fun t => e (x t)) s (e ξ) ↔ classicalIVPOnValue F I x s ξ) ∧
    ((∃ y : ℝ → G,
      classicalIVPOnValue (F.transport e.toContinuousLinearEquiv) I y s (e ξ)) ↔
      ∃ x : ℝ → E, classicalIVPOnValue F I x s ξ)

/-- Ambient representatives agreeing on the actual interval describe the same
solution property, so no assumption about values off that interval is hidden. -/
def representativeIndependence : Prop :=
  ∀ (F : ODE E) (I : TimeInterval) (x y : ℝ → E),
    EqOn x y I.carrier → (solutionOnValue F I x ↔ solutionOnValue F I y)

/-- The two included endpoints use right and left derivatives respectively. -/
def compactEndpointDerivatives : Prop :=
  ∀ (F : ODE E) (a b : ℝ), a < b → ∀ x : ℝ → E,
    compactSolutionOnValue F a b x →
      HasDerivWithinAt x (F.eval a (x a)) (Ici a) a ∧
      HasDerivWithinAt x (F.eval b (x b)) (Iic b) b

end Specs.D13Unified.Ch01.SolutionConcepts

/- Closed specification types quantify the state space and every instance;
these are the declarations compared with the full public implementation types. -/
namespace Specs.D13Unified.Ch01.SolutionConcepts
open _root_.D13Unified
universe u v

def isSolutionOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], solutionOnType (E := E)

def isClassicalSolutionOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], classicalSolutionOnType (E := E)

def isIVPOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], ivpOnType (E := E)

def isClassicalIVPOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], classicalIVPOnType (E := E)

def isCompactSolutionOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], compactSolutionOnType (E := E)

def extendsExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ODE E}, extensionType F

def isMaximalExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ODE E}, maximalType F

def isGlobalExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ODE E}, globalType F

def restrictExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ODE E}, restrictType F

def intervalRestrictExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ODE E}, intervalRestrictType F

def classicalIffSolutionOnExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], classicalIffSolutionOn (E := E)

def normIndependenceExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], normIndependence.{u, v} (E := E)

def normIndependentSolutionsExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], normIndependentSolutions.{u, v} (E := E)

def representativeIndependenceExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], representativeIndependence (E := E)

def compactEndpointDerivativesExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], compactEndpointDerivatives (E := E)

end Specs.D13Unified.Ch01.SolutionConcepts
