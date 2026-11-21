import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DiscontinuityCriterion

/-! Independent statements for paper.tex, d04:06:exceptions. All integrals
are the upstream Darboux integral, and all exceptional sets are ambient sets.
No closedness assumption is imposed on a content-zero exceptional set. -/
noncomputable section
open Set
namespace Specs.D04.C06.ExceptionalSets.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.NullCovers.Model

def unitBox : Box 1 := intervalBox 0 1 (by norm_num)
/-- The zero function modified to one on the rational unit interval. -/
def dirichlet (x : E 1) : ℝ := rationalUnit.indicator (fun _ => 1) x
end Specs.D04.C06.ExceptionalSets.Model

namespace Specs.D04.C06.ExceptionalSets
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.NullCovers.Model
open Specs.D04.C06.DiscontinuityCriterion.Model Model

abbrev unitBoxType := Box 1
def unitBoxValue : unitBoxType := Model.unitBox
abbrev dirichletType := E 1 → ℝ
def dirichletValue : dirichletType := Model.dirichlet

def integrable_continuousType : Prop := ∀ {n : ℕ}, 0 < n →
  ∀ (Q : Box n) (f : E n → ℝ), ContinuousOn f (carrier Q) → Integrable f Q

def integral_eq_of_eq_off_nullType : Prop := ∀ {n : ℕ}, 0 < n →
  ∀ {Q : Box n} {f g : E n → ℝ} (hf : Integrable f Q) (hg : Integrable g Q)
    {S : Set (E n)}, Null S → (∀ x ∈ carrier Q, x ∉ S → f x = g x) →
    integral f Q hf = integral g Q hg

def zero_off_contentZeroType : Prop := ∀ {n : ℕ}, 0 < n →
  ∀ {Q : Box n} {f : E n → ℝ}, Bounded f Q → ∀ {S : Set (E n)},
    ContentZero S → (∀ x ∈ carrier Q, x ∉ S → f x = 0) →
    ∃ hf : Integrable f Q, integral f Q hf = 0

/-- The stated preservation consequence for arbitrary bounded modifications. -/
def modification_contentZeroType : Prop := ∀ {n : ℕ}, 0 < n →
  ∀ {Q : Box n} {f g : E n → ℝ} (hf : Integrable f Q), Bounded g Q →
    ∀ {S : Set (E n)}, ContentZero S →
    (∀ x ∈ carrier Q, x ∉ S → f x = g x) →
    ∃ hg : Integrable g Q, integral g Q hg = integral f Q hf

def zero_integrableType : Prop := Integrable (fun _ => 0) unitBox

def dirichlet_boundedType : Prop := Bounded dirichlet unitBox

def dirichlet_eq_zero_offType : Prop := ∀ x : E 1, x ∉ rationalUnit → dirichlet x = 0

def dirichlet_oscillationType : Prop := ∀ x ∈ carrier unitBox,
  oscillation dirichlet unitBox x = 1

def dirichlet_discontinuousType : Prop := ∀ x ∈ carrier unitBox,
  ¬ ContinuousWithinAt dirichlet (carrier unitBox) x

def dirichlet_not_integrableType : Prop := ¬ Integrable dirichlet unitBox

/-- Includes the nullity of the actual set on which the zero function is changed. -/
def null_modification_counterexampleType : Prop :=
  Null rationalUnit ∧ Integrable (fun _ => 0) unitBox ∧
    Bounded dirichlet unitBox ∧
    (∀ x ∈ carrier unitBox, x ∉ rationalUnit → dirichlet x = 0) ∧
    ¬ Integrable dirichlet unitBox
end Specs.D04.C06.ExceptionalSets
