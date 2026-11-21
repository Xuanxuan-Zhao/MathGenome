import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.AbsoluteConvergence

/-! Independent statements for paper.tex `d04:07:improper`.
All integrals are the shared Darboux/zero-extension Riemann integrals.
An open partial homeomorphism represents precisely a homeomorphism between
its open source and target; the two `ContDiffOn` assumptions make it C¹.
Ambient representatives of functions are used only on the specified domains.
No boundedness on the whole domain or absolute convergence is presumed.
-/
noncomputable section
open Set Filter Topology
open scoped Classical ENNReal
namespace Specs.D04.C07.ImproperSubstitution.Model
open Specs.D04.C06.DarbouxIntegral.Model

def weightedPullback {n : ℕ} (e : OpenPartialHomeomorph (E n) (E n))
    (f : E n → ℝ) (x : E n) : ℝ := f (e x) * |(fderiv ℝ e x).det|
end Specs.D04.C07.ImproperSubstitution.Model

namespace Specs.D04.C07.ImproperSubstitution
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.ImproperExhaustions.Model
open Specs.D04.C06.AbsoluteConvergence.Model Model

abbrev weightedPullbackType := {n : ℕ} → OpenPartialHomeomorph (E n) (E n) →
  (E n → ℝ) → E n → ℝ
def weightedPullbackValue : weightedPullbackType := @Model.weightedPullback

def compactJordan_imageType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {K}, CompactJordanSubset e.source K → CompactJordanSubset e.target (e '' K)

def regularExhaustion_imageType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {K}, RegularExhaustion e.source K → RegularExhaustion e.target (fun j => e '' K j)

/-- The intersection is the inverse image inside the actual domain of e. -/
def regularExhaustion_preimageType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {L}, RegularExhaustion e.target L →
    RegularExhaustion e.source (fun j => e.source ∩ e ⁻¹' L j)

def locally_integrable_pullbackType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {f}, LocallyRiemannIntegrable e.target f →
    LocallyRiemannIntegrable e.source (weightedPullback e f)

/-- Both proper integrals exist on every compact Jordan truncation, not merely
on some selected exhaustion. -/
def proper_substitutionType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {f}, LocallyRiemannIntegrable e.target f → ∀ {K}, CompactJordanSubset e.source K →
    RegionIntegrable (fun y : e '' K => f y) ∧
    RegionIntegrable (fun x : K => weightedPullback e f x) ∧
    regionIntegral (fun y : e '' K => f y) =
      regionIntegral (fun x : K => weightedPullback e f x)

def proper_abs_substitutionType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {f}, LocallyRiemannIntegrable e.target f → ∀ {K}, CompactJordanSubset e.source K →
    RegionIntegrable (fun y : e '' K => |f y|) ∧
    RegionIntegrable (fun x : K => |weightedPullback e f x|) ∧
    regionIntegral (fun y : e '' K => |f y|) =
      regionIntegral (fun x : K => |weightedPullback e f x|)

/-- Equality of extended nonnegative integrals includes the divergent case. -/
def absolute_mass_substitutionType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {f}, LocallyRiemannIntegrable e.target f →
    absoluteMass e.target f = absoluteMass e.source (weightedPullback e f)

def absolutely_convergent_iffType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {f}, LocallyRiemannIntegrable e.target f →
    (AbsolutelyConvergent e.target f ↔ AbsolutelyConvergent e.source (weightedPullback e f))

def improper_substitutionType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {f}, LocallyRiemannIntegrable e.target f →
  (AbsolutelyConvergent e.target f ∨ AbsolutelyConvergent e.source (weightedPullback e f)) →
    improperIntegral e.target f = improperIntegral e.source (weightedPullback e f) ∧
    improperIntegral e.target (fun y => |f y|) =
      improperIntegral e.source (fun x => |weightedPullback e f x|)

/-- Every displayed truncation agrees and the exact same limits exist.
This does not identify limits along two unrelated conditional exhaustions. -/
def integral_along_iffType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {f}, LocallyRiemannIntegrable e.target f →
  ∀ {K}, RegularExhaustion e.source K →
    (∀ j, regionIntegral (fun y : e '' K j => f y) =
      regionIntegral (fun x : K j => weightedPullback e f x)) ∧
    ∀ I, HasIntegralAlong f (fun j => e '' K j) I ↔
      HasIntegralAlong (weightedPullback e f) K I

def conditional_substitution_iffType : Prop := ∀ {n} (e : OpenPartialHomeomorph (E n) (E n)),
  ContDiffOn ℝ 1 e e.source → ContDiffOn ℝ 1 e.symm e.target →
  ∀ {f}, LocallyRiemannIntegrable e.target f →
  ∀ {K}, RegularExhaustion e.source K → ∀ I,
    ConditionalConvergesAlong e.target f (fun j => e '' K j) I ↔
      ConditionalConvergesAlong e.source (weightedPullback e f) K I

/-- The zero-dimensional domain is empty or a singleton. The empty linear
Jacobian has determinant one, and both improper values are evaluations
(or zero on an empty domain). -/
def zero_dimensionType : Prop := ∀ (e : OpenPartialHomeomorph (E 0) (E 0)) (f : E 0 → ℝ),
  (∀ x, (fderiv ℝ e x).det = 1) ∧ weightedPullback e f 0 = f 0 ∧
  improperIntegral e.target f = (if (0 : E 0) ∈ e.target then f 0 else 0) ∧
  improperIntegral e.source (weightedPullback e f) =
    (if (0 : E 0) ∈ e.source then f 0 else 0)

end Specs.D04.C07.ImproperSubstitution
