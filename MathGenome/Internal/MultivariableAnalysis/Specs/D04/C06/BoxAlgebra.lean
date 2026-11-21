import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxIntegral

/-! Scalar part of paper.tex, d04:06:algebra. All objects are the shared
Darboux objects; n is arbitrary, including zero and boxes with zero sides.
The supremum in the last estimate is over the actual closed box. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C06.BoxAlgebra
open Specs.D04.C06.DarbouxIntegral.Model

def integrable_constType : Prop :=
  ∀ {n} (Q : Box n) (a : ℝ), Integrable (fun _ => a) Q

def integral_constType : Prop :=
  ∀ {n} (Q : Box n) (a : ℝ) (h : Integrable (fun _ => a) Q),
    integral (fun _ => a) Q h = a * content Q

def integrable_addType : Prop :=
  ∀ {n} {Q : Box n} {f g : E n → ℝ}, Integrable f Q → Integrable g Q →
    Integrable (fun x => f x + g x) Q

def integrable_smulType : Prop :=
  ∀ {n} {Q : Box n} {f : E n → ℝ} (a : ℝ), Integrable f Q →
    Integrable (fun x => a * f x) Q

def integrable_mulType : Prop :=
  ∀ {n} {Q : Box n} {f g : E n → ℝ}, Integrable f Q → Integrable g Q →
    Integrable (fun x => f x * g x) Q

def integrable_absType : Prop :=
  ∀ {n} {Q : Box n} {f : E n → ℝ}, Integrable f Q →
    Integrable (fun x => |f x|) Q

def integral_addType : Prop :=
  ∀ {n} {Q : Box n} {f g : E n → ℝ}
    (hf : Integrable f Q) (hg : Integrable g Q)
    (h : Integrable (fun x => f x + g x) Q),
    integral (fun x => f x + g x) Q h = integral f Q hf + integral g Q hg

def integral_smulType : Prop :=
  ∀ {n} {Q : Box n} {f : E n → ℝ} (a : ℝ)
    (hf : Integrable f Q) (h : Integrable (fun x => a * f x) Q),
    integral (fun x => a * f x) Q h = a * integral f Q hf

def integrable_sumType : Prop :=
  ∀ {n} {Q : Box n} {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → E n → ℝ),
    (∀ i ∈ s, Integrable (f i) Q) → Integrable (fun x => ∑ i ∈ s, f i x) Q

def integral_sumType : Prop :=
  ∀ {n} {Q : Box n} {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → E n → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) Q)
    (h : Integrable (fun x => ∑ i ∈ s, f i x) Q),
    integral (fun x => ∑ i ∈ s, f i x) Q h =
      ∑ i ∈ s, if hi : i ∈ s then integral (f i) Q (hf i hi) else 0

def integral_monoType : Prop :=
  ∀ {n} {Q : Box n} {f g : E n → ℝ}
    (hf : Integrable f Q) (hg : Integrable g Q),
    (∀ x ∈ carrier Q, f x ≤ g x) → integral f Q hf ≤ integral g Q hg

def integral_abs_boundType : Prop :=
  ∀ {n} {Q : Box n} {f : E n → ℝ}
    (hf : Integrable f Q) (ha : Integrable (fun x => |f x|) Q),
    |integral f Q hf| ≤ integral (fun x => |f x|) Q ha ∧
    integral (fun x => |f x|) Q ha ≤ content Q * sSup ((fun x => |f x|) '' carrier Q)

end Specs.D04.C06.BoxAlgebra
