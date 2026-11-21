import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Pointwise
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
Independent specification of `K03.12.uniform` (paper.tex:1197–1204).
A type `E` is the domain; a subset is represented by its subtype, as in
Pointwise. Indices retain the upstream convention: `n` denotes term `n + 1`.
Uniform convergence has a single tail index for every point of the domain.
For `U : Set ℝ`, functions have domain `U`, and compact subsets are taken
in its induced topology. Compact subsets of this subtype correspond exactly
to ambient compact subsets contained in `U`, via the subtype embedding.
No continuity or boundedness of the functions is required. The equivalence
with Mathlib's neighborhood definition of locally uniform convergence uses
openness of `U`; the compact-subset definition itself makes sense for any `U`.
-/

namespace Specs.SingleVariableAnalysis.Ch12.Uniform

universe u

def realUniformConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℝ) → (E → ℝ) → Prop

def realUniformConvergesValue : realUniformConvergesType :=
  fun F f => ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, |F n x - f x| < ε

def complexUniformConvergesType : Type (u + 1) :=
  {E : Type u} → (ℕ → E → ℂ) → (E → ℂ) → Prop

def complexUniformConvergesValue : complexUniformConvergesType :=
  fun F f => ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖F n x - f x‖ < ε

def realLocallyUniformConvergesType : Type :=
  {U : Set ℝ} → (ℕ → U → ℝ) → (U → ℝ) → Prop

def realLocallyUniformConvergesValue : realLocallyUniformConvergesType :=
  fun {U} F f => ∀ K : Set U, IsCompact K →
    realUniformConvergesValue (fun n (x : K) => F n x) (fun x => f x)

def complexLocallyUniformConvergesType : Type :=
  {U : Set ℝ} → (ℕ → U → ℂ) → (U → ℂ) → Prop

def complexLocallyUniformConvergesValue : complexLocallyUniformConvergesType :=
  fun {U} F f => ∀ K : Set U, IsCompact K →
    complexUniformConvergesValue (fun n (x : K) => F n x) (fun x => f x)

def realUniformConvergesEpsilonIff : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ),
    realUniformConvergesValue F f ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, |F n x - f x| < ε

def realUniformConvergesIff : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ),
    realUniformConvergesValue F f ↔ TendstoUniformly F f Filter.atTop

def realUniformConvergesPointwise : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ),
    realUniformConvergesValue F f → Pointwise.realPointwiseConvergesValue F f

def realUniformConvergesRestrict : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ) (S : Set E),
    realUniformConvergesValue F f →
      realUniformConvergesValue (fun n (x : S) => F n x) (fun x => f x)

def realLocallyUniformConvergesCompactIff : Prop :=
  ∀ {U : Set ℝ} (F : ℕ → U → ℝ) (f : U → ℝ),
    realLocallyUniformConvergesValue F f ↔
      ∀ K : Set U, IsCompact K →
        realUniformConvergesValue (fun n (x : K) => F n x) (fun x => f x)

def realLocallyUniformConvergesIff : Prop :=
  ∀ {U : Set ℝ} (hU : IsOpen U) (F : ℕ → U → ℝ) (f : U → ℝ),
    realLocallyUniformConvergesValue F f ↔ TendstoLocallyUniformly F f Filter.atTop

def realUniformConvergesLocallyUniform : Prop :=
  ∀ {U : Set ℝ} (F : ℕ → U → ℝ) (f : U → ℝ),
    realUniformConvergesValue F f → realLocallyUniformConvergesValue F f

def realUniformConvergesEmpty : Prop :=
  ∀ {E : Type u} [IsEmpty E] (F : ℕ → E → ℝ) (f : E → ℝ),
    realUniformConvergesValue F f

def realLocallyUniformConvergesEmpty : Prop :=
  ∀ {U : Set ℝ} [IsEmpty U] (F : ℕ → U → ℝ) (f : U → ℝ),
    realLocallyUniformConvergesValue F f

def complexUniformConvergesEpsilonIff : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ),
    complexUniformConvergesValue F f ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖F n x - f x‖ < ε

def complexUniformConvergesIff : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ),
    complexUniformConvergesValue F f ↔ TendstoUniformly F f Filter.atTop

def complexUniformConvergesPointwise : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ),
    complexUniformConvergesValue F f → Pointwise.complexPointwiseConvergesValue F f

def complexUniformConvergesRestrict : Prop :=
  ∀ {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ) (S : Set E),
    complexUniformConvergesValue F f →
      complexUniformConvergesValue (fun n (x : S) => F n x) (fun x => f x)

def complexLocallyUniformConvergesCompactIff : Prop :=
  ∀ {U : Set ℝ} (F : ℕ → U → ℂ) (f : U → ℂ),
    complexLocallyUniformConvergesValue F f ↔
      ∀ K : Set U, IsCompact K →
        complexUniformConvergesValue (fun n (x : K) => F n x) (fun x => f x)

def complexLocallyUniformConvergesIff : Prop :=
  ∀ {U : Set ℝ} (hU : IsOpen U) (F : ℕ → U → ℂ) (f : U → ℂ),
    complexLocallyUniformConvergesValue F f ↔ TendstoLocallyUniformly F f Filter.atTop

def complexUniformConvergesLocallyUniform : Prop :=
  ∀ {U : Set ℝ} (F : ℕ → U → ℂ) (f : U → ℂ),
    complexUniformConvergesValue F f → complexLocallyUniformConvergesValue F f

def complexUniformConvergesEmpty : Prop :=
  ∀ {E : Type u} [IsEmpty E] (F : ℕ → E → ℂ) (f : E → ℂ),
    complexUniformConvergesValue F f

def complexLocallyUniformConvergesEmpty : Prop :=
  ∀ {U : Set ℝ} [IsEmpty U] (F : ℕ → U → ℂ) (f : U → ℂ),
    complexLocallyUniformConvergesValue F f

end Specs.SingleVariableAnalysis.Ch12.Uniform
