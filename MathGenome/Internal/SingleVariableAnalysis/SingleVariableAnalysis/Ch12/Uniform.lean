import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Pointwise
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform

/-!
# Uniform and locally uniform convergence

Implements `K03.12.uniform`, paper.tex:1197–1204. Domains are types or
subtypes, and `F n` is the term numbered `n + 1`, as in Pointwise.
Locally uniform convergence on `U ⊆ ℝ` means uniform convergence on every
compact subset of the subtype `U`. The bridge to Mathlib is proved for open
`U`: local compactness supplies compact neighborhoods, and compactness
converts neighborhood estimates into a single uniform tail. No regularity
or boundedness of `F n` or `f` is imposed, and empty domains are allowed.
-/

namespace SingleVariableAnalysis

universe u

/-- One tail threshold works at every point. -/
def RealUniformConverges {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, |F n x - f x| < ε

/-- One tail threshold works at every point. -/
def ComplexUniformConverges {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖F n x - f x‖ < ε

/-- Uniform convergence on each compact subset of the real domain. -/
def RealLocallyUniformConverges {U : Set ℝ} (F : ℕ → U → ℝ) (f : U → ℝ) : Prop :=
  ∀ K : Set U, IsCompact K →
    RealUniformConverges (fun n (x : K) => F n x) (fun x => f x)

/-- Uniform convergence on each compact subset of the real domain. -/
def ComplexLocallyUniformConverges {U : Set ℝ} (F : ℕ → U → ℂ) (f : U → ℂ) : Prop :=
  ∀ K : Set U, IsCompact K →
    ComplexUniformConverges (fun n (x : K) => F n x) (fun x => f x)

theorem realUniformConverges_epsilon_iff {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ) :
    RealUniformConverges F f ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, |F n x - f x| < ε := Iff.rfl

theorem realUniformConverges_iff {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ) :
    RealUniformConverges F f ↔ TendstoUniformly F f Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  simp only [RealUniformConverges, Filter.eventually_atTop, dist_comm (f _) (F _ _),
    Real.dist_eq]

theorem realUniformConverges_pointwise {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ) :
    RealUniformConverges F f → RealPointwiseConverges F f := by
  intro h x ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => hN n hn x⟩

theorem realUniformConverges_restrict {E : Type u} (F : ℕ → E → ℝ) (f : E → ℝ) (S : Set E) :
    RealUniformConverges F f →
      RealUniformConverges (fun n (x : S) => F n x) (fun x => f x) := by
  intro h ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn x => hN n hn x⟩

theorem realLocallyUniformConverges_compact_iff {U : Set ℝ} (F : ℕ → U → ℝ) (f : U → ℝ) :
    RealLocallyUniformConverges F f ↔
      ∀ K : Set U, IsCompact K →
        RealUniformConverges (fun n (x : K) => F n x) (fun x => f x) := Iff.rfl

theorem realLocallyUniformConverges_iff {U : Set ℝ} (hU : IsOpen U) (F : ℕ → U → ℝ) (f : U → ℝ) :
    RealLocallyUniformConverges F f ↔ TendstoLocallyUniformly F f Filter.atTop := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  simp only [RealLocallyUniformConverges, realUniformConverges_iff,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, Function.comp_def]

theorem realUniformConverges_locallyUniform {U : Set ℝ} (F : ℕ → U → ℝ) (f : U → ℝ) :
    RealUniformConverges F f → RealLocallyUniformConverges F f := by
  intro h K _
  exact realUniformConverges_restrict F f K h

theorem realUniformConverges_empty {E : Type u} [IsEmpty E] (F : ℕ → E → ℝ) (f : E → ℝ) :
    RealUniformConverges F f := by
  intro ε _
  exact ⟨0, fun _ _ x => isEmptyElim x⟩

theorem realLocallyUniformConverges_empty {U : Set ℝ} [IsEmpty U] (F : ℕ → U → ℝ) (f : U → ℝ) :
    RealLocallyUniformConverges F f := by
  exact realUniformConverges_locallyUniform F f (realUniformConverges_empty F f)

theorem complexUniformConverges_epsilon_iff {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ) :
    ComplexUniformConverges F f ↔
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖F n x - f x‖ < ε := Iff.rfl

theorem complexUniformConverges_iff {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ) :
    ComplexUniformConverges F f ↔ TendstoUniformly F f Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  simp only [ComplexUniformConverges, Filter.eventually_atTop, dist_comm (f _) (F _ _),
    dist_eq_norm]

theorem complexUniformConverges_pointwise {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ) :
    ComplexUniformConverges F f → ComplexPointwiseConverges F f := by
  intro h x ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => hN n hn x⟩

theorem complexUniformConverges_restrict {E : Type u} (F : ℕ → E → ℂ) (f : E → ℂ) (S : Set E) :
    ComplexUniformConverges F f →
      ComplexUniformConverges (fun n (x : S) => F n x) (fun x => f x) := by
  intro h ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn x => hN n hn x⟩

theorem complexLocallyUniformConverges_compact_iff {U : Set ℝ} (F : ℕ → U → ℂ) (f : U → ℂ) :
    ComplexLocallyUniformConverges F f ↔
      ∀ K : Set U, IsCompact K →
        ComplexUniformConverges (fun n (x : K) => F n x) (fun x => f x) := Iff.rfl

theorem complexLocallyUniformConverges_iff {U : Set ℝ} (hU : IsOpen U) (F : ℕ → U → ℂ) (f : U → ℂ) :
    ComplexLocallyUniformConverges F f ↔ TendstoLocallyUniformly F f Filter.atTop := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  simp only [ComplexLocallyUniformConverges, complexUniformConverges_iff,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, Function.comp_def]

theorem complexUniformConverges_locallyUniform {U : Set ℝ} (F : ℕ → U → ℂ) (f : U → ℂ) :
    ComplexUniformConverges F f → ComplexLocallyUniformConverges F f := by
  intro h K _
  exact complexUniformConverges_restrict F f K h

theorem complexUniformConverges_empty {E : Type u} [IsEmpty E] (F : ℕ → E → ℂ) (f : E → ℂ) :
    ComplexUniformConverges F f := by
  intro ε _
  exact ⟨0, fun _ _ x => isEmptyElim x⟩

theorem complexLocallyUniformConverges_empty {U : Set ℝ} [IsEmpty U] (F : ℕ → U → ℂ) (f : U → ℂ) :
    ComplexLocallyUniformConverges F f := by
  exact complexUniformConverges_locallyUniform F f (complexUniformConverges_empty F f)

end SingleVariableAnalysis
