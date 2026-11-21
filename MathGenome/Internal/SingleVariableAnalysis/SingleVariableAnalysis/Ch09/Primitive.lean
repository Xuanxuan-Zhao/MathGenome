import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Primitive
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.ZeroDerivative

/-!
# Primitives and their additive constants

K03.09.primitive and K03.09.uniqueness. Derivatives use real increments
for both real and complex targets. The indefinite integral is the family
`PrimitiveFamily`, a set of functions. No definite integral or integrability
predicate is introduced here.

The derivative condition is imposed on the interior of the domain. Continuity
at included endpoints is kept separately in `ContinuousPrimitiveOn`; it is
automatic on open sets. Uniqueness uses the upstream equal-derivative theorem
on order-connected real sets, including empty sets and singletons. Applying
that theorem on each interval component gives its own constant; the two
half-lines example shows that a common constant need not exist.
-/

namespace SingleVariableAnalysis

open Set
open scoped Topology
universe u

def IsPrimitiveOn {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) (I : Set ℝ) : Prop :=
  ∀ x ∈ interior I, HasDerivAt F (f x) x

def ContinuousPrimitiveOn {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) (I : Set ℝ) : Prop :=
  ContinuousOn F I ∧ IsPrimitiveOn F f I

def PrimitiveFamily {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (I : Set ℝ) : Set (ℝ → E) := {F | IsPrimitiveOn F f I}

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem primitive_on_open_iff (F f : ℝ → E) (I : Set ℝ) (hI : IsOpen I) :
    IsPrimitiveOn F f I ↔ ∀ x ∈ I, HasDerivAt F (f x) x := by
  simp only [IsPrimitiveOn, hI.interior_eq]

theorem primitive_iff_differentiable_deriv (F f : ℝ → E) (I : Set ℝ) :
    IsPrimitiveOn F f I ↔
      (∀ x ∈ interior I, DifferentiableAt ℝ F x) ∧
      (∀ x ∈ interior I, deriv F x = f x) := by
  constructor
  · intro h
    exact ⟨fun x hx => (h x hx).differentiableAt, fun x hx => (h x hx).deriv⟩
  · rintro ⟨hd, heq⟩ x hx
    rw [← heq x hx]
    exact (hd x hx).hasDerivAt

theorem primitive_iff_increment (F f : ℝ → E) (I : Set ℝ) :
    IsPrimitiveOn F f I ↔ ∀ x ∈ interior I,
      HasRealIncrementDerivative F (f x) x := by
  simp only [IsPrimitiveOn, hasRealIncrementDerivative_iff_hasDerivAt]

theorem continuousPrimitive_on_open_iff (F f : ℝ → E) (I : Set ℝ) (hI : IsOpen I) :
    ContinuousPrimitiveOn F f I ↔ IsPrimitiveOn F f I := by
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  intro x hx
  exact ((primitive_on_open_iff F f I hI).mp h x hx).continuousAt.continuousWithinAt

theorem continuousPrimitive_iff_endpoints (F f : ℝ → E) (I : Set ℝ) :
    ContinuousPrimitiveOn F f I ↔ IsPrimitiveOn F f I ∧
      ∀ x ∈ I, x ∉ interior I → ContinuousWithinAt F I x := by
  constructor
  · intro h
    exact ⟨h.2, fun x hx _ => h.1 x hx⟩
  · rintro ⟨hd, hc⟩
    refine ⟨fun x hx => ?_, hd⟩
    by_cases hint : x ∈ interior I
    · exact (hd x hint).continuousAt.continuousWithinAt
    · exact hc x hx hint

theorem primitive_add_constant (F f : ℝ → E) (I : Set ℝ) (c : E)
    (hF : IsPrimitiveOn F f I) : IsPrimitiveOn (fun x => F x + c) f I := by
  intro x hx
  exact (hF x hx).add_const c

theorem real_primitives_differ_by_constant (F G f : ℝ → ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (hF : ContinuousPrimitiveOn F f I)
    (hG : ContinuousPrimitiveOn G f I) : ∃ c : ℝ, ∀ x ∈ I, F x - G x = c := by
  exact real_equal_derivatives_differ_by_constant F G I hI hF.1 hG.1
    (fun x hx => (hF.2 x hx).differentiableAt)
    (fun x hx => (hG.2 x hx).differentiableAt)
    (fun x hx => (hF.2 x hx).deriv.trans (hG.2 x hx).deriv.symm)

theorem complex_primitives_differ_by_constant (F G f : ℝ → ℂ) (I : Set ℝ)
    (hI : I.OrdConnected) (hF : ContinuousPrimitiveOn F f I)
    (hG : ContinuousPrimitiveOn G f I) : ∃ c : ℂ, ∀ x ∈ I, F x - G x = c := by
  exact complex_equal_derivatives_differ_by_constant F G I hI hF.1 hG.1
    (fun x hx => (hF.2 x hx).differentiableAt)
    (fun x hx => (hG.2 x hx).differentiableAt)
    (fun x hx => (hF.2 x hx).deriv.trans (hG.2 x hx).deriv.symm)

theorem real_open_primitives_differ_by_constant (F G f : ℝ → ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (ho : IsOpen I) (hF : IsPrimitiveOn F f I)
    (hG : IsPrimitiveOn G f I) : ∃ c : ℝ, ∀ x ∈ I, F x - G x = c := by
  exact real_primitives_differ_by_constant F G f I hI
    ((continuousPrimitive_on_open_iff F f I ho).mpr hF)
    ((continuousPrimitive_on_open_iff G f I ho).mpr hG)

theorem complex_open_primitives_differ_by_constant (F G f : ℝ → ℂ) (I : Set ℝ)
    (hI : I.OrdConnected) (ho : IsOpen I) (hF : IsPrimitiveOn F f I)
    (hG : IsPrimitiveOn G f I) : ∃ c : ℂ, ∀ x ∈ I, F x - G x = c := by
  exact complex_primitives_differ_by_constant F G f I hI
    ((continuousPrimitive_on_open_iff F f I ho).mpr hF)
    ((continuousPrimitive_on_open_iff G f I ho).mpr hG)

private theorem primitive_of_eq_add_constant (F G f : ℝ → E) (I : Set ℝ)
    (ho : IsOpen I) (hF : IsPrimitiveOn F f I) (c : E)
    (hc : ∀ x ∈ I, G x = F x + c) : IsPrimitiveOn G f I := by
  intro x hx
  apply (primitive_add_constant F f I c hF x hx).congr_of_eventuallyEq
  filter_upwards [ho.mem_nhds (interior_subset hx)] with y hy
  exact hc y hy

theorem real_primitiveFamily_iff_add_constant (F G f : ℝ → ℝ) (I : Set ℝ)
    (hI : I.OrdConnected) (ho : IsOpen I) (hF : IsPrimitiveOn F f I) :
    G ∈ PrimitiveFamily f I ↔ ∃ c : ℝ, ∀ x ∈ I, G x = F x + c := by
  constructor
  · intro hG
    obtain ⟨c, hc⟩ := real_open_primitives_differ_by_constant G F f I hI ho hG hF
    exact ⟨c, fun x hx => (sub_eq_iff_eq_add.mp (hc x hx)).trans (add_comm c (F x))⟩
  · rintro ⟨c, hc⟩
    exact primitive_of_eq_add_constant F G f I ho hF c hc

theorem complex_primitiveFamily_iff_add_constant (F G f : ℝ → ℂ) (I : Set ℝ)
    (hI : I.OrdConnected) (ho : IsOpen I) (hF : IsPrimitiveOn F f I) :
    G ∈ PrimitiveFamily f I ↔ ∃ c : ℂ, ∀ x ∈ I, G x = F x + c := by
  constructor
  · intro hG
    obtain ⟨c, hc⟩ := complex_open_primitives_differ_by_constant G F f I hI ho hG hF
    exact ⟨c, fun x hx => (sub_eq_iff_eq_add.mp (hc x hx)).trans (add_comm c (F x))⟩
  · rintro ⟨c, hc⟩
    exact primitive_of_eq_add_constant F G f I ho hF c hc

theorem disconnected_primitive_example :
    Specs.SingleVariableAnalysis.Ch09.Primitive.disconnectedPrimitiveExample := by
  let I : Set ℝ := Iio 0 ∪ Ioi 0
  let F : ℝ → ℝ := fun x => if x < 0 then 0 else 1
  let G : ℝ → ℝ := fun _ => 0
  change ContinuousPrimitiveOn F G I ∧ ContinuousPrimitiveOn G G I ∧
    (∀ x : ℝ, x < 0 → F x = 0) ∧ (∀ x : ℝ, 0 < x → F x = 1) ∧
    ¬ (∃ c : ℝ, ∀ x ∈ I, F x - G x = c)
  have hd (x : ℝ) (hx : x ∈ I) : HasDerivAt F (G x) x := by
    rcases hx with hx | hx
    · apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      exact ite_eq_left hy
    · apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      exact ite_eq_right (not_lt.mpr (le_of_lt hy))
  refine ⟨⟨fun x hx => (hd x hx).continuousAt.continuousWithinAt,
    fun x hx => hd x (interior_subset hx)⟩,
    ⟨continuousOn_const, fun x _ => hasDerivAt_const x 0⟩,
    fun x hx => ite_eq_left hx, fun x hx => ite_eq_right (not_lt.mpr hx.le), ?_⟩
  rintro ⟨c, hc⟩
  have hm := hc (-1) (by simp [I])
  have hp := hc 1 (by simp [I])
  norm_num [F, G] at hm hp
  linarith

end SingleVariableAnalysis
