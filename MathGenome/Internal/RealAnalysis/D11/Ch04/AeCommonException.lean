import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.AeCommonException

/-!
# Ordinary almost everywhere and common countable exceptions

The exceptional envelope is measurable in the given sigma-algebra, even on
an incomplete space. The native a.e. bridge uses the canonical outer values
only to obtain a measurable null envelope; it does not infer measurability
of the failure set. No measurability of the functions is needed for equality
congruence. All results allow empty spaces, zero measures and empty families.
-/

open Set MeasureTheory Filter
open scoped Topology

universe u v w z

namespace D11.Ch04.AeCommonException

open D11.Ch01.MeasureDefinitions

/-- A property holds off a measurable null set in the original space. -/
def almostEverywhere {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (P : α → Prop) : Prop :=
  ∃ N : Set α, measurableNull μ N ∧ ∀ x, x ∉ N → P x

/-- Equality of functions outside a measurable null envelope. -/
def aeEq {α : Type u} {β : Type v} [MeasurableSpace α]
    (μ : Measure α) (f g : α → β) : Prop :=
  almostEverywhere μ (fun x => f x = g x)

theorem almostEverywhere_iff_native {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (P : α → Prop) :
    almostEverywhere μ P ↔ ∀ᵐ x ∂μ, P x := by
  classical
  rw [MeasureTheory.ae_iff]
  constructor
  · rintro ⟨N, ⟨_, hN⟩, hP⟩
    exact measure_mono_null (fun x hx => by
      by_contra hxN
      exact hx (hP x hxN)) hN
  · intro h
    obtain ⟨N, hsub, hN, hμN⟩ := exists_measurable_superset_of_null h
    refine ⟨N, ⟨hN, hμN⟩, fun x hx => ?_⟩
    by_contra hPx
    exact hx (hsub hPx)

theorem almostEverywhere_iff_negligible {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (P : α → Prop) :
    almostEverywhere μ P ↔ negligible μ {x | ¬ P x} := by
  rw [almostEverywhere_iff_native, negligible_iff, MeasureTheory.ae_iff]

theorem almostEverywhere_of_forall {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (P : α → Prop) (h : ∀ x, P x) : almostEverywhere μ P :=
  ⟨∅, ⟨MeasurableSet.empty, measure_empty⟩, fun x _ => h x⟩

theorem almostEverywhere_mono {α : Type u} [MeasurableSpace α]
    (μ : Measure α) (P Q : α → Prop) (hP : almostEverywhere μ P)
    (hPQ : ∀ x, P x → Q x) : almostEverywhere μ Q := by
  obtain ⟨N, hN, h⟩ := hP
  exact ⟨N, hN, fun x hx => hPQ x (h x hx)⟩

theorem aeEq_iff_native {α : Type u} {β : Type v} [MeasurableSpace α]
    (μ : Measure α) (f g : α → β) : aeEq μ f g ↔ f =ᵐ[μ] g :=
  almostEverywhere_iff_native μ (fun x => f x = g x)

theorem aeEq_refl {α : Type u} {β : Type v} [MeasurableSpace α]
    (μ : Measure α) (f : α → β) : aeEq μ f f :=
  almostEverywhere_of_forall μ _ (fun _ => rfl)

theorem aeEq_symm {α : Type u} {β : Type v} [MeasurableSpace α]
    (μ : Measure α) (f g : α → β) (h : aeEq μ f g) : aeEq μ g f :=
  almostEverywhere_mono μ _ _ h (fun _ hx => hx.symm)

theorem aeEq_trans {α : Type u} {β : Type v} [MeasurableSpace α]
    (μ : Measure α) (f g h : α → β) (hfg : aeEq μ f g) (hgh : aeEq μ g h) :
    aeEq μ f h := by
  obtain ⟨N, ⟨hN, hμN⟩, hfg⟩ := hfg
  obtain ⟨M, ⟨hM, hμM⟩, hgh⟩ := hgh
  refine ⟨N ∪ M, ⟨hN.union hM, measure_union_null hμN hμM⟩, ?_⟩
  intro x hx
  exact (hfg x (fun hxN => hx (Or.inl hxN))).trans
    (hgh x (fun hxM => hx (Or.inr hxM)))

theorem aeEq_equivalence {α : Type u} {β : Type v} [MeasurableSpace α]
    (μ : Measure α) : Equivalence (aeEq (β := β) μ) :=
  ⟨aeEq_refl μ, fun {f g} => aeEq_symm μ f g,
    fun {f g h} => aeEq_trans μ f g h⟩

/-- A measurable null union works for every assertion of a countable family. -/
theorem common_exception {α : Type u} {ι : Type v} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (P : ι → α → Prop) (h : ∀ i, almostEverywhere μ (P i)) :
    ∃ N : Set α, measurableNull μ N ∧ ∀ x, x ∉ N → ∀ i, P i x := by
  classical
  choose N hN hP using h
  refine ⟨⋃ i, N i, ⟨MeasurableSet.iUnion (fun i => (hN i).1), ?_⟩, ?_⟩
  · exact measure_iUnion_null_iff.mpr (fun i => (hN i).2)
  · intro x hx i
    exact hP i x (fun hxi => hx (mem_iUnion.mpr ⟨i, hxi⟩))

theorem almostEverywhere_all_iff {α : Type u} {ι : Type v}
    [MeasurableSpace α] [Countable ι] (μ : Measure α) (P : ι → α → Prop) :
    almostEverywhere μ (fun x => ∀ i, P i x) ↔ ∀ i, almostEverywhere μ (P i) := by
  constructor
  · intro h i
    exact almostEverywhere_mono μ _ _ h (fun _ hx => hx i)
  · exact common_exception μ P

/-- Applying any defined unary operation preserves a.e. equality. -/
theorem aeEq_unary {α : Type u} {β : Type v} {γ : Type w} [MeasurableSpace α]
    (μ : Measure α) (f g : α → β) (φ : β → γ) (h : aeEq μ f g) :
    aeEq μ (fun x => φ (f x)) (fun x => φ (g x)) :=
  almostEverywhere_mono μ _ _ h (fun _ hx => congrArg φ hx)

/-- Includes addition, multiplication, scalar linear combinations and division
where defined, without requiring measurability or continuity of the operation. -/
theorem aeEq_binary {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}
    [MeasurableSpace α] (μ : Measure α) (f g : α → β) (h k : α → γ)
    (φ : β → γ → δ) (hfg : aeEq μ f g) (hhk : aeEq μ h k) :
    aeEq μ (fun x => φ (f x) (h x)) (fun x => φ (g x) (k x)) := by
  obtain ⟨N, ⟨hN, hμN⟩, hfg⟩ := hfg
  obtain ⟨M, ⟨hM, hμM⟩, hhk⟩ := hhk
  refine ⟨N ∪ M, ⟨hN.union hM, measure_union_null hμN hμM⟩, ?_⟩
  intro x hx
  change φ (f x) (h x) = φ (g x) (k x)
  rw [hfg x (fun h => hx (Or.inl h)), hhk x (fun h => hx (Or.inr h))]

/-- In particular applies to a finite tuple. It also covers countable extrema,
limsup/liminf, or any operation on a countable tuple wherever it is defined. -/
theorem aeEq_countable_operation {α : Type u} {ι : Type v} {β : Type w} {γ : Type z}
    [MeasurableSpace α] [Countable ι] (μ : Measure α)
    (f g : ι → α → β) (φ : (ι → β) → γ) (h : ∀ i, aeEq μ (f i) (g i)) :
    aeEq μ (fun x => φ (fun i => f i x)) (fun x => φ (fun i => g i x)) := by
  obtain ⟨N, hN, hfg⟩ := common_exception μ (fun i x => f i x = g i x) h
  exact ⟨N, hN, fun x hx => congrArg φ (funext (hfg x hx))⟩

/-- If the two equal-a.e. sequences have pointwise limits a.e., those limits
are equal a.e. Both convergence exceptions are included in the envelope. -/
theorem aeEq_pointwise_limit {α : Type u} {β : Type v}
    [MeasurableSpace α] [TopologicalSpace β] [T2Space β]
    (μ : Measure α) (f g : ℕ → α → β) (F G : α → β)
    (h : ∀ n, aeEq μ (f n) (g n))
    (hF : almostEverywhere μ (fun x => Tendsto (fun n => f n x) atTop (𝓝 (F x))))
    (hG : almostEverywhere μ (fun x => Tendsto (fun n => g n x) atTop (𝓝 (G x)))) :
    aeEq μ F G := by
  obtain ⟨N, ⟨hN, hμN⟩, hfg⟩ := common_exception μ (fun n x => f n x = g n x) h
  obtain ⟨M, ⟨hM, hμM⟩, hF⟩ := hF
  obtain ⟨K, ⟨hK, hμK⟩, hG⟩ := hG
  refine ⟨(N ∪ M) ∪ K,
    ⟨(hN.union hM).union hK, measure_union_null (measure_union_null hμN hμM) hμK⟩, ?_⟩
  intro x hx
  have hxN : x ∉ N := fun h => hx (Or.inl (Or.inl h))
  have hxM : x ∉ M := fun h => hx (Or.inl (Or.inr h))
  have hxK : x ∉ K := fun h => hx (Or.inr h)
  exact tendsto_nhds_unique_of_forall (hF x hxM) (hG x hxK) (hfg x hxN)

end D11.Ch04.AeCommonException
