import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.KolmogorovExtension
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.CountableCylinderReduction
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.IonescuTulcea
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch04.Disintegration
import Mathlib.Data.Set.Countable

open MeasureTheory ProbabilityTheory Set
open ProbabilityFoundations.Ch05.CylinderFramework
open ProbabilityFoundations.Ch05.IonescuTulcea

namespace ProbabilityFoundations.Ch05.KolmogorovExtension

universe u v

/-- A consistent sequence of prefix laws is realized by disintegrating each
successive law and applying Ionescu--Tulcea. -/
theorem exists_of_prefix_laws (S : ℕ → Type v) [∀ n, MeasurableSpace (S n)]
    [∀ n, Nonempty (S n)] (hS : ∀ n, Ch04.IsStandardBorel (S n))
    (p : (n : ℕ) → Measure (PrefixSpace S n))
    [∀ n, IsProbabilityMeasure (p n)] (hp : PrefixConsistent S p) :
    ∃ ν : Measure (ProductSpace S), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (prefixProjection S n) = p n := by
  let M (n : ℕ) := (p (n+2)).map (prefixSplit S (n+1))
  have hM (n : ℕ) : IsProbabilityMeasure (M n) := by
    dsimp [M]
    exact (Measure.isProbabilityMeasure_map_iff (prefixSplit S (n+1)).measurable.aemeasurable).2 inferInstance
  have hfst (n : ℕ) : (M n).map Prod.fst = p (n+1) := by
    rw [Measure.map_map measurable_fst (prefixSplit S (n+1)).measurable]
    exact hp (n+1) (n+2) (Nat.le_succ _)
  have hdis (n : ℕ) := Ch04.disintegration (hS (n+1)) (M n) (p (n+1)) (hfst n)
  choose K hK hprod using hdis
  let _ : ∀ n, IsMarkovKernel (K n) := hK
  let μ₁ : Measure (S 0) := (p 1).map (fun x => x ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ 0)⟩)
  have hμ₁ : IsProbabilityMeasure μ₁ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 inferInstance
  have hrec (n : ℕ) : nonemptyPrefixLaw S μ₁ K n = p (n+1) := by
    induction n with
    | zero =>
      change μ₁.map (initialPrefix S) = p 1
      dsimp only [μ₁]
      rw [Measure.map_map (measurable_initialPrefix (S := S))
        (measurable_pi_apply (⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ 0)⟩ : Finset.range 1))]
      have heq : initialPrefix S ∘ (fun x : PrefixSpace S 1 => x ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ 0)⟩) = id := by
        funext x
        apply (prefixSplit S 0).injective
        apply Prod.ext
        · funext i
          exact False.elim (by simpa using i.2)
        · rfl
      rw [heq, Measure.map_id]
    | succ n ih =>
      rw [nonemptyPrefixLaw, ih]
      have hn := hprod n
      change M n = (p (n+1)).compProd (K n) at hn
      rw [← hn]
      exact MeasurableEquiv.map_symm_map _
  obtain ⟨ν, ⟨hν, _, hνp⟩, _⟩ := ionescuTulcea S μ₁ K
  refine ⟨ν, hν, fun n => ?_⟩
  cases n with
  | zero =>
    rw [hνp]
    have h0 := hp 0 1 (Nat.zero_le 1)
    have heq : prefixRestriction S (Nat.zero_le 1) =
        fun _ : PrefixSpace S 1 => emptyPrefix S := by
      funext x i
      exact False.elim (by simpa using i.2)
    rw [heq, Measure.map_const, measure_univ, one_smul] at h0
    exact h0
  | succ n => exact (hνp (n+1)).trans (hrec n)


variable {I : Type u} {S : I → Type v} [∀ i, MeasurableSpace (S i)]

/-- Finite support of the first `n` terms of an enumeration. Repetitions are
allowed, so the same construction covers finite nonempty subfamilies. -/
noncomputable def enumerationSupport (e : ℕ → I) (n : ℕ) : Finset I :=
  by classical exact (Finset.range n).image e

/-- Read an enumerated prefix from its finite support. -/
noncomputable def enumerationPrefix (e : ℕ → I) (n : ℕ) :
    FiniteProduct S (enumerationSupport e n) → PrefixSpace (fun k => S (e k)) n :=
  by
    classical
    exact fun x k => x ⟨e k, Finset.mem_image.mpr ⟨k, k.2, rfl⟩⟩

@[fun_prop]
theorem measurable_enumerationPrefix (e : ℕ → I) (n : ℕ) :
    Measurable (enumerationPrefix (S := S) e n) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

/-- Any sequence of coordinates, even with repetitions, has its prescribed
joint prefix laws under one probability on the sequence space. -/
theorem exists_enumerated_law [∀ i, Nonempty (S i)]
    (hS : ∀ i, Ch04.IsStandardBorel (S i)) (μ : FiniteLaws S)
    (hprob : IsProbabilityFamily S μ) (hcons : Consistent S μ) (e : ℕ → I) :
    ∃ ν : Measure (ProductSpace (fun n => S (e n))), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (prefixProjection (fun k => S (e k)) n) =
        (μ (enumerationSupport e n)).map (enumerationPrefix e n) := by
  classical
  let _ : ∀ F, IsProbabilityMeasure (μ F) := hprob
  let p := fun n => (μ (enumerationSupport e n)).map (enumerationPrefix (S := S) e n)
  have hp : ∀ n, IsProbabilityMeasure (p n) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (measurable_enumerationPrefix (S := S) e n).aemeasurable).2
      inferInstance
  apply exists_of_prefix_laws (fun n => S (e n)) (fun n => hS (e n)) p
  intro m n hmn
  have hsub : enumerationSupport e m ⊆ enumerationSupport e n :=
    Finset.image_subset_image (Finset.range_mono hmn)
  dsimp only [p]
  rw [Measure.map_map (measurable_prefixRestriction (fun k => S (e k)) hmn) (measurable_enumerationPrefix (S := S) e n),
    ← hcons _ _ hsub,
    Measure.map_map (measurable_enumerationPrefix (S := S) e m) (measurable_finiteRestriction S hsub)]
  rfl


/-- Transport along equality of coordinate indices is measurable for the
specified measurable spaces. -/
theorem measurable_coordinateCast {i j : I} (h : i = j) :
    Measurable (fun x : S i => cast (congrArg S h) x) := by
  cases h
  exact measurable_id

omit [∀ i, MeasurableSpace (S i)] in
/-- Evaluation commutes with transport of a coordinate index. -/
theorem coordinateCast_apply {F : Finset I} {i j : I} (h : i = j)
    (hi : i ∈ F) (hj : j ∈ F) (x : FiniteProduct S F) :
    cast (congrArg S h) (x ⟨i, hi⟩) = x ⟨j, hj⟩ := by
  cases h
  rfl

/-- Every countable coordinate subfamily has its specified finite laws. -/
theorem hasCountableExtensions [∀ i, Nonempty (S i)]
    (hS : ∀ i, Ch04.IsStandardBorel (S i)) (μ : FiniteLaws S)
    (hprob : IsProbabilityFamily S μ) (hcons : Consistent S μ) :
    CountableCylinderReduction.HasCountableExtensions S μ := by
  classical
  let _ : ∀ F, IsProbabilityMeasure (μ F) := hprob
  intro J hJ
  by_cases hne : J.Nonempty
  · obtain ⟨f, hf⟩ := hJ.exists_surjective hne
    choose r hr using hf
    let e : ℕ → I := fun n => f n
    have he (j : J) : e (r j) = (j : I) := congrArg Subtype.val (hr j)
    obtain ⟨ν, hν, hνp⟩ := exists_enumerated_law hS μ hprob hcons e
    let _ : IsProbabilityMeasure ν := hν
    let decode : ProductSpace (fun n => S (e n)) → ProductSpace (fun j : J => S j) :=
      fun x j => cast (congrArg S (he j)) (x (r j))
    have hdecode : Measurable decode :=
      Measurable.of_eval (fun j => (measurable_coordinateCast (he j)).comp (measurable_pi_apply _))
    refine ⟨ν.map decode, inferInstance, fun F hF => ?_⟩
    let indices : Finset ℕ := F.attach.image (fun i : F => r ⟨i.val, hF i.property⟩)
    obtain ⟨n, hn⟩ := indices.exists_nat_subset_range
    have hbound (i : F) : r ⟨i, hF i.2⟩ ∈ Finset.range n :=
      hn (Finset.mem_image.mpr ⟨i, Finset.mem_attach _ _, rfl⟩)
    have hsub : F ⊆ enumerationSupport e n := by
      intro i hi
      exact Finset.mem_image.mpr ⟨r ⟨i, hF hi⟩, hbound ⟨i, hi⟩, he ⟨i, hF hi⟩⟩
    let read : PrefixSpace (fun k => S (e k)) n → FiniteProduct S F :=
      fun x i => cast (congrArg S (he ⟨i, hF i.2⟩))
        (x ⟨r ⟨i, hF i.2⟩, hbound i⟩)
    have hread : Measurable read :=
      Measurable.of_eval (fun i => (measurable_coordinateCast (he ⟨i, hF i.2⟩)).comp
        (measurable_pi_apply _))
    rw [Measure.map_map (CountableCylinderReduction.measurable_subfamilyProjection J F hF) hdecode]
    change ν.map (read ∘ prefixProjection (fun k => S (e k)) n) = μ F
    rw [← Measure.map_map hread (measurable_prefixProjection _ n), hνp,
      Measure.map_map hread (measurable_enumerationPrefix (S := S) e n)]
    have hreadq : read ∘ enumerationPrefix e n = finiteRestriction S hsub := by
      funext x i
      exact coordinateCast_apply (he ⟨i, hF i.2⟩) _ _ x
    rw [hreadq]
    exact hcons _ _ hsub
  · let toEmpty : FiniteProduct S ∅ → ProductSpace (fun j : J => S j) :=
      fun _ j => False.elim (hne ⟨j, j.2⟩)
    have hm : Measurable toEmpty := Measurable.of_eval (fun j => False.elim (hne ⟨j, j.2⟩))
    refine ⟨(μ ∅).map toEmpty, inferInstance, fun F hF => ?_⟩
    have hFempty : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hne ⟨i, hF hi⟩
    subst F
    rw [Measure.map_map (CountableCylinderReduction.measurable_subfamilyProjection J ∅ hF) hm]
    have hid : CountableCylinderReduction.subfamilyProjection S J ∅ hF ∘ toEmpty =
        (id : FiniteProduct S ∅ → FiniteProduct S ∅) := by
      funext x i
      exact (Finset.notMem_empty (i : I) i.2).elim
    rw [hid, Measure.map_id]


/-- Kolmogorov extension on the cylinder sigma-algebra for arbitrary index sets.
Nonemptiness follows from the singleton laws; the empty-coordinate law is retained. -/
theorem kolmogorov_extension :
    Specs.ProbabilityFoundations.Ch05.KolmogorovExtension.Extension.{u,v} := by
  intro I S inst hS μ hprob hcons
  classical
  let _ : ∀ i, Nonempty (S i) := fun i => by
    let _ : IsProbabilityMeasure (μ {i}) := hprob {i}
    obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure (μ {i})
    exact ⟨x ⟨i, Finset.mem_singleton_self i⟩⟩
  exact CountableCylinderReduction.countable_cylinder_reduction S μ hprob hcons
    (hasCountableExtensions hS μ hprob hcons)

end ProbabilityFoundations.Ch05.KolmogorovExtension
