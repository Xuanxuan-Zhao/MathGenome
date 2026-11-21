import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.ProductMetrization
import MathGenome.Internal.PointSetTopology.D10Topology.Ch10.CountableProductMetric
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricTopology

/-! Metrization of arbitrary nonempty products (d10:10:product-metric).
A countable local basis uses only countably many coordinates. In a T₁
product every other coordinate must be a singleton. Conversely, restriction
to the countably many nonsingleton coordinates is an embedding into a
countable product of metrizable spaces. -/

open Set Filter Topology
open scoped Topology
universe u v
namespace D10Topology.Ch10
open D10Topology.Ch09 D10Topology.Ch03

/-- Fixing all but one coordinate realizes a factor as a topological subspace. -/
theorem factor_metrizable_of_product {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (a : ∀ i, X i)
    (h : Metrizable (productTopology tX)) (i : I) : Metrizable (tX i) := by
  classical
  letI := tX
  rw [productTopology_eq_pi] at h
  letI := (metrizable_iff_mathlib _).mp h
  apply (metrizable_iff_mathlib _).mpr
  have hl : Function.LeftInverse (Function.eval i) (fun y => Function.update a i y) := by
    intro y
    simp
  exact (hl.isEmbedding (continuous_apply i)
    (continuous_const.update i continuous_id)).metrizableSpace

/-- A first-countable T₁ product with a point has only countably many
nonsingleton factors. The finite supports below come from actual product
neighborhoods, without any countability assumption on the index type. -/
theorem countable_nontrivial_factors {I : Type u} {X : I → Type v}
    [∀ i, TopologicalSpace (X i)] [∀ i, T1Space (X i)]
    [FirstCountableTopology (∀ i, X i)] (a : ∀ i, X i) :
    {i : I | ¬ Subsingleton (X i)}.Countable := by
  classical
  obtain ⟨U, hU⟩ := (𝓝 a).exists_antitone_basis
  have hfinite : ∀ n : ℕ, ∃ F : Finset I, ∃ V : ∀ i, Set (X i),
      (∀ i, V i ∈ 𝓝 (a i)) ∧ (F : Set I).pi V ⊆ U n := by
    intro n
    have hn := hU.toHasBasis.mem_of_mem (i := n) trivial
    rwa [nhds_pi, Filter.mem_pi'] at hn
  choose F V hV hsub using hfinite
  apply (Set.countable_iUnion (fun n => (F n).finite_toSet.countable)).mono
  intro i hi
  by_contra hout
  have hFi : ∀ n, i ∉ F n := by simpa only [Set.mem_iUnion, Finset.mem_coe, not_exists] using hout
  apply hi
  have heq : ∀ y : X i, y = a i := by
    intro y
    by_contra hy
    have hN : Function.eval i ⁻¹' ({y}ᶜ : Set (X i)) ∈ 𝓝 a :=
      (isClosed_singleton.isOpen_compl.preimage (continuous_apply i)).mem_nhds (by
        simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using Ne.symm hy)
    obtain ⟨n, _, hn⟩ := hU.toHasBasis.mem_iff.mp hN
    have hup : Function.update a i y ∈ U n := by
      apply hsub n
      intro j hj
      have hji : j ≠ i := by
        intro hji
        subst j
        exact hFi n hj
      simpa only [Function.update_of_ne hji] using mem_of_mem_nhds (hV n j)
    have hbad := hn hup
    simpa only [Set.mem_preimage, Function.eval, Function.update_self,
      Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false] using hbad
  exact ⟨fun x y => (heq x).trans (heq y).symm⟩

/-- Singleton coordinates can be filled with their basepoint values;
restriction to the remaining coordinates preserves the full topology. -/
theorem product_metrizable_of_countable_nontrivial {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (a : ∀ i, X i)
    (hm : ∀ i, Metrizable (tX i))
    (hc : {i : I | ¬ Subsingleton (X i)}.Countable) :
    Metrizable (productTopology tX) := by
  classical
  letI := tX
  let J : Set I := {i | ¬ Subsingleton (X i)}
  letI : Countable J := hc.to_subtype
  letI : Encodable J := hc.toEncodable
  letI : ∀ j : J, TopologicalSpace.MetrizableSpace (X j) :=
    fun j => (metrizable_iff_mathlib _).mp (hm j)
  letI : ∀ j : J, MetricSpace (X j) := fun j => TopologicalSpace.metrizableSpaceMetric (X j)
  letI : MetricSpace (∀ j : J, X j) := PiCountable.metricSpace
  let r : (∀ i, X i) → (∀ j : J, X j) := fun x j => x j
  let e : (∀ j : J, X j) → (∀ i, X i) :=
    fun x i => if hi : i ∈ J then x ⟨i, hi⟩ else a i
  have hl : Function.LeftInverse e r := by
    intro x
    funext i
    dsimp [e, r]
    split_ifs with hi
    · rfl
    · have hs : Subsingleton (X i) := not_not.mp hi
      exact hs.elim _ _
  have he : Continuous e := by
    apply continuous_pi
    intro i
    by_cases hi : i ∈ J
    · simpa only [e, dite_eq_left hi] using (continuous_apply (⟨i, hi⟩ : J))
    · simpa only [e, dite_eq_right hi] using (continuous_const (y := a i))
  have hr : Continuous r := continuous_pi fun j => continuous_apply (j : I)
  rw [productTopology_eq_pi]
  exact (metrizable_iff_mathlib _).mpr (hl.isEmbedding he hr).metrizableSpace

/-- Exact arbitrary-index characterization. Nonempty products include the
empty index family and ensure that subsingleton factors are singletons. -/
theorem product_metrizable_iff {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (hne : Nonempty (∀ i, X i)) :
    Metrizable (productTopology tX) ↔
      (∀ i, Metrizable (tX i)) ∧ {i : I | ¬ Subsingleton (X i)}.Countable := by
  obtain ⟨a⟩ := hne
  constructor
  · intro h
    have hm := factor_metrizable_of_product tX a h
    refine ⟨hm, ?_⟩
    letI := tX
    letI : ∀ i, TopologicalSpace.MetrizableSpace (X i) :=
      fun i => (metrizable_iff_mathlib _).mp (hm i)
    rw [productTopology_eq_pi] at h
    letI := (metrizable_iff_mathlib _).mp h
    exact countable_nontrivial_factors a
  · rintro ⟨hm, hc⟩
    exact product_metrizable_of_countable_nontrivial tX a hm hc

/-- The conclusion using the literal assertion that every factor outside a
countable exceptional set has a unique point. -/
theorem product_metrizable_iff_singletons {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (hne : Nonempty (∀ i, X i)) :
    Metrizable (productTopology tX) ↔
      (∀ i, Metrizable (tX i)) ∧
        ∃ J : Set I, J.Countable ∧ ∀ i ∉ J, ∃! x : X i, True := by
  classical
  rw [product_metrizable_iff tX hne]
  constructor
  · rintro ⟨hm, hc⟩
    refine ⟨hm, {i | ¬ Subsingleton (X i)}, hc, ?_⟩
    intro i hi
    have hs : Subsingleton (X i) := not_not.mp hi
    exact ⟨hne.some i, trivial, fun y _ => hs.elim _ _⟩
  · rintro ⟨hm, J, hc, hJ⟩
    refine ⟨hm, hc.mono ?_⟩
    intro i hi
    by_contra hout
    obtain ⟨x, _, hx⟩ := hJ i hout
    exact hi ⟨fun y z => (hx y trivial).trans (hx z trivial).symm⟩

theorem finite_product_metrizable {I : Type u} {X : I → Type v} [Finite I]
    (tX : ∀ i, TopologicalSpace (X i)) (hm : ∀ i, Metrizable (tX i)) :
    Metrizable (productTopology tX) := by
  letI := tX
  letI : ∀ i, TopologicalSpace.MetrizableSpace (X i) :=
    fun i => (metrizable_iff_mathlib _).mp (hm i)
  rw [productTopology_eq_pi]
  exact (metrizable_iff_mathlib _).mpr inferInstance

theorem empty_product_metrizable {I : Type u} {X : I → Type v} [IsEmpty I]
    (tX : ∀ i, TopologicalSpace (X i)) :
    (∃! x : (∀ i, X i), True) ∧ Metrizable (productTopology tX) := by
  exact ⟨empty_product_singleton, finite_product_metrizable tX (fun i => isEmptyElim i)⟩

theorem empty_factor_product_metrizable {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (i : I) [IsEmpty (X i)] :
    IsEmpty (∀ j, X j) ∧ Metrizable (productTopology tX) := by
  letI : IsEmpty (∀ j, X j) := product_empty_of_factor i
  refine ⟨inferInstance, ?_⟩
  letI := productTopology tX
  exact (metrizable_iff_mathlib _).mpr inferInstance

end D10Topology.Ch10
