import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BasisNotHamel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15Basis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15Unconditional
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.OrthonormalExpansion
import Mathlib.Analysis.PSeries
import Mathlib.Basic.Denumerable

/-!
Hamel versus Schauder and orthonormal bases, paper.tex 3962–3974.
Fourier expansion over finite subsets is reused from the accepted arbitrary
orthonormal expansion theorem. Pairing ordered partial sums with a fixed basis
vector proves coefficient uniqueness; no coordinate continuity is assumed.
-/

noncomputable section
open Filter Topology
open scoped BigOperators ENNReal InnerProductSpace
universe u v w

namespace ExpandedFA.P1.BasisNotHamel
open Spec

/-- Algebraic span always means finite synthesis. -/
theorem hamel_expansion_finite : Spec.HamelExpansionFinite.{u, v, w} := by
  intro 𝕜 E _ _ _ I e x
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
    (Finsupp.mem_span_range_iff_exists_finsupp (R := 𝕜) (v := e) (x := x))

/-- The square norms are the shifted convergent p-series with exponent two. -/
lemma reciprocal_mem_lp2 (𝕜 : Type u) [RCLike 𝕜] :
    Memℓp (fun n : ℕ => ((n + 1 : ℕ) : 𝕜)⁻¹) 2 := by
  apply memℓp_gen
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  simpa only [norm_inv, RCLike.norm_natCast, ENNReal.toReal_ofNat, Real.rpow_two,
    inv_pow] using hs

/-- A finite unit-vector combination vanishes off its finite index set. -/
lemma finite_unit_synthesis_apply (𝕜 : Type u) [RCLike 𝕜]
    (s : Finset ℕ) (a : ℕ → 𝕜) (j : ℕ) (hj : j ∉ s) :
    (∑ i ∈ s, a i • unitVector 𝕜 i) j = 0 := by
  classical
  simp only [unitVector, ← lp.single_smul, smul_eq_mul, mul_one,
    lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact lp.single_apply_ne (E := fun _ : ℕ => 𝕜) 2 i (a i)
    (by intro h; subst j; exact hj hi)

theorem reciprocal_vector_not_finite : Spec.ReciprocalVector.{u} := by
  intro 𝕜 _
  let x : lp (fun _ : ℕ => 𝕜) 2 := ⟨_, reciprocal_mem_lp2 𝕜⟩
  have hx (n : ℕ) : x n = ((n + 1 : ℕ) : 𝕜)⁻¹ := rfl
  have hn (n : ℕ) : x n ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  have hfinite (s : Finset ℕ) (a : ℕ → 𝕜) :
      x ≠ ∑ n ∈ s, a n • unitVector 𝕜 n := by
    intro h
    obtain ⟨j, _, hj⟩ := Set.infinite_univ.exists_notMem_finset s
    have hz := congrArg (fun y : lp (fun _ : ℕ => 𝕜) 2 => y j) h
    rw [finite_unit_synthesis_apply 𝕜 s a j hj] at hz
    exact hn j hz
  refine ⟨x, hx, Set.eq_univ_of_forall hn, hfinite, ?_⟩
  intro hspan
  obtain ⟨a, ha⟩ := (hamel_expansion_finite (unitVector 𝕜) x).mp hspan
  exact hfinite a.support a ha.symm

theorem standard_system_not_hamel : Spec.NotHamel.{u} := by
  intro 𝕜 _ h
  obtain ⟨x, _, _, _, hx⟩ := reciprocal_vector_not_finite 𝕜
  apply hx
  rw [h]
  trivial

/-- Totality supplies exactly the maximality hypothesis of the accepted net
expansion theorem. The conclusion retains all finite subsets as indices. -/
theorem hilbert_expansion_over_finite_subsets :
    Spec.HilbertFiniteSubsetExpansion.{u, v, w} := by
  intro I 𝕜 H _ _ _ _ e he hc x
  have hm := (Hilbert.OrthonormalExpansion.maximal_iff_total 𝕜 H I e he).mpr hc
  exact Hilbert.OrthonormalExpansion.finiteSubsetNet_expansion 𝕜 H I e hm x

section Hilbert
variable {𝕜 : Type v} {H : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Pairing a norm-convergent ordered orthonormal expansion identifies its
coefficients. This argument does not require completeness of H. -/
lemma orthonormal_ordered_coefficients {e : ℕ → H} (he : Orthonormal 𝕜 e)
    (x : H) (a : ℕ → 𝕜)
    (ha : Tendsto (C15Basis.orderedPartialSum e a) atTop (𝓝 x)) :
    a = fun n => ⟪e n, x⟫_𝕜 := by
  funext j
  have ht := ((innerSL 𝕜 (e j)).continuous.tendsto x).comp ha
  apply tendsto_nhds_unique _ ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  exact (he.inner_right_sum a (Finset.mem_range.mpr hN)).symm

lemma complete_reindex {I : Type u} (e : I → H)
    (hc : (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤)
    {J : Type*} (σ : J ≃ I) :
    (Submodule.span 𝕜 (Set.range (e ∘ σ))).topologicalClosure = ⊤ := by
  rwa [σ.surjective.range_comp e]

variable [CompleteSpace H]

lemma orthonormal_raw_basis {e : ℕ → H} (he : Orthonormal 𝕜 e)
    (hc : (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤) :
    C15Basis.IsRawSchauderBasis (𝕜 := 𝕜) e := by
  refine ⟨he.ne_zero, fun x => ?_⟩
  refine ⟨(fun n => ⟪e n, x⟫_𝕜), ?_, fun a ha =>
    orthonormal_ordered_coefficients he x a ha⟩
  exact (show HasSum (fun n => ⟪e n, x⟫_𝕜 • e n) x from
    hilbert_expansion_over_finite_subsets e he hc x).tendsto_sum_nat

lemma orthonormal_unconditional_basis {e : ℕ → H} (he : Orthonormal 𝕜 e)
    (hc : (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤) :
    C15Unconditional.IsUnconditionalSchauderBasis 𝕜 H e := by
  have hu (x : H) :
      C15Unconditional.HasUnconditionalSum (fun n => ⟪e n, x⟫_𝕜 • e n) x :=
    hilbert_expansion_over_finite_subsets e he hc x
  refine ⟨⟨he.ne_zero, fun x => ?_⟩, ?_⟩
  · refine ⟨(fun n => ⟪e n, x⟫_𝕜),
      C15Unconditional.hasUnconditionalSum_hasSequentialSum _ x (hu x), ?_⟩
    intro a ha
    exact orthonormal_ordered_coefficients he x a
      ((C01Banach.hasSequentialSum_iff H _ x).mp ha)
  · intro x a ha
    have hcoeff := orthonormal_ordered_coefficients he x a
      ((C01Banach.hasSequentialSum_iff H _ x).mp ha)
    exact ⟨x, hcoeff ▸ hu x⟩

lemma orthonormal_finite_raw_basis {d : ℕ} {e : Fin d → H}
    (he : Orthonormal 𝕜 e)
    (hc : (Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤) :
    C15Basis.IsRawFiniteBasis (𝕜 := 𝕜) e := by
  refine ⟨he.ne_zero, fun x => ?_⟩
  have hsum : (∑ i, ⟪e i, x⟫_𝕜 • e i) = x :=
    (hasSum_fintype _).unique (hilbert_expansion_over_finite_subsets e he hc x)
  refine ⟨(fun i => ⟪e i, x⟫_𝕜), hsum, ?_⟩
  intro a ha
  funext i
  change (∑ j, a j • e j) = x at ha
  rw [← ha]
  exact (he.inner_right_fintype a i).symm

end Hilbert

theorem complete_orthonormal_sequence_unconditional :
    Spec.HilbertSequence.{u, v, w} := by
  intro I 𝕜 H _ _ _ _ e he hc σ
  have ho : Orthonormal 𝕜 (e ∘ σ) := he.comp σ σ.injective
  have ht := complete_reindex e hc σ
  let h := orthonormal_raw_basis ho ht
  refine ⟨h, orthonormal_unconditional_basis ho ht, ?_⟩
  intro x n
  exact congrFun
    (orthonormal_ordered_coefficients ho x _ (C15Basis.rawCoordinates_tendsto h x)) n

theorem complete_orthonormal_finite_unconditional :
    Spec.HilbertFinite.{u, v, w} := by
  intro I 𝕜 H _ _ _ _ e he hc d σ
  have ho : Orthonormal 𝕜 (e ∘ σ) := he.comp σ σ.injective
  let h := orthonormal_finite_raw_basis ho (complete_reindex e hc σ)
  refine ⟨h, C15Unconditional.finiteBasis_isUnconditional 𝕜 H (e ∘ σ) h, ?_⟩
  intro x n
  have ht := congrArg (fun z : H => ⟪e (σ n), z⟫_𝕜)
    (C15Basis.finiteCoordinates_expansion h x)
  exact (ho.inner_right_fintype _ n).symm.trans ht

theorem complete_orthonormal_countable_unconditional :
    Spec.HilbertCountable.{u, v, w} := by
  intro I 𝕜 H _ _ _ _ _ e he hc
  cases finite_or_infinite I with
  | inl hf =>
    let := Fintype.ofFinite I
    let σ := (Fintype.equivFin I).symm
    obtain ⟨h, hu, _⟩ := complete_orthonormal_finite_unconditional e he hc _ σ
    exact Or.inl ⟨_, σ, h, hu⟩
  | inr hi =>
    obtain ⟨σ⟩ : Nonempty (ℕ ≃ I) := nonempty_equiv_of_countable
    obtain ⟨h, hu, _⟩ := complete_orthonormal_sequence_unconditional e he hc σ
    exact Or.inr ⟨σ, h, hu⟩

/-- The standard unit vectors have the actual ℓ² inner products. -/
lemma lp2_units_orthonormal (𝕜 : Type u) [RCLike 𝕜] :
    Orthonormal 𝕜 (unitVector 𝕜) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [unitVector, lp.inner_single_left, RCLike.inner_apply, Pi.single_apply]

lemma lp2_units_total (𝕜 : Type u) [RCLike 𝕜] :
    (Submodule.span 𝕜 (Set.range (unitVector 𝕜))).topologicalClosure = ⊤ := by
  let b : HilbertBasis ℕ 𝕜 (lp (fun _ : ℕ => 𝕜) 2) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl 𝕜 _)
  have hb : ⇑b = unitVector 𝕜 := by
    funext n
    exact (b.repr_symm_single n).symm
  simpa only [hb] using b.dense_span

theorem standard_orthonormal_schauder_system : Spec.StandardSystem.{u} := by
  intro 𝕜 _
  have he := lp2_units_orthonormal 𝕜
  have hc := lp2_units_total 𝕜
  exact ⟨he, hc, orthonormal_raw_basis he hc, orthonormal_unconditional_basis he hc⟩

theorem uncountable_orthonormal_family_not_sequence :
    Spec.UncountableNotSequence.{u, v, w} := by
  intro I 𝕜 H _ _ _ e he hI ⟨s, hs⟩
  have hr : (Set.range e).Countable := hs ▸ Set.countable_range s
  have hi : Function.Injective (fun i : I => (⟨e i, Set.mem_range_self i⟩ : Set.range e)) :=
    fun i j hij => he.linearIndependent.injective (congrArg Subtype.val hij)
  have : Countable (Set.range e) := hr.to_subtype
  exact hI (Function.Injective.countable hi)

end ExpandedFA.P1.BasisNotHamel
