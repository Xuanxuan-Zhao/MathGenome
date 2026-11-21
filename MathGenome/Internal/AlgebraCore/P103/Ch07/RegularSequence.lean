import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.RegularSequence
import MathGenome.Internal.AlgebraCore.P103.Ch07.RegularDomain
import MathGenome.Internal.AlgebraCore.P103.Ch07.EmbeddingDimension
import MathGenome.Internal.AlgebraCore.P103.Ch06.SystemsParameters
import MathGenome.Internal.AlgebraCore.P103.Ch06.KrullHeight
import Mathlib.RingTheory.LocalRing.RingHom.Basic

namespace P103.Ch07.RegularSequence

noncomputable section
open IsLocalRing
open P103.Specs.Ch07.EmbeddingDimension
open P103.Specs.Ch06.DimensionConventions
open P103.Specs.Ch07.RegularSequence
universe u
variable {R : Type u} [CommRing R]

lemma spanFinrank_ofList_le_length (xs : List R) :
    (Ideal.ofList xs).spanFinrank ≤ xs.length := by
  classical
  have h := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := R) (M := R) (s := {x | x ∈ xs}) (by simp)
  have he : {x | x ∈ xs} = (xs.toFinset : Set R) := by ext; simp
  rw [he, Set.ncard_coe_finset] at h
  change (Submodule.span R {x | x ∈ xs}).spanFinrank ≤ xs.length
  rw [he]
  exact h.trans xs.toFinset_card_le

lemma ofList_take_le [IsLocalRing R] (xs : List R)
    (hxs : Ideal.ofList xs = maximalIdeal R) (i : ℕ) :
    Ideal.ofList (xs.take i) ≤ maximalIdeal R := by
  rw [← hxs]
  exact Ideal.span_mono (fun _ h => List.mem_of_mem_take h)

lemma map_drop_eq_maximal [IsLocalRing R] (xs : List R)
    (hxs : Ideal.ofList xs = maximalIdeal R) (I : Ideal R)
    [IsLocalRing (R ⧸ I)] (j : ℕ) (hj : Ideal.ofList (xs.take j) ≤ I) :
    Ideal.ofList ((xs.drop j).map (Ideal.Quotient.mk I)) = maximalIdeal (R ⧸ I) := by
  have hbot : (Ideal.ofList (xs.take j)).map (Ideal.Quotient.mk I) = ⊥ := by
    apply bot_unique
    rw [Ideal.map_le_iff_le_comap, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact hj
  have h := congrArg (Ideal.map (Ideal.Quotient.mk I)) hxs
  rw [← List.take_append_drop j xs, Ideal.ofList_append, Ideal.map_sup,
    hbot, bot_sup_eq, Ideal.map_ofList] at h
  exact h.trans (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective)

/-- Dimension comparison proves regularity simultaneously for all prefixes. -/
lemma prefix_regular [IsNoetherianRing R] [IsLocalRing R]
    (d : ℕ) (xs : List R) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (hlen : xs.length = d) (hxs : Ideal.ofList xs = maximalIdeal R)
    (i : ℕ) (hi : i ≤ d) :
    IsRegularLocalRing (R ⧸ Ideal.ofList (xs.take i)) ∧
      ringKrullDim (R ⧸ Ideal.ofList (xs.take i)) = ((d-i : ℕ) : WithBot ℕ∞) := by
  let I := Ideal.ofList (xs.take i)
  have hI : I ≤ maximalIdeal R := ofList_take_le xs hxs i
  have hne : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨n, _, hn, _, _⟩ := P103.Ch06.SystemsParameters.local_ring_parameters (R ⧸ I)
  have hgen := map_drop_eq_maximal xs hxs I i le_rfl
  have he : embeddingDimensionValue (R ⧸ I) ≤ d - i := by
    change Module.finrank _ _ ≤ _
    rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← hgen]
    have hb := spanFinrank_ofList_le_length ((xs.drop i).map (Ideal.Quotient.mk I))
    simpa [hlen] using hb
  have hlow : d ≤ n + i := by
    have hb := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
      (hI.trans (by rw [ringJacobson_eq_maximalIdeal]))
    have hc : I.spanFinrank ≤ i :=
      (spanFinrank_ofList_le_length (xs.take i)).trans (by simp)
    have hc' : (I.spanFinrank : WithBot ℕ∞) ≤ (i : WithBot ℕ∞) := by exact_mod_cast hc
    have hb' := hb.trans (add_le_add le_rfl hc')
    rw [hd, hn, ← Nat.cast_add] at hb'
    exact_mod_cast hb'
  have hu : n ≤ embeddingDimensionValue (R ⧸ I) :=
    P103.Ch07.EmbeddingDimension.dimension_bound (R ⧸ I) n hn
  have hnd : n = d-i := by omega
  have hen : embeddingDimensionValue (R ⧸ I) = n := by omega
  refine ⟨(IsRegularLocalRing.iff_finrank_cotangentSpace _).mpr ?_, ?_⟩
  · change (embeddingDimensionValue (R ⧸ I) : WithBot ℕ∞) = ringKrullDim (R ⧸ I)
    rw [hen, hn]
  · simpa [hnd] using hn

/-- All orders are allowed: the first i generators cannot already contain
    generator i, since consecutive prefix dimensions differ by one. -/
theorem generatingList : generatingListType.{u} := by
  intro R _ _ _ d xs _hreg hd hlen hxs
  refine ⟨fun i hi => prefix_regular d xs hd hlen hxs i hi, ?_, ?_⟩
  · intro i hi
    have hid : i < d := by omega
    let I := Ideal.ofList (xs.take i)
    have hp := prefix_regular d xs hd hlen hxs i (by omega)
    let : IsRegularLocalRing (R ⧸ I) := hp.1
    have hr : regularLocalValue (R ⧸ I) :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace (R ⧸ I)).mp inferInstance
    let : IsDomain (R ⧸ I) := P103.RegularDomain.domain (R ⧸ I) hr
    have hnonzero : Ideal.Quotient.mk I xs[i] ≠ 0 := by
      intro hz
      have hm : xs[i] ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
      have heq : Ideal.ofList (xs.take (i+1)) = I := by
        rw [List.take_succ_eq_append_getElem hi, Ideal.ofList_append,
          Ideal.ofList_singleton]
        exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hm)
      have hn := (prefix_regular d xs hd hlen hxs (i+1) (by omega)).2
      rw [heq] at hn
      have he : ((d-i : ℕ) : WithBot ℕ∞) = ((d-(i+1) : ℕ) : WithBot ℕ∞) :=
        hp.2.symm.trans hn
      have hn' : d-i = d-(i+1) := by exact_mod_cast he
      omega
    intro a b hab
    exact mul_left_cancel₀ hnonzero hab
  · rw [hxs]
    exact (maximalIdeal.isMaximal R).ne_top

/-- Deletion-minimal generators have exactly the cotangent-space dimension. -/
theorem minimalGenerators : minimalGeneratorsType.{u} := by
  intro R _ _ _ d x hreg hx
  obtain ⟨b, _⟩ := P103.Ch07.EmbeddingDimension.minimal_generators_basis R (Fin d) x hx
  have he : embeddingDimensionValue R = d := by
    simpa [embeddingDimensionValue] using Module.finrank_eq_card_basis b
  have hd : ringDimensionValue R = (d : WithBot ℕ∞) := by
    change (embeddingDimensionValue R : WithBot ℕ∞) = ringDimensionValue R at hreg
    simpa [he] using hreg.symm
  refine ⟨hd, generatingList R d (List.ofFn (fun i => (x i : R))) ?_ hd (by simp) ?_⟩
  · change (embeddingDimensionValue R : WithBot ℕ∞) = ringDimensionValue R
    rw [he, hd]
  · have hs : Ideal.ofList (List.ofFn (fun i => (x i : R))) =
        Ideal.span (Set.range (fun i => (x i : R))) := by
      apply congrArg (Ideal.span : Set R → Ideal R)
      ext a
      exact List.mem_ofFn
    rw [hs]
    exact (P103.Ch07.EmbeddingDimension.generators_iff_ideal_span R (Fin d) x).mp hx.1

end
end P103.Ch07.RegularSequence
