import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.SingularApproximation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
universe u v w z
namespace ExpandedFA.TraceIdeals.TraceClassDefinitions
variable {𝕜 : Type u} [RCLike 𝕜]
  {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [NormedAddCommGroup K]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
  [CompleteSpace H] [CompleteSpace K]

abbrev IsTraceClass := @Spec.IsTraceClassValue
abbrev traceNorm := @Spec.TraceNormValue
abbrev rankOne := @Spec.RankOneValue
abbrev trace := @Spec.TraceValue

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem rankOne_apply (u : K) (v x : H) :
    rankOne (𝕜 := 𝕜) u v x = inner 𝕜 v x • u := rfl

open CompactSpectral

lemma singularValue_zero_index (T : H →L[𝕜] K) :
    SingularApproximation.Spec.SingularValueValue T 0 = 0 := by
  simp [SingularApproximation.Spec.SingularValueValue]

/-- The support of the ordered singular sequence, retaining its one-based index. -/
def positiveIndices (T : H →L[𝕜] K) :=
  {n : ℕ // 0 < n ∧ 0 < SingularApproximation.Spec.SingularValueValue T n}

/-- Every positive spectral fiber has the same cardinality in the ordered
sequence and in any singular expansion. -/
lemma singular_fiber_equiv (T : H →L[𝕜] K)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (a : ℝ) :
    Nonempty ({j // S.sigma j = a} ≃
      {n : positiveIndices T // SingularApproximation.Spec.SingularValueValue T n.val = a}) := by
  classical
  by_cases ha : 0 < a
  · let A := {j // S.sigma j = a}
    let B := {n : positiveIndices T // SingularApproximation.Spec.SingularValueValue T n.val = a}
    let C := {n : ℕ // 0 < n ∧ SingularApproximation.Spec.SingularValueValue T n = a}
    let e : B ≃ C := {
      toFun := fun n => ⟨n.val.val, n.val.property.1, n.property⟩
      invFun := fun n => ⟨⟨n.val, n.property.1, n.property.2.symm ▸ ha⟩, n.property.2⟩
      left_inv := by intro n; rfl
      right_inv := by intro n; rfl }
    have hm := SingularApproximation.singular_spectral_multiplicity 𝕜 H K T hT a ha
    letI : Finite A := (S.finite_multiplicity a ha).to_subtype
    letI : Finite C := hm.2.2.1.to_subtype
    letI : Finite B := Finite.of_injective e e.injective
    letI : Fintype A := Fintype.ofFinite A
    letI : Fintype B := Fintype.ofFinite B
    apply Nonempty.intro (Fintype.equivOfCardEq _)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_congr e]
    exact (SingularApproximation.gram_eigenspace_multiplicity T S ha).symm.trans
      hm.2.2.2.symm
  · letI : IsEmpty {j // S.sigma j = a} := ⟨fun j =>
      ha (j.property ▸ S.positive j.val)⟩
    letI : IsEmpty {n : positiveIndices T //
        SingularApproximation.Spec.SingularValueValue T n.val = a} := ⟨fun n =>
      ha (n.property ▸ n.val.property.2)⟩
    exact ⟨Equiv.equivOfIsEmpty _ _⟩

/-- A multiplicity-preserving numbering of all nonzero singular directions. -/
def singularIndexEquiv (T : H →L[𝕜] K)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) : S.Index ≃ positiveIndices T :=
  Equiv.ofFiberEquiv (fun a => Classical.choice (singular_fiber_equiv T hT S a))

lemma singularIndexEquiv_value (T : H →L[𝕜] K)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H K T) (j : S.Index) :
    SingularApproximation.Spec.SingularValueValue T (singularIndexEquiv T hT S j).val =
      S.sigma j :=
  Equiv.ofFiberEquiv_map
    (f := S.sigma)
    (g := fun n : positiveIndices T => SingularApproximation.Spec.SingularValueValue T n.val)
    (fun a => Classical.choice (singular_fiber_equiv T hT S a)) j

lemma positiveIndices_support (T : H →L[𝕜] K)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap) :
    Function.support (SingularApproximation.Spec.SingularValueValue T) ⊆
      {n | 0 < n ∧ 0 < SingularApproximation.Spec.SingularValueValue T n} := by
  intro n hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by
    rintro rfl
    exact hn (singularValue_zero_index T))
  exact ⟨hn0, lt_of_le_of_ne
    ((SingularApproximation.singular_sequence_properties 𝕜 H K T hT).1 n hn0) hn.symm⟩

theorem singularSystem_sum : Spec.SingularSystemSum.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ _ _ T hT S
  have hfull : Summable (SingularApproximation.Spec.SingularValueValue T) :=
    (summable_nat_add_iff 1).mp hT.2
  let e := singularIndexEquiv T hT.1 S
  have hval (j : S.Index) : SingularApproximation.Spec.SingularValueValue T (e j).val =
      S.sigma j := singularIndexEquiv_value T hT.1 S j
  have hsub := hfull.subtype (fun n => 0 < n ∧
    0 < SingularApproximation.Spec.SingularValueValue T n)
  constructor
  · exact ((e.summable_iff).mpr hsub).congr hval
  · calc
      ∑' j, S.sigma j = ∑' j, SingularApproximation.Spec.SingularValueValue T (e j).val :=
        tsum_congr (fun j => (hval j).symm)
      _ = ∑' n : positiveIndices T, SingularApproximation.Spec.SingularValueValue T n.val :=
        e.tsum_eq (fun n : positiveIndices T => SingularApproximation.Spec.SingularValueValue T n.val)
      _ = ∑' n, SingularApproximation.Spec.SingularValueValue T n :=
        tsum_subtype_eq_of_support_subset (positiveIndices_support T hT.1)
      _ = Spec.TraceNormValue T := by
        rw [hfull.tsum_eq_zero_add, singularValue_zero_index, zero_add]
        rfl

omit [CompleteSpace H] in
/-- A finite Bessel bound for the diagonal of a unit rank-one operator. -/
lemma sum_norm_inner_mul_inner_le_one {ι : Type z} (b : HilbertBasis ι 𝕜 H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (s : Finset ι) :
    ∑ i ∈ s, ‖inner 𝕜 v (b i) * inner 𝕜 (b i) u‖ ≤ 1 := by
  have hp (i : ι) : ‖inner 𝕜 v (b i) * inner 𝕜 (b i) u‖ ≤
      (‖inner 𝕜 (b i) v‖ ^ 2 + ‖inner 𝕜 (b i) u‖ ^ 2) / 2 := by
    rw [norm_mul, norm_inner_symm v]
    nlinarith [sq_nonneg (‖inner 𝕜 (b i) v‖ - ‖inner 𝕜 (b i) u‖)]
  calc
    _ ≤ ∑ i ∈ s, (‖inner 𝕜 (b i) v‖ ^ 2 + ‖inner 𝕜 (b i) u‖ ^ 2) / 2 :=
      Finset.sum_le_sum (fun i _ => hp i)
    _ = ((∑ i ∈ s, ‖inner 𝕜 (b i) v‖ ^ 2) +
        ∑ i ∈ s, ‖inner 𝕜 (b i) u‖ ^ 2) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ 1 := by
      have h₁ := b.orthonormal.sum_inner_products_le (s := s) v
      have h₂ := b.orthonormal.sum_inner_products_le (s := s) u
      rw [hv] at h₁
      rw [hu] at h₂
      nlinarith

lemma tsum_norm_inner_mul_inner_le_one {ι : Type z} (b : HilbertBasis ι 𝕜 H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∑' i, ‖inner 𝕜 v (b i) * inner 𝕜 (b i) u‖ ≤ 1 :=
  tsum_le_of_sum_le' (by norm_num) (sum_norm_inner_mul_inner_le_one b u v hu hv)

/-- Absolute convergence licenses exchanging the basis and singular-direction
sums, even when the basis is uncountable. -/
lemma diagonal_singular_formula (T : H →L[𝕜] H)
    (S : SingularExpansion.Spec.SingularSystem 𝕜 H H T) (hσ : Summable S.sigma)
    {ι : Type z} (b : HilbertBasis ι 𝕜 H) :
    Summable (fun i => ‖inner 𝕜 (b i) (T (b i))‖) ∧
    HasSum (fun i => inner 𝕜 (b i) (T (b i)))
      (∑' j, (S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) (S.leftVector j)) := by
  let d : S.Index → ι → 𝕜 := fun j i => (S.sigma j : 𝕜) *
    (inner 𝕜 (S.rightVector j) (b i) * inner 𝕜 (b i) (S.leftVector j))
  have hrow (j : S.Index) : Summable (fun i => ‖d j i‖) := by
    exact (((b.summable_inner_mul_inner (S.rightVector j) (S.leftVector j)).mul_left
      (S.sigma j : 𝕜)).norm)
  have hrow_bound (j : S.Index) : (∑' i, ‖d j i‖) ≤ S.sigma j := by
    simp only [d, norm_mul, RCLike.norm_ofReal, abs_of_pos (S.positive j), tsum_mul_left]
    simpa using mul_le_mul_of_nonneg_left
      (tsum_norm_inner_mul_inner_le_one b (S.leftVector j) (S.rightVector j)
        (S.left_orthonormal.norm_eq_one j) (S.right_orthonormal.norm_eq_one j))
      (le_of_lt (S.positive j))
  have habs : Summable (fun p : S.Index × ι => ‖d p.1 p.2‖) :=
    (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
      ⟨hrow, hσ.of_nonneg_of_le (fun j => tsum_nonneg (fun i => norm_nonneg _)) hrow_bound⟩
  have hab : Summable (Function.uncurry d) := habs.of_norm
  have hdiag (i : ι) : (∑' j, d j i) = inner 𝕜 (b i) (T (b i)) := by
    have hh := (S.expansion (b i)).mapL (innerSL 𝕜 (b i))
    simp only [innerSL_apply_apply, inner_smul_right] at hh
    convert hh.tsum_eq using 1
    congr 1
    funext j
    dsimp [d]
    ring
  have hsum : Summable (fun i => inner 𝕜 (b i) (T (b i))) := by
    simpa only [Function.uncurry_apply_pair, Prod.swap, hdiag] using hab.prod_symm.prod
  refine ⟨hsum.norm, hsum.hasSum_iff.mpr ?_⟩
  calc
    _ = ∑' i, ∑' j, d j i := tsum_congr (fun i => (hdiag i).symm)
    _ = ∑' j, ∑' i, d j i := hab.tsum_comm
    _ = _ := tsum_congr (fun j =>
      ((b.hasSum_inner_mul_inner (S.rightVector j) (S.leftVector j)).mul_left
        (S.sigma j : 𝕜)).tsum_eq)

theorem diagonal_trace : Spec.DiagonalTrace.{u,v,z} := by
  intro 𝕜 _ H _ _ _ T hT ι b
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H H T hT.1
  have hσ := (singularSystem_sum 𝕜 H H T hT S).1
  have hb := diagonal_singular_formula T S hσ b
  have hc := diagonal_singular_formula T S hσ (Spec.chosenBasis (𝕜 := 𝕜) (H := H))
  have he : Spec.TraceValue T = _ := hc.2.tsum_eq
  exact ⟨hb.1, he.symm ▸ hb.2⟩

theorem trace_bound : Spec.TraceBound.{u,v} := by
  intro 𝕜 _ H _ _ _ T hT
  obtain ⟨S⟩ := SingularExpansion.compact_singular_system 𝕜 H H T hT.1
  obtain ⟨hσ, hnorm⟩ := singularSystem_sum 𝕜 H H T hT S
  have htrace : Spec.TraceValue T =
      ∑' j, (S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) (S.leftVector j) :=
    (diagonal_singular_formula T S hσ Spec.chosenBasis).2.tsum_eq
  have hle (j : S.Index) :
      ‖(S.sigma j : 𝕜) * inner 𝕜 (S.rightVector j) (S.leftVector j)‖ ≤ S.sigma j := by
    rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (S.positive j)]
    have hi := norm_inner_le_norm (𝕜 := 𝕜) (S.rightVector j) (S.leftVector j)
    rw [S.right_orthonormal.norm_eq_one j, S.left_orthonormal.norm_eq_one j, one_mul] at hi
    simpa using mul_le_mul_of_nonneg_left hi (le_of_lt (S.positive j))
  have hs := hσ.of_nonneg_of_le (fun j => norm_nonneg _) hle
  rw [htrace, ← hnorm]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hle hσ)

theorem rankOne_application : Spec.RankOneApplication.{u,v,w} := by
  intro 𝕜 _ H K _ _ _ _ u v x
  rfl

theorem rankOne_trace : Spec.RankOneTrace.{u,v} := by
  intro 𝕜 _ H _ _ _ u v
  change (∑' i, inner 𝕜 (Spec.chosenBasis i)
    (inner 𝕜 v (Spec.chosenBasis i) • u)) = inner 𝕜 v u
  simp only [inner_smul_right]
  exact Spec.chosenBasis.tsum_inner_mul_inner v u

end ExpandedFA.TraceIdeals.TraceClassDefinitions
