import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.InverseCodingConstruction
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ShiftSpaces
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ShiftCompactness
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases

namespace D13Unified.Ch17.InverseCodingConstruction
open Set Filter Topology NNReal
open D13Unified.Ch17.ShiftSpaces
noncomputable section

abbrev wordMap := @Specs.D13Unified.Ch17.InverseCodingConstruction.wordMap
abbrev cylinderImage := @Specs.D13Unified.Ch17.InverseCodingConstruction.cylinderImage
abbrev levelSet := @Specs.D13Unified.Ch17.InverseCodingConstruction.levelSet
abbrev limitSet := @Specs.D13Unified.Ch17.InverseCodingConstruction.limitSet

variable {K : Type*} (b : Binary → K → K)

@[simp] lemma wordMap_zero (s : OneSided) (x : K) : wordMap b s 0 x = x := rfl
@[simp] lemma wordMap_succ (s : OneSided) (n : ℕ) (x : K) :
    wordMap b s (n+1) x = wordMap b s n (b (s n) x) := rfl

lemma wordMap_prefix {s t : OneSided} {n : ℕ} (h : ∀ j < n, s j = t j) :
    wordMap b s n = wordMap b t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    simp only [wordMap_succ, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

lemma cylinderImage_prefix {s t : OneSided} {n : ℕ} (h : ∀ j < n, s j = t j) :
    cylinderImage b s n = cylinderImage b t n := by
  exact congrArg Set.range (wordMap_prefix b h)

lemma cylinderImage_nested (s : OneSided) (n : ℕ) :
    cylinderImage b s (n+1) ⊆ cylinderImage b s n := by
  rintro x ⟨y, rfl⟩
  exact ⟨b (s n) y, rfl⟩

lemma wordMap_head (s : OneSided) (n : ℕ) (x : K) :
    wordMap b s (n+1) x = b (s 0) (wordMap b (shiftPlus s) n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [wordMap_succ, ih, wordMap_succ]
    rfl

lemma wordMap_injective (hb : ∀ i, Function.Injective (b i)) (s : OneSided) (n : ℕ) :
    Function.Injective (wordMap b s n) := by
  induction n with
  | zero => exact Function.injective_id
  | succ n ih => exact ih.comp (hb (s n))

theorem levelSet_finiteWords :
    Specs.D13Unified.Ch17.InverseCodingConstruction.levelSet_finiteWordsStatement := by
  intro K b n
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨fun j => s j, ?_⟩
    have he : cylinderImage b s n =
        cylinderImage b (fun j => if h : j < n then s j else 0) n :=
      cylinderImage_prefix b (fun j hj => by simp [hj])
    change x ∈ cylinderImage b (fun j => if h : j < n then s j else 0) n
    exact (Set.ext_iff.mp he x).mp hs
  · intro x hx
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨_, hw⟩

variable [MetricSpace K]

lemma wordMap_lipschitz (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i))
    (s : OneSided) (n : ℕ) : LipschitzWith (q^n) (wordMap b s n) := by
  induction n with
  | zero => simpa [wordMap, Specs.D13Unified.Ch17.InverseCodingConstruction.wordMap] using (LipschitzWith.id : LipschitzWith 1 (id : K → K))
  | succ n ih =>
    change LipschitzWith (q^(n+1)) (fun x => wordMap b s n (b (s n) x))
    simpa only [pow_succ, Function.comp_def] using ih.comp (hb (s n))

variable [CompactSpace K] [Nonempty K]

omit [MetricSpace K] [CompactSpace K] in
lemma cylinderImage_nonempty (s : OneSided) (n : ℕ) :
    (cylinderImage b s n).Nonempty := Set.range_nonempty _

omit [Nonempty K] in
lemma cylinderImage_compact (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i))
    (s : OneSided) (n : ℕ) : IsCompact (cylinderImage b s n) :=
  isCompact_range (wordMap_lipschitz b q hb s n).continuous

omit [Nonempty K] in
lemma cylinderImage_diam (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i))
    (s : OneSided) (n : ℕ) :
    Metric.diam (cylinderImage b s n) ≤ (q : ℝ)^n * Metric.diam (Set.univ : Set K) := by
  simpa [cylinderImage, Specs.D13Unified.Ch17.InverseCodingConstruction.cylinderImage, Set.image_univ] using
    (wordMap_lipschitz b q hb s n).diam_image_le Set.univ isCompact_univ.isBounded

theorem cylinder_geometry :
    Specs.D13Unified.Ch17.InverseCodingConstruction.cylinder_geometryStatement := by
  intro K _ _ _ b q hb s n
  exact ⟨cylinderImage_nonempty b s n, cylinderImage_compact b q hb s n,
    cylinderImage_nested b s n, cylinderImage_diam b q hb s n⟩


lemma cylinder_inter_nonempty (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i))
    (s : OneSided) : (⋂ n : ℕ, cylinderImage b s n).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (cylinderImage_nested b s) (cylinderImage_nonempty b s)
    (cylinderImage_compact b q hb s 0)
    (fun n => (cylinderImage_compact b q hb s n).isClosed)

/-- Choice is only used after proving existence of the nested intersection. -/
def codingPoint (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i)) (s : OneSided) : K :=
  (cylinder_inter_nonempty b q hb s).some

lemma codingPoint_mem (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i))
    (s : OneSided) (n : ℕ) : codingPoint b q hb s ∈ cylinderImage b s n :=
  Set.mem_iInter.mp (cylinder_inter_nonempty b q hb s).some_mem n

omit [CompactSpace K] [Nonempty K] in
lemma diameter_bound_tendsto (q : ℝ≥0) (hq : (q : ℝ) < 1) :
    Tendsto (fun n : ℕ => (q : ℝ)^n * Metric.diam (Set.univ : Set K)) atTop (𝓝 0) := by
  simpa using (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one q.coe_nonneg hq).mul_const
    (Metric.diam (Set.univ : Set K))

omit [Nonempty K] in
lemma dist_le_cylinder_bound (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i))
    (s : OneSided) (n : ℕ) {x y : K}
    (hx : x ∈ cylinderImage b s n) (hy : y ∈ cylinderImage b s n) :
    dist x y ≤ (q : ℝ)^n * Metric.diam (Set.univ : Set K) :=
  (Metric.dist_le_diam_of_mem (cylinderImage_compact b q hb s n).isBounded hx hy).trans
    (cylinderImage_diam b q hb s n)

lemma cylinder_inter_unique (q : ℝ≥0) (hq : (q : ℝ) < 1)
    (hb : ∀ i, LipschitzWith q (b i)) (s : OneSided) {x y : K}
    (hx : ∀ n, x ∈ cylinderImage b s n) (hy : ∀ n, y ∈ cylinderImage b s n) : x = y := by
  apply dist_le_zero.mp
  exact ge_of_tendsto' (diameter_bound_tendsto (K := K) q hq)
    (fun n => dist_le_cylinder_bound b q hb s n (hx n) (hy n))

lemma cylinder_inter_singleton (q : ℝ≥0) (hq : (q : ℝ) < 1)
    (hb : ∀ i, LipschitzWith q (b i)) (s : OneSided) :
    (⋂ n : ℕ, cylinderImage b s n) = {codingPoint b q hb s} := by
  ext x
  constructor
  · intro hx
    exact Set.mem_singleton_iff.mpr (cylinder_inter_unique b q hq hb s
      (Set.mem_iInter.mp hx) (codingPoint_mem b q hb s))
  · rintro rfl
    exact Set.mem_iInter.mpr (codingPoint_mem b q hb s)

lemma codingPoint_prefix_bound (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i))
    {s t : OneSided} {n : ℕ} (h : ∀ j < n, s j = t j) :
    dist (codingPoint b q hb s) (codingPoint b q hb t) ≤
      (q : ℝ)^n * Metric.diam (Set.univ : Set K) := by
  apply dist_le_cylinder_bound b q hb s n (codingPoint_mem b q hb s n)
  rw [cylinderImage_prefix b h]
  exact codingPoint_mem b q hb t n

lemma codingPoint_continuous (q : ℝ≥0) (hq : (q : ℝ) < 1)
    (hb : ∀ i, LipschitzWith q (b i)) : Continuous (codingPoint b q hb) := by
  rw [Metric.continuous_iff']
  intro s ε hε
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    ((diameter_bound_tendsto (K := K) q hq).eventually_lt_const hε)
  apply Filter.mem_of_superset
    ((PiNat.isOpen_cylinder (fun _ => Binary) s n).mem_nhds (PiNat.self_mem_cylinder s n))
  intro t ht
  exact (codingPoint_prefix_bound b q hb (PiNat.mem_cylinder_iff.mp ht)).trans_lt (hn n le_rfl)

lemma codingPoint_mem_limitSet (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i))
    (s : OneSided) : codingPoint b q hb s ∈ limitSet b := by
  apply Set.mem_iInter.mpr
  intro n
  exact Set.mem_iUnion.mpr ⟨s, codingPoint_mem b q hb s (n+1)⟩

/-- Every point surviving all finite levels has an infinite itinerary.
Compactness closes the range of the continuous coding map; the cylinder
estimate puts any surviving point in that range's closure. -/
lemma range_codingPoint (q : ℝ≥0) (hq : (q : ℝ) < 1)
    (hb : ∀ i, LipschitzWith q (b i)) : Set.range (codingPoint b q hb) = limitSet b := by
  apply Set.Subset.antisymm
  · rintro x ⟨s, rfl⟩
    exact codingPoint_mem_limitSet b q hb s
  · intro x hx
    apply (isCompact_range (codingPoint_continuous b q hq hb)).isClosed.closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
      ((diameter_bound_tendsto (K := K) q hq).eventually_lt_const hε)
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hx n)
    refine ⟨codingPoint b q hb s, Set.mem_range_self s, ?_⟩
    exact (dist_le_cylinder_bound b q hb s (n+1) hs (codingPoint_mem b q hb s (n+1))).trans_lt
      (hn (n+1) (Nat.le_succ n))

omit [MetricSpace K] [CompactSpace K] [Nonempty K] in
lemma branch_symbol_eq (hd : Disjoint (Set.range (b 0)) (Set.range (b 1)))
    {i j : Binary} {x y : K} (h : b i x = b j y) : i = j := by
  by_contra hij
  fin_cases i <;> fin_cases j
  · exact hij rfl
  · exact Set.disjoint_left.mp hd ⟨x, h⟩ ⟨y, rfl⟩
  · exact Set.disjoint_left.mp hd ⟨y, rfl⟩ ⟨x, h⟩
  · exact hij rfl

/-- The first differing symbol gives disjoint cylinder images, after
cancelling the common injective prefix. No injectivity of coding is assumed. -/
lemma codingPoint_injective (q : ℝ≥0) (hb : ∀ i, LipschitzWith q (b i))
    (hi : ∀ i, Function.Injective (b i))
    (hd : Disjoint (Set.range (b 0)) (Set.range (b 1))) :
    Function.Injective (codingPoint b q hb) := by
  intro s t hst
  have hp : ∀ n : ℕ, ∀ j < n, s j = t j := by
    intro n
    induction n with
    | zero => intro j hj; omega
    | succ n ih =>
      have heq : wordMap b s n = wordMap b t n := wordMap_prefix b ih
      obtain ⟨x, hx⟩ := codingPoint_mem b q hb s (n+1)
      obtain ⟨y, hy⟩ := codingPoint_mem b q hb t (n+1)
      have hxy : b (s n) x = b (t n) y := by
        apply wordMap_injective b hi s n
        calc
          wordMap b s n (b (s n) x) = codingPoint b q hb s := hx
          _ = codingPoint b q hb t := hst
          _ = wordMap b s n (b (t n) y) := by rw [heq]; exact hy.symm
      have hn : s n = t n := branch_symbol_eq b hd hxy
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact ih j hj
      · exact hn
  funext n
  exact hp (n+1) n (Nat.lt_succ_self n)

lemma codingPoint_head (q : ℝ≥0) (hq : (q : ℝ) < 1)
    (hb : ∀ i, LipschitzWith q (b i)) (s : OneSided) :
    codingPoint b q hb s = b (s 0) (codingPoint b q hb (shiftPlus s)) := by
  apply cylinder_inter_unique b q hq hb s (codingPoint_mem b q hb s)
  intro n
  cases n with
  | zero => exact ⟨_, rfl⟩
  | succ n =>
    obtain ⟨x, hx⟩ := codingPoint_mem b q hb (shiftPlus s) n
    refine ⟨x, ?_⟩
    change wordMap b s (n+1) x = _
    rw [wordMap_head]
    exact congrArg (b (s 0)) hx

/-- The continuous bijection is upgraded only after the independent range
and injectivity arguments above. -/
def codingHomeomorph (q : ℝ≥0) (hq : (q : ℝ) < 1)
    (hb : ∀ i, LipschitzWith q (b i)) (hi : ∀ i, Function.Injective (b i))
    (hd : Disjoint (Set.range (b 0)) (Set.range (b 1))) : OneSided ≃ₜ limitSet b :=
  let f : OneSided → limitSet b := fun s => ⟨codingPoint b q hb s, codingPoint_mem_limitSet b q hb s⟩
  let hf : Continuous f := (codingPoint_continuous b q hq hb).subtype_mk _
  let hbij : Function.Bijective f := ⟨
    fun s t h => codingPoint_injective b q hb hi hd (congrArg Subtype.val h),
    fun x => by
      have hr : x.val ∈ Set.range (codingPoint b q hb) := by
        rw [range_codingPoint b q hq hb]
        exact x.property
      obtain ⟨s, hs⟩ := hr
      exact ⟨s, Subtype.ext hs⟩⟩
  (Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed hf hf.isClosedMap

theorem coding_exists :
    Specs.D13Unified.Ch17.InverseCodingConstruction.coding_existsStatement := by
  intro K _ _ _ b q hq hb hi hd
  refine ⟨codingHomeomorph b q hq hb hi hd, ?_, ?_⟩
  · exact cylinder_inter_singleton b q hq hb
  · exact codingPoint_head b q hq hb

theorem local_conjugacy :
    Specs.D13Unified.Ch17.InverseCodingConstruction.local_conjugacyStatement := by
  intro K _ _ _ b q hq hb hi hd Y _ ι U _ F _ hbU hF
  obtain ⟨π, hπ, hhead⟩ := coding_exists b q hq hb hi hd
  refine ⟨π, hπ, ?_⟩
  intro s
  have hmem : (π s : K) ∈ U := hhead s ▸ hbU (s 0) (π (shiftPlus s))
  refine ⟨hmem, ?_⟩
  have he : (⟨(π s : K), hmem⟩ : U) = ⟨b (s 0) (π (shiftPlus s)), hbU _ _⟩ :=
    Subtype.ext (hhead s)
  rw [he]
  exact hF _ _


theorem ambient_conjugacy :
    Specs.D13Unified.Ch17.InverseCodingConstruction.ambient_conjugacyStatement := by
  intro X _ K hK hn b q hq hb hi hd U hU F hFc hbU hF
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hn.to_subtype
  let V : Set K := Subtype.val ⁻¹' U
  let g : V → U := fun x => ⟨x.val.val, x.property⟩
  have hg : Continuous g := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  obtain ⟨π, hπ, hconj⟩ := local_conjugacy b q hq hb hi hd
    (Subtype.val : K → X) V (hU.preimage continuous_subtype_val)
    (F ∘ g) (hFc.comp hg) hbU hF
  exact ⟨π, hπ, hconj⟩

end
end D13Unified.Ch17.InverseCodingConstruction
