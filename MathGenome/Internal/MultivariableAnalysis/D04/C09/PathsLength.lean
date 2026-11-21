import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.PathsLength
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Continuous
import MathGenome.Internal.MultivariableAnalysis.D04.C06.SubdivisionUniformVector
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Calculus.MeanValue
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.TaggedEquivalence

noncomputable section
open Set
open scoped BigOperators ENNReal
namespace D04.C09
open SingleVariableAnalysis.Riemann
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C01.EuclideanInterfaces.Model

abbrev IntervalPath := Specs.D04.C09.PathsLength.Model.IntervalPath
abbrev trace := @Specs.D04.C09.PathsLength.Model.trace
abbrev SimpleArc := @Specs.D04.C09.PathsLength.Model.SimpleArc
abbrev SimpleClosed := @Specs.D04.C09.PathsLength.Model.SimpleClosed
abbrev C1Piece := @Specs.D04.C09.PathsLength.Model.C1Piece
abbrev PiecewiseC1Data := @Specs.D04.C09.PathsLength.Model.PiecewiseC1Data
abbrev PiecewiseC1 := @Specs.D04.C09.PathsLength.Model.PiecewiseC1
abbrev PiecewiseRegular := @Specs.D04.C09.PathsLength.Model.PiecewiseRegular
abbrev polygonalLength := @Specs.D04.C09.PathsLength.Model.polygonalLength
abbrev length := @Specs.D04.C09.PathsLength.Model.length
abbrev piecewiseSpeedIntegral := @Specs.D04.C09.PathsLength.Model.piecewiseSpeedIntegral

/-- Extend a finite partition constantly beyond its last point. -/
def partitionSequence {a b : ℝ} (P : Partition a b) (k : ℕ) : ℝ :=
  P.point ⟨min k P.n, by omega⟩

lemma partitionSequence_mono {a b : ℝ} (P : Partition a b) : Monotone (partitionSequence P) := by
  intro i j hij
  apply P.strictMono.monotone
  exact min_le_min_right _ hij

lemma partitionSequence_point {a b : ℝ} (P : Partition a b) (i : Fin (P.n + 1)) :
    partitionSequence P i.val = P.point i := by
  simp only [partitionSequence, min_eq_left (Nat.le_of_lt_succ i.isLt)]

lemma partitionSequence_range {a b : ℝ} (P : Partition a b) :
    partitionSequence P '' Iic P.n = (points P : Set ℝ) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨min i P.n, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨i.val, Nat.le_of_lt_succ i.isLt, partitionSequence_point P i⟩

lemma polygonalLength_nonneg {n} (γ : ℝ → E n) {a b} (P : Partition a b) :
    0 ≤ polygonalLength γ P := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma polygonalLength_eq_variation_points {n} (γ : ℝ → E n) {a b} (P : Partition a b) :
    ENNReal.ofReal (polygonalLength γ P) = eVariationOn γ (points P : Set ℝ) := by
  rw [← partitionSequence_range P,
    eVariationOn.image_range_of_monotone γ (partitionSequence_mono P) P.n]
  change ENNReal.ofReal (∑ i : Fin P.n, ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖) = _
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _),
    ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [show i.val + 1 = i.succ.val from rfl,
    partitionSequence_point P i.succ,
    show i.val = i.castSucc.val from rfl, partitionSequence_point P i.castSucc,
    edist_comm, edist_eq_enorm_sub, ofReal_norm]

theorem polygonalLength_refinement {n} (γ : ℝ → E n) {a b}
    (P R : Partition a b) (h : Refines R P) :
    polygonalLength γ P ≤ polygonalLength γ R := by
  apply (ENNReal.ofReal_le_ofReal_iff (polygonalLength_nonneg γ R)).mp
  rw [polygonalLength_eq_variation_points, polygonalLength_eq_variation_points]
  exact eVariationOn.mono γ h

theorem length_eq_variation {n} (γ : ℝ → E n) {a b} (hab : a ≤ b) :
    length γ a b = eVariationOn γ (Icc a b) := by
  apply le_antisymm
  · apply iSup_le
    intro P
    rw [polygonalLength_eq_variation_points]
    exact eVariationOn.mono γ (fun x hx => (endpoints P).2.2 x hx)
  · apply iSup_le
    rintro ⟨k, u, hu, hmem⟩
    let s : Finset ℝ := insert a (insert b ((Finset.range (k+1)).image u))
    have ha : a ∈ s := Finset.mem_insert_self _ _
    have hb : b ∈ s := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hs : ∀ x ∈ s, x ∈ Icc a b := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨le_rfl, hab⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hab, le_rfl⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hmem i
    let P := ofPoints s ha hb hs
    have hp : points P = s := points_ofPoints s ha hb hs
    have hsum : (∑ i ∈ Finset.range k, edist (γ (u (i+1))) (γ (u i))) ≤
        eVariationOn γ (points P : Set ℝ) := by
      apply eVariationOn.sum_le_of_monotoneOn_Iic (hu.monotoneOn _)
      intro i hi
      rw [hp]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩))
    exact hsum.trans (by rw [← polygonalLength_eq_variation_points]; exact le_iSup (fun Q : Partition a b => ENNReal.ofReal (polygonalLength γ Q)) P)

theorem length_add {n} (γ : ℝ → E n) {a c b} (hac : a ≤ c) (hcb : c ≤ b) :
    length γ a b = length γ a c + length γ c b := by
  rw [length_eq_variation γ (hac.trans hcb), length_eq_variation γ hac,
    length_eq_variation γ hcb]
  simpa using (eVariationOn.Icc_add_Icc γ (s := Set.univ) hac hcb (mem_univ c)).symm

theorem polygonalLength_degenerate {n} (γ : ℝ → E n) (a : ℝ) (P : Partition a a) :
    polygonalLength γ P = 0 := by
  have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a P)
  simp [Specs.D04.C09.PathsLength.Model.polygonalLength]

theorem length_degenerate {n} (γ : ℝ → E n) (a : ℝ) : length γ a a = 0 := by
  simp [Specs.D04.C09.PathsLength.Model.length, polygonalLength_degenerate]

theorem length_constant {n} (x : E n) (a b : ℝ) : length (fun _ => x) a b = 0 := by
  simp [Specs.D04.C09.PathsLength.Model.length, Specs.D04.C09.PathsLength.Model.polygonalLength]

theorem length_zero_dimension (γ : ℝ → E 0) (a b : ℝ) : length γ a b = 0 := by
  have heq : γ = fun _ => (0 : E 0) := funext (fun _ => Subsingleton.elim _ _)
  rw [heq, length_constant]


theorem constant_piecewiseC1 {n a b} (γ : IntervalPath n a b) (x : E n)
    (hx : ∀ t ∈ Icc a b, γ t = x) : PiecewiseC1 γ := by
  obtain ⟨P⟩ := partition_exists γ.ordered
  refine ⟨⟨P, fun _ _ => 0, ?_⟩⟩
  intro i
  refine ⟨continuousOn_const, ?_⟩
  intro t ht
  exact (hasDerivWithinAt_const t (cell P i) x).congr_of_mem
    (fun y hy => hx y (cell_subset_interval P i hy)) ht

theorem constant_not_regular {n a b} (γ : IntervalPath n a b) (x : E n)
    (hab : a < b) (hx : ∀ t ∈ Icc a b, γ t = x) : ¬ PiecewiseRegular γ := by
  rintro ⟨d, hd⟩
  have hn : 0 < d.partition.n := by
    by_contra hn
    have hz : d.partition.n = 0 := by omega
    have he : (0 : Fin (d.partition.n+1)) = Fin.last d.partition.n := Fin.ext (by simp [hz])
    have h := congrArg d.partition.point he
    rw [d.partition.first, d.partition.last] at h
    exact hab.ne h
  let i : Fin d.partition.n := ⟨0, hn⟩
  let l := d.partition.point i.castSucc
  let r := d.partition.point i.succ
  have hlr : l < r := d.partition.strictMono (Fin.castSucc_lt_succ (i := i))
  let t := (l+r)/2
  have ht : t ∈ Ioo l r := by dsimp [t]; constructor <;> linarith
  have hder : HasDerivAt γ (d.velocity i t) t :=
    ((d.smooth i).2 t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hc : HasDerivAt γ (0 : E n) t :=
    ((hasDerivWithinAt_const t (Icc l r) x).congr_of_mem
      (fun y hy => hx y (cell_subset_interval d.partition i hy)) ⟨ht.1.le, ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
  exact hd i t ⟨ht.1.le, ht.2.le⟩ (hder.unique hc)

lemma C1Piece.speed_integrable {n} {γ v : ℝ → E n} {a b : ℝ}
    (hab : a ≤ b) (h : C1Piece γ v a b) : RealIntegrable (fun t => ‖v t‖) a b := by
  apply real_continuous_integrable _ hab
  intro t ht
  exact (SingleVariableAnalysis.relativeContinuousAt_within_iff _ _ _).mpr (h.1.norm t ht)

theorem speed_integrable {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ) :
    ∀ i, RealIntegrable (fun t => ‖d.velocity i t‖)
      (d.partition.point i.castSucc) (d.partition.point i.succ) := by
  intro i
  exact C1Piece.speed_integrable
    (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le (d.smooth i)

/-- Uniform first-order estimate on a closed cell. The derivative at a tag is
one-sided when the tag is an endpoint; only within-derivatives are used. -/
lemma chord_error {n} {γ v : ℝ → E n} {a b u w s η : ℝ}
    (h : C1Piece γ v a b) (huw : u ≤ w) (hsub : Icc u w ⊆ Icc a b)
    (hv : ∀ t ∈ Icc u w, ‖v t - v s‖ ≤ η) :
    ‖γ w - γ u - (w-u) • v s‖ ≤ η * (w-u) := by
  have hd : ∀ t ∈ Icc u w,
      HasDerivWithinAt (fun z => γ z - z • v s) (v t - v s) (Icc u w) t := by
    intro t ht
    exact ((h.2 t (hsub ht)).mono hsub).sub
      (by simpa using (((hasDerivAt_id t).smul_const (v s)).hasDerivWithinAt (s := Icc u w)))
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hv (convex_Icc u w)
    (left_mem_Icc.mpr huw) (right_mem_Icc.mpr huw)
  have halg : (γ w - w • v s) - (γ u - u • v s) = γ w - γ u - (w-u) • v s := by
    rw [sub_smul]; abel
  simpa only [halg, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huw)] using he

/-- Polygonal sums are uniformly close to tagged speed sums at sufficiently
small mesh. This is the quantitative step of the length proof. -/
lemma polygonalLength_tagged_error {n} {γ v : ℝ → E n} {a b : ℝ}
    (h : C1Piece γ v a b) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ (P : Partition a b) (ξ : Tagging P), mesh P < δ →
      |polygonalLength γ P - taggedSum P ξ (fun t => ‖v t‖)| ≤ η * (b-a) := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous h.1
  obtain ⟨δ, hδ, hclose⟩ := (Metric.uniformContinuousOn_iff.mp hu) η hη
  refine ⟨δ, hδ, ?_⟩
  intro P ξ hmesh
  have hcell (i : Fin P.n) :
      |‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ -
        cellLength P i * ‖v (ξ i)‖| ≤ η * cellLength P i := by
    have hv : ∀ t ∈ cell P i, ‖v t - v (ξ i)‖ ≤ η := by
      intro t ht
      exact (show ‖v t - v (ξ i)‖ < η from by
        rw [← dist_eq_norm]
        exact hclose t (cell_subset_interval P i ht) (ξ i)
          (cell_subset_interval P i (ξ i).property)
          ((dist_le_cellLength P i ht (ξ i).property).trans_lt
            ((cellLength_le_mesh P i).trans_lt hmesh))).le
    have he := chord_error h (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
      (cell_subset_interval P i) hv
    have hn := abs_norm_sub_norm_le (γ (P.point i.succ) - γ (P.point i.castSucc))
      (cellLength P i • v (ξ i))
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (cell_positive P i)] at hn
    exact hn.trans he
  calc
    _ = |∑ i : Fin P.n, (‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ -
        cellLength P i * ‖v (ξ i)‖)| := by
      simp only [Specs.D04.C09.PathsLength.Model.polygonalLength, taggedSum, S.sumValue,
        smul_eq_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin P.n, |‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ -
        cellLength P i * ‖v (ξ i)‖| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n, η * cellLength P i := Finset.sum_le_sum (fun i _ => hcell i)
    _ = η * (b-a) := by rw [← Finset.mul_sum, sum_cellLength]

lemma C1Piece.polygonalLength_mesh_limit {n} {γ v : ℝ → E n} {a b : ℝ}
    (hab : a ≤ b) (h : C1Piece γ v a b)
    (hv : RealIntegrable (fun t => ‖v t‖) a b) :
    ∀ ε > 0, ∃ δ > 0, ∀ P : Partition a b, mesh P < δ →
      |polygonalLength γ P - realIntegral _ hv| < ε := by
  intro ε hε
  rcases lt_or_eq_of_le hab with hab | rfl
  · let η := ε / (4*(b-a))
    have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))
    obtain ⟨δ₁, hδ₁, h₁⟩ := polygonalLength_tagged_error h hη
    have hlim := (real_tagged_equivalence (fun t => ‖v t‖) hab.le hv.bounded (realIntegral _ hv)).mp ⟨hv, rfl⟩
    obtain ⟨δ₂, hδ₂, h₂⟩ := hlim (ε/2) (half_pos hε)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    intro P hP
    obtain ⟨ξ⟩ := tags_exist P
    have he₁ := h₁ P ξ (hP.trans_le (min_le_left _ _))
    have he₂ := h₂ P ξ (hP.trans_le (min_le_right _ _))
    have heta : η * (b-a) = ε/4 := by dsimp [η]; field_simp
    rw [heta] at he₁
    have ht := abs_add_le (polygonalLength γ P - taggedSum P ξ (fun t => ‖v t‖))
      (taggedSum P ξ (fun t => ‖v t‖) - realIntegral _ hv)
    rw [Real.norm_eq_abs] at he₂
    have halg : polygonalLength γ P - taggedSum P ξ (fun t => ‖v t‖) +
        (taggedSum P ξ (fun t => ‖v t‖) - realIntegral _ hv) =
        polygonalLength γ P - realIntegral _ hv := by ring
    rw [halg] at ht
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro P _
    rw [polygonalLength_degenerate, realIntegral_degenerate]
    simpa using hε


open D04.Darboux.Subdivision in
lemma polygonalLength_split {n} (γ : ℝ → E n) {a b : ℝ} {P R : Partition a b}
    (h : Refines R P) :
    polygonalLength γ R = ∑ i, polygonalLength γ (restrictPartition h i) := by
  change (∑ j : Fin R.n, ‖γ (R.point j.succ) - γ (R.point j.castSucc)‖) = _
  rw [← (cellEquiv h).sum_comp (fun j => ‖γ (R.point j.succ) - γ (R.point j.castSucc)‖),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, _) = ∑ j, _
  apply Finset.sum_congr rfl
  intro j _
  rw [restrict_left, restrict_right]
  rfl

open D04.Darboux.Subdivision in
lemma mesh_restrict_le {a b : ℝ} {P R : Partition a b} (h : Refines R P) (i : Fin P.n) :
    mesh (restrictPartition h i) ≤ mesh R := by
  apply mesh_le _ (mesh_nonneg R)
  intro j
  simpa only [cellLength, S.lengthValue, restrict_left, restrict_right] using
    cellLength_le_mesh R (embedCell h i j)

theorem polygonalLength_mesh_limit {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (h : ∀ i, RealIntegrable (fun t => ‖d.velocity i t‖)
      (d.partition.point i.castSucc) (d.partition.point i.succ)) :
    ∀ ε > 0, ∃ δ > 0, ∀ P : Partition a b, Refines P d.partition → mesh P < δ →
      |polygonalLength γ P - piecewiseSpeedIntegral d h| < ε := by
  classical
  intro ε hε
  let η := ε / ((d.partition.n : ℝ) + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hex (i : Fin d.partition.n) := C1Piece.polygonalLength_mesh_limit
    (d.partition.strictMono (Fin.castSucc_lt_succ (i := i))).le (d.smooth i) (h i) η hη
  choose δ hδ hclose using hex
  let s : Finset ℝ := insert 1 (Finset.univ.image δ)
  let δ₀ : ℝ := s.inf' (Finset.insert_nonempty _ _) id
  have hδ₀ : 0 < δ₀ := by
    obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_inf' (s := s) (Finset.insert_nonempty _ _) id
    change 0 < s.inf' (Finset.insert_nonempty _ _) id
    rw [he]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hδ i
  refine ⟨δ₀, hδ₀, ?_⟩
  intro P hP hm
  have hle (i : Fin d.partition.n) : δ₀ ≤ δ i :=
    Finset.inf'_le id (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  have hc (i : Fin d.partition.n) :
      |polygonalLength γ (D04.Darboux.Subdivision.restrictPartition hP i) -
        realIntegral (fun t => ‖d.velocity i t‖) (h i)| ≤ η :=
    (hclose i _ ((mesh_restrict_le hP i).trans_lt (hm.trans_le (hle i)))).le
  rw [polygonalLength_split γ hP]
  change |(∑ i, _) - ∑ i, _| < ε
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin d.partition.n,
        |polygonalLength γ (D04.Darboux.Subdivision.restrictPartition hP i) -
          realIntegral (fun t => ‖d.velocity i t‖) (h i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d.partition.n, η := Finset.sum_le_sum (fun i _ => hc i)
    _ = (d.partition.n : ℝ) * η := by simp
    _ < ε := by
      dsimp [η]
      have ht : (d.partition.n : ℝ) < (d.partition.n : ℝ) + 1 := by linarith
      have he : ((d.partition.n : ℝ) + 1) * (ε / ((d.partition.n : ℝ) + 1)) = ε := by
        field_simp
      have hh := mul_lt_mul_of_pos_right ht hη
      dsimp [η] at hh
      rw [he] at hh
      exact hh

/-- A mesh limit of polygonal lengths on partitions containing a fixed finite
set of joins equals the supremum over *all* partitions. -/
lemma length_eq_of_mesh_limit {n} (γ : ℝ → E n) {a b : ℝ} (hab : a ≤ b)
    (J : Partition a b) (I : ℝ)
    (hlim : ∀ ε > 0, ∃ δ > 0, ∀ P : Partition a b,
      Refines P J → mesh P < δ → |polygonalLength γ P - I| < ε) :
    length γ a b = ENNReal.ofReal I := by
  have hex (P : Partition a b) {δ : ℝ} (hδ : 0 < δ) :
      ∃ R : Partition a b, Refines R P ∧ Refines R J ∧ mesh R < δ := by
    obtain ⟨T, hT⟩ := exists_fine_partition hab δ hδ
    obtain ⟨S, _, hSP, hSJ⟩ := common_refinement P J
    obtain ⟨R, _, hRS, hRT⟩ := common_refinement S T
    exact ⟨R, Finset.Subset.trans hSP hRS, Finset.Subset.trans hSJ hRS,
      (Step.mesh_refinement_le T R hRT).trans_lt hT⟩
  have hub : ∀ P : Partition a b, polygonalLength γ P ≤ I := by
    intro P
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨δ, hδ, hc⟩ := hlim ε hε
    obtain ⟨R, hRP, hRJ, hm⟩ := hex P hδ
    have hclose := (abs_lt.mp (hc R hRJ hm)).2
    have href := polygonalLength_refinement γ P R hRP
    linarith
  have hupper : length γ a b ≤ ENNReal.ofReal I :=
    iSup_le (fun P => ENNReal.ofReal_le_ofReal (hub P))
  have hfinite : length γ a b ≠ ∞ := ne_of_lt (hupper.trans_lt ENNReal.ofReal_lt_top)
  apply le_antisymm hupper
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hlim ε hε
  obtain ⟨R, _, hRJ, hm⟩ := hex J hδ
  have hclose := (abs_lt.mp (hc R hRJ hm)).1
  have hpoly : polygonalLength γ R ≤ (length γ a b).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
      (le_iSup (fun P : Partition a b => ENNReal.ofReal (polygonalLength γ P)) R)
  linarith

theorem length_speed_integral {n a b} {γ : IntervalPath n a b} (d : PiecewiseC1Data γ)
    (h : ∀ i, RealIntegrable (fun t => ‖d.velocity i t‖)
      (d.partition.point i.castSucc) (d.partition.point i.succ)) :
    length γ a b = ENNReal.ofReal (piecewiseSpeedIntegral d h) ∧ length γ a b < ∞ := by
  have he := length_eq_of_mesh_limit γ γ.ordered d.partition (piecewiseSpeedIntegral d h)
    (polygonalLength_mesh_limit d h)
  exact ⟨he, by rw [he]; exact ENNReal.ofReal_lt_top⟩

theorem piecewiseC1_finite {n a b} (γ : IntervalPath n a b) (hγ : PiecewiseC1 γ) :
    length γ a b < ∞ := by
  obtain ⟨d⟩ := hγ
  exact (length_speed_integral d (speed_integrable d)).2

theorem piecewiseSpeedIntegral_degenerate {n a} {γ : IntervalPath n a a}
    (d : PiecewiseC1Data γ) (h : ∀ i, RealIntegrable (fun t => ‖d.velocity i t‖)
      (d.partition.point i.castSucc) (d.partition.point i.succ)) :
    piecewiseSpeedIntegral d h = 0 := by
  have : IsEmpty (Fin d.partition.n) :=
    Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a d.partition)
  exact Finset.sum_of_isEmpty _

end D04.C09
