import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.Reparametrization
import MathGenome.Internal.MultivariableAnalysis.D04.C09.LineIntegrals
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.MonotoneSubstitution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set
open scoped BigOperators ENNReal
namespace D04.C09.Reparametrization
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
open SingleVariableAnalysis.Riemann
open D04.C09

abbrev ScalarC1Data := Specs.D04.C09.Reparametrization.Model.ScalarC1Data
abbrev ParameterChange := Specs.D04.C09.Reparametrization.Model.ParameterChange
abbrev reparametrize := @Specs.D04.C09.Reparametrization.Model.reparametrize

lemma ParameterChange.bijOn {a b c d} (h : ParameterChange a b c d) :
    BijOn h (Icc c d) (Icc a b) := by
  refine ⟨h.mapsTo, ?_, ?_⟩
  · intro x hx y hy he
    simpa [h.left_inv x hx, h.left_inv y hy] using congrArg h.inverse he
  · intro y hy
    exact ⟨h.inverse y, h.inverse_mapsTo hy, h.right_inv y hy⟩

theorem monotonicity {a b c d} (h : ParameterChange a b c d) :
    StrictMonoOn h (Icc c d) ∨ StrictAntiOn h (Icc c d) :=
  ContinuousOn.strictMonoOn_of_injOn_Icc' h.source_ordered h.continuousOn h.bijOn.injOn

theorem singleton_iff {a b c d} (h : ParameterChange a b c d) : a = b ↔ c = d := by
  constructor
  · intro hab
    have hc := h.mapsTo (left_mem_Icc.mpr h.source_ordered)
    have hd := h.mapsTo (right_mem_Icc.mpr h.source_ordered)
    have he : h c = h d := by rcases hc with ⟨hc₁, hc₂⟩; rcases hd with ⟨hd₁, hd₂⟩; linarith
    exact h.bijOn.injOn ⟨le_rfl, h.source_ordered⟩ ⟨h.source_ordered, le_rfl⟩ he
  · intro hcd
    have ha := h.inverse_mapsTo (left_mem_Icc.mpr h.target_ordered)
    have hb := h.inverse_mapsTo (right_mem_Icc.mpr h.target_ordered)
    have he : h.inverse a = h.inverse b := by rcases ha with ⟨ha₁, ha₂⟩; rcases hb with ⟨hb₁, hb₂⟩; linarith
    simpa [h.right_inv a (left_mem_Icc.mpr h.target_ordered),
      h.right_inv b (right_mem_Icc.mpr h.target_ordered)] using congrArg h he

theorem trace_reparametrize {n a b c d} (γ : IntervalPath n a b)
    (h : ParameterChange a b c d) : trace (reparametrize γ h) = trace γ := by
  change (γ ∘ h) '' Icc c d = γ '' Icc a b
  rw [image_comp, h.bijOn.image_eq]

theorem length_reparametrize {n a b c d} (γ : IntervalPath n a b)
    (h : ParameterChange a b c d) : length (reparametrize γ h) c d = length γ a b := by
  rw [length_eq_variation _ h.source_ordered, length_eq_variation _ h.target_ordered]
  change eVariationOn (γ ∘ h) (Icc c d) = _
  rcases monotonicity h with hm | hm
  · rw [eVariationOn.comp_eq_of_monotoneOn γ h hm.monotoneOn, h.bijOn.image_eq]
  · rw [eVariationOn.comp_eq_of_antitoneOn γ h hm.antitoneOn, h.bijOn.image_eq]

/-- `true` records increasing traversal; `false` records decreasing traversal. -/
def Oriented {a b c d} (h : ParameterChange a b c d) (inc : Bool) : Prop :=
  if inc then StrictMonoOn h (Icc c d) else StrictAntiOn h (Icc c d)

/-- Reverse the enumeration exactly when the parameter change reverses order. -/
def orderIndex (inc : Bool) {n : ℕ} (i : Fin n) : Fin n :=
  if inc then i else i.rev

lemma orderIndex_involutive (inc : Bool) {n : ℕ} (i : Fin n) :
    orderIndex inc (orderIndex inc i) = i := by cases inc <;> simp [orderIndex]

lemma orderIndex_sum (inc : Bool) {n : ℕ} (f : Fin n → ℝ) :
    (∑ i, f (orderIndex inc i)) = ∑ i, f i := by
  exact Fintype.sum_equiv
    ⟨orderIndex inc, orderIndex inc, orderIndex_involutive inc, orderIndex_involutive inc⟩
    _ _ (fun _ => rfl)

lemma endpoints_increasing {a b c d} (h : ParameterChange a b c d)
    (hm : StrictMonoOn h (Icc c d)) : h c = a ∧ h d = b := by
  have hc := h.mapsTo (left_mem_Icc.mpr h.source_ordered)
  have hd := h.mapsTo (right_mem_Icc.mpr h.source_ordered)
  obtain ⟨x, hx, he⟩ := h.bijOn.surjOn (left_mem_Icc.mpr h.target_ordered)
  obtain ⟨y, hy, he'⟩ := h.bijOn.surjOn (right_mem_Icc.mpr h.target_ordered)
  exact ⟨le_antisymm (by simpa only [he] using hm.monotoneOn (left_mem_Icc.mpr h.source_ordered) hx hx.1) hc.1,
    le_antisymm hd.2 (by simpa only [he'] using hm.monotoneOn hy (right_mem_Icc.mpr h.source_ordered) hy.2)⟩

lemma endpoints_decreasing {a b c d} (h : ParameterChange a b c d)
    (hm : StrictAntiOn h (Icc c d)) : h d = a ∧ h c = b := by
  have hc := h.mapsTo (left_mem_Icc.mpr h.source_ordered)
  have hd := h.mapsTo (right_mem_Icc.mpr h.source_ordered)
  obtain ⟨x, hx, he⟩ := h.bijOn.surjOn (left_mem_Icc.mpr h.target_ordered)
  obtain ⟨y, hy, he'⟩ := h.bijOn.surjOn (right_mem_Icc.mpr h.target_ordered)
  exact ⟨le_antisymm (by simpa only [he] using hm.antitoneOn hx (right_mem_Icc.mpr h.source_ordered) hx.2) hd.1,
    le_antisymm hc.2 (by simpa only [he'] using hm.antitoneOn (left_mem_Icc.mpr h.source_ordered) hy hy.1)⟩

/-- The increasing enumeration of the image of a partition. -/
def imagePartition {a b c d} (h : ParameterChange a b c d) (inc : Bool)
    (hm : Oriented h inc) (R : Partition c d) : Partition a b where
  n := R.n
  point i := h (R.point (orderIndex inc i))
  strictMono := by
    intro i j hij
    cases inc with
    | true => exact hm (graph_point_mem R _) (graph_point_mem R _) (R.strictMono hij)
    | false =>
      exact hm (graph_point_mem R _) (graph_point_mem R _)
        (R.strictMono (Fin.rev_lt_rev.mpr hij))
  first := by
    cases inc with
    | true => simpa [orderIndex, R.first] using (endpoints_increasing h hm).1
    | false => simpa [orderIndex, R.last] using (endpoints_decreasing h hm).1
  last := by
    cases inc with
    | true => simpa [orderIndex, R.last] using (endpoints_increasing h hm).2
    | false => simpa [orderIndex, R.first] using (endpoints_decreasing h hm).2

lemma imagePartition_points {a b c d} (h : ParameterChange a b c d) (inc : Bool)
    (hm : Oriented h inc) (R : Partition c d) :
    points (imagePartition h inc hm R) = (points R).image h := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨R.point (orderIndex inc i),
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨orderIndex inc i, Finset.mem_univ _, by
      simp [imagePartition, orderIndex_involutive]⟩

/-- A joint subdivision includes all parameter joins and all preimages of
path joins. Its image refines the path partition. -/
lemma joint_partition {a b c d} (h : ParameterChange a b c d) (inc : Bool)
    (hm : Oriented h inc) (P : Partition a b) :
    ∃ R : Partition c d, Refines R h.forward.partition ∧
      Refines (imagePartition h inc hm R) P ∧
      Refines (imagePartition h inc hm R) h.backward.partition := by
  classical
  let s := points h.forward.partition ∪
    (points P ∪ points h.backward.partition).image h.inverse
  have hs : ∀ x ∈ s, x ∈ Icc c d := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (endpoints h.forward.partition).2.2 x hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      apply h.inverse_mapsTo
      rcases Finset.mem_union.mp hy with hy | hy
      · exact (endpoints P).2.2 y hy
      · exact (endpoints h.backward.partition).2.2 y hy
  obtain ⟨R, hR⟩ := finite_representation s
    (Finset.mem_union_left _ (endpoints h.forward.partition).1)
    (Finset.mem_union_left _ (endpoints h.forward.partition).2.1) hs
  change points R = s at hR
  refine ⟨R, ?_, ?_, ?_⟩
  · change points h.forward.partition ⊆ points R
    rw [hR]
    exact Finset.subset_union_left
  · change points P ⊆ points (imagePartition h inc hm R)
    rw [imagePartition_points, hR]
    intro x hx
    exact Finset.mem_image.mpr ⟨h.inverse x,
      Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨x, Finset.mem_union_left _ hx, rfl⟩),
      h.right_inv x ((endpoints P).2.2 x hx)⟩
  · change points h.backward.partition ⊆ points (imagePartition h inc hm R)
    rw [imagePartition_points, hR]
    intro x hx
    exact Finset.mem_image.mpr ⟨h.inverse x,
      Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨x, Finset.mem_union_right _ hx, rfl⟩),
      h.right_inv x ((endpoints h.backward.partition).2.2 x hx)⟩

lemma imagePartition_maps_cell {a b c d} (h : ParameterChange a b c d) (inc : Bool)
    (hm : Oriented h inc) (R : Partition c d) (j : Fin R.n) :
    MapsTo h (cell R j) (cell (imagePartition h inc hm R) (orderIndex inc j)) := by
  intro t ht
  have ht' := cell_subset_interval R j ht
  have hl := graph_point_mem R j.castSucc
  have hr := graph_point_mem R j.succ
  cases inc with
  | true => exact ⟨hm.monotoneOn hl ht' ht.1, hm.monotoneOn ht' hr ht.2⟩
  | false =>
    change h (R.point ((orderIndex false j).castSucc.rev)) ≤ h t ∧
      h t ≤ h (R.point ((orderIndex false j).succ.rev))
    simpa [orderIndex, Fin.rev_castSucc, Fin.rev_succ] using
      And.intro (hm.antitoneOn ht' hr ht.2) (hm.antitoneOn hl ht' ht.1)


open D04.Darboux.Subdivision

/-- Chain-rule data on the joint partition. -/
def composeData {n a b c d} {γ : IntervalPath n a b}
    (h : ParameterChange a b c d) (inc : Bool) (hm : Oriented h inc)
    (v : PiecewiseC1Data γ) (R : Partition c d)
    (hR : Refines R h.forward.partition)
    (hQ : Refines (imagePartition h inc hm R) v.partition) :
    PiecewiseC1Data (reparametrize γ h) where
  partition := R
  velocity j t := h.forward.derivative (parentCell hR j) t •
    v.velocity (parentCell hQ (orderIndex inc j)) (h t)
  smooth j := by
    have hs := parentCell_subset hR j
    have ht : MapsTo h (cell R j)
        (cell v.partition (parentCell hQ (orderIndex inc j))) :=
      fun _ hx => parentCell_subset hQ _ (imagePartition_maps_cell h inc hm R j hx)
    refine ⟨?_, ?_⟩
    · exact ((h.forward.smooth _).1.mono hs).smul
        ((v.smooth _).1.comp (h.continuousOn.mono (cell_subset_interval R j)) ht)
    · intro t hmem
      exact ((v.smooth _).2 (h t) (ht hmem)).scomp t
        (((h.forward.smooth _).2 t (hs hmem)).mono hs) ht

theorem piecewiseC1_reparametrize {n a b c d} (γ : IntervalPath n a b)
    (h : ParameterChange a b c d) : PiecewiseC1 γ → PiecewiseC1 (reparametrize γ h) := by
  rintro ⟨v⟩
  rcases monotonicity h with hm | hm
  · obtain ⟨R, hR, hQ, _⟩ := joint_partition h true hm v.partition
    exact ⟨composeData h true hm v R hR hQ⟩
  · obtain ⟨R, hR, hQ, _⟩ := joint_partition h false hm v.partition
    exact ⟨composeData h false hm v R hR hQ⟩

lemma parameter_derivative_sign {a b c d} (h : ParameterChange a b c d)
    (inc : Bool) (hm : Oriented h inc) (R : Partition c d)
    (hR : Refines R h.forward.partition) (j : Fin R.n) (t : ℝ) (ht : t ∈ cell R j) :
    |h.forward.derivative (parentCell hR j) t| =
      (if inc then 1 else -1) * h.forward.derivative (parentCell hR j) t := by
  have hd := ((h.forward.smooth _).2 t (parentCell_subset hR j ht)).mono
    (parentCell_subset hR j)
  have hu := uniqueDiffOn_Icc (R.strictMono (Fin.castSucc_lt_succ (i := j))) t ht
  cases inc with
  | true =>
    have hn := (hm.monotoneOn.mono (cell_subset_interval R j)).derivWithin_nonneg (x := t)
    rw [hd.derivWithin hu] at hn
    simpa using abs_of_nonneg hn
  | false =>
    have hn := (hm.antitoneOn.mono (cell_subset_interval R j)).derivWithin_nonpos (x := t)
    rw [hd.derivWithin hu] at hn
    simpa using abs_of_nonpos hn


lemma signed_cell_substitution {a b c d} (h : ParameterChange a b c d)
    (inc : Bool) (hm : Oriented h inc) (R : Partition c d)
    (hR : Refines R h.forward.partition) (j : Fin R.n) (f : ℝ → ℝ)
    (hf : RealIntegrable f
      ((imagePartition h inc hm R).point (orderIndex inc j).castSucc)
      ((imagePartition h inc hm R).point (orderIndex inc j).succ)) :
    ∃ hg : RealIntegrable
      (fun t => h.forward.derivative (parentCell hR j) t * f (h t))
      (R.point j.castSucc) (R.point j.succ),
      realIntegral _ hg = (if inc then 1 else -1) * realIntegral f hf := by
  have hs := parentCell_subset hR j
  have hd : C1OnInterval h (h.forward.derivative (parentCell hR j))
      (R.point j.castSucc) (R.point j.succ) :=
    ⟨(h.forward.smooth _).1.mono hs,
      fun t ht => ((h.forward.smooth _).2 t (hs ht)).mono hs⟩
  have hl := graph_point_mem R j.castSucc
  have hr := graph_point_mem R j.succ
  have hlr := R.strictMono (Fin.castSucc_lt_succ (i := j))
  cases inc with
  | true =>
    have horder := (hm hl hr hlr).le
    have hfo : Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue f
        (h (R.point j.castSucc)) (h (R.point j.succ)) := by
      simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue,
        min_eq_left horder, max_eq_right horder, imagePartition, orderIndex,
        Bool.true_eq, ↓reduceIte] using hf
    obtain ⟨hg, he⟩ := real_monotone_substitution h _ f hlr.le hd
      (Or.inl (hm.monotoneOn.mono (cell_subset_interval R j))) hfo
    refine ⟨hg, ?_⟩
    simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegralValue,
      ite_eq_left horder, min_eq_left horder, max_eq_right horder, imagePartition, orderIndex, Bool.true_eq, ↓reduceIte, one_mul] using he
  | false =>
    have horder := hm hl hr hlr
    have hfo : Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue f
        (h (R.point j.castSucc)) (h (R.point j.succ)) := by
      simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegrableValue,
        min_eq_right horder.le, max_eq_left horder.le, imagePartition, orderIndex,
        Bool.false_eq_true, ↓reduceIte, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev] using hf
    obtain ⟨hg, he⟩ := real_monotone_substitution h _ f hlr.le hd
      (Or.inr (hm.antitoneOn.mono (cell_subset_interval R j))) hfo
    refine ⟨hg, ?_⟩
    simpa only [Specs.SingleVariableAnalysis.Ch08.Oriented.realIntegralValue,
      ite_eq_right (not_le.mpr horder), min_eq_right horder.le, max_eq_left horder.le, imagePartition, orderIndex, Bool.false_eq_true,
      ↓reduceIte, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev, neg_one_mul] using he

/-- Density substitution uses the absolute derivative. Directed substitution
uses the derivative itself. Both are proper Riemann statements. -/
lemma cell_substitution {a b c d} (h : ParameterChange a b c d)
    (density inc : Bool) (hm : Oriented h inc) (R : Partition c d)
    (hR : Refines R h.forward.partition) (j : Fin R.n) (f : ℝ → ℝ)
    (hf : RealIntegrable f
      ((imagePartition h inc hm R).point (orderIndex inc j).castSucc)
      ((imagePartition h inc hm R).point (orderIndex inc j).succ)) :
    ∃ hg : RealIntegrable
      (fun t => (if density then |h.forward.derivative (parentCell hR j) t|
        else h.forward.derivative (parentCell hR j) t) * f (h t))
      (R.point j.castSucc) (R.point j.succ),
      realIntegral _ hg = (if density || inc then 1 else -1) * realIntegral f hf := by
  obtain ⟨hg, he⟩ := signed_cell_substitution h inc hm R hR j f hf
  cases density with
  | false => exact ⟨hg, he⟩
  | true =>
    obtain ⟨hk, hke⟩ := real_mul_value hg (if inc then 1 else -1)
    obtain ⟨hg', he'⟩ := riemann_congr hk (g := fun t =>
      |h.forward.derivative (parentCell hR j) t| * f (h t)) (by
        intro t ht
        dsimp only
        rw [parameter_derivative_sign h inc hm R hR j t ht, mul_assoc])
    refine ⟨hg', he'.trans (hke.trans ?_)⟩
    rw [he]
    cases inc <;> simp


/-- Substitution on the joint subdivision, followed by finite additivity.
`density` selects absolute homogeneity or linear homogeneity in velocity. -/
lemma pieceIntegral_composeData {n a b c d} {γ : IntervalPath n a b}
    (h : ParameterChange a b c d) (density inc : Bool) (hm : Oriented h inc)
    (v : PiecewiseC1Data γ) (R : Partition c d)
    (hR : Refines R h.forward.partition)
    (hQ : Refines (imagePartition h inc hm R) v.partition)
    (H : E n → E n → ℝ)
    (hH : ∀ x r z, H x (r • z) = (if density then |r| else r) * H x z)
    (hv : PieceIntegrable v H) :
    ∃ hw : PieceIntegrable (composeData h inc hm v R hR hQ) H,
      pieceIntegral (composeData h inc hm v R hR hQ) H hw =
        (if density || inc then 1 else -1) * pieceIntegral v H hv := by
  let Q := imagePartition h inc hm R
  let F (k : Fin Q.n) (t : ℝ) := H (γ t) (v.velocity (parentCell hQ k) t)
  obtain ⟨hf, hsum⟩ := sum_integrals_refinement hQ
    (fun i t => H (γ t) (v.velocity i t)) F hv (fun _ _ _ => rfl)
  have hsub (j : Fin R.n) := cell_substitution h density inc hm R hR j
    (F (orderIndex inc j)) (hf (orderIndex inc j))
  choose hg hval using hsub
  have hcong (j : Fin R.n) := riemann_congr (hg j)
    (g := fun t => H ((reparametrize γ h) t)
      ((composeData h inc hm v R hR hQ).velocity j t)) (by
        intro t _
        dsimp only [composeData, reparametrize,
          Specs.D04.C09.Reparametrization.Model.reparametrize, F, Function.comp_apply,
          IntervalPath.toFun]
        exact (hH _ _ _).symm)
  choose hw hwval using hcong
  refine ⟨hw, ?_⟩
  change (∑ j, realIntegral _ (hw j)) =
    (if density || inc then 1 else -1) * (∑ i, realIntegral _ (hv i))
  calc
    _ = ∑ j, (if density || inc then 1 else -1) *
        realIntegral (F (orderIndex inc j)) (hf (orderIndex inc j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (hwval j).trans (hval j)
    _ = (if density || inc then 1 else -1) *
        ∑ k, realIntegral (F k) (hf k) := by
      rw [← Finset.mul_sum]
      exact congrArg ((if density || inc then 1 else -1) * ·)
        (orderIndex_sum inc (fun k : Fin Q.n => realIntegral (F k) (hf k)))
    _ = _ := congrArg ((if density || inc then 1 else -1) * ·) hsum.symm

/-- The result applies to every choice of admissible path pieces. -/
lemma pieceIntegral_reparametrize {n a b c d} {γ : IntervalPath n a b}
    (h : ParameterChange a b c d) (density inc : Bool) (hm : Oriented h inc)
    (v : PiecewiseC1Data γ) (w : PiecewiseC1Data (reparametrize γ h))
    (H : E n → E n → ℝ)
    (hH : ∀ x r z, H x (r • z) = (if density then |r| else r) * H x z)
    (hv : PieceIntegrable v H) (hw : PieceIntegrable w H) :
    pieceIntegral w H hw = (if density || inc then 1 else -1) * pieceIntegral v H hv := by
  obtain ⟨R, hR, hQ, _⟩ := joint_partition h inc hm v.partition
  obtain ⟨hw', he⟩ := pieceIntegral_composeData h density inc hm v R hR hQ H hH hv
  exact (pieceIntegral_independent w (composeData h inc hm v R hR hQ) H hw hw').trans he

theorem scalar_reparametrize {n a b c d} {γ : IntervalPath n a b}
    (h : ParameterChange a b c d) (v : PiecewiseC1Data γ)
    (w : PiecewiseC1Data (reparametrize γ h)) (f : E n → ℝ)
    (hv : ScalarIntegrable v f) (hw : ScalarIntegrable w f) :
    scalarLineIntegral w f hw = scalarLineIntegral v f hv := by
  have hH (x : E n) (r : ℝ) (z : E n) :
      f x * ‖r • z‖ = |r| * (f x * ‖z‖) := by
    rw [norm_smul, Real.norm_eq_abs]; ring
  change pieceIntegral w (fun x z => f x * ‖z‖) hw =
    pieceIntegral v (fun x z => f x * ‖z‖) hv
  rcases monotonicity h with hm | hm
  · simpa using pieceIntegral_reparametrize h true true hm v w _ hH hv hw
  · simpa using pieceIntegral_reparametrize h true false hm v w _ hH hv hw

theorem covector_reparametrize_increasing {n a b c d} {γ : IntervalPath n a b}
    (h : ParameterChange a b c d) (hm : StrictMonoOn h (Icc c d))
    (v : PiecewiseC1Data γ) (w : PiecewiseC1Data (reparametrize γ h))
    (α : E n → E n →L[ℝ] ℝ) (hv : CovectorIntegrable v α) (hw : CovectorIntegrable w α) :
    covectorLineIntegral w α hw = covectorLineIntegral v α hv := by
  have hH (x : E n) (r : ℝ) (z : E n) : α x (r • z) = r * α x z := by simp
  change pieceIntegral w (fun x z => α x z) hw = pieceIntegral v (fun x z => α x z) hv
  simpa using pieceIntegral_reparametrize h false true hm v w _ hH hv hw

theorem covector_reparametrize_decreasing {n a b c d} {γ : IntervalPath n a b}
    (h : ParameterChange a b c d) (hm : StrictAntiOn h (Icc c d))
    (v : PiecewiseC1Data γ) (w : PiecewiseC1Data (reparametrize γ h))
    (α : E n → E n →L[ℝ] ℝ) (hv : CovectorIntegrable v α) (hw : CovectorIntegrable w α) :
    covectorLineIntegral w α hw = -covectorLineIntegral v α hv := by
  have hH (x : E n) (r : ℝ) (z : E n) : α x (r • z) = r * α x z := by simp
  change pieceIntegral w (fun x z => α x z) hw = -pieceIntegral v (fun x z => α x z) hv
  simpa using pieceIntegral_reparametrize h false false hm v w _ hH hv hw


theorem continuous_reparametrize {n a b c d} {γ : IntervalPath n a b}
    (h : ParameterChange a b c d) (v : PiecewiseC1Data γ)
    (f : E n → ℝ) (α : E n → E n →L[ℝ] ℝ)
    (hf : ContinuousOn f (trace γ)) (hα : ContinuousOn α (trace γ)) :
    ∃ w : PiecewiseC1Data (reparametrize γ h),
      ∃ hv : ScalarIntegrable v f, ∃ hw : ScalarIntegrable w f,
      ∃ hαv : CovectorIntegrable v α, ∃ hαw : CovectorIntegrable w α,
      scalarLineIntegral w f hw = scalarLineIntegral v f hv ∧
      (StrictMonoOn h (Icc c d) →
        covectorLineIntegral w α hαw = covectorLineIntegral v α hαv) ∧
      (StrictAntiOn h (Icc c d) →
        covectorLineIntegral w α hαw = -covectorLineIntegral v α hαv) := by
  obtain ⟨w⟩ := piecewiseC1_reparametrize γ h ⟨v⟩
  have hf' : ContinuousOn f (trace (reparametrize γ h)) := by
    rw [trace_reparametrize]; exact hf
  have hα' : ContinuousOn α (trace (reparametrize γ h)) := by
    rw [trace_reparametrize]; exact hα
  refine ⟨w, scalar_integrable v f hf, scalar_integrable w f hf',
    covector_integrable v α hα, covector_integrable w α hα',
    scalar_reparametrize h v w f _ _, ?_, ?_⟩
  · intro hm
    exact covector_reparametrize_increasing h hm v w α _ _
  · intro hm
    exact covector_reparametrize_decreasing h hm v w α _ _

theorem degenerate_reparametrize {n a c d} {γ : IntervalPath n a a}
    (h : ParameterChange a a c d) (v : PiecewiseC1Data γ)
    (w : PiecewiseC1Data (reparametrize γ h)) (f : E n → ℝ)
    (α : E n → E n →L[ℝ] ℝ) (hv : ScalarIntegrable v f) (hw : ScalarIntegrable w f)
    (hαv : CovectorIntegrable v α) (hαw : CovectorIntegrable w α) :
    length γ a a = 0 ∧ length (reparametrize γ h) c d = 0 ∧
    scalarLineIntegral v f hv = 0 ∧ scalarLineIntegral w f hw = 0 ∧
    covectorLineIntegral v α hαv = 0 ∧ covectorLineIntegral w α hαw = 0 := by
  have hcd := (singleton_iff h).mp rfl
  subst d
  exact ⟨length_degenerate γ a, length_degenerate _ c,
    scalarLineIntegral_degenerate v f hv, scalarLineIntegral_degenerate w f hw,
    covectorLineIntegral_degenerate v α hαv, covectorLineIntegral_degenerate w α hαw⟩

end D04.C09.Reparametrization
