import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Linearity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.TaggedEquivalence

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

/-- Addition commutes with all finite tagged sums and their fine-mesh limits. -/
theorem FineTaggedLimit.add {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    {f g : ℝ → E} {a b : ℝ} {I J : E}
    (hf : FineTaggedLimit f a b I) (hg : FineTaggedLimit g a b J) :
    FineTaggedLimit (fun x => f x + g x) a b (I + J) := by
  intro ε hε
  obtain ⟨δf, hδf, hcf⟩ := hf (ε / 2) (half_pos hε)
  obtain ⟨δg, hδg, hcg⟩ := hg (ε / 2) (half_pos hε)
  refine ⟨min δf δg, lt_min hδf hδg, fun P ξ hP => ?_⟩
  have hf' := hcf P ξ (hP.trans_le (min_le_left _ _))
  have hg' := hcg P ξ (hP.trans_le (min_le_right _ _))
  have he : taggedSum P ξ (fun x => f x + g x) - (I + J) =
      (taggedSum P ξ f - I) + (taggedSum P ξ g - J) := by
    simp only [taggedSum, S.sumValue, smul_add, Finset.sum_add_distrib]
    abel
  rw [he]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem FineTaggedLimit.mul {K : Type*} [RCLike K]
    {f : ℝ → K} {a b : ℝ} {I : K} (hf : FineTaggedLimit f a b I) (α : K) :
    FineTaggedLimit (fun x => α * f x) a b (α * I) := by
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hf (ε / (‖α‖ + 1)) (by positivity)
  refine ⟨δ, hδ, fun P ξ hP => ?_⟩
  have he : taggedSum P ξ (fun x => α * f x) - α * I =
      α * (taggedSum P ξ f - I) := by
    simp only [taggedSum, S.sumValue, mul_sub, Finset.mul_sum, mul_smul_comm]
  rw [he, norm_mul]
  have ht := hc P ξ hP
  have ht' := (lt_div_iff₀ (show 0 < ‖α‖ + 1 by positivity)).mp ht
  nlinarith [norm_nonneg (taggedSum P ξ f - I)]

theorem FineTaggedLimit.zero {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (a b : ℝ) : FineTaggedLimit (fun _ => (0 : E)) a b 0 := by
  intro ε hε
  exact ⟨1, zero_lt_one, by intros; simpa [S.sumValue] using hε⟩

theorem boundedOnInterval_of_abs {f : ℝ → ℝ} {a b M : ℝ}
    (hf : ∀ x ∈ Set.Icc a b, |f x| ≤ M) : BoundedOnInterval f a b :=
  ⟨⟨-M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hf x hx)).1⟩,
   ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact (abs_le.mp (hf x hx)).2⟩⟩

theorem BoundedOnInterval.abs_bound {f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOnInterval f a b) : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
  obtain ⟨L, hL⟩ := hf.1
  obtain ⟨U, hU⟩ := hf.2
  refine ⟨max |L| |U|, fun x hx => abs_le.mpr ⟨?_, ?_⟩⟩
  · exact (neg_le_neg (le_max_left _ _)).trans
      ((neg_abs_le L).trans (hL (Set.mem_image_of_mem _ hx)))
  · exact (hU (Set.mem_image_of_mem _ hx)).trans ((le_abs_self U).trans (le_max_right _ _))

theorem BoundedOnInterval.add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOnInterval f a b) (hg : BoundedOnInterval g a b) :
    BoundedOnInterval (fun x => f x + g x) a b := by
  obtain ⟨M, hM⟩ := hf.abs_bound
  obtain ⟨N, hN⟩ := hg.abs_bound
  exact boundedOnInterval_of_abs (fun x hx =>
    (abs_add_le _ _).trans (add_le_add (hM x hx) (hN x hx)))

theorem BoundedOnInterval.mul {f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOnInterval f a b) (α : ℝ) :
    BoundedOnInterval (fun x => α * f x) a b := by
  obtain ⟨M, hM⟩ := hf.abs_bound
  apply boundedOnInterval_of_abs (M := |α| * M)
  intro x hx
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg α)

theorem real_add_value {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b) :
    ∃ h : RealIntegrable (fun x => f x + g x) a b,
      realIntegral _ h = realIntegral f hf + realIntegral g hg := by
  apply (real_tagged_equivalence _ hf.ordered (hf.bounded.add hg.bounded) _).mpr
  exact ((real_tagged_equivalence _ hf.ordered hf.bounded _).mp ⟨hf, rfl⟩).add
    ((real_tagged_equivalence _ hg.ordered hg.bounded _).mp ⟨hg, rfl⟩)

theorem real_mul_value {f : ℝ → ℝ} {a b : ℝ} (hf : RealIntegrable f a b) (α : ℝ) :
    ∃ h : RealIntegrable (fun x => α * f x) a b,
      realIntegral _ h = α * realIntegral f hf := by
  apply (real_tagged_equivalence _ hf.ordered (hf.bounded.mul α) _).mpr
  exact ((real_tagged_equivalence _ hf.ordered hf.bounded _).mp ⟨hf, rfl⟩).mul α

theorem real_zero_value {a b : ℝ} (hab : a ≤ b) :
    ∃ h : RealIntegrable (fun _ => 0) a b, realIntegral _ h = 0 := by
  apply (real_tagged_equivalence _ hab (boundedOnInterval_of_abs (M := 0) (by simp)) _).mpr
  exact FineTaggedLimit.zero a b

theorem real_finite_linearity : Specs.SingleVariableAnalysis.Ch08.Linearity.realFiniteLinearity := by
  intro n
  induction n with
  | zero =>
    intro α f a b hab h
    simpa using real_zero_value hab
  | succ n ih =>
    intro α f a b hab h
    obtain ⟨ht, hIt⟩ := ih (fun j => α j.succ) (fun j => f j.succ) hab (fun j => h j.succ)
    obtain ⟨hh, hIh⟩ := real_mul_value (h 0) (α 0)
    obtain ⟨hs, hIs⟩ := real_add_value hh ht
    refine ⟨?_, ?_⟩
    · simpa only [Fin.sum_univ_succ] using hs
    · simpa only [Fin.sum_univ_succ, hIt, hIh] using hIs



theorem ComplexIntegrable.norm_bound {f : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := BoundedOnInterval.abs_bound (RealIntegrable.bounded hf.1)
  obtain ⟨N, hN⟩ := BoundedOnInterval.abs_bound (RealIntegrable.bounded hf.2)
  exact ⟨M + N, fun x hx => (Complex.norm_le_abs_re_add_abs_im _).trans
    (add_le_add (hM x hx) (hN x hx))⟩

theorem complex_add_value {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b) :
    ∃ h : ComplexIntegrable (fun x => f x + g x) a b,
      complexIntegral _ h = complexIntegral f hf + complexIntegral g hg := by
  obtain ⟨M, hM⟩ := hf.norm_bound
  obtain ⟨N, hN⟩ := hg.norm_bound
  have hb : ∃ C : ℝ, ∀ x ∈ Set.Icc a b, ‖f x + g x‖ ≤ C :=
    ⟨M + N, fun x hx => (norm_add_le _ _).trans (add_le_add (hM x hx) (hN x hx))⟩
  apply (complex_tagged_equivalence _ (RealIntegrable.ordered hf.1) hb _).mpr
  exact ((complex_tagged_equivalence _ (RealIntegrable.ordered hf.1) ⟨M, hM⟩ _).mp ⟨hf, rfl⟩).add
    ((complex_tagged_equivalence _ (RealIntegrable.ordered hg.1) ⟨N, hN⟩ _).mp ⟨hg, rfl⟩)

theorem complex_mul_value {f : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexIntegrable f a b) (α : ℂ) :
    ∃ h : ComplexIntegrable (fun x => α * f x) a b,
      complexIntegral _ h = α * complexIntegral f hf := by
  obtain ⟨M, hM⟩ := hf.norm_bound
  have hb : ∃ C : ℝ, ∀ x ∈ Set.Icc a b, ‖α * f x‖ ≤ C := by
    refine ⟨‖α‖ * M, fun x hx => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hM x hx) (norm_nonneg _)
  apply (complex_tagged_equivalence _ (RealIntegrable.ordered hf.1) hb _).mpr
  exact ((complex_tagged_equivalence _ (RealIntegrable.ordered hf.1) ⟨M, hM⟩ _).mp ⟨hf, rfl⟩).mul α

theorem complex_zero_value {a b : ℝ} (hab : a ≤ b) :
    ∃ h : ComplexIntegrable (fun _ => 0) a b, complexIntegral _ h = 0 := by
  apply (complex_tagged_equivalence _ hab ⟨0, by simp⟩ _).mpr
  exact FineTaggedLimit.zero a b

theorem complex_finite_linearity : Specs.SingleVariableAnalysis.Ch08.Linearity.complexFiniteLinearity := by
  intro n
  induction n with
  | zero =>
    intro α f a b hab h
    simpa using complex_zero_value hab
  | succ n ih =>
    intro α f a b hab h
    obtain ⟨ht, hIt⟩ := ih (fun j => α j.succ) (fun j => f j.succ) hab (fun j => h j.succ)
    obtain ⟨hh, hIh⟩ := complex_mul_value (h 0) (α 0)
    obtain ⟨hs, hIs⟩ := complex_add_value hh ht
    refine ⟨?_, ?_⟩
    · simpa only [Fin.sum_univ_succ] using hs
    · simpa only [Fin.sum_univ_succ, hIt, hIh] using hIs



/-- Concatenate strict partitions, identifying the shared endpoint once. -/
def joinPartition {a c b : ℝ} (P : Partition a c) (Q : Partition c b) : Partition a b where
  n := P.n + Q.n
  point i := if h : i.val ≤ P.n then P.point ⟨i.val, by omega⟩
    else Q.point ⟨i.val - P.n, by omega⟩
  strictMono := by
    intro i j hij
    dsimp
    split_ifs with hi hj hj
    · exact P.strictMono hij
    · have hl : P.point ⟨i.val, by omega⟩ ≤ c := by
        simpa only [P.last] using P.strictMono.monotone
          (show (⟨i.val, by omega⟩ : Fin (P.n+1)) ≤ Fin.last P.n from hi)
      have hr : c < Q.point ⟨j.val - P.n, by omega⟩ := by
        simpa only [Q.first] using Q.strictMono
          (show (0 : Fin (Q.n+1)) < ⟨j.val - P.n, by omega⟩ from by
            change 0 < j.val - P.n; omega)
      exact hl.trans_lt hr
    · have : i.val < j.val := hij
      omega
    · apply Q.strictMono
      change i.val - P.n < j.val - P.n
      have : i.val < j.val := hij
      omega
  first := by simpa using P.first
  last := by
    dsimp
    split_ifs with h
    · have hz : Q.n = 0 := by omega
      have hc : c = b := by
        have he : (0 : Fin (Q.n+1)) = Fin.last Q.n := Fin.ext (by simp [hz])
        exact Q.first.symm.trans ((congrArg Q.point he).trans Q.last)
      exact (congrArg P.point (Fin.ext (by dsimp; omega))).trans (P.last.trans hc)
    · convert Q.last using 2
      apply Fin.ext
      simp

theorem join_point_left {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (i : Fin (P.n+1)) (j : Fin ((joinPartition P Q).n+1)) (h : j.val = i.val) :
    (joinPartition P Q).point j = P.point i := by
  have hi : j.val ≤ P.n := by have := i.isLt; omega
  simp only [joinPartition, dite_eq_left hi]
  congr 1
  exact Fin.ext h

theorem join_point_right {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (i : Fin (Q.n+1)) (j : Fin ((joinPartition P Q).n+1)) (h : j.val = P.n + i.val) :
    (joinPartition P Q).point j = Q.point i := by
  by_cases hi : i.val = 0
  · have hj : j.val ≤ P.n := by omega
    simp only [joinPartition, dite_eq_left hj]
    have he : (⟨j.val, by omega⟩ : Fin (P.n+1)) = Fin.last P.n := Fin.ext (by simp; omega)
    rw [he, P.last, show i = 0 from Fin.ext hi, Q.first]
  · have hj : ¬ j.val ≤ P.n := by omega
    simp only [joinPartition, dite_eq_right hj]
    congr 1
    apply Fin.ext
    dsimp
    omega

/-- A general sum of cell coefficients splits without any regularity premise. -/
noncomputable def cellSum (φ : Set ℝ → ℝ) {a b : ℝ} (P : Partition a b) : ℝ :=
  ∑ i : Fin P.n, φ (cell P i) * cellLength P i

theorem cellSum_join (φ : Set ℝ → ℝ) {a c b : ℝ}
    (P : Partition a c) (Q : Partition c b) :
    cellSum φ (joinPartition P Q) = cellSum φ P + cellSum φ Q := by
  change (∑ i : Fin (P.n + Q.n), φ (cell (joinPartition P Q) i) * cellLength (joinPartition P Q) i) = _
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [cell, D.cellValue, cellLength, S.lengthValue]
    rw [join_point_left P Q i.castSucc _ rfl, join_point_left P Q i.succ _ rfl]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [cell, D.cellValue, cellLength, S.lengthValue]
    rw [join_point_right P Q i.castSucc _ rfl, join_point_right P Q i.succ _ (by
      change P.n + i.val + 1 = P.n + (i.val + 1); omega)]



def leftPartition {a b : ℝ} (P : Partition a b) (k : Fin (P.n+1)) :
    Partition a (P.point k) where
  n := k.val
  point i := P.point ⟨i.val, by have := k.isLt; omega⟩
  strictMono := fun _ _ h => P.strictMono h
  first := P.first
  last := by apply congrArg P.point; exact Fin.ext rfl

def rightPartition {a b : ℝ} (P : Partition a b) (k : Fin (P.n+1)) :
    Partition (P.point k) b where
  n := P.n - k.val
  point i := P.point ⟨k.val + i.val, by have := k.isLt; omega⟩
  strictMono := by intro i j hij; apply P.strictMono; change k.val + i.val < k.val + j.val; omega
  first := by apply congrArg P.point; exact Fin.ext (Nat.add_zero _)
  last := by
    convert P.last using 2
    apply Fin.ext
    dsimp
    have := k.isLt
    omega

theorem partition_ext {a b : ℝ} {P Q : Partition a b} (hn : P.n = Q.n)
    (hp : ∀ i j, i.val = j.val → P.point i = Q.point j) : P = Q := by
  cases P with
  | mk n p hm hf hl =>
    cases Q with
    | mk m q hm' hf' hl' =>
      dsimp at hn hp
      subst m
      have he : p = q := funext (fun i => hp i i rfl)
      subst q
      rfl

theorem join_left_right {a b : ℝ} (P : Partition a b) (k : Fin (P.n+1)) :
    joinPartition (leftPartition P k) (rightPartition P k) = P := by
  apply partition_ext (by dsimp [joinPartition, leftPartition, rightPartition]; have := k.isLt; omega)
  intro i j hij
  dsimp [joinPartition, leftPartition, rightPartition]
  split_ifs with hi
  · simp only [hi, ↓reduceDIte]
    apply congrArg P.point
    exact Fin.ext hij
  · simp only [hi, ↓reduceDIte]
    apply congrArg P.point
    apply Fin.ext
    dsimp
    omega

theorem BoundedOnInterval.mono {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : BoundedOnInterval f a b) (hs : Set.Icc c d ⊆ Set.Icc a b) :
    BoundedOnInterval f c d :=
  ⟨hf.1.mono (Set.image_mono hs), hf.2.mono (Set.image_mono hs)⟩

theorem upperSum_join (f : ℝ → ℝ) {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (hf : BoundedOnInterval f a b) (hl : BoundedOnInterval f a c)
    (hr : BoundedOnInterval f c b) :
    upperSum f (joinPartition P Q) hf = upperSum f P hl + upperSum f Q hr :=
  cellSum_join (fun J => sSup (f '' J)) P Q

theorem lowerSum_join (f : ℝ → ℝ) {a c b : ℝ} (P : Partition a c) (Q : Partition c b)
    (hf : BoundedOnInterval f a b) (hl : BoundedOnInterval f a c)
    (hr : BoundedOnInterval f c b) :
    lowerSum f (joinPartition P Q) hf = lowerSum f P hl + lowerSum f Q hr :=
  cellSum_join (fun J => sInf (f '' J)) P Q

/-- Inserting a specified point gives a refinement that is a concatenation. -/
theorem exists_split_refinement {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (P : Partition a b) :
    ∃ (L : Partition a c) (R : Partition c b), Refines (joinPartition L R) P := by
  classical
  let s := insert c (points P)
  have ha : a ∈ s := Finset.mem_insert_of_mem (endpoints P).1
  have hb : b ∈ s := Finset.mem_insert_of_mem (endpoints P).2.1
  have hs : ∀ x ∈ s, x ∈ Set.Icc a b := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hac, hcb⟩
    · exact (endpoints P).2.2 x hx
  obtain ⟨Q, hQ⟩ := finite_representation s ha hb hs
  change points Q = s at hQ
  have hc : c ∈ points Q := by rw [hQ]; exact Finset.mem_insert_self _ _
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hc
  have href : Refines Q P := by
    change points P ⊆ points Q
    rw [hQ]
    exact Finset.subset_insert _ _
  rw [← hk]
  exact ⟨leftPartition Q k, rightPartition Q k, by rw [join_left_right]; exact href⟩



/-- Inclusive version of the Darboux criterion, using the empty partition at a singleton. -/
theorem realIntegrable_iff_small_gap (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : BoundedOnInterval f a b) :
    RealIntegrable f a b ↔ ∀ ε : ℝ, 0 < ε →
      ∃ P : Partition a b, upperSum f P hf - lowerSum f P hf < ε := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · exact darboux_criterion f hab hf
  · constructor
    · intro _ ε hε
      have hz : lowerSum f (emptyPartition a) hf = 0 ∧
          upperSum f (emptyPartition a) hf = 0 := degenerate_sums f a _ hf
      exact ⟨emptyPartition a, by rw [hz.1, hz.2]; simpa using hε⟩
    · intro _
      exact realIntegrable_degenerate f a

theorem real_split : Specs.SingleVariableAnalysis.Ch08.Linearity.realSplit := by
  intro f a c b hac hcb hf
  have hab := hac.trans hcb
  have hl : BoundedOnInterval f a c := BoundedOnInterval.mono hf (Set.Icc_subset_Icc le_rfl hcb)
  have hr : BoundedOnInterval f c b := BoundedOnInterval.mono hf (Set.Icc_subset_Icc hac le_rfl)
  have gap_join (L : Partition a c) (R : Partition c b) :
      upperSum f (joinPartition L R) hf - lowerSum f (joinPartition L R) hf =
        (upperSum f L hl - lowerSum f L hl) + (upperSum f R hr - lowerSum f R hr) := by
    rw [upperSum_join f L R hf hl hr, lowerSum_join f L R hf hl hr]
    ring
  constructor
  · constructor
    · intro h
      have hparts : ∀ ε : ℝ, 0 < ε → ∃ (L : Partition a c) (R : Partition c b),
          (upperSum f L hl - lowerSum f L hl) + (upperSum f R hr - lowerSum f R hr) < ε := by
        intro ε hε
        obtain ⟨P, hP⟩ := (realIntegrable_iff_small_gap f hab hf).mp h ε hε
        obtain ⟨L, R, href⟩ := exists_split_refinement hac hcb P
        refine ⟨L, R, ?_⟩
        rw [← gap_join]
        have hu := upper_refinement f P (joinPartition L R) hf href
        have hl' := lower_refinement f P (joinPartition L R) hf href
        linarith
      constructor
      · apply (realIntegrable_iff_small_gap f hac hl).mpr
        intro ε hε
        obtain ⟨L, R, hLR⟩ := hparts ε hε
        exact ⟨L, by linarith [lowerSum_le_upperSum f R hr]⟩
      · apply (realIntegrable_iff_small_gap f hcb hr).mpr
        intro ε hε
        obtain ⟨L, R, hLR⟩ := hparts ε hε
        exact ⟨R, by linarith [lowerSum_le_upperSum f L hl]⟩
    · rintro ⟨hL, hR⟩
      apply (realIntegrable_iff_small_gap f hab hf).mpr
      intro ε hε
      obtain ⟨L, hL'⟩ := (realIntegrable_iff_small_gap f hac hl).mp hL (ε/2) (half_pos hε)
      obtain ⟨R, hR'⟩ := (realIntegrable_iff_small_gap f hcb hr).mp hR (ε/2) (half_pos hε)
      exact ⟨joinPartition L R, by rw [gap_join]; linarith⟩
  · intro h hL hR
    by_contra hne
    let ε := |realIntegral f h - (realIntegral f hL + realIntegral f hR)|
    have hε : 0 < ε := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨L, hL'⟩ := (realIntegrable_iff_small_gap f hac hl).mp hL (ε/2) (half_pos hε)
    obtain ⟨R, hR'⟩ := (realIntegrable_iff_small_gap f hcb hr).mp hR (ε/2) (half_pos hε)
    have hW := realIntegral_bounds f h (joinPartition L R)
    have hIL := realIntegral_bounds f hL L
    have hIR := realIntegral_bounds f hR R
    change lowerSum f (joinPartition L R) hf ≤ realIntegral f h ∧
      realIntegral f h ≤ upperSum f (joinPartition L R) hf at hW
    rw [upperSum_join f L R hf hl hr, lowerSum_join f L R hf hl hr] at hW
    change lowerSum f L hl ≤ realIntegral f hL ∧ realIntegral f hL ≤ upperSum f L hl at hIL
    change lowerSum f R hr ≤ realIntegral f hR ∧ realIntegral f hR ≤ upperSum f R hr at hIR
    have hbound : ε ≤ (upperSum f L hl - lowerSum f L hl) +
        (upperSum f R hr - lowerSum f R hr) := by
      apply abs_le.mpr
      constructor <;> linarith [hW.1, hW.2, hIL.1, hIL.2, hIR.1, hIR.2]
    linarith

theorem complex_split : Specs.SingleVariableAnalysis.Ch08.Linearity.complexSplit := by
  intro f a c b hac hcb hf
  obtain ⟨hfr, hfi⟩ := complex_components_bounded f hf
  have hre := real_split (fun x => (f x).re) hac hcb hfr
  have him := real_split (fun x => (f x).im) hac hcb hfi
  constructor
  · constructor
    · intro h
      exact ⟨⟨(hre.1.mp h.1).1, (him.1.mp h.2).1⟩,
        ⟨(hre.1.mp h.1).2, (him.1.mp h.2).2⟩⟩
    · rintro ⟨hl, hr⟩
      exact ⟨hre.1.mpr ⟨hl.1, hr.1⟩, him.1.mpr ⟨hl.2, hr.2⟩⟩
  · intro h hl hr
    apply Complex.ext
    · simp only [Complex.add_re]
      rw [(complexIntegral_components f h).1, (complexIntegral_components f hl).1,
        (complexIntegral_components f hr).1]
      exact hre.2 h.1 hl.1 hr.1
    · simp only [Complex.add_im]
      rw [(complexIntegral_components f h).2, (complexIntegral_components f hl).2,
        (complexIntegral_components f hr).2]
      exact him.2 h.2 hl.2 hr.2

end SingleVariableAnalysis.Riemann
