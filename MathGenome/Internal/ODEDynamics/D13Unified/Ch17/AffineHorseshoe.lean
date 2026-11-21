import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.AffineHorseshoe
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.HorseshoeCoding
import Mathlib.Topology.Piecewise
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace D13Unified.Ch17.AffineHorseshoe
open Set Topology
open ShiftSpaces HorseshoeCoding
noncomputable section
open scoped Classical

abbrev horizontalStrip := Specs.D13Unified.Ch17.AffineHorseshoe.horizontalStrip
abbrev verticalDomain := Specs.D13Unified.Ch17.AffineHorseshoe.verticalDomain
abbrev horizontalDomain := Specs.D13Unified.Ch17.AffineHorseshoe.horizontalDomain
abbrev unitSquare := Specs.D13Unified.Ch17.AffineHorseshoe.unitSquare
abbrev invariantSet := Specs.D13Unified.Ch17.AffineHorseshoe.invariantSet
abbrev fullOrbitSet := Specs.D13Unified.Ch17.AffineHorseshoe.fullOrbitSet
abbrev diagonal := Specs.D13Unified.Ch17.AffineHorseshoe.diagonal

lemma branch_continuous (r : ℝ) (a : Binary) : Continuous (affineBranch r a) := by
  unfold affineBranch Specs.D13Unified.Ch17.HorseshoeCoding.affineBranch
  fun_prop

lemma vertical_closed (r : ℝ) (a : Binary) : IsClosed (verticalStrip r a) := by
  unfold verticalStrip Specs.D13Unified.Ch17.HorseshoeCoding.verticalStrip
  split_ifs <;> exact isClosed_Icc.prod isClosed_Icc

lemma horizontal_closed (r : ℝ) (a : Binary) : IsClosed (horizontalStrip r a) := by
  unfold horizontalStrip Specs.D13Unified.Ch17.AffineHorseshoe.horizontalStrip
  split_ifs <;> exact isClosed_Icc.prod isClosed_Icc

theorem strips_disjoint : Specs.D13Unified.Ch17.AffineHorseshoe.strips_disjointStatement := by
  intro r _ hrh
  constructor
  · apply Set.disjoint_left.mpr
    intro p hp hq
    have h0 : p.1 ≤ r := hp.1.2
    have h1 : 1-r ≤ p.1 := by simpa [verticalStrip,
      Specs.D13Unified.Ch17.HorseshoeCoding.verticalStrip] using hq.1.1
    linarith
  · apply Set.disjoint_left.mpr
    intro p hp hq
    have h0 : p.2 ≤ r := hp.2.2
    have h1 : 1-r ≤ p.2 := by simpa [horizontalStrip,
      Specs.D13Unified.Ch17.AffineHorseshoe.horizontalStrip] using hq.2.1
    linarith

/-- The inverse formula on the horizontal branch. -/
def inverseBranch (r : ℝ) (a : Binary) (p : ℝ × ℝ) : ℝ × ℝ :=
  (r*p.1 + (1-r)*(a.val : ℝ), (p.2-(1-r)*(a.val : ℝ))/r)

lemma branch_inverse {r : ℝ} (hr : r ≠ 0) (a : Binary) (p : ℝ × ℝ) :
    affineBranch r a (inverseBranch r a p) = p ∧
    inverseBranch r a (affineBranch r a p) = p := by
  constructor <;> apply Prod.ext <;>
    dsimp [affineBranch, Specs.D13Unified.Ch17.HorseshoeCoding.affineBranch, inverseBranch]
  all_goals field_simp; all_goals ring

lemma branch_maps {r : ℝ} (hr : 0 < r) (_hrh : r < 1/2) (a : Binary)
    {p : ℝ × ℝ} (hp : p ∈ verticalStrip r a) :
    affineBranch r a p ∈ horizontalStrip r a := by
  fin_cases a
  all_goals simp only [verticalStrip, Specs.D13Unified.Ch17.HorseshoeCoding.verticalStrip,
    horizontalStrip, Specs.D13Unified.Ch17.AffineHorseshoe.horizontalStrip,
    affineBranch, Specs.D13Unified.Ch17.HorseshoeCoding.affineBranch] at *
  all_goals norm_num at *
  all_goals simp only [le_div_iff₀ hr, div_le_iff₀ hr]
  all_goals constructor <;> constructor
  all_goals nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]

lemma inverse_maps {r : ℝ} (hr : 0 < r) (_hrh : r < 1/2) (a : Binary)
    {p : ℝ × ℝ} (hp : p ∈ horizontalStrip r a) :
    inverseBranch r a p ∈ verticalStrip r a := by
  fin_cases a
  all_goals simp only [verticalStrip, Specs.D13Unified.Ch17.HorseshoeCoding.verticalStrip,
    horizontalStrip, Specs.D13Unified.Ch17.AffineHorseshoe.horizontalStrip,
    inverseBranch] at *
  all_goals norm_num at *
  all_goals simp only [le_div_iff₀ hr, div_le_iff₀ hr]
  all_goals constructor <;> constructor
  all_goals nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]

theorem strip_images : Specs.D13Unified.Ch17.AffineHorseshoe.strip_imagesStatement := by
  intro r hr hrh a
  apply Subset.antisymm
  · rintro p ⟨q,hq,rfl⟩
    exact branch_maps hr hrh a hq
  · intro p hp
    exact ⟨inverseBranch r a p, inverse_maps hr hrh a hp, (branch_inverse hr.ne' a p).1⟩


/-- Select the unique branch of a point of the actual domain. -/
def symbol (r : ℝ) (p : ℝ × ℝ) : Binary := if p ∈ verticalStrip r 0 then 0 else 1

lemma symbol_mem (r : ℝ) {p : ℝ × ℝ} (hp : p ∈ verticalDomain r) :
    p ∈ verticalStrip r (symbol r p) := by
  unfold symbol
  split_ifs with h
  · exact h
  · exact hp.resolve_left h

lemma map_mem {r : ℝ} (hr : 0 < r) (hrh : r < 1/2)
    (p : verticalDomain r) : stripMap r p ∈ horizontalDomain r := by
  have heq : stripMap r p = affineBranch r (symbol r p.val) p.val :=
    stripMap_branch r hr hrh (symbol r p.val) p.val (symbol_mem r p.property) p.property
  rw [heq]
  have h := branch_maps hr hrh (symbol r p.val) (symbol_mem r p.property)
  generalize ha : symbol r p.val = a at h
  fin_cases a
  · exact Or.inl h
  · exact Or.inr h

lemma map_continuous {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) :
    Continuous (stripMap r) := by
  let A : Set (verticalDomain r) := Subtype.val ⁻¹' verticalStrip r 0
  let B : Set (verticalDomain r) := Subtype.val ⁻¹' verticalStrip r 1
  have hu : A ∪ B = univ := by ext p; simp only [mem_union, mem_univ, iff_true]; exact p.property
  have hc (a : Binary) : ContinuousOn (stripMap r)
      (Subtype.val ⁻¹' verticalStrip r a) := by
    apply ((branch_continuous r a).comp continuous_subtype_val).continuousOn.congr
    intro p hp
    exact stripMap_branch r hr hrh a p.val hp p.property
  rw [← continuousOn_univ, ← hu]
  exact (hc 0).union_of_isClosed (hc 1)
    ((vertical_closed r 0).preimage continuous_subtype_val)
    ((vertical_closed r 1).preimage continuous_subtype_val)

lemma horizontal_symbol_unique {r : ℝ} (hr : 0 < r) (hrh : r < 1/2)
    {a b : Binary} {p : ℝ × ℝ} (ha : p ∈ horizontalStrip r a)
    (hb : p ∈ horizontalStrip r b) : a = b := by
  by_contra h
  fin_cases a <;> fin_cases b
  all_goals try exact h rfl
  · exact Set.disjoint_left.mp (strips_disjoint r hr hrh).2 ha hb
  · exact Set.disjoint_left.mp (strips_disjoint r hr hrh).2 hb ha

lemma map_injective {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) :
    Function.Injective (stripMap r) := by
  intro p q hpq
  have hp := symbol_mem r p.property
  have hq := symbol_mem r q.property
  have heq : affineBranch r (symbol r p.val) p.val = affineBranch r (symbol r q.val) q.val := by
    simpa only [stripMap_branch r hr hrh _ _ hp p.property,
      stripMap_branch r hr hrh _ _ hq q.property] using hpq
  have hab : symbol r p.val = symbol r q.val :=
    horizontal_symbol_unique hr hrh (heq ▸ branch_maps hr hrh _ hp) (branch_maps hr hrh _ hq)
  rw [hab] at heq
  apply Subtype.ext
  have h := congrArg (inverseBranch r (symbol r q.val)) heq
  simpa only [(branch_inverse hr.ne' _ _).2] using h

lemma map_surjective {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) :
    Function.Surjective (fun p : verticalDomain r =>
      (⟨stripMap r p, map_mem hr hrh p⟩ : horizontalDomain r)) := by
  intro q
  have pre (a : Binary) (hq : q.val ∈ horizontalStrip r a) :
      ∃ p : verticalDomain r, stripMap r p = q.val := by
    have hp := inverse_maps hr hrh a hq
    have hd : inverseBranch r a q.val ∈ verticalDomain r := by
      fin_cases a
      · exact Or.inl hp
      · exact Or.inr hp
    refine ⟨⟨inverseBranch r a q.val, hd⟩, ?_⟩
    exact (stripMap_branch r hr hrh a _ hp hd).trans (branch_inverse hr.ne' a q.val).1
  obtain ⟨p,hp⟩ := q.property.elim (pre 0) (pre 1)
  exact ⟨p, Subtype.ext hp⟩

theorem strip_homeomorph : Specs.D13Unified.Ch17.AffineHorseshoe.strip_homeomorphStatement := by
  intro r hr hrh
  have hcompact : IsCompact (verticalDomain r) := by
    apply IsCompact.union
    · exact isCompact_Icc.prod isCompact_Icc
    · simpa [verticalStrip, Specs.D13Unified.Ch17.HorseshoeCoding.verticalStrip]
        using (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (1-r) 1 ×ˢ Icc (0:ℝ) 1))
  let : CompactSpace (verticalDomain r) := isCompact_iff_compactSpace.mp hcompact
  let f : verticalDomain r → horizontalDomain r := fun p => ⟨stripMap r p, map_mem hr hrh p⟩
  have hf : Continuous f := (map_continuous hr hrh).subtype_mk _
  let e := Equiv.ofBijective f ⟨fun p q h => map_injective hr hrh (congrArg Subtype.val h),
    map_surjective hr hrh⟩
  exact ⟨e.toHomeomorphOfContinuousClosed hf hf.isClosedMap, fun _ => rfl⟩


lemma coding_invariant {r : ℝ} (_hr : 0 < r) (_hrh : r < 1/2) (s : TwoSided) :
    coding r s ∈ invariantSet r :=
  ⟨⟨future s, rfl⟩, ⟨past s, rfl⟩⟩

lemma coding_unit {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (s : TwoSided) :
    coding r s ∈ unitSquare :=
  ⟨CantorGeometry.coding_mem_unit hr hrh _, CantorGeometry.coding_mem_unit hr hrh _⟩

/-- Translation by any integer, so no negative iterate of a partial map is invented. -/
def translate (s : TwoSided) (n : ℤ) : TwoSided := fun j => s (j+n)

lemma translate_zero (s : TwoSided) : translate s 0 = s := by funext j; simp [translate]
lemma shift_translate (s : TwoSided) (n : ℤ) : shift (translate s n) = translate s (n+1) := by
  funext j
  change s (j+1+n) = s (j+(n+1))
  congr 1; omega
lemma translate_head (s : TwoSided) (n : ℤ) : translate s n 0 = s n := by simp [translate]

lemma coded_full_orbit {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (s : TwoSided) :
    coding r s ∈ fullOrbitSet r := by
  refine ⟨fun n => coding r (translate s n), ?_, ?_⟩
  · exact congrArg (coding r) (translate_zero s)
  · intro n
    refine ⟨coding_unit hr hrh _, ?_⟩
    obtain ⟨hd, heq⟩ := coding_strip_map r hr hrh (translate s n)
    exact ⟨hd, by simpa only [shift_translate] using heq⟩

/-- The bounded error in a contracting recurrence vanishes. This is the
r^n remainder estimate for the digit series, used in both time directions. -/
lemma bounded_recurrence_unique {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (u v : ℕ → ℝ) (hu : ∀ n, u n ∈ Icc 0 1) (hv : ∀ n, v n ∈ Icc 0 1)
    (hrec : ∀ n, u n - v n = r * (u (n+1) - v (n+1))) : u 0 = v 0 := by
  have heq (n : ℕ) : u 0 - v 0 = r^n * (u n-v n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hrec n, pow_succ]; ring
  have hbound (n : ℕ) : |u 0-v 0| ≤ r^n := by
    rw [heq n, abs_mul, abs_of_nonneg (pow_nonneg hr.le _)]
    apply mul_le_of_le_one_right (pow_nonneg hr.le _)
    rw [abs_le]
    exact ⟨by linarith [(hu n).1, (hv n).2], by linarith [(hu n).2, (hv n).1]⟩
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1
  have hz : |u 0-v 0| ≤ 0 := ge_of_tendsto' hlim hbound
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

lemma orbit_unique {r : ℝ} (hr : 0 < r) (hrh : r < 1/2)
    (s : TwoSided) (z w : ℤ → ℝ × ℝ)
    (hz : ∀ n, z n ∈ unitSquare) (hw : ∀ n, w n ∈ unitSquare)
    (hze : ∀ n, affineBranch r (s n) (z n) = z (n+1))
    (hwe : ∀ n, affineBranch r (s n) (w n) = w (n+1)) : z 0 = w 0 := by
  have hx (n : ℤ) : (z n).1-(w n).1 = r*((z (n+1)).1-(w (n+1)).1) := by
    have h1 := congrArg Prod.fst (hze n)
    have h2 := congrArg Prod.fst (hwe n)
    change ((z n).1 - (1-r)*((s n).val : ℝ))/r = (z (n+1)).1 at h1
    change ((w n).1 - (1-r)*((s n).val : ℝ))/r = (w (n+1)).1 at h2
    have h1' := (div_eq_iff hr.ne').mp h1
    have h2' := (div_eq_iff hr.ne').mp h2
    nlinarith
  have hy (n : ℤ) : (z (n+1)).2-(w (n+1)).2 = r*((z n).2-(w n).2) := by
    have h1 := congrArg Prod.snd (hze n)
    have h2 := congrArg Prod.snd (hwe n)
    change r*(z n).2 + (1-r)*((s n).val : ℝ) = (z (n+1)).2 at h1
    change r*(w n).2 + (1-r)*((s n).val : ℝ) = (w (n+1)).2 at h2
    nlinarith
  apply Prod.ext
  · exact bounded_recurrence_unique hr (by linarith)
      (fun n => (z (n:ℤ)).1) (fun n => (w (n:ℤ)).1)
      (fun n => (hz _).1) (fun n => (hw _).1)
      (fun n => by simpa only [Nat.cast_add, Nat.cast_one] using hx (n:ℤ))
  · apply bounded_recurrence_unique hr (by linarith)
      (fun n => (z (-(n:ℤ))).2) (fun n => (w (-(n:ℤ))).2)
      (fun n => (hz _).2) (fun n => (hw _).2)
    intro n
    have h := hy (-(n:ℤ)-1)
    have he : -(n:ℤ)-1+1 = -(n:ℤ) := by omega
    rw [he] at h
    simpa only [Nat.cast_add, Nat.cast_one, neg_add, sub_eq_add_neg] using h

theorem maximal_full_orbit : Specs.D13Unified.Ch17.AffineHorseshoe.maximal_full_orbitStatement := by
  intro r hr hrh
  apply Subset.antisymm
  · rintro p ⟨z,hz0,hz⟩
    let s : TwoSided := fun n => symbol r (z n)
    let w : ℤ → ℝ × ℝ := fun n => coding r (translate s n)
    have hze (n : ℤ) : affineBranch r (s n) (z n) = z (n+1) := by
      obtain ⟨hd,heq⟩ := (hz n).2
      exact (stripMap_branch r hr hrh (s n) (z n) (symbol_mem r hd) hd).symm.trans heq
    have hwe (n : ℤ) : affineBranch r (s n) (w n) = w (n+1) := by
      have h := affine_intertwining r hr hrh (translate s n)
      simpa only [translate_head, shift_translate] using h
    have h := orbit_unique hr hrh s z w (fun n => (hz n).1)
      (fun n => coding_unit hr hrh _) hze hwe
    rw [hz0] at h
    rw [h]
    exact coding_invariant hr hrh _
  · rintro p ⟨⟨u,hu⟩, ⟨v,hv⟩⟩
    have hp : coding r (join (u,v)) = p := by
      apply Prod.ext
      · exact hu
      · exact hv
    rw [← hp]
    exact coded_full_orbit hr hrh _

theorem restriction_conjugacy :
    Specs.D13Unified.Ch17.AffineHorseshoe.restriction_conjugacyStatement := by
  intro r hr hrh
  obtain ⟨h,hh⟩ := coding_homeomorph r hr hrh
  let F := fun p => h (shift (h.symm p))
  refine ⟨h, F, hh, ?_, ?_⟩
  · intro p
    obtain ⟨hd,heq⟩ := coding_strip_map r hr hrh (h.symm p)
    have hp : Specs.D13Unified.Ch17.HorseshoeCoding.coding r (h.symm p) =
        (p.1.val,p.2.val) := by
      calc
        _ = ((h (h.symm p)).1.val, (h (h.symm p)).2.val) := (hh _).symm
        _ = _ := by rw [h.apply_symm_apply]
    have hd' : (p.1.val,p.2.val) ∈ verticalDomain r := hp ▸ hd
    have he : (⟨coding r (h.symm p), hd⟩ : verticalDomain r) =
        ⟨(p.1.val,p.2.val), hd'⟩ := Subtype.ext hp
    exact ⟨hd', (congrArg (stripMap r) he).symm.trans (heq.trans (hh _).symm)⟩
  · intro s
    change h (shift s) = h (shift (h.symm (h s)))
    rw [h.symm_apply_apply]

theorem branch_derivative : Specs.D13Unified.Ch17.AffineHorseshoe.branch_derivativeStatement := by
  intro r _hr _hrh a p
  have hx := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).sub_const ((1-r)*(a.val : ℝ))
  have hy := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_mul r
  convert (hx.const_mul r⁻¹).prodMk (hy.add_const ((1-r)*(a.val : ℝ))) using 1
  · funext q
    dsimp [affineBranch, Specs.D13Unified.Ch17.HorseshoeCoding.affineBranch]
    rw [div_eq_mul_inv, mul_comm]
  · rfl

theorem expansion_contraction : Specs.D13Unified.Ch17.AffineHorseshoe.expansion_contractionStatement := by
  intro r hr hrh
  refine ⟨(one_lt_inv₀ hr).mpr (by linarith), hr, by linarith, ?_, ?_⟩
  · intro v
    have h : diagonal r (v,0) = (r⁻¹*v,0) := by
      simp [diagonal, Specs.D13Unified.Ch17.AffineHorseshoe.diagonal]
    refine ⟨h, ?_⟩
    rw [h]
    simp [Prod.norm_def, norm_mul,
      Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]; positivity
  · intro v
    have h : diagonal r (0,v) = (0,r*v) := by
      simp [diagonal, Specs.D13Unified.Ch17.AffineHorseshoe.diagonal]
    refine ⟨h, ?_⟩
    rw [h]
    simp [Prod.norm_def, norm_mul, Real.norm_of_nonneg hr.le]; positivity

end
end D13Unified.Ch17.AffineHorseshoe
