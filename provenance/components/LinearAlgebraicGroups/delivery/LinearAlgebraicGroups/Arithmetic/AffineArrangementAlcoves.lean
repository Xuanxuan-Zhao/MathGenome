import Specs.LinearAlgebraicGroups.Arithmetic.AffineArrangementAlcoves
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Set

namespace LinearAlgebraicGroups.Arithmetic.AffineArrangement

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (D : Datum K V ι)

theorem reflectionFormula : Expected.ReflectionFormula D := by
  intro a x
  rw [Datum.reflection, AffineEquiv.coe_mul]
  change (-a.2) • D.coroot a.1 + D.linearReflection a.1 x = _
  rw [Datum.linearReflection, Module.reflection_apply, Datum.value, add_smul,
    ← Int.cast_smul_eq_zsmul K, Int.cast_neg, neg_smul]
  abel

@[simp] theorem reflection_linear (a : Wall ι) :
    (D.reflection a).linear = D.linearReflection a.1 := by
  change (1 : V ≃ₗ[K] V) * D.linearReflection a.1 = _
  simp

theorem value_reflection_self (a : Wall ι) (x : V) :
    D.value a (D.reflection a x) = -D.value a x := by
  rw [reflectionFormula]
  simp only [Datum.value, map_sub, map_smul, smul_eq_mul, D.diagonal]
  ring

theorem reflectionInvolution : Expected.ReflectionInvolution D := by
  intro a
  apply AffineEquiv.ext
  intro x
  change D.reflection a (D.reflection a x) = x
  rw [reflectionFormula, value_reflection_self, reflectionFormula, neg_smul]
  abel

theorem reflection_inv (a : Wall ι) : (D.reflection a)⁻¹ = D.reflection a := by
  have h := reflectionInvolution D a
  simpa using congrArg (fun g => (D.reflection a)⁻¹ * g) h.symm

variable [LinearOrder K] [IsStrictOrderedRing K]

theorem value_injective (hD : D.ReducedDirections) :
    Function.Injective D.value := by
  rintro ⟨i, m⟩ ⟨j, n⟩ h
  have hmn : m = n := by
    have hm := congrFun h (0 : V)
    simpa [Datum.value] using hm
  subst n
  suffices h : i = j by subst j; rfl
  apply hD.1
  ext x
  exact add_right_cancel (congrFun h x)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem neg_index (hR : D.ReflectionClosed) (i : ι) :
    ∃ j, D.root j = -D.root i ∧ D.coroot j = -D.coroot i := by
  obtain ⟨j, hj, hc⟩ := hR i i
  refine ⟨j, ?_, ?_⟩
  · rw [hj]
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Datum.linearReflection,
      Module.reflection_apply, map_sub, map_smul, smul_eq_mul, D.diagonal,
      LinearMap.neg_apply]
    ring
  · rw [hc, Datum.linearReflection, Module.reflection_apply_self]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem opposite_value_coroot (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    (a : Wall ι) :
    (∀ x, D.value (D.opposite a) x = - D.value a x) ∧
      D.coroot (D.opposite a).1 = -D.coroot a.1 := by
  classical
  obtain ⟨j, hj, hc⟩ := neg_index D hR a.1
  have hex : ∃ i, D.root i = -D.root a.1 := ⟨j, hj⟩
  have hi : hex.choose = j := hD.1 (hex.choose_spec.trans hj.symm)
  simp only [Datum.opposite, dite_eq_left hex, hi, hc, and_true]
  intro x
  simp [Datum.value, hj, add_comm]

theorem oppositeRules : Expected.OppositeRules D := by
  intro hR hD a
  obtain ⟨hv, hc⟩ := opposite_value_coroot D hR hD a
  refine ⟨hv, hc, value_injective D hD ?_, ?_⟩
  · funext x
    rw [(opposite_value_coroot D hR hD _).1, hv, neg_neg]
  · apply AffineEquiv.ext
    intro x
    rw [reflectionFormula, reflectionFormula, hv, hc, smul_neg, neg_smul, neg_neg]

theorem transports_unique (hD : D.ReducedDirections) {g : V ≃ᵃ[K] V}
    {a b c : Wall ι} (hb : D.Transports g a b) (hc : D.Transports g a c) : b = c := by
  apply value_injective D hD
  funext x
  obtain ⟨y, rfl⟩ := g.surjective x
  rw [hb.1, hc.1]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Datum.Transports.inv {D : Datum K V ι} {g : V ≃ᵃ[K] V} {a b : Wall ι}
    (h : D.Transports g a b) : D.Transports g⁻¹ b a := by
  constructor
  · intro x
    have hx := h.1 (g.symm x)
    change D.value a (g.symm x) = D.value b x
    simpa using hx.symm
  · change g.linear.symm (D.coroot b.1) = _
    rw [← h.2, LinearEquiv.symm_apply_apply]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Datum.Transports.mul {D : Datum K V ι} {g h : V ≃ᵃ[K] V} {a b c : Wall ι}
    (hg : D.Transports g b c) (hh : D.Transports h a b) :
    D.Transports (g * h) a c := by
  constructor
  · intro x
    change D.value c (g (h x)) = _
    rw [hg.1, hh.1]
  · change g.linear (h.linear (D.coroot a.1)) = _
    rw [hh.2, hg.2]

private theorem mem_symmetries (hD : D.ReducedDirections) (g : V ≃ᵃ[K] V)
    (hg : ∀ a, ∃ b, D.Transports g a b) (hi : ∀ a, ∃ b, D.Transports g⁻¹ a b) :
    g ∈ D.symmetries := by
  classical
  let f : Wall ι → Wall ι := fun a => (hg a).choose
  have hf (a : Wall ι) : D.Transports g a (f a) := (hg a).choose_spec
  have hinj : Function.Injective f := by
    intro a b hab
    have h := (hf a).inv
    rw [hab] at h
    exact transports_unique D hD h (hf b).inv
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a, ha⟩ := hi b
    exact ⟨a, transports_unique D hD (hf a) ha.inv⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem reflection_transports (hR : D.ReflectionClosed) (a b : Wall ι) :
    ∃ c, D.Transports (D.reflection a) b c := by
  obtain ⟨i, hi, hc⟩ := hR a.1 b.1
  obtain ⟨m, hm⟩ := D.integral i a.1
  refine ⟨(i, b.2 + a.2 * m), ?_, ?_⟩
  · intro x
    have hh : D.root i (D.linearReflection a.1 x) = D.root b.1 x := by
      rw [hi]
      exact congrArg (D.root b.1) ((Module.involutive_reflection (D.diagonal a.1)) x)
    change D.root i ((-a.2) • D.coroot a.1 + D.linearReflection a.1 x) +
      ((b.2 + a.2 * m : ℤ) : K) = _
    simp only [Datum.value, map_add, ← Int.cast_smul_eq_zsmul K, map_smul, smul_eq_mul,
      Int.cast_neg, Int.cast_add, Int.cast_mul, hm, hh]
    ring
  · exact hc.symm

theorem reflection_mem_symmetries (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    (a : Wall ι) : D.reflection a ∈ D.symmetries := by
  apply mem_symmetries D hD
  · exact reflection_transports D hR a
  · rw [reflection_inv]
    exact reflection_transports D hR a

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem translation_transports (v : V) (hv : ∀ i, ∃ m : ℤ, D.root i v = (m : K))
    (a : Wall ι) :
    ∃ b, D.Transports (AffineEquiv.constVAdd K V v) a b := by
  obtain ⟨m, hm⟩ := hv a.1
  refine ⟨(a.1, a.2 - m), fun x => ?_, rfl⟩
  change D.root a.1 (v + x) + ((a.2 - m : ℤ) : K) = _
  simp only [Datum.value, map_add, hm, Int.cast_sub]
  ring

theorem groupPreservation : Expected.GroupPreservation D := by
  intro hR hD
  refine ⟨(Subgroup.closure_le _).mpr ?_, (Subgroup.closure_le _).mpr ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact reflection_mem_symmetries D hR hD a
  · rintro g (⟨i, rfl⟩ | ⟨v, hv, rfl⟩)
    · have he : D.reflection (i, 0) = (D.linearReflection i).toAffineEquiv := by
        rw [Datum.reflection]
        change AffineEquiv.constVAdd K V ((-(0 : ℤ)) • D.coroot i) * _ = _
        rw [neg_zero, zero_smul, AffineEquiv.constVAdd_zero, ← AffineEquiv.one_def, one_mul]
      change (D.linearReflection i).toAffineEquiv ∈ D.symmetries
      rw [← he]
      exact reflection_mem_symmetries D hR hD (i, 0)
    · apply mem_symmetries D hD
      · exact translation_transports D v hv
      · change ∀ a, ∃ b, D.Transports (AffineEquiv.constVAdd K V (-v)) a b
        refine translation_transports D (-v) (fun i => ?_)
        obtain ⟨m, hm⟩ := hv i
        exact ⟨-m, by simp [hm]⟩

theorem Datum.Transports.opposite {D : Datum K V ι} (hR : D.ReflectionClosed)
    (hD : D.ReducedDirections) {g : V ≃ᵃ[K] V} {a b : Wall ι}
    (h : D.Transports g a b) : D.Transports g (D.opposite a) (D.opposite b) := by
  obtain ⟨ha, hca⟩ := opposite_value_coroot D hR hD a
  obtain ⟨hb, hcb⟩ := opposite_value_coroot D hR hD b
  exact ⟨fun x => by rw [hb, ha, h.1], by rw [hca, hcb, map_neg, h.2]⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem Datum.Transports.conjugates {D : Datum K V ι} {g : V ≃ᵃ[K] V} {a b : Wall ι}
    (h : D.Transports g a b) : D.reflection b = g * D.reflection a * g⁻¹ := by
  apply AffineEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := g.surjective x
  change D.reflection b (g y) = g (D.reflection a (g.symm (g y)))
  rw [g.symm_apply_apply, reflectionFormula, reflectionFormula, h.1]
  rw [sub_eq_neg_add (a := g y), sub_eq_neg_add (a := y)]
  change _ = g ((-(D.value a y • D.coroot a.1)) +ᵥ y)
  rw [g.map_vadd, map_neg, map_smul, h.2]
  rfl

/-- The action on signed equations is precomposition with the inverse affine map. -/
@[instance_reducible] noncomputable def signedMulAction (hD : D.ReducedDirections) :
    MulAction D.symmetries (Wall ι) where
  smul g a := g.property.choose a
  one_smul a := transports_unique D hD ((1 : D.symmetries).property.choose_spec a)
    ⟨fun _ => rfl, rfl⟩
  mul_smul g h a := transports_unique D hD ((g * h).property.choose_spec a)
    ((g.property.choose_spec _).mul (h.property.choose_spec a))

theorem signedAction : Expected.SignedAction D := by
  intro hR hD
  refine ⟨signedMulAction D hD, fun g a => ?_⟩
  have h := g.property.choose_spec a
  exact ⟨h, transports_unique D hD (g.property.choose_spec _) (h.opposite hR hD),
    h.conjugates⟩

theorem alcove_iff (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    {p x : V} (hp : D.regular p) : x ∈ D.alcove p ↔
      ∀ a, (0 < D.value a x ↔ 0 < D.value a p) ∧
        (D.value a x < 0 ↔ D.value a p < 0) := by
  refine ⟨fun hx a => ?_, fun hx a ha => (hx a).1.mpr ha⟩
  have ho := (opposite_value_coroot D hR hD a).1
  have hneg (h : D.value a p < 0) : D.value a x < 0 := by
    have hab : D.positive p (D.opposite a) := by
      change 0 < D.value (D.opposite a) p
      rwa [ho, neg_pos]
    have hh := hx (D.opposite a) hab
    change 0 < D.value (D.opposite a) x at hh
    rwa [ho, neg_pos] at hh
  rcases (hp a).lt_or_gt with hn | hh
  · have hnx := hneg hn
    exact ⟨iff_of_false (not_lt_of_ge hnx.le) (not_lt_of_ge hn.le), iff_of_true hnx hn⟩
  · have hhx := hx a hh
    exact ⟨iff_of_true hhx hh, iff_of_false (not_lt_of_ge hhx.le) (not_lt_of_ge hh.le)⟩

theorem regular_of_mem_alcove (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    {p x : V} (hp : D.regular p) (hx : x ∈ D.alcove p) : D.regular x := by
  intro a
  have h := (alcove_iff D hR hD hp).mp hx a
  rcases (hp a).lt_or_gt with hn | hh
  · exact ((h.2).mpr hn).ne
  · exact ((h.1).mpr hh).ne'

omit [IsStrictOrderedRing K] in
theorem alcove_eq_of_mem {p q : V} (hq : q ∈ D.alcove p) (hp : p ∈ D.alcove q) :
    D.alcove p = D.alcove q := by
  ext x
  exact ⟨fun hx a ha => hx a (hp a ha), fun hx a ha => hx a (hq a ha)⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem symmetry_reg (g : V ≃ᵃ[K] V) (hg : g ∈ D.symmetries)
    {p : V} (hp : D.regular p) : D.regular (g p) := by
  obtain ⟨σ, hσ⟩ := hg
  intro a
  obtain ⟨b, rfl⟩ := σ.surjective a
  rw [(hσ b).1]
  exact hp b

omit [IsStrictOrderedRing K] in
theorem symmetry_alcove (g : V ≃ᵃ[K] V) (hg : g ∈ D.symmetries) (p : V) :
    g '' D.alcove p = D.alcove (g p) := by
  obtain ⟨σ, hσ⟩ := hg
  have h (x : V) : g x ∈ D.alcove (g p) ↔ x ∈ D.alcove p := by
    constructor
    · intro hx a ha
      have hh := hx (σ a)
      simp only [Datum.positive, (hσ a).1] at hh
      exact hh ha
    · intro hx b
      obtain ⟨a, rfl⟩ := σ.surjective b
      simp only [Datum.positive, (hσ a).1]
      exact hx a
  ext y
  obtain ⟨x, rfl⟩ := g.surjective y
  exact ⟨fun ⟨z, hz, he⟩ => (h x).mpr (g.injective he ▸ hz),
    fun hx => ⟨x, (h x).mp hx, rfl⟩⟩

theorem signsAndAlcoveAction : Expected.SignsAndAlcoveAction D := by
  intro hR hD p hp
  exact ⟨fun _ => alcove_iff D hR hD hp,
    fun g hg => ⟨symmetry_reg D g hg hp, symmetry_alcove D g hg p⟩⟩

/-- Symmetries send alcoves to their images under the affine maps. -/
@[instance_reducible] def chamberMulAction : MulAction D.symmetries D.Chamber where
  smul g C := ⟨(g.val : V → V) '' C.val, by
    obtain ⟨p, hp, he⟩ := C.property
    exact ⟨g.val p, symmetry_reg D g.val g.property hp, by
      rw [he, symmetry_alcove D g.val g.property p]⟩⟩
  one_smul C := Subtype.ext (Set.image_id _)
  mul_smul g h C := by
    apply Subtype.ext
    change (fun x => g.val (h.val x)) '' C.val = (g.val : V → V) '' ((h.val : V → V) '' C.val)
    exact (Set.image_image _ _ _).symm

omit [IsStrictOrderedRing K] in
theorem chamberAction : Expected.ChamberAction D := by
  refine ⟨chamberMulAction D, ?_⟩
  intro g C
  rfl

/-- Pullback of the affine equation by the inverse symmetry. -/
theorem signed_value (hD : D.ReducedDirections) (g : D.symmetries) (a : Wall ι) (x : V) :
    D.value (@SMul.smul _ _ (signedMulAction D hD).toSMul g a) x =
      D.value a (g.val.symm x) := by
  change D.value (g.property.choose a) x = _
  have h := (g.property.choose_spec a).1 (g.val.symm x)
  simpa using h

theorem opposite_positive (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    {p : V} (hp : D.regular p) (a : Wall ι) :
    D.positive p (D.opposite a) ↔ ¬D.positive p a := by
  change 0 < D.value (D.opposite a) p ↔ ¬0 < D.value a p
  rw [(opposite_value_coroot D hR hD a).1, neg_pos, not_lt]
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (hp a)⟩

theorem reflection_transports_opposite (hR : D.ReflectionClosed)
    (hD : D.ReducedDirections) (a : Wall ι) :
    D.Transports (D.reflection a) a (D.opposite a) := by
  obtain ⟨hv, hc⟩ := opposite_value_coroot D hR hD a
  exact ⟨fun x => by rw [hv, value_reflection_self, neg_neg],
    by rw [hc, reflection_linear, Datum.linearReflection, Module.reflection_apply_self]⟩

theorem simpleWallSigns : Expected.SimpleWallSigns D := by
  intro hR hD p a hp ha
  refine ⟨reflection_transports_opposite D hR hD a, ?_⟩
  obtain ⟨_, z, hz, hother⟩ := ha
  intro b c ht hb hne
  have hfix : D.reflection a z = z := by rw [reflectionFormula, hz, zero_smul, sub_zero]
  have hcz : 0 < D.value c z := by rw [← hfix, ht.1]; exact hother b hb hne
  rcases (hp c).lt_or_gt with hn | hh
  · have ho := (opposite_value_coroot D hR hD c).1
    have hop : D.positive p (D.opposite c) := by
      change 0 < D.value (D.opposite c) p
      rw [ho]
      exact neg_pos.mpr hn
    by_cases he : D.opposite c = a
    · have hnz := ho z
      rw [he, hz] at hnz
      linarith
    · have hh := hother _ hop he
      change 0 < D.value (D.opposite c) z at hh
      rw [ho] at hh
      linarith
  · exact hh


private def blend (x y : V) (t : K) : V := (1 - t) • x + t • y

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem value_blend (a : Wall ι) (x y : V) (t : K) :
    D.value a (blend x y t) = (1 - t) * D.value a x + t * D.value a y := by
  simp only [Datum.value, blend, map_add, map_smul, smul_eq_mul]
  ring

private theorem positive_lower_bound {J : Type*} (s : Finset J) (f : J → K)
    (hf : ∀ j ∈ s, 0 < f j) : ∃ d : K, 0 < d ∧ ∀ j ∈ s, d ≤ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert j s _ ih =>
    obtain ⟨d, hd, hds⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hj := hf j (Finset.mem_insert_self j s)
    refine ⟨min d (f j), lt_min hd hj, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hds i hi)

variable [Finite ι] [Archimedean K]

private theorem positive_gap (x : V) :
    ∃ δ : K, 0 < δ ∧ ∀ a, D.positive x a → δ ≤ D.value a x := by
  classical
  let : FloorRing K := Archimedean.floorRing K
  let : Fintype ι := Fintype.ofFinite ι
  let f (i : ι) : K := D.root i x + 1 - (⌈D.root i x⌉ : K)
  have hf (i : ι) : 0 < f i := sub_pos.mpr (Int.ceil_lt_add_one _)
  obtain ⟨δ, hδ, hle⟩ := positive_lower_bound Finset.univ f (fun i _ => hf i)
  refine ⟨δ, hδ, fun a ha => (hle a.1 (Finset.mem_univ _)).trans ?_⟩
  have ha' : 0 < D.root a.1 x + (a.2 : K) := ha
  have hceil := Int.le_ceil (D.root a.1 x)
  have hk : -⌈D.root a.1 x⌉ < a.2 := by
    by_contra! hn
    have hnk : (a.2 : K) ≤ ((-⌈D.root a.1 x⌉ : ℤ) : K) := by exact_mod_cast hn
    rw [Int.cast_neg] at hnk
    linarith
  have hkn : ((-⌈D.root a.1 x⌉ + 1 : ℤ) : K) ≤ (a.2 : K) := by
    exact_mod_cast (Int.add_one_le_iff.mpr hk)
  simp only [Int.cast_add, Int.cast_neg, Int.cast_one] at hkn
  change D.root a.1 x + 1 - (⌈D.root a.1 x⌉ : K) ≤ D.root a.1 x + (a.2 : K)
  linarith

private theorem blend_near (x y : V) :
    ∃ ε : K, 0 < ε ∧ ∀ t ∈ Ioo 0 ε, blend x y t ∈ D.alcove x := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨δ, hδ, hgap⟩ := positive_gap D x
  let f (i : ι) : K := δ / (|D.root i y - D.root i x| + 1)
  have hf (i : ι) : 0 < f i := div_pos hδ (by positivity)
  obtain ⟨ε, hε, hle⟩ := positive_lower_bound Finset.univ f (fun i _ => hf i)
  refine ⟨ε, hε, fun t ht a ha => ?_⟩
  have hdist := (lt_div_iff₀ (by positivity : 0 < |D.root a.1 y - D.root a.1 x| + 1)).mp
    (ht.2.trans_le (hle a.1 (Finset.mem_univ _)))
  have hbound := mul_le_mul_of_nonneg_left (neg_abs_le (D.root a.1 y - D.root a.1 x)) ht.1.le
  have hgap' := hgap a ha
  change 0 < D.value a (blend x y t)
  rw [value_blend]
  dsimp only [Datum.value] at hgap' ⊢
  nlinarith only [hdist, hbound, hgap', ht.1]

omit [IsStrictOrderedRing K] [Finite ι] [Archimedean K] in
private theorem alcove_trans {x y z : V} (hy : y ∈ D.alcove x) (hz : z ∈ D.alcove y) :
    z ∈ D.alcove x := fun a ha => hz a (hy a ha)

/-- Finitely many proper affine equations can be avoided in a small perturbation.
The perturbation stays in the prescribed affine slice and retains strict wall signs. -/
private theorem exists_avoid {J : Type*} (s : Finset J) (F : J → V → K)
    (hF : ∀ j x y t, F j (blend x y t) = (1 - t) * F j x + t * F j y)
    (S : Set V) (hS : ∀ x y, x ∈ S → y ∈ S → ∀ t : K, blend x y t ∈ S)
    (hproper : ∀ j ∈ s, ∃ y ∈ S, F j y ≠ 0) {z : V} (hz : z ∈ S) :
    ∃ x ∈ S, x ∈ D.alcove z ∧ ∀ j ∈ s, F j x ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨z, hz, fun _ => id, by simp⟩
  | @insert j s _ ih =>
    obtain ⟨x, hx, hzx, hold⟩ := ih (fun i hi => hproper i (Finset.mem_insert_of_mem hi))
    by_cases hj : F j x = 0
    · obtain ⟨y, hy, hny⟩ := hproper j (Finset.mem_insert_self _ _)
      obtain ⟨ε, hε, hnear⟩ := blend_near D x y
      have hbad (i : J) (hi : i ∈ insert j s) :
          {t : K | F i (blend x y t) = 0}.Subsingleton := by
        intro a ha b hb
        change F i (blend x y a) = 0 at ha
        change F i (blend x y b) = 0 at hb
        rw [hF] at ha hb
        by_contra hne
        have hprod : (a - b) * (F i y - F i x) = 0 := by linear_combination ha - hb
        have heq := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne))
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hny (heq.trans hj)
        · exact hold i hi (by linear_combination ha - a * heq)
      have hfin : (⋃ i ∈ (↑(insert j s) : Set J), {t : K | F i (blend x y t) = 0}).Finite :=
        (insert j s).finite_toSet.biUnion (fun i hi => (hbad i hi).finite)
      obtain ⟨t, ht, hn⟩ := (Set.Ioo_infinite hε).exists_notMem_finite hfin
      refine ⟨blend x y t, hS x y hx hy t, alcove_trans D hzx (hnear t ht), fun i hi hzero => hn ?_⟩
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hzero⟩
    · exact ⟨x, hx, hzx, fun i hi => by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hj
        · exact hold i hi⟩

omit [Finite ι] [Archimedean K] in
private theorem proportional_values (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    (a b : Wall ι) (c : K) (h : ∀ x, D.value b x = c * D.value a x) :
    b = a ∨ b = D.opposite a := by
  have h0 := h 0
  simp only [Datum.value, map_zero, zero_add] at h0
  have hr : D.root b.1 = c • D.root a.1 := by
    ext x
    have hx := h x
    simp only [Datum.value] at hx
    simp only [LinearMap.smul_apply, smul_eq_mul]
    linear_combination hx - h0
  rcases hD.2 a.1 b.1 c hr with he | hn
  · have hc : c = 1 := by
      have hh := congrFun (congrArg DFunLike.coe hr) (D.coroot a.1)
      rw [← he] at hh
      simp only [D.diagonal, LinearMap.smul_apply, smul_eq_mul] at hh
      linarith
    left
    apply value_injective D hD
    funext x
    rw [h, hc, one_mul]
  · have hc : c = -1 := by
      have hh := LinearMap.congr_fun (hn.symm.trans hr) (D.coroot a.1)
      simp only [D.diagonal, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul] at hh
      linarith
    right
    apply value_injective D hD
    funext x
    rw [h, hc, neg_one_mul, (opposite_value_coroot D hR hD a).1]

private theorem separators_finite (p q : V) : (D.separators p q).Finite := by
  let : FloorRing K := Archimedean.floorRing K
  apply Set.Finite.of_finite_fibers Prod.fst (Set.toFinite _)
  intro i _
  apply Set.Finite.of_injOn (t := Icc (-⌈D.root i p⌉) (-⌊D.root i q⌋)) (f := Prod.snd)
  · rintro ⟨j, k⟩ ⟨⟨hp, hq⟩, hj⟩
    change j ∈ ({i} : Set ι) at hj
    have hj' : j = i := Set.mem_singleton_iff.mp hj
    subst j
    change 0 < D.root i p + (k : K) at hp
    change D.root i q + (k : K) < 0 at hq
    have hcp := Int.le_ceil (D.root i p)
    have hfq := Int.floor_le (D.root i q)
    refine ⟨?_, ?_⟩
    · exact_mod_cast (show ((-⌈D.root i p⌉ : ℤ) : K) ≤ (k : K) by push_cast; linarith)
    · exact_mod_cast (show (k : K) ≤ ((-⌊D.root i q⌋ : ℤ) : K) by push_cast; linarith)
  · rintro ⟨j, k⟩ ⟨_, hj⟩ ⟨l, m⟩ ⟨_, hl⟩ hkm
    have hji : j = i := Set.mem_singleton_iff.mp hj
    have hli : l = i := Set.mem_singleton_iff.mp hl
    subst j
    subst l
    exact Prod.ext rfl hkm
  · exact Set.finite_Icc _ _

private theorem first_simple_separator (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    {p q : V} (hq : D.regular q) (hn : (D.separators p q).Nonempty) :
    ∃ a ∈ D.separators p q, D.IsSimple p a := by
  classical
  let s := (separators_finite D p q).toFinset
  have hs (a : Wall ι) : a ∈ s ↔ a ∈ D.separators p q := Set.Finite.mem_toFinset _
  let pairs := (s ×ˢ s).filter fun ab => ab.1 ≠ ab.2
  let F (ab : Wall ι × Wall ι) (x : V) :=
    D.value ab.1 p * D.value ab.2 x - D.value ab.2 p * D.value ab.1 x
  have hF (ab : Wall ι × Wall ι) (x y : V) (t : K) :
      F ab (blend x y t) = (1 - t) * F ab x + t * F ab y := by
    simp only [F, value_blend]
    ring
  have hproper (ab : Wall ι × Wall ι) (hab : ab ∈ pairs) :
      ∃ x ∈ (univ : Set V), F ab x ≠ 0 := by
    obtain ⟨hab, hne⟩ := Finset.mem_filter.mp hab
    have ha : 0 < D.value ab.1 p := ((hs _).mp (Finset.mem_product.mp hab).1).1
    have hb : 0 < D.value ab.2 p := ((hs _).mp (Finset.mem_product.mp hab).2).1
    by_contra! hn
    have he (x : V) : D.value ab.2 x = (D.value ab.2 p / D.value ab.1 p) * D.value ab.1 x := by
      have hz : F ab x = 0 := hn x (mem_univ _)
      dsimp [F] at hz
      rw [div_mul_eq_mul_div, eq_div_iff ha.ne']
      linear_combination hz
    rcases proportional_values D hR hD ab.1 ab.2 _ he with h | h
    · exact hne h.symm
    · rw [h, (opposite_value_coroot D hR hD _).1] at hb
      linarith
  obtain ⟨q', -, hqq', havoid⟩ :=
    exists_avoid D pairs F hF univ (fun _ _ _ _ _ => mem_univ _) hproper (mem_univ q)
  have hsign (a : Wall ι) := (alcove_iff D hR hD hq).mp hqq' a
  let t (a : Wall ι) := D.value a p / (D.value a p - D.value a q')
  have hends {a : Wall ι} (ha : a ∈ D.separators p q) :
      0 < D.value a p ∧ D.value a q' < 0 := ⟨ha.1, (hsign a).2.mpr ha.2⟩
  have hden {a : Wall ι} (ha : a ∈ D.separators p q) :
      0 < D.value a p - D.value a q' := sub_pos.mpr ((hends ha).2.trans (hends ha).1)
  have ht {a : Wall ι} (ha : a ∈ D.separators p q) : 0 < t a ∧ t a < 1 :=
    ⟨div_pos (hends ha).1 (hden ha),
      (div_lt_one (hden ha)).mpr (by linarith only [(hends ha).2])⟩
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image t (by simpa [s] using hn)
  have ha' := (hs a).mp ha
  have ht_eq {b : Wall ι} (hb : b ∈ D.separators p q) :
      t b * (D.value b p - D.value b q') = D.value b p :=
    div_mul_cancel₀ _ (hden hb).ne'
  refine ⟨a, ha', ha'.1, blend p q' (t a), ?_, ?_⟩
  · rw [value_blend]
    linear_combination -(ht_eq ha')
  · intro b hb hne
    change 0 < D.value b (blend p q' (t a))
    rw [value_blend]
    rcases (hq b).lt_or_gt with hbn | hbp
    · have hb' : b ∈ D.separators p q := ⟨hb, hbn⟩
      have hle := hmin b ((hs b).mpr hb')
      have hne' : t a ≠ t b := by
        intro he
        have he' := (div_eq_div_iff (hden ha').ne' (hden hb').ne').mp he
        apply havoid (a, b)
        · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, (hs b).mpr hb'⟩, Ne.symm hne⟩
        · dsimp [F]
          linear_combination -he'
      have hgap := mul_pos (sub_pos.mpr (lt_of_le_of_ne hle hne')) (hden hb')
      nlinarith only [hgap, ht_eq hb']
    · have h1 := mul_pos (sub_pos.mpr (ht ha').2) hb
      have h2 := mul_pos (ht ha').1 ((hsign b).1.mpr hbp)
      exact add_pos h1 h2


omit [Finite ι] [Archimedean K] in
private theorem separators_reflected (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    {p q : V} (hp : D.regular p) {a : Wall ι}
    (ha : D.IsSimple p a) (hsep : a ∈ D.separators p q) :
    (D.separators p (D.reflection a q)).ncard = (D.separators p q \ {a}).ncard := by
  obtain ⟨σ, hσ⟩ := reflection_mem_symmetries D hR hD a
  have hσopp : σ a = D.opposite a :=
    transports_unique D hD (hσ a) (reflection_transports_opposite D hR hD a)
  have himage : σ '' (D.separators p q \ {a}) = D.separators p (D.reflection a q) := by
    ext b
    constructor
    · rintro ⟨c, ⟨hc, hne⟩, rfl⟩
      exact ⟨(simpleWallSigns D hR hD p a hp ha).2 _ _ (hσ c) hc.1
        (Set.mem_singleton_iff.not.mp hne), by rw [(hσ c).1]; exact hc.2⟩
    · intro hb
      have hne : b ≠ a := by
        intro he
        have hh := hb.2
        change D.value b (D.reflection a q) < 0 at hh
        rw [he, value_reflection_self] at hh
        have hn := hsep.2
        linarith
      have hinv := (hσ (σ.symm b)).inv
      rw [σ.apply_symm_apply, reflection_inv] at hinv
      refine ⟨σ.symm b, ⟨⟨(simpleWallSigns D hR hD p a hp ha).2 _ _ hinv hb.1 hne, ?_⟩,
        ?_⟩, σ.apply_symm_apply b⟩
      · rw [← (hσ (σ.symm b)).1 q, σ.apply_symm_apply]
        exact hb.2
      · exact Set.mem_singleton_iff.not.mpr (by
          intro he
          have hh := congrArg σ he
          rw [σ.apply_symm_apply, hσopp] at hh
          have hbp := hb.1
          change 0 < D.value b p at hbp
          rw [hh, (opposite_value_coroot D hR hD a).1] at hbp
          have hpa : 0 < D.value a p := ha.1
          linarith)
  rw [← himage, Set.ncard_image_of_injective _ σ.injective]

omit [IsStrictOrderedRing K] [Finite ι] [Archimedean K] in
private theorem simple_group_le_ordinary (p : V) : D.simpleGroup p ≤ D.ordinary :=
  (Subgroup.closure_le _).mpr (fun _ ⟨a, _, ha⟩ => ha ▸ Subgroup.subset_closure ⟨a, rfl⟩)

private theorem move_into_alcove (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    {p q : V} (hp : D.regular p) (hq : D.regular q) :
    ∃ g ∈ D.simpleGroup p, g q ∈ D.alcove p := by
  generalize hn : (D.separators p q).ncard = n
  induction n using Nat.strong_induction_on generalizing q with
  | h n ih =>
    by_cases hem : (D.separators p q).Nonempty
    · obtain ⟨a, hsep, ha⟩ := first_simple_separator D hR hD hq hem
      have hrg : D.reflection a ∈ D.simpleGroup p := Subgroup.subset_closure ⟨a, ha, rfl⟩
      have hreg := symmetry_reg D _ (reflection_mem_symmetries D hR hD a) hq
      have hlt : (D.separators p (D.reflection a q)).ncard < n := by
        rw [separators_reflected D hR hD hp ha hsep, ← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem hsep (separators_finite D p q)
      obtain ⟨g, hg, hqg⟩ := ih _ hlt hreg rfl
      exact ⟨g * D.reflection a, (D.simpleGroup p).mul_mem hg hrg, hqg⟩
    · refine ⟨1, (D.simpleGroup p).one_mem, fun a ha => ?_⟩
      rcases (hq a).lt_or_gt with hneg | hpos
      · exact (hem ⟨a, ha, hneg⟩).elim
      · exact hpos

omit [Finite ι] [Archimedean K] in
private theorem zero_slice (a : Wall ι) (x : V) :
    D.value a (x - (D.value a x / 2) • D.coroot a.1) = 0 := by
  simp only [Datum.value, map_sub, map_smul, smul_eq_mul, D.diagonal]
  ring

omit [Finite ι] [Archimedean K] in
private theorem vanishing_on_wall (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    (a b : Wall ι) (h : ∀ x, D.value a x = 0 → D.value b x = 0) :
    b = a ∨ b = D.opposite a := by
  apply proportional_values D hR hD a b (D.root b.1 (D.coroot a.1) / 2)
  intro x
  have hz := h _ (zero_slice D a x)
  simp only [Datum.value, map_sub, map_smul, smul_eq_mul] at hz
  simp only [Datum.value]
  linear_combination hz

private theorem wall_point (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    (a : Wall ι) :
    ∃ z, D.value a z = 0 ∧ ∀ b, b ≠ a → b ≠ D.opposite a → D.value b z ≠ 0 := by
  classical
  let z : V := 0 - (D.value a 0 / 2) • D.coroot a.1
  have hz : D.value a z = 0 := zero_slice D a 0
  let S : Set V := {x | D.value a x = 0}
  let T : Set (Wall ι) := {b | D.value b z = 0 ∧ b ≠ a ∧ b ≠ D.opposite a}
  have hfin : T.Finite := by
    apply Set.Finite.of_injOn (t := (univ : Set ι)) (f := Prod.fst) (fun _ _ => mem_univ _) ?_ (Set.toFinite _)
    rintro ⟨i, m⟩ hi ⟨j, n⟩ hj he
    change i = j at he
    subst j
    have hm : D.root i z + (m : K) = 0 := hi.1
    have hn : D.root i z + (n : K) = 0 := hj.1
    exact Prod.ext rfl (by exact_mod_cast (show (m : K) = (n : K) by linarith))
  have hS (x y : V) (hx : x ∈ S) (hy : y ∈ S) (t : K) : blend x y t ∈ S := by
    change D.value a (blend x y t) = 0
    change D.value a x = 0 at hx
    change D.value a y = 0 at hy
    simp [value_blend, hx, hy]
  have hproper (b : Wall ι) (hb : b ∈ hfin.toFinset) :
      ∃ y ∈ S, D.value b y ≠ 0 := by
    by_contra! hn
    have hb' := hfin.mem_toFinset.mp hb
    exact (vanishing_on_wall D hR hD a b hn).elim hb'.2.1 hb'.2.2
  obtain ⟨x, hx, hxz, havoid⟩ :=
    exists_avoid D hfin.toFinset D.value (value_blend D) S hS hproper hz
  refine ⟨x, hx, fun b hba hbo => ?_⟩
  rcases lt_trichotomy (D.value b z) 0 with hneg | he | hpos
  · have ho := (opposite_value_coroot D hR hD b).1
    have hh : D.positive z (D.opposite b) := by
      change 0 < D.value (D.opposite b) z
      rw [ho]
      exact neg_pos.mpr hneg
    have hp : 0 < D.value (D.opposite b) x := hxz _ hh
    rw [ho] at hp
    exact (neg_pos.mp hp).ne
  · exact havoid b (hfin.mem_toFinset.mpr ⟨he, hba, hbo⟩)
  · exact (hxz b hpos).ne'

private theorem every_wall_is_simple (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    (a : Wall ι) : ∃ q, D.regular q ∧ D.IsSimple q a := by
  obtain ⟨z, hz, hother⟩ := wall_point D hR hD a
  obtain ⟨ε, hε, hnear⟩ := blend_near D z (z + D.coroot a.1)
  obtain ⟨t, ht0, htε⟩ := exists_between hε
  let q := blend z (z + D.coroot a.1) t
  have hqz : q ∈ D.alcove z := hnear t ⟨ht0, htε⟩
  have hq : 0 < D.value a q := by
    have hh : D.value a (z + D.coroot a.1) = 2 := by
      simp only [Datum.value, map_add, D.diagonal]
      have hz' : D.root a.1 z + (a.2 : K) = 0 := hz
      linarith
    change 0 < D.value a (blend z (z + D.coroot a.1) t)
    rw [value_blend, hz, hh, mul_zero, zero_add]
    positivity
  have hsign (b : Wall ι) (hn : D.value b z < 0) : D.value b q < 0 := by
    have ho := (opposite_value_coroot D hR hD b).1
    have hb : D.positive z (D.opposite b) := by
      change 0 < D.value (D.opposite b) z
      rw [ho]
      exact neg_pos.mpr hn
    have hh : 0 < D.value (D.opposite b) q := hqz _ hb
    rw [ho] at hh
    exact neg_pos.mp hh
  have hop : D.value (D.opposite a) q < 0 := by
    rw [(opposite_value_coroot D hR hD a).1]
    exact neg_lt_zero.mpr hq
  refine ⟨q, fun b => ?_, hq, z, hz, fun b hb hba => ?_⟩
  · by_cases he : b = a
    · exact he ▸ hq.ne'
    by_cases he' : b = D.opposite a
    · exact he' ▸ hop.ne
    rcases (hother b he he').lt_or_gt with hn | hp
    · exact (hsign b hn).ne
    · exact (hqz b hp).ne'
  · have hbo : b ≠ D.opposite a := by
      intro he
      change 0 < D.value b q at hb
      rw [he] at hb
      exact (not_lt_of_ge hop.le) hb
    rcases (hother b hba hbo).lt_or_gt with hn | hp
    · exact ((not_lt_of_ge (hsign b hn).le) hb).elim
    · exact hp

omit [Finite ι] [Archimedean K] in
private theorem transports_simple (g : V ≃ᵃ[K] V) (hg : g ∈ D.symmetries)
    {p : V} {a b : Wall ι} (ht : D.Transports g a b)
    (ha : D.IsSimple p a) (hD : D.ReducedDirections) : D.IsSimple (g p) b := by
  obtain ⟨σ, hσ⟩ := hg
  have he := transports_unique D hD (hσ a) ht
  subst b
  obtain ⟨hp, z, hz, hother⟩ := ha
  refine ⟨?_, g z, (hσ a).1 z |>.trans hz, ?_⟩
  · change 0 < D.value (σ a) (g p)
    rwa [(hσ a).1]
  · intro c hc hne
    obtain ⟨d, rfl⟩ := σ.surjective c
    change 0 < D.value (σ d) (g p) at hc
    change 0 < D.value (σ d) (g z)
    rw [(hσ d).1] at hc ⊢
    exact hother _ hc (fun h => hne (congrArg σ h))

omit [Finite ι] [Archimedean K] in
private theorem simple_of_mem_alcove (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    {p q : V} (hp : D.regular p) (hq : q ∈ D.alcove p) {a : Wall ι}
    (ha : D.IsSimple q a) : D.IsSimple p a := by
  have hs := (alcove_iff D hR hD hp).mp hq
  obtain ⟨ha, z, hz, hother⟩ := ha
  exact ⟨(hs a).1.mp ha, z, hz, fun b hb hne => hother b ((hs b).1.mpr hb) hne⟩

theorem generationAndTransitivity :
    Expected.GenerationAndTransitivity D := by
  intro hR hD p hp
  have hle := simple_group_le_ordinary D p
  refine ⟨le_antisymm hle ((Subgroup.closure_le _).mpr ?_), ?_⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨q, hq, haq⟩ := every_wall_is_simple D hR hD a
    obtain ⟨g, hg, hgp⟩ := move_into_alcove D hR hD hp hq
    have hsym := (groupPreservation D hR hD).1 (hle hg)
    obtain ⟨σ, hσ⟩ := hsym
    have hs := transports_simple D g ⟨σ, hσ⟩ (hσ a) haq hD
    have hsp := simple_of_mem_alcove D hR hD hp hgp hs
    have hgen : D.reflection (σ a) ∈ D.simpleGroup p := Subgroup.subset_closure ⟨_, hsp, rfl⟩
    have he : D.reflection a = g⁻¹ * D.reflection (σ a) * g := by
      rw [(hσ a).conjugates]
      group
    rw [he]
    exact (D.simpleGroup p).mul_mem ((D.simpleGroup p).mul_mem ((D.simpleGroup p).inv_mem hg) hgen) hg
  · intro q hq
    obtain ⟨g, hg, hgp⟩ := move_into_alcove D hR hD hp hq
    have hsym := (groupPreservation D hR hD).1 (hle hg)
    have hback : p ∈ D.alcove (g q) :=
      fun a ha => ((alcove_iff D hR hD hp).mp hgp a).1.mp ha
    have he := alcove_eq_of_mem D hgp hback
    refine ⟨g⁻¹, D.ordinary.inv_mem (hle hg), ?_⟩
    rw [he, symmetry_alcove D g⁻¹ (D.symmetries.inv_mem hsym)]
    change D.alcove (g.symm (g q)) = _
    rw [g.symm_apply_apply]

omit [Finite ι] in
theorem realComponents {n : ℕ} (D : Datum ℝ (Fin n → ℝ) ι) :
    Expected.RealComponents D := by
  intro hR hD p hp
  have hc : Convex ℝ (D.alcove p) := by
    intro x hx y hy a b ha hb hab w hw
    have hblend : a • x + b • y = blend x y b := by
      have he : a = 1 - b := by linarith
      rw [he]
      rfl
    change 0 < D.value w (a • x + b • y)
    rw [hblend, value_blend, ← show a = 1 - b by linarith]
    have hxp : 0 < D.value w x := hx w hw
    have hyp : 0 < D.value w y := hy w hw
    rcases ha.eq_or_lt with he | hpos
    · have hbe : b = 1 := by linarith
      simpa [← he, hbe] using hyp
    · exact add_pos_of_pos_of_nonneg (mul_pos hpos hxp) (mul_nonneg hb hyp.le)
  have hsub : D.alcove p ⊆ {x | D.regular x} :=
    fun _ hx => regular_of_mem_alcove D hR hD hp hx
  apply subset_antisymm _ (hc.isPreconnected.subset_connectedComponentIn (fun _ => id) hsub)
  intro x hx a ha
  have hcval : Continuous (D.value a) :=
    (D.root a.1).continuous_of_finiteDimensional.add continuous_const
  have hcon := isPreconnected_connectedComponentIn (F := {x | D.regular x}) (x := p)
  have him := (hcon.image (D.value a) hcval.continuousOn).ordConnected
  have hpm : D.value a p ∈ D.value a '' connectedComponentIn {x | D.regular x} p :=
    ⟨p, mem_connectedComponentIn hp, rfl⟩
  have hxm : D.value a x ∈ D.value a '' connectedComponentIn {x | D.regular x} p :=
    ⟨x, hx, rfl⟩
  change 0 < D.value a x
  by_contra! hn
  obtain ⟨y, hy, he⟩ := him.out hxm hpm ⟨hn, ha.le⟩
  exact (connectedComponentIn_subset _ _ hy a) he


theorem wallGeometry : Expected.WallGeometry D := by
  intro hR hD a
  refine ⟨fun b => ?_, every_wall_is_simple D hR hD a⟩
  constructor
  · intro he
    apply vanishing_on_wall D hR hD a b
    intro x hx
    have hm : x ∈ ({x | D.value a x = 0} : Set V) := hx
    rwa [he] at hm
  · rintro (rfl | rfl)
    · rfl
    · ext x
      change D.value a x = 0 ↔ D.value (D.opposite a) x = 0
      rw [(opposite_value_coroot D hR hD a).1, neg_eq_zero]

omit [Finite ι] [Archimedean K] in
theorem reflection_fixed_iff (a : Wall ι) (x : V) :
    D.reflection a x = x ↔ D.value a x = 0 := by
  rw [reflectionFormula, sub_eq_self]
  have hc : D.coroot a.1 ≠ 0 := by
    intro he
    have hh := D.diagonal a.1
    rw [he, map_zero] at hh
    exact two_ne_zero hh.symm
  simp [smul_eq_zero, hc]

omit [Finite ι] [Archimedean K] in
/-- Positive simple walls give distinct affine reflections. -/
theorem simple_reflection_injective (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    (p : V) : Function.Injective (fun a : {a // D.IsSimple p a} => D.reflection a.val) := by
  intro a b h
  change D.reflection a.val = D.reflection b.val at h
  apply Subtype.ext
  have he : ∀ x, D.value a.val x = 0 → D.value b.val x = 0 := by
    intro x hx
    rw [← reflection_fixed_iff, ← h, reflection_fixed_iff]
    exact hx
  rcases vanishing_on_wall D hR hD a.val b.val he with he | he
  · exact he.symm
  · have hbp : 0 < D.value b.val p := b.property.1
    rw [he, (opposite_value_coroot D hR hD a.val).1] at hbp
    exact ((neg_pos.mp hbp).not_gt a.property.1).elim

section Real

variable {n : ℕ} (E : Datum ℝ (Fin n → ℝ) ι)

omit [Finite ι] in
private theorem continuous_value (a : Wall ι) : Continuous (E.value a) :=
  (E.root a.1).continuous_of_finiteDimensional.add continuous_const

theorem isOpen_alcove (p : Fin n → ℝ) : IsOpen (E.alcove p) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨δ, hδ, hgap⟩ := positive_gap E x
  let U : Set (Fin n → ℝ) := ⋂ i : ι, {y | |E.root i y - E.root i x| < δ}
  have hU : IsOpen U := isOpen_iInter_of_finite (fun i =>
    isOpen_lt (((E.root i).continuous_of_finiteDimensional.sub continuous_const).abs)
      continuous_const)
  have hxU : x ∈ U := Set.mem_iInter.mpr (fun i => by simp [hδ])
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy a ha
  have hle := hgap a (hx a ha)
  have hr : |E.root a.1 y - E.root a.1 x| < δ := Set.mem_iInter.mp hy a.1
  change 0 < E.value a y
  dsimp only [Datum.value] at hle ⊢
  have hdist := (abs_lt.mp hr).1
  linarith

omit [Finite ι] in
theorem closure_alcove (p : Fin n → ℝ) :
    closure (E.alcove p) = {z | ∀ a, E.positive p a → 0 ≤ E.value a z} := by
  apply subset_antisymm
  · intro z hz a ha
    have hsub : E.alcove p ⊆ {x | 0 ≤ E.value a x} := fun _ hx => (hx a ha).le
    exact (closure_minimal hsub (isClosed_le continuous_const (continuous_value E a))) hz
  · intro z hz
    let f : ℝ → Fin n → ℝ := blend z p
    have hf : Continuous f := by
      change Continuous (fun t : ℝ => (1 - t) • z + t • p)
      fun_prop
    have h0 : f 0 = z := by simp [f, blend]
    have hc0 : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
      rw [closure_Ioc zero_ne_one]
      exact ⟨le_rfl, zero_le_one⟩
    rw [← h0]
    apply closure_mono _ (image_closure_subset_closure_image hf ⟨0, hc0, rfl⟩)
    rintro _ ⟨t, ht, rfl⟩ a ha
    change 0 < E.value a (blend z p t)
    rw [value_blend]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr ht.2) (hz a ha)) (mul_pos ht.1 ha)

theorem realBoundingWalls : Expected.RealBoundingWalls E := by
  intro hR hD p _ a
  constructor
  · rintro ⟨ha, z, hz, hrest⟩
    refine ⟨ha, E.alcove z, isOpen_alcove E z, ⟨z, (fun _ => id), hz⟩, ?_⟩
    rintro y ⟨hy, hyw⟩
    rw [closure_alcove]
    intro b hb
    by_cases he : b = a
    · subst b
      exact le_of_eq hyw.symm
    · exact (hy b (hrest b hb he)).le
  · rintro ⟨ha, U, hU, ⟨z, hzU, hz⟩, hsub⟩
    change E.value a z = 0 at hz
    refine ⟨ha, z, hz, fun b hb hne => ?_⟩
    have hzle : 0 ≤ E.value b z := by
      have h := hsub ⟨hzU, hz⟩
      rw [closure_alcove] at h
      exact h b hb
    change 0 < E.value b z
    by_contra! hn
    have hzero := le_antisymm hn hzle
    have hvan (y : Fin n → ℝ) (hy : E.value a y = 0) : E.value b y = 0 := by
      let f : ℝ → Fin n → ℝ := blend z y
      have hf : Continuous f := by
        change Continuous (fun t : ℝ => (1 - t) • z + t • y)
        fun_prop
      have h0 : f 0 ∈ U := by simpa [f, blend] using hzU
      obtain ⟨l, r, ⟨hl, hr⟩, hi⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp ((hU.preimage hf).mem_nhds h0)
      have hnon (t : ℝ) (ht : t ∈ Ioo l r) : 0 ≤ t * E.value b y := by
        have hwall : E.value a (f t) = 0 := by
          change E.value a (blend z y t) = 0
          simp [value_blend, hz, hy]
        have hh := hsub ⟨hi ht, hwall⟩
        rw [closure_alcove] at hh
        have h := hh b hb
        change 0 ≤ E.value b (blend z y t) at h
        simpa [value_blend, hzero] using h
      rcases lt_trichotomy (E.value b y) 0 with hn' | he | hp'
      · have hh := hnon (r / 2) ⟨by linarith, by linarith⟩
        exact ((mul_neg_of_pos_of_neg (by linarith) hn').not_ge hh).elim
      · exact he
      · have hh := hnon (l / 2) ⟨by linarith, by linarith⟩
        exact ((mul_neg_of_neg_of_pos (by linarith) hp').not_ge hh).elim
    rcases vanishing_on_wall E hR hD a b hvan with he | he
    · exact hne he
    · have hb' : 0 < E.value b p := hb
      rw [he, (opposite_value_coroot E hR hD a).1] at hb'
      exact (neg_pos.mp hb').not_gt ha

end Real

end LinearAlgebraicGroups.Arithmetic.AffineArrangement
