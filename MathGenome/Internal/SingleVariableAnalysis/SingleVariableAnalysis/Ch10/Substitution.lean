import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Substitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.MonotoneSubstitution
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch10.OneEndpoint

namespace SingleVariableAnalysis.Riemann.Improper.Substitution
open Specs.SingleVariableAnalysis.Ch10.Substitution
open Set

namespace Ray

theorem le_refl (r : Ray) (x : ℝ) : r.le x x := by cases r <;> exact le_rfl

theorem le_total (r : Ray) (x y : ℝ) : r.le x y ∨ r.le y x := by
  cases r <;> exact _root_.le_total _ _

theorem lt_of_not_le (r : Ray) {x y : ℝ} (h : ¬ r.le y x) : r.lt x y := by
  cases r <;> exact _root_.lt_of_not_ge h

theorem lt_of_lt_of_le (r : Ray) {x y z : ℝ} (h : r.lt x y) (h' : r.le y z) : r.lt x z := by
  cases r with
  | right => exact h.trans_le h'
  | left => exact h'.trans_lt h

theorem not_le_of_lt (r : Ray) {x y : ℝ} (h : r.lt x y) : ¬ r.le y x := by
  cases r <;> exact _root_.not_le_of_gt h

theorem index_mem (r : Ray) (t : r.Index) : r.point t ∈ r.domain := by
  cases r with
  | right => exact ⟨t.property.1.le, t.property.2⟩
  | left => exact ⟨t.property.1, t.property.2.le⟩

theorem base_lt (r : Ray) (t : r.Index) : r.lt r.base (r.point t) := by
  cases r with
  | right => exact t.property.1
  | left => exact t.property.2

theorem mem_index (r : Ray) {x : ℝ} (hx : x ∈ r.domain) (h : r.lt r.base x) :
    ∃ t : r.Index, r.point t = x := by
  cases r with
  | right => exact ⟨⟨x, h, hx.2⟩, rfl⟩
  | left => exact ⟨⟨x, hx.1, h⟩, rfl⟩

theorem base_le (r : Ray) {x : ℝ} (hx : x ∈ r.domain) : r.le r.base x := by
  cases r with
  | right => exact hx.1
  | left => exact hx.2

theorem eq_base_or_index (r : Ray) {x : ℝ} (hx : x ∈ r.domain) :
    x = r.base ∨ ∃ t : r.Index, r.point t = x := by
  cases r with
  | right a b =>
    rcases hx.1.eq_or_lt with he | hl
    · exact Or.inl he.symm
    · exact Or.inr ⟨⟨x, hl, hx.2⟩, rfl⟩
  | left a b =>
    rcases hx.2.eq_or_lt with he | hl
    · exact Or.inl he
    · exact Or.inr ⟨⟨x, hx.1, hl⟩, rfl⟩

theorem later (r : Ray) (t u : r.Index) :
    ∃ v : r.Index, r.lt (r.point t) (r.point v) ∧ r.lt (r.point u) (r.point v) := by
  cases r with
  | right => exact right_later t u
  | left => exact left_earlier t u

theorem regular_nonempty (r : Ray) {k : ScalarKind} {f : ℝ → ScalarValue k}
    (hf : r.Regular k f) : Nonempty r.Index := by
  cases r with
  | right a b =>
    cases b using WithTop.recTopCoe with
    | top => exact ⟨⟨a+1, lt_add_one _, WithTop.coe_lt_top _⟩⟩
    | coe b =>
      obtain ⟨t, hat, htb⟩ := exists_between (WithTop.coe_lt_coe.mp hf.1)
      exact ⟨⟨t, hat, WithTop.coe_lt_coe.mpr htb⟩⟩
  | left a b =>
    cases a using WithBot.recBotCoe with
    | bot => exact ⟨⟨b-1, WithBot.bot_lt_coe _, sub_one_lt _⟩⟩
    | coe a =>
      obtain ⟨t, hat, htb⟩ := exists_between (WithBot.coe_lt_coe.mp hf.1)
      exact ⟨⟨t, WithBot.coe_lt_coe.mpr hat, htb⟩⟩

theorem hasIntegral_iff (r : Ray) (k : ScalarKind) (f : ℝ → ScalarValue k) (L : ScalarValue k) :
    r.HasIntegral k f L ↔ ∃ h : r.Regular k f,
      ∀ ε > 0, ∃ u : r.Index, ∀ t : r.Index,
        r.lt (r.point u) (r.point t) → dist (r.truncation k f h t) L < ε := by
  cases r with
  | right => rfl
  | left =>
    have hd (x y : ScalarValue k) : dist (-x) y = dist x (-y) := by
      simpa only [neg_neg] using (dist_neg_neg x (-y))
    simp only [Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.HasIntegral,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.Regular,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.truncation,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.lt,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      Specs.SingleVariableAnalysis.Ch10.OneEndpoint.leftHasIntegralValue, hd]
    rfl

end Ray

namespace Ray

theorem base_mem (r : Ray) (h : Nonempty r.Index) : r.base ∈ r.domain := by
  obtain ⟨t⟩ := h
  cases r with
  | right => exact ⟨le_rfl, (WithTop.coe_lt_coe.mpr t.property.1).trans t.property.2⟩
  | left => exact ⟨t.property.1.trans (WithBot.coe_lt_coe.mpr t.property.2), le_rfl⟩

theorem later_mem (r : Ray) (h : Nonempty r.Index) {y : ℝ} (hy : y ∈ r.domain) :
    ∃ t : r.Index, r.lt y (r.point t) := by
  rcases eq_base_or_index r hy with he | ⟨t, rfl⟩
  · obtain ⟨t⟩ := h
    exact ⟨t, he ▸ base_lt r t⟩
  · obtain ⟨u, htu, _⟩ := later r t t
    exact ⟨u, htu⟩

theorem domain_hull (r : Ray) (t : r.Index) :
    Icc (min r.base (r.point t)) (max r.base (r.point t)) ⊆ r.domain := by
  cases r with
  | right a b =>
    intro x hx
    have ht := t.property
    simp only [Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      min_eq_left ht.1.le, max_eq_right ht.1.le, mem_Icc] at hx
    exact ⟨hx.1, (WithTop.coe_le_coe.mpr hx.2).trans_lt ht.2⟩
  | left a b =>
    intro x hx
    have ht := t.property
    simp only [Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      min_eq_right ht.2.le, max_eq_left ht.2.le, mem_Icc] at hx
    exact ⟨ht.1.trans_le (WithBot.coe_le_coe.mpr hx.1), hx.2⟩

theorem regular_oriented (r : Ray) (k : ScalarKind) (f : ℝ → ScalarValue k)
    (hf : r.Regular k f) {x : ℝ} (hx : x ∈ r.domain) :
    orientedIntegrable k f r.base x := by
  rcases eq_base_or_index r hx with rfl | ⟨t, rfl⟩
  · simpa only [orientedIntegrable, min_self, max_self] using integrable_degenerate k f r.base
  · cases r with
    | right a b =>
      simpa only [orientedIntegrable, Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
        Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
        min_eq_left t.property.1.le, max_eq_right t.property.1.le] using hf.2 t
    | left a b =>
      simpa only [orientedIntegrable, Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
        Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
        min_eq_right t.property.2.le, max_eq_left t.property.2.le] using hf.2 t

theorem truncation_eq_oriented (r : Ray) (k : ScalarKind) (f : ℝ → ScalarValue k)
    (hf : r.Regular k f) (t : r.Index)
    (ht : orientedIntegrable k f r.base (r.point t)) :
    r.truncation k f hf t = orientedIntegral k f ht := by
  cases r with
  | right a b =>
    change _ = if a ≤ t.val then _ else _
    rw [ite_eq_left t.property.1.le]
    simp only [Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      min_eq_left t.property.1.le, max_eq_right t.property.1.le]
    rfl
  | left a b =>
    change _ = if b ≤ t.val then _ else _
    rw [ite_eq_right (not_le.mpr t.property.2)]
    simp only [Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      min_eq_right t.property.2.le, max_eq_left t.property.2.le]
    rfl

theorem regular_of_oriented (r : Ray) (k : ScalarKind) (f : ℝ → ScalarValue k)
    (hne : Nonempty r.Index)
    (h : ∀ t : r.Index, orientedIntegrable k f r.base (r.point t)) : r.Regular k f := by
  obtain ⟨u⟩ := hne
  cases r with
  | right a b =>
    refine ⟨(WithTop.coe_lt_coe.mpr u.property.1).trans u.property.2, fun t => ?_⟩
    simpa only [orientedIntegrable, Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      min_eq_left t.property.1.le, max_eq_right t.property.1.le] using h t
  | left a b =>
    refine ⟨u.property.1.trans (WithBot.coe_lt_coe.mpr u.property.2), fun t => ?_⟩
    simpa only [orientedIntegrable, Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      min_eq_right t.property.2.le, max_eq_left t.property.2.le] using h t


theorem base_mem_of_mem (r : Ray) {x : ℝ} (hx : x ∈ r.domain) : r.base ∈ r.domain := by
  cases r with
  | right => exact ⟨le_rfl, (WithTop.coe_le_coe.mpr hx.1).trans_lt hx.2⟩
  | left => exact ⟨hx.1.trans_le (WithBot.coe_le_coe.mpr hx.2), le_rfl⟩

end Ray

namespace Parameterization

/-- Maps into the indicated half-open interval force the compatible directed
order. A monotone map with the other direction would be constant at the base. -/
theorem directed_monotone {s r : Ray} {φ dφ : ℝ → ℝ}
    (hp : Parameterization s r φ dφ) {x y : ℝ}
    (hx : x ∈ s.domain) (hy : y ∈ s.domain) (hxy : s.le x y) :
    r.le (φ x) (φ y) := by
  have hb := Ray.base_mem_of_mem s hx
  have hbx := Ray.base_le s hx
  have he := hp.base_eq
  have transport (z : ℝ) (h : φ s.base ≤ z) : r.base ≤ z := he ▸ h
  have hfy := hp.maps hy
  rcases hp.monotone with hm | hm
  · cases s <;> cases r
    · exact hm hx hy hxy
    · exact hfy.2.trans (transport _ (hm hb hx hbx))
    · exact (hm hx hb hbx).trans (he.symm ▸ hfy.1)
    · exact hm hy hx hxy
  · cases s <;> cases r
    · exact (hm hb hx hbx).trans (he.symm ▸ hfy.1)
    · exact hm hx hy hxy
    · exact hm hy hx hxy
    · exact hfy.2.trans (transport _ (hm hx hb hbx))

theorem preimage_index {s r : Ray} {φ dφ : ℝ → ℝ} (hp : Parameterization s r φ dφ)
    (y : r.Index) : ∃ t : s.Index, φ (s.point t) = r.point y := by
  obtain ⟨x, hx, he⟩ := hp.onto (Ray.index_mem r y)
  rcases Ray.eq_base_or_index s hx with hbase | ⟨t, rfl⟩
  · have hbad : r.point y = r.base := he.symm.trans ((congrArg φ hbase).trans hp.base_eq)
    have hh := Ray.base_lt r y
    rw [hbad] at hh
    cases r <;> exact False.elim (lt_irrefl _ hh)
  · exact ⟨t, he⟩

theorem source_nonempty {s r : Ray} {φ dφ : ℝ → ℝ} (hp : Parameterization s r φ dφ)
    (h : Nonempty r.Index) : Nonempty s.Index := by
  obtain ⟨y⟩ := h
  obtain ⟨t, _⟩ := Parameterization.preimage_index hp y
  exact ⟨t⟩

theorem image_later {s r : Ray} {φ dφ : ℝ → ℝ} (hp : Parameterization s r φ dφ)
    (h : Nonempty r.Index) {y : ℝ} (hy : y ∈ r.domain) :
    ∃ T : s.Index, ∀ t : s.Index,
      s.lt (s.point T) (s.point t) → r.lt y (φ (s.point t)) := by
  obtain ⟨z, hyz⟩ := Ray.later_mem r h hy
  obtain ⟨T, hT⟩ := Parameterization.preimage_index hp z
  refine ⟨T, fun t ht => Ray.lt_of_lt_of_le r hyz ?_⟩
  rw [← hT]
  apply Parameterization.directed_monotone hp (Ray.index_mem s T) (Ray.index_mem s t)
  cases s <;> exact ht.le

theorem preimage_later {s r : Ray} {φ dφ : ℝ → ℝ} (hp : Parameterization s r φ dφ)
    (T t : s.Index) (h : r.lt (φ (s.point T)) (φ (s.point t))) :
    s.lt (s.point T) (s.point t) := by
  apply Ray.lt_of_not_le s
  intro hle
  exact Ray.not_le_of_lt r h
    (Parameterization.directed_monotone hp (Ray.index_mem s t) (Ray.index_mem s T) hle)

theorem monotone_hull {s r : Ray} {φ dφ : ℝ → ℝ} (hp : Parameterization s r φ dφ)
    (t : s.Index) :
    MonotoneOn φ (Icc (min s.base (s.point t)) (max s.base (s.point t))) ∨
      AntitoneOn φ (Icc (min s.base (s.point t)) (max s.base (s.point t))) := by
  rcases hp.monotone with hm | hm
  · exact Or.inl (hm.mono (Ray.domain_hull s t))
  · exact Or.inr (hm.mono (Ray.domain_hull s t))

end Parameterization

theorem parameterization_cofinal : parameterizationCofinal := by
  intro s r φ dφ hp hne y hy
  exact Parameterization.image_later hp hne hy

/-- The compact substitution theorem, bundled over exactly the two scalars. -/
theorem proper_substitution (k : ScalarKind) (φ dφ : ℝ → ℝ)
    (f : ℝ → ScalarValue k) {a b : ℝ} (hab : a ≤ b)
    (hc : C1OnInterval φ dφ a b)
    (hm : MonotoneOn φ (Icc a b) ∨ AntitoneOn φ (Icc a b))
    (hf : orientedIntegrable k f (φ a) (φ b)) :
    ∃ hg : Specs.SingleVariableAnalysis.Ch08.Integral.scalarIntegrableValue k
      (transform k f φ dφ) a b,
      Specs.SingleVariableAnalysis.Ch08.Integral.scalarIntegralValue k _ hg =
        orientedIntegral k f hf := by
  cases k with
  | real => exact real_monotone_substitution φ dφ f hab hc hm hf
  | complex => exact complex_monotone_substitution φ dφ f hab hc hm hf

/-- Sorting the endpoints changes only the sign of the oriented value. -/
theorem oriented_symmetry (k : ScalarKind) (f : ℝ → ScalarValue k) {a b : ℝ}
    (h : orientedIntegrable k f a b) (hr : orientedIntegrable k f b a) :
    orientedIntegral k f h = -orientedIntegral k f hr := by
  cases k with
  | real => exact oriented_real_symmetry f a b h hr
  | complex => exact oriented_complex_symmetry f a b h hr

/-- Proper substitution on an arbitrarily directed compact truncation. -/
theorem proper_directed {s r : Ray} (k : ScalarKind) (f : ℝ → ScalarValue k)
    {φ dφ : ℝ → ℝ} (hp : Parameterization s r φ dφ) (hf : r.Regular k f)
    (t : s.Index) :
    ∃ (hg : orientedIntegrable k (transform k f φ dφ) s.base (s.point t))
      (hft : orientedIntegrable k f r.base (φ (s.point t))),
      orientedIntegral k (transform k f φ dφ) hg = orientedIntegral k f hft := by
  have hft := Ray.regular_oriented r k f hf (hp.maps (Ray.index_mem s t))
  have hc := hp.c1 t
  have hm := Parameterization.monotone_hull hp t
  cases s with
  | right a b =>
    have ht := t.property.1.le
    have hb : φ a = r.base := hp.base_eq
    simp only [Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      min_eq_left ht, max_eq_right ht] at hc hm
    have hf' : orientedIntegrable k f (φ a) (φ t.val) := by rw [hb]; exact hft
    obtain ⟨hg, he⟩ := proper_substitution k φ dφ f ht hc hm hf'
    have hg' : orientedIntegrable k (transform k f φ dφ) a t.val := by
      simpa only [orientedIntegrable, min_eq_left ht, max_eq_right ht] using hg
    refine ⟨hg', hft, ?_⟩
    change orientedIntegral k _ hg' = _
    rw [orientedIntegral, ite_eq_left ht]
    simpa only [Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      min_eq_left ht, max_eq_right ht, hb] using he
  | left a b =>
    have ht := t.property.2.le
    have hb : φ b = r.base := hp.base_eq
    simp only [Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
      min_eq_right ht, max_eq_left ht] at hc hm
    have hf' : orientedIntegrable k f (φ t.val) (φ b) := by
      rw [hb]
      simpa only [orientedIntegrable, Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point,
        min_comm, max_comm] using hft
    obtain ⟨hg, he⟩ := proper_substitution k φ dφ f ht hc hm hf'
    have hg' : orientedIntegrable k (transform k f φ dφ) b t.val := by
      simpa only [orientedIntegrable, min_eq_right ht, max_eq_left ht] using hg
    refine ⟨hg', hft, ?_⟩
    change orientedIntegral k _ hg' = _
    rw [orientedIntegral, ite_eq_right (not_le.mpr t.property.2)]
    simp only [min_eq_right ht, max_eq_left ht]
    rw [he]
    have hf'' : orientedIntegrable k f (φ b) (φ t.val) := by rw [hb]; exact hft
    have hs := oriented_symmetry k f hf'' hf'
    simpa only [Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.base,
      Specs.SingleVariableAnalysis.Ch10.Substitution.Ray.point, hb] using hs.symm


theorem substitution_regular : substitutionRegular := by
  intro s r k f φ dφ hp hf
  apply Ray.regular_of_oriented s k (transform k f φ dφ)
    (Parameterization.source_nonempty hp (Ray.regular_nonempty r hf))
  intro t
  exact (proper_directed k f hp hf t).choose

theorem substitution_truncation : substitutionTruncation := by
  intro s r k f φ dφ hp hf hg t
  obtain ⟨hg', hft, he⟩ := proper_directed k f hp hf t
  exact ⟨hft, (Ray.truncation_eq_oriented s k _ hg t hg').trans he⟩

/-- The truncation identity when the image is strictly past the target base. -/
theorem truncation_image {s r : Ray} (k : ScalarKind) (f : ℝ → ScalarValue k)
    {φ dφ : ℝ → ℝ} (hp : Parameterization s r φ dφ) (hf : r.Regular k f)
    (hg : s.Regular k (transform k f φ dφ)) (t : s.Index) (y : r.Index)
    (himage : φ (s.point t) = r.point y) :
    s.truncation k (transform k f φ dφ) hg t = r.truncation k f hf y := by
  obtain ⟨hft, he⟩ := substitution_truncation s r k f φ dφ hp hf hg t
  rw [Ray.truncation_eq_oriented r k f hf y (Ray.regular_oriented r k f hf (Ray.index_mem r y))]
  simpa only [himage] using he

namespace Ray

theorem lt_trans (r : Ray) {x y z : ℝ} (h : r.lt x y) (h' : r.lt y z) : r.lt x z := by
  cases r with
  | right => exact h.trans h'
  | left => exact h'.trans h

/-- Uniqueness is inherited from the already proved one-endpoint limits. -/
theorem hasIntegral_unique (r : Ray) (k : ScalarKind) (f : ℝ → ScalarValue k)
    (L M : ScalarValue k) (hL : r.HasIntegral k f L) (hM : r.HasIntegral k f M) : L = M := by
  cases r with
  | right a b => exact right_unique k f a b L M hL hM
  | left a b => exact neg_injective (left_unique k f a b (-L) (-M) hL hM)

end Ray

/-- Cofinality transfers the forward limit; onto and monotonicity transfer
all target truncations back, without choosing a differentiable inverse. -/
theorem substitution_hasIntegral : substitutionHasIntegral := by
  intro s r k f φ dφ hp hf L
  have hg := substitution_regular s r k f φ dφ hp hf
  have hne := Ray.regular_nonempty r hf
  rw [Ray.hasIntegral_iff, Ray.hasIntegral_iff]
  constructor
  · rintro ⟨hf', hL⟩
    refine ⟨hg, fun ε hε => ?_⟩
    obtain ⟨u, hu⟩ := hL ε hε
    obtain ⟨T, hT⟩ := Parameterization.image_later hp hne (Ray.index_mem r u)
    refine ⟨T, fun t ht => ?_⟩
    have hlate := hT t ht
    obtain ⟨y, hy⟩ := Ray.mem_index r (hp.maps (Ray.index_mem s t))
      (Ray.lt_trans r (Ray.base_lt r u) hlate)
    rw [truncation_image k f hp hf hg t y hy.symm]
    apply hu y
    simpa only [hy] using hlate
  · rintro ⟨hg', hL⟩
    refine ⟨hf, fun ε hε => ?_⟩
    obtain ⟨T, hT⟩ := hL ε hε
    obtain ⟨u, hu⟩ := Ray.later_mem r hne (hp.maps (Ray.index_mem s T))
    refine ⟨u, fun y hy => ?_⟩
    obtain ⟨t, ht⟩ := Parameterization.preimage_index hp y
    have hlate : r.lt (φ (s.point T)) (φ (s.point t)) := by
      rw [ht]
      exact Ray.lt_trans r hu hy
    have hclose := hT t (Parameterization.preimage_later hp T t hlate)
    rw [truncation_image k f hp hf hg' t y ht] at hclose
    exact hclose

theorem substitution_converges : substitutionConverges := by
  intro s r k f φ dφ hp hf
  exact exists_congr (fun L => substitution_hasIntegral s r k f φ dφ hp hf L)

theorem substitution_integral : substitutionIntegral := by
  intro s r k f φ dφ hp hf hr hs
  apply Ray.hasIntegral_unique s k (transform k f φ dφ)
  · exact (substitution_hasIntegral s r k f φ dφ hp hf _).mp (Classical.choose_spec hr)
  · exact Classical.choose_spec hs

theorem substitution_reverse : substitutionReverse := by
  intro s r k f φ dφ hp hf L
  exact substitution_hasIntegral s r k f φ dφ hp hf (-L)

end SingleVariableAnalysis.Riemann.Improper.Substitution
