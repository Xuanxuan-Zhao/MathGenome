import Specs.LinearAlgebraicGroups.Arithmetic.SpinOrthogonalWords
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

namespace LinearAlgebraicGroups.Arithmetic.SpinOrthogonalWords

open LinearAlgebraicGroups.Specs.Arithmetic.SpinOrthogonalWords
open LinearMap

universe u v

variable {F : Type u} [Field F] {V : Type v} [AddCommGroup V] [Module F V]

private theorem polar_swap (q : QuadraticForm F V) (x y : V) :
    q.polarBilin x y = q.polarBilin y x :=
  QuadraticMap.polar_comm q x y

private theorem polar_diag (q : QuadraticForm F V) (x : V) :
    q.polarBilin x x = 2 * q x := by
  simpa only [QuadraticMap.polarBilin_apply_apply, two_smul, two_mul] using
    QuadraticMap.polar_self q x

private theorem norm_add (q : QuadraticForm F V) (x y : V) :
    q (x + y) = q x + q y + q.polarBilin x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

private theorem norm_sub (q : QuadraticForm F V) (x y : V) :
    q (x - y) = q x + q y - q.polarBilin x y := by
  rw [sub_eq_add_neg, norm_add, q.map_neg, map_neg, sub_eq_add_neg]

private theorem polar_preserve (q : QuadraticForm F V) (g : V →ₗ[F] V)
    (hg : ∀ x, q (g x) = q x) (x y : V) :
    q.polarBilin (g x) (g y) = q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hg]

private def reflect (q : QuadraticForm F V) (w : V) : V →ₗ[F] V :=
  LinearMap.id - ((q w)⁻¹ • q.polarBilin w).smulRight w

private theorem reflect_apply (q : QuadraticForm F V) (w x : V) :
    reflect q w x = x - (q.polarBilin w x / q w) • w := by
  simp [reflect, div_eq_inv_mul]

private theorem reflect_norm (q : QuadraticForm F V) {w : V} (hw : q w ≠ 0) (x : V) :
    q (reflect q w x) = q x := by
  rw [reflect_apply, norm_sub, q.map_smul, map_smul, polar_swap q x w]
  simp only [smul_eq_mul]
  field_simp
  ring

private theorem reflect_involutive (q : QuadraticForm F V) {w : V} (hw : q w ≠ 0) (x : V) :
    reflect q w (reflect q w x) = x := by
  let b := q.polarBilin w x
  have h : (b - (b / q w) * (2 * q w)) / q w = -(b / q w) := by
    field_simp
    ring
  rw [reflect_apply q w (reflect q w x), reflect_apply q w x]
  simp only [map_sub, map_smul, polar_diag, smul_eq_mul]
  change x - (b / q w) • w - ((b - (b / q w) * (2 * q w)) / q w) • w = x
  rw [h, neg_smul, sub_neg_eq_add, sub_add_cancel]

private theorem reflect_fixed (q : QuadraticForm F V) {w x : V}
    (h : q.polarBilin w x = 0) : reflect q w x = x := by
  simp [reflect_apply, h]

private theorem reflect_difference (q : QuadraticForm F V) {a b : V}
    (hab : q a = q b) (hn : q (a - b) ≠ 0) :
    reflect q (a - b) a = b := by
  have hB : q.polarBilin (a - b) a = q (a - b) := by
    rw [map_sub, LinearMap.sub_apply, polar_diag, polar_swap q b a, norm_sub, hab]
    ring
  rw [reflect_apply, hB, div_self hn, one_smul, sub_sub_cancel]

private def word (q : QuadraticForm F V) (l : List V) : V →ₗ[F] V :=
  l.foldr (fun w g => (reflect q w).comp g) LinearMap.id

private theorem word_apply (q : QuadraticForm F V) (l : List V) (x : V) :
    word q l x = l.foldr (fun w z => z - (q.polarBilin w z / q w) • w) x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change reflect q w (word q l x) = _
    rw [reflect_apply, ih]
    rfl

private theorem word_append (q : QuadraticForm F V) (l m : List V) (x : V) :
    word q (l ++ m) x = word q l (word q m x) := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change reflect q w (word q (l ++ m) x) = reflect q w (word q l (word q m x))
    rw [ih]

private theorem word_norm (q : QuadraticForm F V) (l : List V)
    (hl : ∀ w ∈ l, q w ≠ 0) (x : V) : q (word q l x) = q x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change q (reflect q w (word q l x)) = _
    rw [reflect_norm q (hl w (by simp))]
    exact ih (fun z hz => hl z (List.mem_cons_of_mem _ hz))

private theorem word_reverse (q : QuadraticForm F V) (l : List V)
    (hl : ∀ w ∈ l, q w ≠ 0) (x : V) : word q l.reverse (word q l x) = x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    rw [List.reverse_cons, word_append]
    change word q l.reverse (reflect q w (reflect q w (word q l x))) = _
    rw [reflect_involutive q (hl w (by simp))]
    exact ih (fun z hz => hl z (List.mem_cons_of_mem _ hz))

private theorem word_fixed (q : QuadraticForm F V) (l : List V) {x : V}
    (h : ∀ w ∈ l, q.polarBilin w x = 0) : word q l x = x := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change reflect q w (word q l x) = x
    rw [ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    exact reflect_fixed q (h w (by simp))

/-- On an affine line through a vector of nonzero norm, avoid the roots of the
norm polynomial and the two pairing polynomials. -/
private theorem exists_norm_and_pairings [Infinite F] (q : QuadraticForm F V)
    (f g : V →ₗ[F] F) (hq : ∃ z, q z ≠ 0)
    (hf : ∃ z, f z ≠ 0) (hg : ∃ z, g z ≠ 0) :
    ∃ z, q z ≠ 0 ∧ f z ≠ 0 ∧ g z ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := hq
  obtain ⟨b, hb⟩ := hf
  obtain ⟨c, hc⟩ := hg
  obtain ⟨d, hd, hd'⟩ : ∃ d, f d ≠ 0 ∧ g d ≠ 0 := by
    by_cases hgb : g b = 0
    · by_cases hfc : f c = 0
      · exact ⟨b + c, by simpa [hfc] using hb, by simpa [hgb] using hc⟩
      · exact ⟨c, hfc, hc⟩
    · exact ⟨b, hb, hgb⟩
  let p := Polynomial.C (q a) + Polynomial.C (q.polarBilin a d) * Polynomial.X +
    Polynomial.C (q d) * Polynomial.X ^ 2
  let s := Polynomial.C (f a) + Polynomial.C (f d) * Polynomial.X
  let t := Polynomial.C (g a) + Polynomial.C (g d) * Polynomial.X
  have hp : p ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    exact ha (by simpa [p] using this)
  have hs : s ≠ 0 := by
    intro h
    have := congrArg (fun P : Polynomial F => P.coeff 1) h
    exact hd (by simpa [s, Polynomial.coeff_C_mul_X] using this)
  have ht : t ≠ 0 := by
    intro h
    have := congrArg (fun P : Polynomial F => P.coeff 1) h
    exact hd' (by simpa [t, Polynomial.coeff_C_mul_X] using this)
  obtain ⟨k, hk⟩ : ∃ k : F, (p * s * t).eval k ≠ 0 := by
    by_contra! h
    exact (mul_ne_zero (mul_ne_zero hp hs) ht) (Polynomial.zero_of_eval_zero _ h)
  refine ⟨a + k • d, ?_, ?_, ?_⟩
  · have he : p.eval k = q (a + k • d) := by
      simp [p, norm_add, q.map_smul, pow_two]
      ring
    exact fun h => hk (by simp [he, h])
  · have he : s.eval k = f (a + k • d) := by
      simp only [s, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, map_add, map_smul, smul_eq_mul]
      ring
    exact fun h => hk (by simp [he, h])
  · have he : t.eval k = g (a + k • d) := by
      simp only [t, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, map_add, map_smul, smul_eq_mul]
      ring
    exact fun h => hk (by simp [he, h])

private theorem nonradical_pairing (q : QuadraticForm F V)
    (h : q.polarBilin ≠ 0) : ∃ u v : V, q.polarBilin u v ≠ 0 := by
  by_contra! hzero
  exact h (LinearMap.ext fun u => LinearMap.ext fun v => hzero u v)

private theorem norm_exists (q : QuadraticForm F V) (h : q.polarBilin ≠ 0) :
    ∃ z, q z ≠ 0 := by
  by_contra! hzero
  obtain ⟨u, v, huv⟩ := nonradical_pairing q h
  exact huv (by simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hzero])

private theorem align_line (q : QuadraticForm F V) (h₂ : (2 : F) ≠ 0)
    {a b : V} (hab : q a = q b) (hb : q b ≠ 0) :
    ∃ l : List V, (∀ w ∈ l, q w ≠ 0) ∧ word q l a = b := by
  by_cases hd : q (a - b) = 0
  · have hs : q (a - -b) ≠ 0 := by
      rw [sub_neg_eq_add]
      intro hz
      have hsum := norm_add q a b
      have hdiff := norm_sub q a b
      rw [hab, hz] at hsum
      rw [hab, hd] at hdiff
      have h : (2 : F) * 2 * q b = 0 := by linear_combination -hsum - hdiff
      exact (mul_ne_zero (mul_ne_zero h₂ h₂) hb) h
    have he := reflect_difference q (b := -b) (by simpa only [q.map_neg] using hab) hs
    have hf : reflect q b (-b) = b := by
      have hc : -(2 * q b) / q b = -(2 : F) := by
        field_simp
      rw [reflect_apply, map_neg, polar_diag, hc]
      module
    refine ⟨[b, a - -b], ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hb
      · exact hs
    · change reflect q b (reflect q (a - -b) a) = b
      rw [he, hf]
  · exact ⟨[a - b], by simpa, reflect_difference q hab hd⟩

/-- Transport between equal-norm vectors using symmetries supported in the
chosen subspace. The vectors being aligned may lie outside that subspace. -/
private theorem align_alternating [Infinite F] (q : QuadraticForm F V)
    (h₂ : (2 : F) = 0) (N : Submodule F V) {a b : V}
    (hab : q a = q b) (hdiff : a - b ∈ N)
    (hn : ∃ z : N, q z ≠ 0)
    (ha : ∃ z : N, q.polarBilin a z ≠ 0) (hb : ∃ z : N, q.polarBilin b z ≠ 0) :
    ∃ l : List V, (∀ w ∈ l, w ∈ N ∧ q w ≠ 0) ∧ word q l a = b := by
  have align {x : V} (hx : q x = q b) (hxb : q.polarBilin x b ≠ 0) :
      q (x - b) ≠ 0 ∧ reflect q (x - b) x = b := by
    have hn' : q (x - b) ≠ 0 := by
      rw [norm_sub, hx, ← two_mul, h₂, zero_mul, zero_sub]
      exact neg_ne_zero.mpr hxb
    exact ⟨hn', reflect_difference q hx hn'⟩
  by_cases h : q.polarBilin a b = 0
  · obtain ⟨z, hz, hza, hzb⟩ :=
      exists_norm_and_pairings (q.comp N.subtype) ((q.polarBilin a).comp N.subtype)
        ((q.polarBilin b).comp N.subtype) hn ha hb
    change q (z : V) ≠ 0 at hz
    change q.polarBilin a z ≠ 0 at hza
    change q.polarBilin b z ≠ 0 at hzb
    let x := reflect q z a
    have hxb : q.polarBilin x b ≠ 0 := by
      dsimp only [x]
      rw [reflect_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
        h, zero_sub, polar_swap q z a, polar_swap q z b, smul_eq_mul]
      exact neg_ne_zero.mpr (mul_ne_zero (div_ne_zero hza hz) hzb)
    have hdiff' : x - b ∈ N := by
      have he : x - b = (a - b) - (q.polarBilin z a / q z) • (z : V) := by
        dsimp only [x]
        rw [reflect_apply]
        abel
      rw [he]
      exact N.sub_mem hdiff (N.smul_mem _ z.prop)
    obtain ⟨hqn, he⟩ := align ((reflect_norm q hz a).trans hab) hxb
    refine ⟨[x - b, z], ?_, he⟩
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨hdiff', hqn⟩
    · exact ⟨z.prop, hz⟩
  · obtain ⟨hn', he⟩ := align hab h
    exact ⟨[a - b], by simpa using And.intro hdiff hn', he⟩

private theorem orthogonal_span_singleton_mem (q : QuadraticForm F V) (v x : V) :
    x ∈ LinearMap.BilinForm.orthogonal q.polarBilin (F ∙ v) ↔ q.polarBilin v x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  refine ⟨fun h => h v (Submodule.mem_span_singleton_self v), ?_⟩
  intro h y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp [h]

private theorem fixes_span (g : V →ₗ[F] V) {s : Set V} (h : ∀ x ∈ s, g x = x) :
    ∀ x ∈ Submodule.span F s, g x = x := by
  have hs : Submodule.span F s ≤ LinearMap.ker (g - LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    simpa [sub_eq_zero] using h x hx
  intro x hx
  simpa [sub_eq_zero] using hs hx

private theorem align_subspace [Infinite F] [FiniteDimensional F V] (q : QuadraticForm F V)
    (hB : q.polarBilin ≠ 0) (g : V →ₗ[F] V) (hg : ∀ x, q (g x) = q x) :
    ∃ W : Submodule F V, W ≠ ⊥ ∧ IsCompl W (LinearMap.BilinForm.orthogonal q.polarBilin W) ∧
      ∃ l : List V, (∀ w ∈ l, q w ≠ 0) ∧ ∀ x ∈ W, word q l (g x) = x := by
  classical
  obtain ⟨z, hz⟩ := norm_exists q hB
  by_cases h₂ : (2 : F) = 0
  · have diag (x : V) : q.polarBilin x x = 0 := by rw [polar_diag, h₂, zero_mul]
    obtain ⟨y, t, hyt⟩ := nonradical_pairing q hB
    let f := q.polarBilin t
    have hf : ∃ y, f y ≠ 0 := ⟨y, (polar_swap q t y).trans_ne hyt⟩
    obtain ⟨v, hv, htv, _⟩ := exists_norm_and_pairings q f f ⟨z, hz⟩ hf hf
    have hvt : q.polarBilin v t ≠ 0 := (polar_swap q v t).trans_ne htv
    have hgv : q.polarBilin (g v) (g t) ≠ 0 := (polar_preserve q g hg v t).trans_ne hvt
    obtain ⟨l, hl, hvfix⟩ := align_alternating q h₂ (⊤ : Submodule F V) (hg v)
      (Submodule.mem_top) ⟨⟨v, Submodule.mem_top⟩, hv⟩
      ⟨⟨g t, Submodule.mem_top⟩, hgv⟩ ⟨⟨t, Submodule.mem_top⟩, hvt⟩
    have hln (x) (hx : x ∈ l) := (hl x hx).2
    let j := (word q l).comp g
    have hj (x : V) : q (j x) = q x := (word_norm q l hln (g x)).trans (hg x)
    have hjv : j v = v := hvfix
    -- Align the partner using only symmetries that fix the first vector.
    let N := LinearMap.BilinForm.orthogonal q.polarBilin (F ∙ v)
    have hvN : v ∈ N := (orthogonal_span_singleton_mem q v v).2 (diag v)
    have hplane := polar_preserve q j hj v t
    rw [hjv] at hplane
    have hdiff : j t - t ∈ N := by
      apply (orthogonal_span_singleton_mem q v (j t - t)).2
      rw [map_sub, hplane, sub_self]
    obtain ⟨m, hm, htfix⟩ := align_alternating q h₂ N (hj t) hdiff
      ⟨⟨v, hvN⟩, hv⟩
      ⟨⟨v, hvN⟩, (polar_swap q (j t) v).trans_ne (hplane.trans_ne hvt)⟩
      ⟨⟨v, hvN⟩, htv⟩
    let W := F ∙ v ⊔ F ∙ t
    have hvW : v ∈ W := Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    have htW : t ∈ W := Submodule.mem_sup_right (Submodule.mem_span_singleton_self t)
    have hW : W ≠ ⊥ := by
      intro h
      have hv0 : v = 0 := (Submodule.mem_bot F).mp (h ▸ hvW)
      exact hv (hv0 ▸ q.map_zero)
    have hc : IsCompl W (LinearMap.BilinForm.orthogonal q.polarBilin W) := by
      apply (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (B := q.polarBilin)
        (W := W) (fun a b h => (polar_swap q b a).trans h)).mpr
      rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp ha
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
      have hs' := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx') t htW
      have hr' := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx') v hvW
      have hs0 : s * q.polarBilin t v = 0 := by
        simpa only [map_add, map_smul, smul_eq_mul, diag, mul_zero, add_zero] using hs'
      have hr0 : r * q.polarBilin v t = 0 := by
        simpa only [map_add, map_smul, smul_eq_mul, diag, mul_zero, zero_add] using hr'
      simp [(mul_eq_zero.mp hs0).resolve_right htv, (mul_eq_zero.mp hr0).resolve_right hvt]
    have hfixv : word q m (j v) = v := by
      rw [hjv]
      apply word_fixed
      intro x hx
      rw [polar_swap q x v]
      exact (orthogonal_span_singleton_mem q v x).mp (hm x hx).1
    refine ⟨W, hW, hc, m ++ l, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hm x hx).2
      · exact hln x hx
    · have hspan : W = Submodule.span F ({v, t} : Set V) := by
        simp [W, Submodule.span_insert]
      have hfix := fixes_span ((word q m).comp j) (s := ({v, t} : Set V)) (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hfixv
        · exact htfix)
      intro x hx
      rw [word_append]
      exact hfix x (hspan ▸ hx)
  · obtain ⟨l, hl, hfix⟩ := align_line q h₂ (hg z) hz
    let W := F ∙ z
    have hW : W ≠ ⊥ := by
      intro h
      have hzW : z ∈ W := Submodule.mem_span_singleton_self z
      have hz0 : z = 0 := (Submodule.mem_bot F).mp (h ▸ hzW)
      exact hz (hz0 ▸ q.map_zero)
    have hc : IsCompl W (LinearMap.BilinForm.orthogonal q.polarBilin W) := by
      apply LinearMap.BilinForm.isCompl_span_singleton_orthogonal
      rw [polar_diag]
      exact mul_ne_zero h₂ hz
    refine ⟨W, hW, hc, l, hl, ?_⟩
    change ∀ x ∈ W, ((word q l).comp g) x = x
    exact fixes_span _ (fun x hx => (Set.mem_singleton_iff.mp hx).symm ▸ hfix)

private abbrev Regular (q : QuadraticForm F V) : Prop :=
  LinearMap.ker q.polarBilin = ⊥ ∨
    ∃ r : V, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = F ∙ r

/-- A regular space with zero polar form is zero or an anisotropic radical line.
On that line the only norm-preserving scalar has square one in characteristic two. -/
private theorem identity_of_zero_polar (q : QuadraticForm F V) (hq : Regular q)
    (hB : q.polarBilin = 0) (g : V →ₗ[F] V) (hg : ∀ x, q (g x) = q x) (x : V) :
    g x = x := by
  have mem (y : V) : y ∈ LinearMap.ker q.polarBilin := by simp [hB]
  rcases hq with hq | ⟨r, hr, hq⟩
  · have zero (y : V) : y = 0 := (Submodule.mem_bot F).mp (hq ▸ mem y)
    exact (zero (g x)).trans (zero x).symm
  · have h₂ : (2 : F) = 0 := by
      have h := polar_diag q r
      rw [hB, LinearMap.zero_apply, LinearMap.zero_apply, eq_comm] at h
      exact (mul_eq_zero.mp h).resolve_right hr
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hq ▸ mem (g r))
    have hnorm := hg r
    rw [← ha, q.map_smul, smul_eq_mul] at hnorm
    have hsq : a * a = 1 := by
      apply mul_right_cancel₀ hr
      simpa using hnorm
    have hf : (a - 1) * (a + 1) = 0 := by linear_combination hsq
    have ha₁ : a = 1 := by
      rcases mul_eq_zero.mp hf with h | h
      · exact sub_eq_zero.mp h
      · linear_combination h - h₂
    have hgr : g r = r := by simpa [ha₁] using ha.symm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hq ▸ mem x)
    rw [← hc, map_smul, hgr]

/-- In an orthogonal direct sum the radical of the perpendicular summand is
the ambient radical, viewed inside that summand. -/
private theorem regular_orthogonal (q : QuadraticForm F V) (hq : Regular q)
    (W : Submodule F V) (hc : W ⊔ LinearMap.BilinForm.orthogonal q.polarBilin W = ⊤) :
    Regular (q.comp (LinearMap.BilinForm.orthogonal q.polarBilin W).subtype) := by
  let N := LinearMap.BilinForm.orthogonal q.polarBilin W
  let Q := q.comp N.subtype
  have radical_iff (z : N) :
      z ∈ LinearMap.ker Q.polarBilin ↔ (z : V) ∈ LinearMap.ker q.polarBilin := by
    simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply]
    constructor
    · intro hz x
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
        (show x ∈ W ⊔ N from hc.symm ▸ Submodule.mem_top)
      have hza := (LinearMap.BilinForm.mem_orthogonal_iff.mp z.prop) a ha
      have hzb : q.polarBilin z b = 0 := hz ⟨b, hb⟩
      rw [map_add, polar_swap q z a, hza, hzb, add_zero]
    · exact fun h z' => h z'
  change Regular Q
  rcases hq with hq | ⟨r, hr, hq⟩
  · left
    ext z
    rw [radical_iff, hq, Submodule.mem_bot, Submodule.mem_bot]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · have hrker : r ∈ LinearMap.ker q.polarBilin :=
      hq.symm ▸ Submodule.mem_span_singleton_self r
    have hrN : r ∈ N := by
      apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
      intro x _
      rw [polar_swap q x r, LinearMap.mem_ker.mp hrker, LinearMap.zero_apply]
    let r' : N := ⟨r, hrN⟩
    refine Or.inr ⟨r', hr, ?_⟩
    ext z
    rw [radical_iff, hq, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩, fun ⟨a, ha⟩ => ⟨a, congrArg Subtype.val ha⟩⟩

private theorem word_restrict (q : QuadraticForm F V) (N : Submodule F V)
    (l : List N) (x : N) :
    (word (q.comp N.subtype) l x : V) = word q (l.map Subtype.val) (x : V) := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change (reflect (q.comp N.subtype) w (word (q.comp N.subtype) l x) : V) =
      reflect q w (word q (l.map Subtype.val) x)
    rw [reflect_apply, reflect_apply, ← ih]
    rfl

private theorem generate {F : Type u} [Field F] [Infinite F] (n : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (q : QuadraticForm F V), Module.finrank F V = n → Regular q →
      ∀ g : V →ₗ[F] V, (∀ x, q (g x) = q x) →
      ∃ l : List V, (∀ w ∈ l, q w ≠ 0) ∧ ∀ x, g x = word q l x := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ q hn hq g hg
    by_cases hB : q.polarBilin = 0
    · exact ⟨[], by simp, identity_of_zero_polar q hq hB g hg⟩
    obtain ⟨W, hW, hc, l, hl, hfix⟩ := align_subspace q hB g hg
    let N := LinearMap.BilinForm.orthogonal q.polarBilin W
    let Q := q.comp N.subtype
    have hN : N < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro he
      have hi := hc.inf_eq_bot
      change W ⊓ N = ⊥ at hi
      rw [he, inf_top_eq] at hi
      exact hW hi
    have hdim : Module.finrank F N < n := by
      simpa only [finrank_top, hn] using Submodule.finrank_lt_finrank_of_lt hN
    have hQ : Regular Q := regular_orthogonal q hq W hc.sup_eq_top
    let j := (word q l).comp g
    have hj (x : V) : q (j x) = q x := (word_norm q l hl (g x)).trans (hg x)
    have hjN (z : N) : j z ∈ N := by
      apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
      intro a ha
      calc
        q.polarBilin a (j z) = q.polarBilin (j a) (j z) := by
          rw [show j a = a from hfix a ha]
        _ = q.polarBilin a z := polar_preserve q j hj a z
        _ = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp z.prop) a ha
    -- Induct on the perpendicular and extend its word back to the whole space.
    let jN : N →ₗ[F] N := (j.comp N.subtype).codRestrict N hjN
    obtain ⟨m, hm, hmj⟩ := ih _ hdim Q rfl hQ jN (fun z => hj z)
    have hem (x : V) : j x = word q (m.map Subtype.val) x := by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
        (show x ∈ W ⊔ N from hc.sup_eq_top.symm ▸ Submodule.mem_top)
      let z : N := ⟨b, hb⟩
      have hzb : j b = word q (m.map Subtype.val) b :=
        (congrArg Subtype.val (hmj z)).trans (word_restrict q N m z)
      have hwa : word q (m.map Subtype.val) a = a := by
        apply word_fixed
        intro w hw
        obtain ⟨w', _, rfl⟩ := List.mem_map.mp hw
        rw [polar_swap q w'.val a]
        exact (LinearMap.BilinForm.mem_orthogonal_iff.mp w'.prop) a ha
      rw [map_add, map_add, show j a = a from hfix a ha, hzb, hwa]
    refine ⟨l.reverse ++ m.map Subtype.val, ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hl w (List.mem_reverse.mp hw)
      · obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
        exact hm w' hw'
    · intro x
      rw [word_append, ← hem]
      exact (word_reverse q l hl (g x)).symm

/-- The Cartan–Dieudonné word over an infinite field, including the regular
characteristic-two forms with a one-dimensional polar radical. -/
theorem orthogonalWords : OrthogonalWords.{u, v} := by
  intro F _ _ V _ _ _ q hq g hg
  obtain ⟨l, hl, he⟩ := generate (Module.finrank F V) q rfl hq g.toLinearMap hg
  exact ⟨l, hl, fun x => (he x).trans (word_apply q l x)⟩

end LinearAlgebraicGroups.Arithmetic.SpinOrthogonalWords
