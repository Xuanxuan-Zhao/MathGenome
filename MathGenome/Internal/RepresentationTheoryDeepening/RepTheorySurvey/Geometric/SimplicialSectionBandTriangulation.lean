import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SimplicialSectionBandTriangulation
import Mathlib.Analysis.Convex.Topology
import Mathlib.SetTheory.Cardinal.Order

/-!
# Triangulating a cylinder with prescribed level functions

The affine interpolants of the level functions agree on common base faces and
have the same pointwise collapse pattern as the original levels. The geometric
complex uses staircase simplices between consecutive interpolants. A finite
union of compact parametrized graphs gives the homeomorphism to the original
levels, including the fibres where a gap collapses.
-/

namespace RepTheorySurvey.Geometric.SimplicialSectionBandTriangulation

open Set Geometry Filter Topology
open scoped BigOperators

noncomputable section

private theorem exists_positive_weights_subfinset {V : Type*} [AddCommGroup V] [Module ℝ V]
    {s : Finset V} {p : V} (hp : p ∈ convexHull ℝ (s : Set V)) :
    ∃ t ⊆ s, t.Nonempty ∧ ∃ w : V → ℝ,
      (∀ q ∈ t, 0 < w q) ∧ ∑ q ∈ t, w q = 1 ∧ ∑ q ∈ t, w q • q = p := by
  classical
  obtain ⟨w, hw₀, hw₁, hwp⟩ := Finset.mem_convexHull'.mp hp
  let t := s.filter (fun q => 0 < w q)
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hz (q : V) (hq : q ∈ s) (hn : q ∉ t) : w q = 0 :=
    le_antisymm (le_of_not_gt fun he => hn (Finset.mem_filter.mpr ⟨hq, he⟩)) (hw₀ q hq)
  have hsum := (Finset.sum_subset hts hz).trans hw₁
  have ht : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun he => by simp [he] at hsum
  exact ⟨t, hts, ht, w, fun q hq => (Finset.mem_filter.mp hq).2, hsum,
    (Finset.sum_subset hts fun q hq hn => by rw [hz q hq hn, zero_smul]).trans hwp⟩

section BarycentricCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private structure AffineCoordinates (s : Finset E) where
  weight : E → E →ᵃ[ℝ] ℝ
  weight_combination : ∀ (w : E → ℝ), ∑ v ∈ s, w v = 1 →
    ∀ v ∈ s, weight v (∑ u ∈ s, w u • u) = w v

private def affineCoordinates (s : Finset E) (hs : AffineIndependent ℝ ((↑) : s → E)) :
    AffineCoordinates s := by
  classical
  let hex := exists_subset_affineIndependent_affineSpan_eq_top hs
  let t := hex.choose
  have ht : (s : Set E) ⊆ t := hex.choose_spec.1
  let B : AffineBasis t ℝ E := ⟨Subtype.val, hex.choose_spec.2.1, by
    simpa [t] using hex.choose_spec.2.2⟩
  let weight (v : E) : E →ᵃ[ℝ] ℝ :=
    if hv : v ∈ s then B.coord ⟨v, ht hv⟩ else AffineMap.const ℝ E 0
  refine ⟨weight, ?_⟩
  · intro w hw v hv
    let e : s ↪ t := ⟨fun x => ⟨x.val, ht x.property⟩, fun _ _ h => Subtype.ext (congrArg (fun y : t => y.val) h)⟩
    let f : Finset t := Finset.univ.map e
    have hsum : ∑ x ∈ f, w x.val = 1 := by
      unfold f
      rw [Finset.sum_map]
      change (∑ x ∈ s.attach, w x.val) = 1
      exact (Finset.sum_attach s w).trans hw
    have hcomb : f.affineCombination ℝ B (fun x => w x.val) = ∑ x ∈ s, w x • x := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      change (∑ x ∈ f, w x.val • x.val) = _
      rw [Finset.sum_map]
      change (∑ x ∈ s.attach, w x.val • x.val) = _
      exact Finset.sum_attach s (fun x => w x • x)
    have hvf : e ⟨v, hv⟩ ∈ f := Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
    have he := B.coord_apply_combination_of_mem hvf hsum
    rw [hcomb] at he
    change (weight v) _ = _
    rw [show weight v = B.coord (e ⟨v, hv⟩) by rw [show weight v = B.coord ⟨v, ht hv⟩ by simp [weight, hv]]; rfl]
    exact he

omit [FiniteDimensional ℝ E] in
private theorem AffineCoordinates.spec {s : Finset E} (C : AffineCoordinates s) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) :
    (∀ v ∈ s, 0 ≤ C.weight v x) ∧ (∑ v ∈ s, C.weight v x = 1) ∧
      (∑ v ∈ s, C.weight v x • v = x) := by
  obtain ⟨w, hw₀, hw₁, rfl⟩ := Finset.mem_convexHull'.mp hx
  have he := C.weight_combination w hw₁
  exact ⟨fun v hv => (he v hv).symm ▸ hw₀ v hv,
    (Finset.sum_congr rfl he).trans hw₁,
    Finset.sum_congr rfl fun v hv => by rw [he v hv]⟩

omit [FiniteDimensional ℝ E] in
private theorem AffineCoordinates.restrict {s t : Finset E} (C : AffineCoordinates s)
    (D : AffineCoordinates t) (hts : t ⊆ s) {x : E} (hx : x ∈ convexHull ℝ (t : Set E))
    {v : E} (hv : v ∈ s) :
    C.weight v x = (t : Set E).indicator (fun u => D.weight u x) v := by
  classical
  obtain ⟨w, _, hw₁, rfl⟩ := Finset.mem_convexHull'.mp hx
  let w' : E → ℝ := (t : Set E).indicator w
  have hs₁ : ∑ v ∈ s, w' v = 1 := by rwa [Finset.sum_indicator_subset w hts]
  have hsx : ∑ v ∈ s, w' v • v = ∑ v ∈ t, w v • v := by
    rw [← Finset.sum_subset hts (f := fun v => w' v • v)
      (fun v _ hv => by simp [w', hv])]
    exact Finset.sum_congr rfl fun v hv => by simp [w', hv]
  rw [← hsx, C.weight_combination w' hs₁ v hv, hsx]
  by_cases hvt : v ∈ t
  · simp [w', hvt, D.weight_combination w hw₁ v hvt]
  · simp [w', hvt]

omit [FiniteDimensional ℝ E] in
private theorem AffineCoordinates.spec_span {s : Finset E} (C : AffineCoordinates s) {x : E}
    (hx : x ∈ affineSpan ℝ (s : Set E)) :
    (∑ v ∈ s, C.weight v x = 1) ∧ (∑ v ∈ s, C.weight v x • v = x) := by
  classical
  have hr : Set.range ((↑) : s → E) = (s : Set E) := Subtype.range_coe
  rw [← hr] at hx
  obtain ⟨w, hw₁, hx⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw₁] at hx
  let w' : E → ℝ := fun v => if hv : v ∈ s then w ⟨v, hv⟩ else 0
  have hval (v : s) : w' v.val = w v := by simp [w', v.property]
  have hw₁' : ∑ v ∈ s, w' v = 1 := by
    rw [← Finset.sum_attach]
    change (∑ v : s, w' v.val) = _
    simpa only [hval] using hw₁
  have hx' : ∑ v ∈ s, w' v • v = x := by
    rw [← Finset.sum_attach]
    change (∑ v : s, w' v.val • v.val) = _
    simpa only [hval] using hx.symm
  have hcoord (v : E) (hv : v ∈ s) : C.weight v x = w' v := by
    rw [← hx', C.weight_combination _ hw₁' v hv]
  exact ⟨(Finset.sum_congr rfl hcoord).trans hw₁',
    (Finset.sum_congr rfl fun v hv => by rw [hcoord v hv]).trans hx'⟩

private theorem AffineCoordinates.mem_intrinsicInterior {s : Finset E} (C : AffineCoordinates s)
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) :
    x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ↔
      ∀ v ∈ s, 0 < C.weight v x := by
  classical
  rw [intrinsicInterior, affineSpan_convexHull]
  let A := affineSpan ℝ (s : Set E)
  let X : Set A := Subtype.val ⁻¹' convexHull ℝ (s : Set E)
  change x ∈ Subtype.val '' interior X ↔ _
  constructor
  · rintro ⟨y, hy, rfl⟩ v hv
    by_contra! h
    have hz : C.weight v y.val = 0 := le_antisymm h ((C.spec hx).1 v hv)
    have hv₁ : C.weight v v = 1 := by
      let w : E → ℝ := fun u => if u = v then 1 else 0
      have hw₁ : ∑ u ∈ s, w u = 1 := by simp [w, hv]
      have hwx : ∑ u ∈ s, w u • u = v := by simp [w, hv, ite_smul]
      have he := C.weight_combination _ hw₁ v hv
      rw [hwx] at he
      simpa [w] using he
    let curve (r : ℝ) : A :=
      ⟨AffineMap.lineMap y.val v r,
        AffineMap.lineMap_mem r y.property (mem_affineSpan ℝ hv)⟩
    have hc : Continuous curve :=
      show Continuous (fun r => (⟨_, _⟩ : A)) from
        Continuous.subtype_mk (f := AffineMap.lineMap y.val v)
          (by
            change Continuous fun r : ℝ => (AffineMap.lineMap y.val v : ℝ →ᵃ[ℝ] E) r
            simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
            exact (continuous_id.smul continuous_const).add continuous_const) _
    have hc₀ : curve 0 = y := Subtype.ext (AffineMap.lineMap_apply_zero _ _)
    have he : curve ⁻¹' X ∈ nhds (0 : ℝ) :=
      hc.continuousAt.preimage_mem_nhds (hc₀ ▸ mem_interior_iff_mem_nhds.mp hy)
    have hleft : NeBot (nhdsWithin (0 : ℝ) (Iio 0)) := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio]
      exact (le_rfl : (0 : ℝ) ≤ 0)
    obtain ⟨r, hr, hrneg⟩ := ((eventually_nhdsWithin_of_eventually_nhds he).and
      (self_mem_nhdsWithin : ∀ᶠ r in nhdsWithin (0 : ℝ) (Iio 0), r ∈ Iio 0)).exists
    have hnonneg := (C.spec (show (curve r).val ∈ convexHull ℝ (s : Set E) from hr)).1 v hv
    change 0 ≤ C.weight v (AffineMap.lineMap y.val v r) at hnonneg
    rw [AffineMap.apply_lineMap, hz, hv₁, AffineMap.lineMap_apply] at hnonneg
    simp only [vsub_eq_sub, vadd_eq_add, sub_zero, smul_eq_mul, mul_one, add_zero] at hnonneg
    exact (not_lt_of_ge hnonneg) hrneg
  · intro h
    have hxA : x ∈ A := by
      change x ∈ affineSpan ℝ (s : Set E)
      rw [← affineSpan_convexHull]
      exact mem_affineSpan ℝ hx
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    let U : Set A := ⋂ v ∈ s, (fun y : A => C.weight v y.val) ⁻¹' Ioi 0
    have hU : IsOpen U := s.finite_toSet.isOpen_biInter fun v _ =>
      isOpen_Ioi.preimage ((C.weight v).continuous_of_finiteDimensional.comp continuous_subtype_val)
    have hUX : U ⊆ X := by
      intro y hy
      have hp (v : E) (hv : v ∈ s) : 0 < C.weight v y.val := Set.mem_iInter₂.mp hy v hv
      exact Finset.mem_convexHull'.mpr
        ⟨_, fun v hv => (hp v hv).le, (C.spec_span y.property).1, (C.spec_span y.property).2⟩
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hU.mem_nhds (Set.mem_iInter₂.mpr h)) hUX)

end BarycentricCoordinates

section VerticalInterpolation

private def adjacent {n : ℕ} (i j : Fin n) : Prop := i ≤ j ∧ j.val ≤ i.val + 1

private theorem adjacent_map {m n : ℕ} {q : Fin m → Fin n}
    (hm : Monotone q) (hs : Function.Surjective q) {i j : Fin m} (h : adjacent i j) :
    adjacent (q i) (q j) := by
  have hij := h.1
  have hdiff := h.2
  refine ⟨hm hij, ?_⟩
  by_contra! hgap
  let k : Fin n := ⟨(q i).val + 1, by omega⟩
  obtain ⟨r, hr⟩ := hs k
  have hlo : q i < q r := by rw [hr]; exact Nat.lt_succ_self _
  have hhi : q r < q j := by rw [hr]; exact hgap
  have h₁ := hm.reflect_lt hlo
  have h₂ := hm.reflect_lt hhi
  exact (Nat.not_lt_of_ge hdiff) (by omega)

private theorem exists_adjacent_bounds {n : ℕ} (f : Fin (n + 2) → ℝ)
    {z : ℝ} (hl : f 0 ≤ z) (hu : z ≤ f (Fin.last (n + 1))) :
    ∃ i j, adjacent i j ∧ z ∈ Icc (f i) (f j) := by
  classical
  let P (j : ℕ) := ∃ h : j < n + 2, z ≤ f ⟨j, h⟩
  have hp : ∃ j, P j := ⟨n + 1, Nat.lt_succ_self _, hu⟩
  obtain ⟨hidx, hz⟩ := Nat.find_spec hp
  let j : Fin (n + 2) := ⟨Nat.find hp, hidx⟩
  by_cases hj : Nat.find hp = 0
  · have he : j = 0 := Fin.ext hj
    exact ⟨0, 0, ⟨le_rfl, by omega⟩, hl, he ▸ hz⟩
  · let i : Fin (n + 2) := ⟨Nat.find hp - 1, by omega⟩
    have hij : adjacent i j := ⟨by change i.val ≤ j.val; dsimp [i, j]; omega,
      by dsimp [i, j]; omega⟩
    refine ⟨i, j, hij, le_of_not_ge ?_, hz⟩
    intro h
    exact Nat.find_min hp (show i.val < Nat.find hp from by dsimp [i]; omega) ⟨i.isLt, h⟩

private def interpolate (l u t : ℝ) : ℝ := l + t * (u - l)

private theorem interpolate_mem {l u t : ℝ} (h : l ≤ u) (ht : t ∈ Icc (0 : ℝ) 1) :
    interpolate l u t ∈ Icc l u := by
  obtain ⟨ht₀, ht₁⟩ := ht
  exact ⟨by simp only [interpolate]; nlinarith,
    by simp only [interpolate]; nlinarith⟩

private theorem exists_interpolate {l u z : ℝ} (hz : z ∈ Icc l u) :
    ∃ t ∈ Icc (0 : ℝ) 1, interpolate l u t = z := by
  obtain ⟨hl, hu⟩ := hz
  rcases (hl.trans hu).eq_or_lt with he | he
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [interpolate]; linarith⟩
  · have h := sub_pos.mpr he
    refine ⟨(z - l) / (u - l),
      ⟨div_nonneg (sub_nonneg.mpr hl) h.le, (div_le_one h).mpr (by linarith)⟩, ?_⟩
    dsimp [interpolate]
    field_simp
    ring

private def verticalMatch {n : ℕ} (f g : Fin n → ℝ) (z w : ℝ) : Prop :=
  ∃ i j, adjacent i j ∧ ∃ t ∈ Icc (0 : ℝ) 1,
    interpolate (f i) (f j) t = z ∧ interpolate (g i) (g j) t = w

private theorem verticalMatch_symm {n : ℕ} {f g : Fin n → ℝ} {z w : ℝ} :
    verticalMatch f g z w ↔ verticalMatch g f w z := by
  constructor <;> rintro ⟨i, j, hij, t, ht, hf, hg⟩ <;> exact ⟨i, j, hij, t, ht, hg, hf⟩

private theorem interpolate_at_lower {l u l' u' t : ℝ}
    (hc : l = u → l' = u') (he : interpolate l u t = l) :
    interpolate l' u' t = l' := by
  by_cases h₀ : l = u
  · simp [interpolate, hc h₀]
  · have : t * (u - l) = 0 := by linarith [show l + t * (u - l) = l from he]
    rcases mul_eq_zero.mp this with ht | hu
    · simp [interpolate, ht]
    · exact False.elim (h₀ (sub_eq_zero.mp hu).symm)

private theorem interpolate_at_upper {l u l' u' t : ℝ}
    (hc : l = u → l' = u') (he : interpolate l u t = u) :
    interpolate l' u' t = u' := by
  by_cases h₀ : l = u
  · simp [interpolate, hc h₀]
  · have : (t - 1) * (u - l) = 0 := by
      dsimp [interpolate] at he
      linear_combination he
    rcases mul_eq_zero.mp this with ht | hu
    · simp [interpolate, sub_eq_zero.mp ht]
    · exact False.elim (h₀ (sub_eq_zero.mp hu).symm)

private theorem verticalMatch_unique {n : ℕ} {f g : Fin n → ℝ}
    (hf : Monotone f) (hc : ∀ i j, f i = f j → g i = g j)
    {z w w' : ℝ} (h : verticalMatch f g z w) (h' : verticalMatch f g z w') :
    w = w' := by
  obtain ⟨i, j, hij, t, ht, rfl, rfl⟩ := h
  obtain ⟨i', j', hij', t', ht', he, rfl⟩ := h'
  have separated {i j i' j' : Fin n} {t t' : ℝ}
      (hj : j ≤ i') (ha : i ≤ j) (hb : i' ≤ j')
      (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1)
      (he : interpolate (f i) (f j) t = interpolate (f i') (f j') t') :
      interpolate (g i) (g j) t = interpolate (g i') (g j') t' := by
    have h₁ := (interpolate_mem (hf ha) ht).2
    have h₂ := (interpolate_mem (hf hb) ht').1
    have h₃ := hf hj
    have hel : interpolate (f i) (f j) t = f j := by linarith
    have her : interpolate (f i') (f j') t' = f i' := by linarith
    rw [interpolate_at_upper (hc i j) hel, interpolate_at_lower (hc i' j') her,
      hc j i' (by linarith)]
  by_cases h₁ : j ≤ i'
  · exact separated h₁ hij.1 hij'.1 ht ht' he.symm
  by_cases h₂ : j' ≤ i
  · exact (separated h₂ hij'.1 hij.1 ht' ht he).symm
  obtain ⟨hij₁, hij₂⟩ := hij
  obtain ⟨hij₃, hij₄⟩ := hij'
  have ei : i = i' := Fin.ext (by omega)
  have ej : j = j' := Fin.ext (by omega)
  subst i' j'
  by_cases h₀ : f i = f j
  · simp [interpolate, hc i j h₀]
  · have ht₀ : t' = t := by
      dsimp [interpolate] at he
      have hprod : (t' - t) * (f j - f i) = 0 := by linear_combination he
      exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr (Ne.symm h₀)))
    rw [ht₀]

end VerticalInterpolation

section Staircase

variable {V : Type*}

private def fiber (t : Finset (V × ℝ)) (v : V) : Finset (V × ℝ) :=
  open Classical in t.filter (fun p => p.1 = v)

private theorem mem_fiber {t : Finset (V × ℝ)} {v : V} {p : V × ℝ} :
    p ∈ fiber t v ↔ p ∈ t ∧ p.1 = v := by
  classical
  simp [fiber]

private def projectedWeight (t : Finset (V × ℝ)) (w : V × ℝ → ℝ) (v : V) : ℝ :=
  ∑ p ∈ fiber t v, w p

private theorem sum_fibers {M : Type*} [AddCommMonoid M] {s : Finset V} {t : Finset (V × ℝ)}
    (h : ∀ p ∈ t, p.1 ∈ s) (f : V × ℝ → M) :
    ∑ v ∈ s, ∑ p ∈ fiber t v, f p = ∑ p ∈ t, f p := by
  classical
  exact Finset.sum_fiberwise_of_maps_to h f

private theorem sum_projectedWeight_smul {M : Type*} [AddCommMonoid M] [Module ℝ M]
    {s : Finset V} {t : Finset (V × ℝ)} (h : ∀ p ∈ t, p.1 ∈ s)
    (w : V × ℝ → ℝ) (f : V → M) :
    ∑ v ∈ s, projectedWeight t w v • f v = ∑ p ∈ t, w p • f p.1 := by
  calc
    _ = ∑ v ∈ s, ∑ p ∈ fiber t v, w p • f p.1 := by
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [projectedWeight, Finset.sum_smul]
      exact Finset.sum_congr rfl fun p hp => by rw [(mem_fiber.mp hp).2]
    _ = _ := sum_fibers h _

private theorem projectedWeight_pos {t : Finset (V × ℝ)} {w : V × ℝ → ℝ}
    (hw : ∀ p ∈ t, 0 < w p) {p : V × ℝ} (hp : p ∈ t) :
    0 < projectedWeight t w p.1 := by
  rw [projectedWeight]
  exact Finset.sum_pos (fun q hq => hw q (mem_fiber.mp hq).1)
    ⟨p, mem_fiber.mpr ⟨hp, rfl⟩⟩

private theorem projectedWeight_of_combination [AddCommGroup V] [Module ℝ V]
    {s : Finset V} {t : Finset (V × ℝ)}
    (h : ∀ p ∈ t, p.1 ∈ s) (w : V × ℝ → ℝ) (hw : ∑ p ∈ t, w p = 1)
    (p : V × ℝ) (hp : ∑ q ∈ t, w q • q = p) :
    (∑ v ∈ s, projectedWeight t w v = 1) ∧
      (∑ v ∈ s, projectedWeight t w v • v = p.1) := by
  refine ⟨(sum_fibers h w).trans hw, ?_⟩
  rw [sum_projectedWeight_smul h w (fun v => v)]
  simpa only [map_sum, LinearMap.fst_apply, map_smul] using congrArg (LinearMap.fst ℝ V ℝ) hp

variable [LinearOrder V]

private structure Staircase (s : Finset V) (t : Finset (V × ℝ)) (l u : V → ℝ) : Prop where
  projects : ∀ p ∈ t, p.1 ∈ s
  endpoints : ∀ p ∈ t, p.2 = l p.1 ∨ p.2 = u p.1
  ordered : ∀ p ∈ t, ∀ q ∈ t, p.2 < u p.1 → l q.1 < q.2 → q.1 ≤ p.1

private theorem Staircase.snd_bounds {s : Finset V} {t : Finset (V × ℝ)} {l u : V → ℝ}
    (h : Staircase s t l u) (hlu : ∀ v ∈ s, l v ≤ u v)
    {w : V × ℝ → ℝ} (hw : ∀ p ∈ t, 0 ≤ w p) :
    (∑ v ∈ s, projectedWeight t w v * l v) ≤ ∑ p ∈ t, w p * p.2 ∧
      (∑ p ∈ t, w p * p.2) ≤ ∑ v ∈ s, projectedWeight t w v * u v := by
  have he (p : V × ℝ) (hp : p ∈ t) : l p.1 ≤ p.2 ∧ p.2 ≤ u p.1 := by
    rcases h.endpoints p hp with he | he <;> rw [he]
    · exact ⟨le_rfl, hlu _ (h.projects p hp)⟩
    · exact ⟨hlu _ (h.projects p hp), le_rfl⟩
  have hl := sum_projectedWeight_smul h.projects w l
  have hu := sum_projectedWeight_smul h.projects w u
  simp only [smul_eq_mul] at hl hu
  rw [hl, hu]
  exact ⟨Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (he p hp).1 (hw p hp),
    Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (he p hp).2 (hw p hp)⟩

private theorem Staircase.eq_endpoints_of_sum_eq {s : Finset V} {t : Finset (V × ℝ)} {l u : V → ℝ}
    (h : Staircase s t l u) (hlu : ∀ v ∈ s, l v ≤ u v)
    {w : V × ℝ → ℝ} (hw : ∀ p ∈ t, 0 < w p) :
    ((∑ p ∈ t, w p * p.2) = ∑ v ∈ s, projectedWeight t w v * l v) ↔
      (∀ p ∈ t, p.2 = l p.1) := by
  have hl := sum_projectedWeight_smul h.projects w l
  simp only [smul_eq_mul] at hl
  rw [hl]
  refine ⟨fun he p hp => ?_, fun he => Finset.sum_congr rfl fun p hp => by rw [he p hp]⟩
  by_contra hn
  have hle (p : V × ℝ) (hp : p ∈ t) : l p.1 ≤ p.2 := by
    rcases h.endpoints p hp with he | he
    · exact he.ge
    · exact (hlu _ (h.projects p hp)).trans he.ge
  have hlt := lt_of_le_of_ne (hle p hp) (Ne.symm hn)
  exact (ne_of_lt (Finset.sum_lt_sum
    (fun q hq => mul_le_mul_of_nonneg_left (hle q hq) (hw q hq).le)
    ⟨p, hp, mul_lt_mul_of_pos_left hlt (hw p hp)⟩)) he.symm

private theorem Staircase.eq_upper_of_sum_eq {s : Finset V} {t : Finset (V × ℝ)} {l u : V → ℝ}
    (h : Staircase s t l u) (hlu : ∀ v ∈ s, l v ≤ u v)
    {w : V × ℝ → ℝ} (hw : ∀ p ∈ t, 0 < w p) :
    ((∑ p ∈ t, w p * p.2) = ∑ v ∈ s, projectedWeight t w v * u v) ↔
      (∀ p ∈ t, p.2 = u p.1) := by
  have hu := sum_projectedWeight_smul h.projects w u
  simp only [smul_eq_mul] at hu
  rw [hu]
  refine ⟨fun he p hp => ?_, fun he => Finset.sum_congr rfl fun p hp => by rw [he p hp]⟩
  by_contra hn
  have hle (p : V × ℝ) (hp : p ∈ t) : p.2 ≤ u p.1 := by
    rcases h.endpoints p hp with he | he
    · exact he.le.trans (hlu _ (h.projects p hp))
    · exact he.le
  have hlt := lt_of_le_of_ne (hle p hp) hn
  exact (ne_of_lt (Finset.sum_lt_sum
    (fun q hq => mul_le_mul_of_nonneg_left (hle q hq) (hw q hq).le)
    ⟨p, hp, mul_lt_mul_of_pos_left hlt (hw p hp)⟩)) he

private def upperWeight (t : Finset (V × ℝ)) (w : V × ℝ → ℝ) (l u : V → ℝ) (v : V) : ℝ :=
  if l v < u v then (t : Set (V × ℝ)).indicator w (v, u v) else 0

private theorem Staircase.sum_fiber_split {s : Finset V} {t : Finset (V × ℝ)} {l u : V → ℝ}
    (h : Staircase s t l u) (hlu : ∀ v ∈ s, l v ≤ u v)
    (w : V × ℝ → ℝ) (v : V) (f : (V × ℝ) → ℝ) :
    ∑ p ∈ fiber t v, w p * f p =
      projectedWeight t w v * f (v, l v) +
        upperWeight t w l u v * (f (v, u v) - f (v, l v)) := by
  classical
  have he (p : V × ℝ) (hp : p ∈ fiber t v) : p = (v, l v) ∨ p = (v, u v) := by
    have ⟨hp₁, hp₂⟩ := mem_fiber.mp hp
    have hp₃ := h.endpoints p hp₁
    rw [hp₂] at hp₃
    exact hp₃.imp (Prod.ext hp₂) (Prod.ext hp₂)
  by_cases hlt : l v < u v
  · rw [upperWeight, ite_eq_left hlt, projectedWeight, Finset.sum_mul, ← sub_eq_iff_eq_add']
    rw [← Finset.sum_sub_distrib]
    by_cases hu : (v, u v) ∈ t
    · rw [Set.indicator_of_mem (show (v, u v) ∈ (t : Set (V × ℝ)) from hu)]
      rw [Finset.sum_eq_single (v, u v)]
      · ring
      · intro p hp hpne
        rw [(he p hp).resolve_right hpne, sub_self]
      · exact fun hn => False.elim (hn (mem_fiber.mpr ⟨hu, rfl⟩))
    · rw [Set.indicator_of_notMem (show (v, u v) ∉ (t : Set (V × ℝ)) from hu), zero_mul]
      apply Finset.sum_eq_zero
      intro p hp
      have hep := (he p hp).resolve_right fun eq => hu (eq ▸ (mem_fiber.mp hp).1)
      rw [hep, sub_self]
  · rw [upperWeight, ite_eq_right hlt, zero_mul, add_zero, projectedWeight, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hlue : l v = u v :=
      le_antisymm (hlu _ ((mem_fiber.mp hp).2 ▸ h.projects p (mem_fiber.mp hp).1)) (le_of_not_gt hlt)
    rcases he p hp with he | he
    · rw [← he]
    · have he' : p = (v, l v) := by simpa only [hlue] using he
      rw [← he']

private theorem Staircase.upperWeight_nonneg_le {t : Finset (V × ℝ)} {l u : V → ℝ}
    {w : V × ℝ → ℝ} (hw : ∀ p ∈ t, 0 ≤ w p) (v : V) :
    0 ≤ upperWeight t w l u v ∧ upperWeight t w l u v ≤ projectedWeight t w v := by
  classical
  by_cases hlt : l v < u v ∧ (v, u v) ∈ t
  · rw [upperWeight, ite_eq_left hlt.1, Set.indicator_of_mem hlt.2]
    exact ⟨hw _ hlt.2, Finset.single_le_sum (fun p hp => hw p (mem_fiber.mp hp).1)
      (mem_fiber.mpr ⟨hlt.2, rfl⟩)⟩
  · have hz : upperWeight t w l u v = 0 := by
      rcases not_and_or.mp hlt with hn | hn
      · simp [upperWeight, hn]
      · simp [upperWeight, Set.indicator_of_notMem (show (v, u v) ∉ (t : Set _) from hn)]
    rw [hz]
    exact ⟨le_rfl, Finset.sum_nonneg fun p hp => hw p (mem_fiber.mp hp).1⟩

private theorem Staircase.upper_mem_of_pos {t : Finset (V × ℝ)} {l u : V → ℝ}
    {w : V × ℝ → ℝ} {v : V} (hw : 0 < upperWeight t w l u v) :
    l v < u v ∧ (v, u v) ∈ t := by
  classical
  by_contra! hn
  rcases not_and_or.mp (show ¬ (l v < u v ∧ (v, u v) ∈ t) from fun h => hn h.1 h.2) with h | h
  · simp [upperWeight, h] at hw
  · simp [upperWeight, Set.indicator_of_notMem (show (v, u v) ∉ (t : Set _) from h)] at hw

private theorem Staircase.lower_mem_of_lt {s : Finset V} {t : Finset (V × ℝ)} {l u : V → ℝ}
    (h : Staircase s t l u) {w : V × ℝ → ℝ} {v : V} (hv : l v < u v)
    (hw : upperWeight t w l u v < projectedWeight t w v) : (v, l v) ∈ t := by
  classical
  by_contra hn
  have he (p : V × ℝ) (hp : p ∈ fiber t v) : p = (v, u v) := by
    have ⟨hpt, hpv⟩ := mem_fiber.mp hp
    have hp' := h.endpoints p hpt
    rw [hpv] at hp'
    exact Prod.ext hpv (hp'.resolve_left fun eq => by
      have hpEq : p = (v, l v) := Prod.ext hpv eq
      exact hn (hpEq ▸ hpt))
  by_cases hu : (v, u v) ∈ t
  · have hf : fiber t v = {(v, u v)} := by
      ext p
      simp only [Finset.mem_singleton]
      exact ⟨he p, fun hp => hp ▸ mem_fiber.mpr ⟨hu, rfl⟩⟩
    simp [upperWeight, hv, Set.indicator_of_mem (show (v, u v) ∈ (t : Set _) from hu),
      projectedWeight, hf] at hw
  · have hf : fiber t v = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun p hp =>
      hu (he p hp ▸ (mem_fiber.mp hp).1)
    simp [upperWeight, hv, Set.indicator_of_notMem (show (v, u v) ∉ (t : Set _) from hu),
      projectedWeight, hf] at hw

-- Moving upper weight between two vertices while preserving the total height
-- would require each vertex to precede the other in the staircase order.
private theorem Staircase.upperWeight_unique {s : Finset V} {t t' : Finset (V × ℝ)} {l u : V → ℝ}
    (h : Staircase s t l u) (h' : Staircase s t' l u) (hlu : ∀ v ∈ s, l v ≤ u v)
    {w w' : V × ℝ → ℝ} (hw : ∀ p ∈ t, 0 ≤ w p) (hw' : ∀ p ∈ t', 0 ≤ w' p)
    (hm : ∀ v ∈ s, projectedWeight t w v = projectedWeight t' w' v)
    (hy : ∑ p ∈ t, w p * p.2 = ∑ p ∈ t', w' p * p.2) :
    ∀ v ∈ s, upperWeight t w l u v = upperWeight t' w' l u v := by
  let M := upperWeight t w l u
  let M' := upperWeight t' w' l u
  have hsum (t : Finset (V × ℝ)) (w : V × ℝ → ℝ) (h : Staircase s t l u) :
      ∑ p ∈ t, w p * p.2 =
        (∑ v ∈ s, projectedWeight t w v * l v) + ∑ v ∈ s, upperWeight t w l u v * (u v - l v) := by
    rw [← sum_fibers h.projects, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => h.sum_fiber_split hlu w v Prod.snd
  rw [hsum t w h, hsum t' w' h'] at hy
  have hme := Finset.sum_congr rfl fun v hv => congrArg (· * l v) (hm v hv)
  rw [hme, add_right_inj] at hy
  change ∑ v ∈ s, M v * (u v - l v) = ∑ v ∈ s, M' v * (u v - l v) at hy
  have hmove (v : V) (hv : v ∈ s) (hlt : M v < M' v) :
      l v < u v ∧ (v, l v) ∈ t ∧ (v, u v) ∈ t' := by
    have hp := upper_mem_of_pos ((upperWeight_nonneg_le (l := l) (u := u) hw v).1.trans_lt hlt)
    have hsmall := hlt.trans_le (upperWeight_nonneg_le (l := l) (u := u) hw' v).2
    rw [← hm v hv] at hsmall
    exact ⟨hp.1, h.lower_mem_of_lt hp.1 hsmall, hp.2⟩
  have hmove' (v : V) (hv : v ∈ s) (hlt : M' v < M v) :
      l v < u v ∧ (v, l v) ∈ t' ∧ (v, u v) ∈ t := by
    have hp := upper_mem_of_pos ((upperWeight_nonneg_le (l := l) (u := u) hw' v).1.trans_lt hlt)
    have hsmall := hlt.trans_le (upperWeight_nonneg_le (l := l) (u := u) hw v).2
    rw [hm v hv] at hsmall
    exact ⟨hp.1, h'.lower_mem_of_lt hp.1 hsmall, hp.2⟩
  have impossible (v x : V) (hv : v ∈ s) (hx : x ∈ s) (hvlt : M v < M' v) (hxlt : M' x < M x) :
      False := by
    obtain ⟨hvlu, hvl, hvu⟩ := hmove v hv hvlt
    obtain ⟨hxlu, hxl, hxu⟩ := hmove' x hx hxlt
    have hxv : x ≤ v := h.ordered (v, l v) hvl (x, u x) hxu hvlu hxlu
    have hvx : v ≤ x := h'.ordered (x, l x) hxl (v, u v) hvu hxlu hvlu
    rw [le_antisymm hvx hxv] at hvlt
    exact lt_asymm hvlt hxlt
  intro v hv
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hlt
  · have hvlu := (hmove v hv hlt).1
    have hle (x : V) (hx : x ∈ s) : M x ≤ M' x :=
      le_of_not_gt fun hxlt => impossible v x hv hx hlt hxlt
    exact (ne_of_lt (Finset.sum_lt_sum
      (fun x hx => mul_le_mul_of_nonneg_right (hle x hx) (sub_nonneg.mpr (hlu x hx)))
      ⟨v, hv, mul_lt_mul_of_pos_right hlt (sub_pos.mpr hvlu)⟩)) hy
  · have hvlu := (hmove' v hv hlt).1
    have hle (x : V) (hx : x ∈ s) : M' x ≤ M x :=
      le_of_not_gt fun hxlt => impossible x v hx hv hxlt hlt
    exact (ne_of_lt (Finset.sum_lt_sum
      (fun x hx => mul_le_mul_of_nonneg_right (hle x hx) (sub_nonneg.mpr (hlu x hx)))
      ⟨v, hv, mul_lt_mul_of_pos_right hlt (sub_pos.mpr hvlu)⟩)) hy.symm

private theorem Staircase.weights_unique {s : Finset V} {t t' : Finset (V × ℝ)} {l u : V → ℝ}
    (h : Staircase s t l u) (h' : Staircase s t' l u) (hlu : ∀ v ∈ s, l v ≤ u v)
    {w w' : V × ℝ → ℝ} (hw : ∀ p ∈ t, 0 ≤ w p) (hw' : ∀ p ∈ t', 0 ≤ w' p)
    (hm : ∀ v ∈ s, projectedWeight t w v = projectedWeight t' w' v)
    (hy : ∑ p ∈ t, w p * p.2 = ∑ p ∈ t', w' p * p.2)
    (p : V × ℝ) (hp : p.1 ∈ s) :
    (t : Set (V × ℝ)).indicator w p = (t' : Set (V × ℝ)).indicator w' p := by
  classical
  let f (q : V × ℝ) : ℝ := if q = p then 1 else 0
  have he := h.sum_fiber_split hlu w p.1 f
  have he' := h'.sum_fiber_split hlu w' p.1 f
  rw [hm _ hp, h.upperWeight_unique h' hlu hw hw' hm hy _ hp, ← he'] at he
  simpa [f, mul_ite, mem_fiber, Set.indicator_apply] using he

private theorem Staircase.projectedWeight_eq [AddCommGroup V] [Module ℝ V]
    {s : Finset V} {t t' : Finset (V × ℝ)} {l u l' u' : V → ℝ}
    (h : Staircase s t l u) (h' : Staircase s t' l' u')
    (hs : AffineIndependent ℝ ((↑) : s → V))
    {w w' : V × ℝ → ℝ} (htot : ∑ p ∈ t, w p = ∑ p ∈ t', w' p)
    (hpoint : ∑ p ∈ t, w p • p = ∑ p ∈ t', w' p • p) :
    ∀ v ∈ s, projectedWeight t w v = projectedWeight t' w' v := by
  apply hs.eq_of_sum_eq_sum_subtype
  · exact (sum_fibers h.projects w).trans (htot.trans (sum_fibers h'.projects w').symm)
  · rw [sum_projectedWeight_smul h.projects w (fun x => x),
      sum_projectedWeight_smul h'.projects w' (fun x => x)]
    simpa only [map_sum, LinearMap.fst_apply, map_smul] using congrArg (LinearMap.fst ℝ V ℝ) hpoint

private theorem Staircase.affineIndependent [AddCommGroup V] [Module ℝ V]
    {s : Finset V} {t : Finset (V × ℝ)} {l u : V → ℝ}
    (h : Staircase s t l u) (hlu : ∀ v ∈ s, l v ≤ u v)
    (hs : AffineIndependent ℝ ((↑) : s → V)) :
    AffineIndependent ℝ ((↑) : t → V × ℝ) := by
  classical
  rw [affineIndependent_iff]
  intro T d hT hn p hp
  let V' : Finset (V × ℝ) := T.image Subtype.val
  have hv' : V' ⊆ t := by
    intro q hq
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hq
    exact q.property
  let delta (q : V × ℝ) : ℝ := if hq : q ∈ t then (T : Set t).indicator d ⟨q, hq⟩ else 0
  have hd (q : t) : delta q.val = (T : Set t).indicator d q := by simp [delta, q.property]
  have hdz (q : V × ℝ) (hq : q ∈ t) (hq' : q ∉ V') : delta q = 0 := by
    have hq'' : (⟨q, hq⟩ : t) ∉ T := fun hx => hq' (Finset.mem_image_of_mem Subtype.val hx)
    simp [delta, hq, hq'']
  have hsum : ∑ q ∈ t, delta q = 0 := by
    rw [← Finset.sum_subset hv' (f := delta) hdz, Finset.sum_image Subtype.val_injective.injOn]
    exact (Finset.sum_congr rfl fun q hq => by rw [hd q, Set.indicator_of_mem hq]).trans hT
  have hcomb : ∑ q ∈ t, delta q • q = 0 := by
    rw [← Finset.sum_subset hv' (f := fun q => delta q • q)
      (fun q hq hq' => by rw [hdz q hq hq', zero_smul]),
      Finset.sum_image Subtype.val_injective.injOn]
    exact (Finset.sum_congr rfl fun q hq => by rw [hd q, Set.indicator_of_mem hq]).trans hn
  let M := ∑ q ∈ t, |delta q|
  let w (q : V × ℝ) := M + delta q
  let w' (_ : V × ℝ) := M
  have hw (q : V × ℝ) (hq : q ∈ t) : 0 ≤ w q := by
    have he := Finset.single_le_sum (fun p (_ : p ∈ t) => abs_nonneg (delta p)) hq
    dsimp [w, M]
    linarith [neg_abs_le (delta q)]
  have hw' (q : V × ℝ) (_ : q ∈ t) : 0 ≤ w' q :=
    Finset.sum_nonneg fun p _ => abs_nonneg (delta p)
  have htotal : ∑ q ∈ t, w q = ∑ q ∈ t, w' q := by simp [w, w', Finset.sum_add_distrib, hsum]
  have hpoint : ∑ q ∈ t, w q • q = ∑ q ∈ t, w' q • q := by
    simp [w, w', add_smul, Finset.sum_add_distrib, hcomb]
  have hheight := congrArg (LinearMap.snd ℝ V ℝ) hpoint
  simp only [map_sum, map_smul, LinearMap.snd_apply, smul_eq_mul] at hheight
  have he := h.weights_unique h hlu hw hw' (h.projectedWeight_eq h hs htotal hpoint) hheight
    p.val (h.projects p.val p.property)
  simp only [Set.indicator_of_mem p.property, w, w', hd, Set.indicator_of_mem hp] at he
  linarith

end Staircase

section Cylinder

open SimplicialSectionBandTriangulationSpecs

variable {σ : Type*} [Fintype σ]
variable {K : SimplicialComplex ℝ (σ → ℝ)} {a b : ℝ} (D : LevelFamily K a b)

private def coordinates (s : Face K) : AffineCoordinates s.val :=
  affineCoordinates s.val (K.indep s.property)

private def vertexHeight (s : Face K) (i : Fin (D.count s + 2)) (v : (σ → ℝ)) : ℝ :=
  open Classical in
  if hv : v ∈ s.val then
    (D.level s i ⟨v, subset_convexHull ℝ _ hv⟩ : ℝ)
  else 0

private theorem vertexHeight_eq (s : Face K) (i : Fin (D.count s + 2)) {v : (σ → ℝ)}
    (hv : v ∈ s.val) :
    vertexHeight D s i v = (D.level s i ⟨v, subset_convexHull ℝ _ hv⟩ : ℝ) := by
  simp [vertexHeight, hv]

private def linearLevel (s : Face K) (i : Fin (D.count s + 2)) (x : (σ → ℝ)) : ℝ :=
  ∑ v ∈ s.val, (coordinates s).weight v x * vertexHeight D s i v

private theorem continuous_linearLevel (s : Face K) (i : Fin (D.count s + 2)) :
    Continuous (linearLevel D s i) := by
  unfold linearLevel
  exact continuous_finsetSum _ fun v _ =>
    ((coordinates s).weight v).continuous_of_finiteDimensional.mul continuous_const

private theorem monotone_linearLevel (s : Face K) {x : (σ → ℝ)} (hx : x ∈ faceHull s) :
    Monotone fun i => linearLevel D s i x := by
  intro i j hij
  exact Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left
    (by simpa only [vertexHeight_eq D s _ hv] using
      D.monotone_level s ⟨v, subset_convexHull ℝ _ hv⟩ hij) (((coordinates s).spec hx).1 v hv)

private theorem linearLevel_first (s : Face K) {x : (σ → ℝ)} (hx : x ∈ faceHull s) :
    linearLevel D s 0 x = a := by
  have he (v : (σ → ℝ)) (hv : v ∈ s.val) : vertexHeight D s 0 v = a :=
    (vertexHeight_eq D s _ hv).trans (D.first_level _ _)
  rw [linearLevel, Finset.sum_congr rfl (fun v hv => by rw [he v hv]),
    ← Finset.sum_mul, ((coordinates s).spec hx).2.1, one_mul]

private theorem linearLevel_last (s : Face K) {x : (σ → ℝ)} (hx : x ∈ faceHull s) :
    linearLevel D s (Fin.last (D.count s + 1)) x = b := by
  have he (v : (σ → ℝ)) (hv : v ∈ s.val) : vertexHeight D s (Fin.last (D.count s + 1)) v = b :=
    (vertexHeight_eq D s _ hv).trans (D.last_level _ _)
  rw [linearLevel, Finset.sum_congr rfl (fun v hv => by rw [he v hv]),
    ← Finset.sum_mul, ((coordinates s).spec hx).2.1, one_mul]

private theorem strictMono_linearLevel (s : Face K) {x : (σ → ℝ)}
    (hx : x ∈ intrinsicInterior ℝ (faceHull s)) :
    StrictMono fun i => linearLevel D s i x := by
  classical
  intro i j hij
  have hc := ((coordinates s).mem_intrinsicInterior (intrinsicInterior_subset hx)).mp hx
  obtain ⟨v, hv, hval⟩ := D.separates_at_vertex s i j (ne_of_lt hij)
  have hle (u : (σ → ℝ)) (hu : u ∈ s.val) : vertexHeight D s i u ≤ vertexHeight D s j u := by
    simpa only [vertexHeight_eq D s _ hu] using
      D.monotone_level s ⟨u, subset_convexHull ℝ _ hu⟩ hij.le
  have hvstrict : vertexHeight D s i v < vertexHeight D s j v := by
    refine lt_of_le_of_ne (hle v hv) ?_
    intro he
    apply hval
    apply Subtype.ext
    rwa [vertexHeight_eq D s _ hv, vertexHeight_eq D s _ hv] at he
  exact Finset.sum_lt_sum (fun u hu => mul_le_mul_of_nonneg_left (hle u hu) (hc u hu).le)
    ⟨v, hv, mul_lt_mul_of_pos_left hvstrict (hc v hv)⟩

private theorem linearLevel_restrict (r s : Face K) (hrs : r.val ⊆ s.val)
    (q : Fin (D.count s + 2) → Fin (D.count r + 2))
    (hq : ∀ i (x : faceHull r),
      D.level s i ⟨x.val, convexHull_mono (Finset.coe_subset.mpr hrs) x.property⟩ =
        D.level r (q i) x)
    (i : Fin (D.count s + 2)) {x : (σ → ℝ)} (hx : x ∈ faceHull r) :
    linearLevel D s i x = linearLevel D r (q i) x := by
  classical
  unfold linearLevel
  rw [← Finset.sum_subset hrs (f := fun v =>
    (coordinates s).weight v x * vertexHeight D s i v) (fun v hv hn => by
      rw [(coordinates s).restrict (coordinates r) hrs hx hv]
      simp [hn])]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [(coordinates s).restrict (coordinates r) hrs hx (hrs hv)]
  simp only [Set.indicator_of_mem hv, vertexHeight_eq D s _ (hrs hv),
    vertexHeight_eq D r _ hv]
  exact congrArg ((coordinates r).weight v x * ·)
    (congrArg Subtype.val (hq i ⟨v, subset_convexHull ℝ _ hv⟩))

private theorem exists_relativeInterior_subface (s : Face K) {x : (σ → ℝ)}
    (hx : x ∈ faceHull s) :
    ∃ r : Face K, r.val ⊆ s.val ∧ x ∈ intrinsicInterior ℝ (faceHull r) := by
  classical
  obtain ⟨r, hrs, hr, w, hw₀, hw₁, hwx⟩ := exists_positive_weights_subfinset hx
  let t : Face K := ⟨r, K.down_closed s.property hrs hr⟩
  have ht : x ∈ faceHull t :=
    Finset.mem_convexHull'.mpr ⟨w, fun v hv => (hw₀ v hv).le, hw₁, hwx⟩
  refine ⟨t, hrs, ((coordinates t).mem_intrinsicInterior ht).mpr fun v hv => ?_⟩
  have he := (coordinates t).weight_combination w hw₁ v hv
  rw [hwx] at he
  rw [he]
  exact hw₀ v hv

private theorem level_collapse_iff (s : Face K) {x : (σ → ℝ)} (hx : x ∈ faceHull s)
    (i j : Fin (D.count s + 2)) :
    linearLevel D s i x = linearLevel D s j x ↔ D.level s i ⟨x, hx⟩ = D.level s j ⟨x, hx⟩ := by
  obtain ⟨r, hrs, hrx⟩ := exists_relativeInterior_subface s hx
  obtain ⟨q, _, _, hq⟩ := D.restrict_levels r s hrs
  have hr : x ∈ faceHull r := intrinsicInterior_subset hrx
  rw [linearLevel_restrict D r s hrs q hq i hr, linearLevel_restrict D r s hrs q hq j hr]
  rw [show D.level s i ⟨x, hx⟩ = D.level r (q i) ⟨x, hr⟩ from hq i ⟨x, hr⟩]
  rw [show D.level s j ⟨x, hx⟩ = D.level r (q j) ⟨x, hr⟩ from hq j ⟨x, hr⟩]
  constructor
  · exact fun h => congrArg (fun k => D.level r k ⟨x, hr⟩) ((strictMono_linearLevel D r hrx).injective h)
  · exact fun h => congrArg (fun k => linearLevel D r k x)
      ((D.strictMono_level r ⟨x, hr⟩ hrx).injective (congrArg Subtype.val h))

private def cylinderGraph : Set ((σ → ℝ) × ℝ × ℝ) :=
  {p | ∃ (s : Face K) (hx : p.1 ∈ faceHull s),
    verticalMatch (fun i => linearLevel D s i p.1)
      (fun i => (D.level s i ⟨p.1, hx⟩ : ℝ)) p.2.1 p.2.2}

private theorem isCompact_cylinderGraph (hK : K.faces.Finite) :
    IsCompact (cylinderGraph D) := by
  classical
  let : Finite (Face K) := hK.to_subtype
  let image (s : Face K) (i j : Fin (D.count s + 2)) : Set ((σ → ℝ) × ℝ × ℝ) :=
    (fun p : faceHull s × Set.Icc (0 : ℝ) 1 =>
      (p.1.val, interpolate (linearLevel D s i p.1.val) (linearLevel D s j p.1.val) p.2.val,
        interpolate (D.level s i p.1) (D.level s j p.1) p.2.val)) '' Set.univ
  have hgraph : cylinderGraph D =
      ⋃ (s : Face K) (i : Fin (D.count s + 2)) (j : Fin (D.count s + 2))
        (_h : adjacent i j), image s i j := by
    ext p
    constructor
    · rintro ⟨s, hx, i, j, hij, t, ht, e₁, e₂⟩
      exact mem_iUnion₂.mpr ⟨s, i, mem_iUnion₂.mpr
        ⟨j, hij, ⟨(⟨p.1, hx⟩, ⟨t, ht⟩), trivial, Prod.ext rfl (Prod.ext e₁ e₂)⟩⟩⟩
    · intro hp
      rcases mem_iUnion₂.mp hp with ⟨s, i, hp⟩
      rcases mem_iUnion₂.mp hp with ⟨j, hij, ⟨⟨x, t⟩, -, rfl⟩⟩
      exact ⟨s, x.property, i, j, hij, t.val, t.property, rfl, rfl⟩
  rw [hgraph]
  apply isCompact_iUnion
  intro s
  apply isCompact_iUnion
  intro i
  apply isCompact_iUnion
  intro j
  apply isCompact_iUnion
  intro _
  let : CompactSpace (faceHull s) :=
    isCompact_iff_compactSpace.mp (s.val.finite_toSet.isCompact_convexHull ℝ)
  let : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  apply isCompact_univ.image
  have hx : Continuous (fun p : faceHull s × Set.Icc (0 : ℝ) 1 => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have ht : Continuous (fun p : faceHull s × Set.Icc (0 : ℝ) 1 => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  show Continuous (fun p : faceHull s × Set.Icc (0 : ℝ) 1 =>
      (p.1.val, interpolate (linearLevel D s i p.1.val) (linearLevel D s j p.1.val) p.2.val,
        interpolate (D.level s i p.1) (D.level s j p.1) p.2.val))
  unfold interpolate
  refine hx.prodMk (Continuous.prodMk ?_ ?_)
  · exact ((continuous_linearLevel D s i).comp hx).add
      (ht.mul (((continuous_linearLevel D s j).comp hx).sub ((continuous_linearLevel D s i).comp hx)))
  · have h (k) : Continuous (fun p : faceHull s × Set.Icc (0 : ℝ) 1 =>
        (D.level s k p.1 : ℝ)) :=
      (continuous_subtype_val.comp (D.continuous_level s k)).comp continuous_fst
    exact (h i).add (ht.mul ((h j).sub (h i)))

private def cylinder (K : SimplicialComplex ℝ (σ → ℝ)) (a b : ℝ) :
    Set ((σ → ℝ) × ℝ) := K.space ×ˢ Icc a b

private theorem match_restrict (r s : Face K) (hrs : r.val ⊆ s.val)
    {x : σ → ℝ} (hx : x ∈ faceHull r) {z w : ℝ}
    (h : verticalMatch (fun i => linearLevel D s i x)
      (fun i => (D.level s i ⟨x, convexHull_mono (Finset.coe_subset.mpr hrs) hx⟩ : ℝ)) z w) :
    verticalMatch (fun i => linearLevel D r i x)
      (fun i => (D.level r i ⟨x, hx⟩ : ℝ)) z w := by
  obtain ⟨i, j, hij, t, ht, he, he'⟩ := h
  obtain ⟨q, hqₘ, hqₛ, hq⟩ := D.restrict_levels r s hrs
  refine ⟨q i, q j, adjacent_map hqₘ hqₛ hij, t, ht, ?_, ?_⟩
  · simpa only [linearLevel_restrict D r s hrs q hq _ hx] using he
  · simpa only [hq _ ⟨x, hx⟩] using he'

private theorem graph_functional {x : σ → ℝ} {z w z' w' : ℝ}
    (h : (x, z, w) ∈ cylinderGraph D) (h' : (x, z', w') ∈ cylinderGraph D) :
    (z = z' → w = w') ∧ (w = w' → z = z') := by
  classical
  obtain ⟨s, hs, hs'⟩ := h
  obtain ⟨t, ht, ht'⟩ := h'
  have hx : x ∈ convexHull ℝ ((s.val ∩ t.val : Finset (σ → ℝ)) : Set (σ → ℝ)) :=
    by simpa only [Finset.coe_inter] using
      K.inter_subset_convexHull s.property t.property ⟨hs, ht⟩
  have hne : (s.val ∩ t.val).Nonempty := by
    by_contra! h
    rw [h, Finset.coe_empty, convexHull_empty] at hx
    exact hx
  let r : Face K := ⟨s.val ∩ t.val, K.down_closed s.property Finset.inter_subset_left hne⟩
  have hr : x ∈ faceHull r := hx
  have h₁ := match_restrict D r s Finset.inter_subset_left hr hs'
  have h₂ := match_restrict D r t Finset.inter_subset_right hr ht'
  have hc (i j : Fin (D.count r + 2)) :
      linearLevel D r i x = linearLevel D r j x ↔
        (D.level r i ⟨x, hr⟩ : ℝ) = (D.level r j ⟨x, hr⟩ : ℝ) :=
    (level_collapse_iff D r hr i j).trans Subtype.ext_iff
  exact ⟨fun he => verticalMatch_unique (monotone_linearLevel D r hr)
      (fun i j => (hc i j).mp) h₁ (he.symm ▸ h₂),
    fun he => verticalMatch_unique (D.monotone_level r ⟨x, hr⟩)
      (fun i j => (hc i j).mpr) (verticalMatch_symm.mp h₁) (he.symm ▸ verticalMatch_symm.mp h₂)⟩

private theorem graph_mem_cylinder {p : (σ → ℝ) × ℝ × ℝ} (hp : p ∈ cylinderGraph D) :
    (p.1, p.2.1) ∈ cylinder K a b ∧ (p.1, p.2.2) ∈ cylinder K a b := by
  obtain ⟨s, hx, i, j, hij, t, ht, h₁, h₂⟩ := hp
  have hb := K.convexHull_subset_space s.property hx
  have hmono := monotone_linearLevel D s hx
  have hlo : linearLevel D s 0 p.1 ≤ linearLevel D s i p.1 := hmono (Fin.zero_le i)
  have hhi : linearLevel D s j p.1 ≤ linearLevel D s (Fin.last (D.count s + 1)) p.1 :=
    hmono (Fin.le_last j)
  rw [linearLevel_first D s hx] at hlo
  rw [linearLevel_last D s hx] at hhi
  have hPL := interpolate_mem (hmono hij.1) ht
  have hAct := interpolate_mem (D.monotone_level s ⟨p.1, hx⟩ hij.1) ht
  rw [h₁] at hPL
  rw [h₂] at hAct
  exact ⟨⟨hb, hlo.trans hPL.1, hPL.2.trans hhi⟩,
    ⟨hb, (D.level s i ⟨p.1, hx⟩).property.1.trans hAct.1,
      hAct.2.trans (D.level s j ⟨p.1, hx⟩).property.2⟩⟩

private theorem exists_graph_input {x : σ → ℝ} {w : ℝ} (hp : (x, w) ∈ cylinder K a b) :
    ∃ z, (x, z, w) ∈ cylinderGraph D := by
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp hp.1
  let face : Face K := ⟨s, hs⟩
  let f (i : Fin (D.count face + 2)) := (D.level face i ⟨x, hx⟩ : ℝ)
  have hlo : f 0 ≤ w := by simpa only [f, D.first_level] using hp.2.1
  have hhi : w ≤ f (Fin.last (D.count face + 1)) := by
    simpa only [f, D.last_level] using hp.2.2
  obtain ⟨i, j, hij, hijw⟩ := exists_adjacent_bounds f hlo hhi
  obtain ⟨t, ht, he⟩ := exists_interpolate hijw
  exact ⟨interpolate (linearLevel D face i x) (linearLevel D face j x) t,
    face, hx, i, j, hij, t, ht, rfl, he⟩

private theorem exists_graph_output {x : σ → ℝ} {z : ℝ} (hp : (x, z) ∈ cylinder K a b) :
    ∃ w, (x, z, w) ∈ cylinderGraph D := by
  obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp hp.1
  let face : Face K := ⟨s, hs⟩
  let f (i : Fin (D.count face + 2)) := linearLevel D face i x
  have hlo : f 0 ≤ z := by simpa only [f, linearLevel_first D face hx] using hp.2.1
  have hhi : z ≤ f (Fin.last (D.count face + 1)) := by
    simpa only [f, linearLevel_last D face hx] using hp.2.2
  obtain ⟨i, j, hij, hijz⟩ := exists_adjacent_bounds f hlo hhi
  obtain ⟨t, ht, he⟩ := exists_interpolate hijz
  exact ⟨interpolate (D.level face i ⟨x, hx⟩) (D.level face j ⟨x, hx⟩) t,
    face, hx, i, j, hij, t, ht, he, rfl⟩

private theorem exists_cylinderHomeomorph (hK : K.faces.Finite) :
    ∃ e : cylinder K a b ≃ₜ cylinder K a b, ∀ p : cylinder K a b,
      (e p).val.1 = p.val.1 ∧ (p.val.1, p.val.2, (e p).val.2) ∈ cylinderGraph D := by
  classical
  let G := cylinderGraph D
  let C := cylinder K a b
  let toFirst (p : G) : C := ⟨(p.val.1, p.val.2.1), (graph_mem_cylinder D p.property).1⟩
  let toSecond (p : G) : C := ⟨(p.val.1, p.val.2.2), (graph_mem_cylinder D p.property).2⟩
  have hf₁ : Continuous toFirst := by
    unfold toFirst
    exact (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.fst).subtype_mk _
  have hf₂ : Continuous toSecond := by
    unfold toSecond
    exact (continuous_subtype_val.fst.prodMk continuous_subtype_val.snd.snd).subtype_mk _
  have hb₁ : Function.Bijective toFirst := by
    constructor
    · rintro ⟨⟨x, z, w⟩, h⟩ ⟨⟨x', z', w'⟩, h'⟩ he
      have hx : x = x' := congrArg (fun q : C => q.val.1) he
      have hz : z = z' := congrArg (fun q : C => q.val.2) he
      subst x' z'
      have hw : w = w' := (graph_functional D h h').1 rfl
      subst w'
      rfl
    · rintro ⟨⟨x, z⟩, h⟩
      obtain ⟨w, hw⟩ := exists_graph_output D h
      exact ⟨⟨(x, z, w), hw⟩, rfl⟩
  have hb₂ : Function.Bijective toSecond := by
    constructor
    · rintro ⟨⟨x, z, w⟩, h⟩ ⟨⟨x', z', w'⟩, h'⟩ he
      have hx : x = x' := congrArg (fun q : C => q.val.1) he
      have hw : w = w' := congrArg (fun q : C => q.val.2) he
      subst x' w'
      have hz : z = z' := (graph_functional D h h').2 rfl
      subst z'
      rfl
    · rintro ⟨⟨x, w⟩, h⟩
      obtain ⟨z, hz⟩ := exists_graph_input D h
      exact ⟨⟨(x, z, w), hz⟩, rfl⟩
  let : CompactSpace G := isCompact_iff_compactSpace.mp (isCompact_cylinderGraph D hK)
  let e₁ : G ≃ₜ C := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective toFirst hb₁) hf₁
  let e₂ : G ≃ₜ C := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective toSecond hb₂) hf₂
  refine ⟨e₁.symm.trans e₂, ?_⟩
  intro p
  let q := e₁.symm p
  have heq : toFirst q = p := e₁.apply_symm_apply p
  have hxy := congrArg (fun p : C => p.val.1) heq
  have hz := congrArg (fun p : C => p.val.2) heq
  change q.val.1 = p.val.1 at hxy
  change q.val.2.1 = p.val.2 at hz
  refine ⟨hxy, ?_⟩
  change (p.val.1, p.val.2, q.val.2.2) ∈ G
  rw [← hxy, ← hz]
  exact q.property

section Mesh

variable [LinearOrder (σ → ℝ)]

private def IsLiftedFace (t : Finset ((σ → ℝ) × ℝ)) : Prop :=
  open Classical in
  t.Nonempty ∧ ∃ (s : Face K) (i j : Fin (D.count s + 2)),
    adjacent i j ∧ t.image Prod.fst = s.val ∧
      Staircase s.val t (vertexHeight D s i) (vertexHeight D s j)

private theorem IsLiftedFace.down_closed {t r : Finset ((σ → ℝ) × ℝ)}
    (ht : IsLiftedFace D t) (hrt : r ⊆ t) (hr : r.Nonempty) :
    IsLiftedFace D r := by
  classical
  obtain ⟨_, s, i, j, hij, -, h⟩ := ht
  let proj := r.image Prod.fst
  have hproj : proj ⊆ s.val := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact h.projects p (hrt hp)
  let s' : Face K := ⟨proj, K.down_closed s.property hproj (hr.image _)⟩
  obtain ⟨q, hqₘ, hqₛ, hq⟩ := D.restrict_levels s' s hproj
  have hv (p : (σ → ℝ) × ℝ) (hp : p ∈ r) : p.1 ∈ s'.val := Finset.mem_image_of_mem _ hp
  have he (k : Fin (D.count s + 2)) (p : (σ → ℝ) × ℝ) (hp : p ∈ r) :
      vertexHeight D s k p.1 = vertexHeight D s' (q k) p.1 := by
    rw [vertexHeight_eq D s _ (hproj (hv p hp)), vertexHeight_eq D s' _ (hv p hp)]
    exact congrArg Subtype.val (hq k ⟨p.1, subset_convexHull ℝ _ (hv p hp)⟩)
  refine ⟨hr, s', q i, q j, adjacent_map hqₘ hqₛ hij, rfl, ⟨hv, ?_, ?_⟩⟩
  · intro p hp
    rw [← he i p hp, ← he j p hp]
    exact h.endpoints p (hrt hp)
  · intro p hp p' hp'
    rw [← he j p hp, ← he i p' hp']
    exact h.ordered p (hrt hp) p' (hrt hp')

omit [LinearOrder (σ → ℝ)] in
private theorem vertexHeight_mono (s : Face K) {i j : Fin (D.count s + 2)}
    (hij : i ≤ j) {v : σ → ℝ} (hv : v ∈ s.val) :
    vertexHeight D s i v ≤ vertexHeight D s j v := by
  rw [vertexHeight_eq D s _ hv, vertexHeight_eq D s _ hv]
  exact D.monotone_level s ⟨v, subset_convexHull ℝ _ hv⟩ hij

private theorem liftedFace_indep {t : Finset ((σ → ℝ) × ℝ)} (ht : IsLiftedFace D t) :
    AffineIndependent ℝ ((↑) : t → (σ → ℝ) × ℝ) := by
  obtain ⟨_, s, i, j, hij, -, h⟩ := ht
  exact h.affineIndependent (fun _ hv => vertexHeight_mono D s hij.1 hv) (K.indep s.property)

omit [LinearOrder (σ → ℝ)] in
private theorem baseFace_eq_of_mem_intrinsicInterior {s t : Face K} {x : σ → ℝ}
    (hs : x ∈ intrinsicInterior ℝ (faceHull s))
    (ht : x ∈ intrinsicInterior ℝ (faceHull t)) : s = t := by
  classical
  have hst : x ∈ convexHull ℝ ((s.val ∩ t.val : Finset (σ → ℝ)) : Set (σ → ℝ)) := by
    simpa only [Finset.coe_inter] using K.inter_subset_convexHull s.property t.property
      ⟨intrinsicInterior_subset hs, intrinsicInterior_subset ht⟩
  have hne : (s.val ∩ t.val).Nonempty := by
    by_contra! h
    rw [h, Finset.coe_empty, convexHull_empty] at hst
    exact hst
  let r : Face K := ⟨s.val ∩ t.val, K.down_closed s.property Finset.inter_subset_left hne⟩
  have pos (u : Face K) (hu : x ∈ intrinsicInterior ℝ (faceHull u))
      (hsub : r.val ⊆ u.val) : u.val ⊆ r.val := by
    intro v hv
    by_contra hn
    have hp := ((coordinates u).mem_intrinsicInterior (intrinsicInterior_subset hu)).mp hu v hv
    rw [(coordinates u).restrict (coordinates r) hsub hst hv, Set.indicator_of_notMem hn] at hp
    exact (lt_irrefl _) hp
  exact Subtype.ext (Finset.Subset.antisymm
    (fun v hv => Finset.mem_inter.mp (pos s hs Finset.inter_subset_left hv) |>.2)
    (fun v hv => Finset.mem_inter.mp (pos t ht Finset.inter_subset_right hv) |>.1))

private theorem lifted_combination {s : Face K} {t : Finset ((σ → ℝ) × ℝ)}
    {i j : Fin (D.count s + 2)} (hij : i ≤ j)
    (h : Staircase s.val t (vertexHeight D s i) (vertexHeight D s j))
    {w : (σ → ℝ) × ℝ → ℝ} (hw₀ : ∀ p ∈ t, 0 < w p) (hw₁ : ∑ p ∈ t, w p = 1)
    {p : (σ → ℝ) × ℝ} (hp : ∑ q ∈ t, w q • q = p)
    (he : t.image Prod.fst = s.val) :
    p.1 ∈ intrinsicInterior ℝ (faceHull s) ∧
      p.2 ∈ Icc (linearLevel D s i p.1) (linearLevel D s j p.1) ∧
      (p.2 = linearLevel D s i p.1 ↔ ∀ q ∈ t, q.2 = vertexHeight D s i q.1) ∧
      (p.2 = linearLevel D s j p.1 ↔ ∀ q ∈ t, q.2 = vertexHeight D s j q.1) := by
  classical
  have ⟨h₁, hc⟩ := projectedWeight_of_combination h.projects w hw₁ p hp
  have hpos (v : σ → ℝ) (hv : v ∈ s.val) : 0 < projectedWeight t w v := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (he.symm ▸ hv)
    exact projectedWeight_pos hw₀ hq
  have hcHull : p.1 ∈ faceHull s :=
    Finset.mem_convexHull'.mpr ⟨_, fun v hv => (hpos v hv).le, h₁, hc⟩
  have hcoords (v : σ → ℝ) (hv : v ∈ s.val) : (coordinates s).weight v p.1 =
      projectedWeight t w v := by
    have h := (coordinates s).weight_combination _ h₁ v hv
    rwa [hc] at h
  have hlevel (k : Fin (D.count s + 2)) : linearLevel D s k p.1 =
      ∑ v ∈ s.val, projectedWeight t w v * vertexHeight D s k v :=
    Finset.sum_congr rfl fun v hv => by rw [hcoords v hv]
  have hsecond : ∑ q ∈ t, w q * q.2 = p.2 := by
    simpa only [map_sum, map_smul, LinearMap.snd_apply, smul_eq_mul] using
      congrArg (LinearMap.snd ℝ (σ → ℝ) ℝ) hp
  have hmono (v : σ → ℝ) (hv : v ∈ s.val) :
      vertexHeight D s i v ≤ vertexHeight D s j v := vertexHeight_mono D s hij hv
  refine ⟨((coordinates s).mem_intrinsicInterior hcHull).mpr (fun v hv => hcoords v hv ▸ hpos v hv),
    ?_, ?_, ?_⟩
  · simpa only [Set.mem_Icc, hlevel, hsecond] using h.snd_bounds hmono (fun q hq => (hw₀ q hq).le)
  · simpa only [hlevel, hsecond] using h.eq_endpoints_of_sum_eq hmono hw₀
  · simpa only [hlevel, hsecond] using h.eq_upper_of_sum_eq hmono hw₀

omit [LinearOrder (σ → ℝ)] in
private theorem eq_liftedFinset_of_same_endpoint {s : Finset (σ → ℝ)}
    {t t' : Finset ((σ → ℝ) × ℝ)} (f : (σ → ℝ) → ℝ)
    (hproj : t.image Prod.fst = s) (hproj' : t'.image Prod.fst = s)
    (h : ∀ q ∈ t, q.2 = f q.1) (h' : ∀ q ∈ t', q.2 = f q.1) :
    t = t' := by
  classical
  have sub (T U : Finset ((σ → ℝ) × ℝ))
      (hp : T.image Prod.fst = U.image Prod.fst)
      (he : ∀ q ∈ T, q.2 = f q.1) (he' : ∀ q ∈ U, q.2 = f q.1) : T ⊆ U := by
    intro q hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp (hp ▸ Finset.mem_image_of_mem Prod.fst hq)
    have hEq : p = q := Prod.ext hpq (by rw [he' p hp, he q hq, hpq])
    exact hEq ▸ hp
  exact Finset.Subset.antisymm (sub t t' (hproj.trans hproj'.symm) h h')
    (sub t' t (hproj'.trans hproj.symm) h' h)

-- Positive support determines the open base face. Over that face, distinct
-- closed bands intersect only at a common endpoint level.
private theorem lifted_positive_support_unique {t t' : Finset ((σ → ℝ) × ℝ)}
    (ht : IsLiftedFace D t) (ht' : IsLiftedFace D t') {w w' : ((σ → ℝ) × ℝ) → ℝ}
    (hw₀ : ∀ q ∈ t, 0 < w q) (hw₁ : ∑ q ∈ t, w q = 1)
    (hw'₀ : ∀ q ∈ t', 0 < w' q) (hw'₁ : ∑ q ∈ t', w' q = 1)
    {p : (σ → ℝ) × ℝ} (hp : ∑ q ∈ t, w q • q = p) (hp' : ∑ q ∈ t', w' q • q = p) :
    t = t' := by
  classical
  obtain ⟨_, s, i, j, hij, hproj, h⟩ := ht
  obtain ⟨_, s', i', j', hij', hproj', h'⟩ := ht'
  obtain ⟨h₁, hb, hlo, hhi⟩ := lifted_combination D hij.1 h hw₀ hw₁ hp hproj
  obtain ⟨h₁', hb', hlo', hhi'⟩ := lifted_combination D hij'.1 h' hw'₀ hw'₁ hp' hproj'
  have hs : s = s' := baseFace_eq_of_mem_intrinsicInterior h₁ h₁'
  subst s'
  have hmono := strictMono_linearLevel D s h₁
  by_cases hsep : j ≤ i'
  · have hPL := hmono.monotone hsep
    have hJ : p.2 = linearLevel D s j p.1 := le_antisymm hb.2 (hPL.trans hb'.1)
    have hI : p.2 = linearLevel D s i' p.1 := le_antisymm (hb.2.trans hPL) hb'.1
    have hidx := hmono.injective (hJ.symm.trans hI)
    subst i'
    exact eq_liftedFinset_of_same_endpoint (vertexHeight D s j) hproj hproj' (hhi.mp hJ) (hlo'.mp hI)
  by_cases hsep' : j' ≤ i
  · have hPL := hmono.monotone hsep'
    have hJ : p.2 = linearLevel D s j' p.1 := le_antisymm hb'.2 (hPL.trans hb.1)
    have hI : p.2 = linearLevel D s i p.1 := le_antisymm (hb'.2.trans hPL) hb.1
    have hidx := hmono.injective (hJ.symm.trans hI)
    subst j'
    exact eq_liftedFinset_of_same_endpoint (vertexHeight D s i) hproj hproj' (hlo.mp hI) (hhi'.mp hJ)
  obtain ⟨hij₁, hij₂⟩ := hij
  obtain ⟨hij₃, hij₄⟩ := hij'
  have ei : i = i' := Fin.ext (by omega)
  have ej : j = j' := Fin.ext (by omega)
  subst i' j'
  have he := hp.trans hp'.symm
  have hS := congrArg (LinearMap.snd ℝ (σ → ℝ) ℝ) he
  simp only [map_sum, map_smul, LinearMap.snd_apply, smul_eq_mul] at hS
  have hweight := h.weights_unique h' (fun v hv => vertexHeight_mono D s hij₁ hv)
    (fun q hq => (hw₀ q hq).le) (fun q hq => (hw'₀ q hq).le)
    (h.projectedWeight_eq h' (K.indep s.property) (hw₁.trans hw'₁.symm) he) hS
  ext q
  constructor
  · intro hq
    by_contra hn
    have hh := hweight q (h.projects q hq)
    rw [Set.indicator_of_mem hq, Set.indicator_of_notMem hn] at hh
    exact (hw₀ q hq).ne' hh
  · intro hq
    by_contra hn
    have hh := hweight q (h'.projects q hq)
    rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hq] at hh
    exact (hw'₀ q hq).ne' hh.symm

private def liftedComplex : SimplicialComplex ℝ ((σ → ℝ) × ℝ) where
  faces := {t | IsLiftedFace D t}
  isRelLowerSet_faces := fun {_} ht => ⟨ht.1, fun {_} hsub hn => IsLiftedFace.down_closed D ht hsub hn⟩
  indep := fun {_} ht => liftedFace_indep D ht
  inter_subset_convexHull := by
    classical
    intro t t' ht ht' p hp
    obtain ⟨r, hrt, hr, w, hw₀, hw₁, hwp⟩ := exists_positive_weights_subfinset hp.1
    obtain ⟨r', hrt', hr', w', hw'₀, hw'₁, hwp'⟩ := exists_positive_weights_subfinset hp.2
    have he := lifted_positive_support_unique D
      (IsLiftedFace.down_closed D ht hrt hr) (IsLiftedFace.down_closed D ht' hrt' hr')
      hw₀ hw₁ hw'₀ hw'₁ hwp hwp'
    subst r'
    exact convexHull_mono (show (r : Set ((σ → ℝ) × ℝ)) ⊆ (t : Set _) ∩ (t' : Set _)
      from fun _ hq => ⟨hrt hq, hrt' hq⟩)
      (Finset.mem_convexHull'.mpr ⟨w, fun q hq => (hw₀ q hq).le, hw₁, hwp⟩)

private theorem lifted_faces_finite (hK : K.faces.Finite) :
    (liftedComplex D).faces.Finite := by
  classical
  let vertices (s : Face K) : Set ((σ → ℝ) × ℝ) :=
    ⋃ i : Fin (D.count s + 2), (fun v : σ → ℝ => (v, vertexHeight D s i v)) '' (s.val : Set _)
  let : Finite (Face K) := hK.to_subtype
  have hv : (⋃ s : Face K, vertices s).Finite :=
    Set.finite_iUnion fun s => Set.finite_iUnion fun i => s.val.finite_toSet.image _
  refine hv.toFinset.powerset.finite_toSet.subset ?_
  intro t ht
  apply Finset.mem_powerset.mpr
  intro p hp
  apply hv.mem_toFinset.mpr
  obtain ⟨_, s, i, j, _, _, h⟩ := ht
  refine mem_iUnion.mpr ⟨s, ?_⟩
  rcases h.endpoints p hp with h₁ | h₂
  · exact mem_iUnion.mpr ⟨i, p.1, h.projects p hp, Prod.ext rfl h₁.symm⟩
  · exact mem_iUnion.mpr ⟨j, p.1, h.projects p hp, Prod.ext rfl h₂.symm⟩

private theorem exists_staircase_cut {V : Type*} [LinearOrder V] (s : Finset V) (hs : s.Nonempty)
    (g : V → ℝ) (hg : ∀ v ∈ s, 0 ≤ g v)
    {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z ≤ ∑ v ∈ s, g v) :
    ∃ c ∈ s, (∑ v ∈ s, if v < c then g v else 0) ≤ z ∧
      z ≤ ∑ v ∈ s, if v ≤ c then g v else 0 := by
  classical
  induction s using Finset.induction_on_min generalizing z with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | insert c s hmin ih =>
    have hnc : c ∉ s := fun hc => (lt_irrefl c) (hmin c hc)
    rw [Finset.sum_insert hnc] at hz₁
    have hgs : ∀ v ∈ s, 0 ≤ g v := fun v hv => hg v (Finset.mem_insert_of_mem hv)
    by_cases hz : z ≤ g c
    · refine ⟨c, Finset.mem_insert_self _ _, ?_, ?_⟩
      · rw [Finset.sum_insert hnc, ite_eq_right (lt_irrefl c),
          Finset.sum_eq_zero (fun v hv => ite_eq_right (hmin v hv).not_gt), zero_add]
        exact hz₀
      · rw [Finset.sum_insert hnc, ite_eq_left (le_refl c),
          Finset.sum_eq_zero (fun v hv => ite_eq_right (hmin v hv).not_ge), add_zero]
        exact hz
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun h => by
        simp [h] at hz₁
        exact hz hz₁
      obtain ⟨d, hd, hlo, hhi⟩ := ih hne hgs
        (show 0 ≤ z - g c by linarith) (show z - g c ≤ ∑ v ∈ s, g v by linarith)
      refine ⟨d, Finset.mem_insert_of_mem hd, ?_, ?_⟩
      · rw [Finset.sum_insert hnc, ite_eq_left (hmin d hd)]
        linarith
      · rw [Finset.sum_insert hnc, ite_eq_left (hmin d hd).le]
        linarith

-- The staircase uses one total order of the vertices, independent of the
-- coordinatewise order on the base.
private abbrev vertexLT {V : Type*} [LinearOrder V] (v w : V) : Prop := v < w
private abbrev vertexLE {V : Type*} [LinearOrder V] (v w : V) : Prop := v ≤ w

local infix:50 " ≺ " => vertexLT
local infix:50 " ≼ " => vertexLE

private theorem vertexLE_of_lt {V : Type*} [LinearOrder V] {v w : V} (h : v ≺ w) :
    v ≼ w := le_of_lt h

private theorem vertexLE_of_not_le {V : Type*} [LinearOrder V] {v w : V} (h : ¬ v ≼ w) :
    w ≼ v := (lt_of_not_ge h).le

private theorem vertexLE_trans {V : Type*} [LinearOrder V] {v w x : V} (h : v ≼ w)
    (h' : w ≼ x) : v ≼ x := le_trans h h'

private theorem band_covered (s : Face K) {i j : Fin (D.count s + 2)} (hij : adjacent i j)
    {p : (σ → ℝ) × ℝ} (hp : p.1 ∈ faceHull s)
    (hz : p.2 ∈ Icc (linearLevel D s i p.1) (linearLevel D s j p.1)) :
    p ∈ (liftedComplex D).space := by
  classical
  let l := vertexHeight D s i
  let u := vertexHeight D s j
  let w := fun v => (coordinates s).weight v p.1
  let g := fun v => w v * (u v - l v)
  let L := linearLevel D s i p.1
  have ⟨hw₀, hw₁, hwp⟩ := (coordinates s).spec hp
  have hg (v : σ → ℝ) (hv : v ∈ s.val) : 0 ≤ g v :=
    mul_nonneg (hw₀ v hv) (sub_nonneg.mpr (vertexHeight_mono D s hij.1 hv))
  have hsum : ∑ v ∈ s.val, g v = linearLevel D s j p.1 - L := by
    simp only [g, l, u, mul_sub, Finset.sum_sub_distrib, L, linearLevel, w]
  obtain ⟨c, hc, hlo, hhi⟩ := exists_staircase_cut s.val
    (K.nonempty_of_mem_faces s.property) g hg
    (show 0 ≤ p.2 - L from sub_nonneg.mpr hz.1)
    (show p.2 - L ≤ ∑ v ∈ s.val, g v by rw [hsum]; linarith [hz.2])
  let lo (v : σ → ℝ) := (v, if v ≺ c then u v else l v)
  let hi (v : σ → ℝ) := (v, if v ≼ c then u v else l v)
  let t := s.val.image lo ∪ s.val.image hi
  have inLo (v : σ → ℝ) (hv : v ∈ s.val) : lo v ∈ t :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  have inHi (v : σ → ℝ) (hv : v ∈ s.val) : hi v ∈ t :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv)
  have pts (q : (σ → ℝ) × ℝ) (hq : q ∈ t) :
      q.1 ∈ s.val ∧ (q.2 = l q.1 ∨ q.2 = u q.1) ∧
        (q.2 < u q.1 → c ≼ q.1) ∧ (l q.1 < q.2 → q.1 ≼ c) := by
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      change v ∈ s.val ∧ ((if v ≺ c then u v else l v) = l v ∨
        (if v ≺ c then u v else l v) = u v) ∧
        ((if v ≺ c then u v else l v) < u v → c ≼ v) ∧
        (l v < (if v ≺ c then u v else l v) → v ≼ c)
      by_cases hv' : v ≺ c
      · simp [hv, hv', vertexLE_of_lt hv']
      · simp [hv, hv', le_of_not_gt hv']
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
      change v ∈ s.val ∧ ((if v ≼ c then u v else l v) = l v ∨
        (if v ≼ c then u v else l v) = u v) ∧
        ((if v ≼ c then u v else l v) < u v → c ≼ v) ∧
        (l v < (if v ≼ c then u v else l v) → v ≼ c)
      by_cases hv' : v ≼ c
      · simp [hv, hv']
      · simp [hv, hv', vertexLE_of_not_le hv']
  have he : t.image Prod.fst = s.val := by
    ext v
    constructor
    · intro hv
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      exact (pts q hq).1
    · intro hv
      exact Finset.mem_image_of_mem Prod.fst (inLo v hv)
  have hface : t ∈ (liftedComplex D).faces :=
    ⟨⟨lo c, inLo c hc⟩, s, i, j, hij, he,
      fun q hq => (pts q hq).1, fun q hq => (pts q hq).2.1,
      fun q hq r hr hl hu => vertexLE_trans ((pts r hr).2.2.2 hu) ((pts q hq).2.2.1 hl)⟩
  let Y := convexHull ℝ (t : Set ((σ → ℝ) × ℝ))
  have ha (P : (σ → ℝ) → Prop) [DecidablePred P] :
      (∑ v ∈ s.val, w v • (v, if P v then u v else l v)) =
        (p.1, L + ∑ v ∈ s.val, if P v then g v else 0) := by
    apply Prod.ext
    · change (LinearMap.fst ℝ (σ → ℝ) ℝ) (∑ v ∈ s.val, w v • (v, if P v then u v else l v)) = _
      simpa only [map_sum, LinearMap.fst_apply, map_smul] using
        (show (∑ v ∈ s.val, w v • v) = p.1 from hwp)
    · change (LinearMap.snd ℝ (σ → ℝ) ℝ) (∑ v ∈ s.val, w v • (v, if P v then u v else l v)) = _
      rw [map_sum]
      simp only [map_smul, LinearMap.snd_apply, smul_eq_mul]
      unfold L linearLevel
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : P v
      · simp [h, g, l, w]; ring
      · simp [h, l, w]
  let zlo := L + ∑ v ∈ s.val, if v ≺ c then g v else 0
  let zhi := L + ∑ v ∈ s.val, if v ≼ c then g v else 0
  have hLo : (p.1, zlo) ∈ Y := by
    rw [← ha (· ≺ c)]
    exact (convex_convexHull ℝ _).sum_mem hw₀ hw₁ fun v hv =>
      subset_convexHull ℝ _ (inLo v hv)
  have hHi : (p.1, zhi) ∈ Y := by
    rw [← ha (· ≼ c)]
    exact (convex_convexHull ℝ _).sum_mem hw₀ hw₁ fun v hv =>
      subset_convexHull ℝ _ (inHi v hv)
  have hpz : p.2 ∈ Icc zlo zhi := ⟨by dsimp [zlo]; linarith, by dsimp [zhi]; linarith⟩
  obtain ⟨θ, hθ, hval⟩ := exists_interpolate hpz
  have hseg : p ∈ segment ℝ (p.1, zlo) (p.1, zhi) := by
    have eq : (AffineMap.lineMap (p.1, zlo) (p.1, zhi) : ℝ →ᵃ[ℝ] (σ → ℝ) × ℝ) θ = p := by
      apply Prod.ext
      · simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
      · simpa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, interpolate, add_comm] using hval
    have hline := lineMap_mem_segment ℝ (p.1, zlo) (p.1, zhi) hθ
    rwa [eq] at hline
  exact SimplicialComplex.mem_space_iff.mpr
    ⟨t, hface, (convex_convexHull ℝ _).segment_subset hLo hHi hseg⟩

private theorem lifted_space :
    (liftedComplex D).space = cylinder K a b := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hpt⟩ := SimplicialComplex.mem_space_iff.mp hp
    obtain ⟨r, hrt, hr, w, hw₀, hw₁, hwp⟩ := exists_positive_weights_subfinset hpt
    obtain ⟨_, s, i, j, hij, he, h⟩ := IsLiftedFace.down_closed D ht hrt hr
    have ⟨hpi, hz, _⟩ := lifted_combination D hij.1 h hw₀ hw₁ hwp he
    have hx := intrinsicInterior_subset hpi
    have hm := monotone_linearLevel D s hx
    refine ⟨K.convexHull_subset_space s.property hx, ?_, ?_⟩
    · have hh : linearLevel D s 0 p.1 ≤ linearLevel D s i p.1 := hm (Fin.zero_le i)
      rw [linearLevel_first D s hx] at hh
      exact hh.trans hz.1
    · have hh : linearLevel D s j p.1 ≤ linearLevel D s (Fin.last (D.count s + 1)) p.1 :=
        hm (Fin.le_last j)
      rw [linearLevel_last D s hx] at hh
      exact hz.2.trans hh
  · intro hp
    obtain ⟨s, hs, hx⟩ := SimplicialComplex.mem_space_iff.mp hp.1
    let r : Face K := ⟨s, hs⟩
    let f := fun i => linearLevel D r i p.1
    have hlo : f 0 ≤ p.2 := by simpa only [f, linearLevel_first D r hx] using hp.2.1
    have hhi : p.2 ≤ f (Fin.last (D.count r + 1)) := by
      simpa only [f, linearLevel_last D r hx] using hp.2.2
    obtain ⟨i, j, hij, hz⟩ := exists_adjacent_bounds f hlo hhi
    exact band_covered D r hij hx hz

omit [LinearOrder (σ → ℝ)] in
private theorem graph_preserves_interval {s : Face K} {i j : Fin (D.count s + 2)}
    (hij : adjacent i j) {x : σ → ℝ} (hx : x ∈ faceHull s) {z w : ℝ}
    (hg : (x, z, w) ∈ cylinderGraph D)
    (hz : z ∈ Icc (linearLevel D s i x) (linearLevel D s j x)) :
    w ∈ Icc (D.level s i ⟨x, hx⟩ : ℝ) (D.level s j ⟨x, hx⟩ : ℝ) ∧
      (w = (D.level s i ⟨x, hx⟩ : ℝ) ↔ z = linearLevel D s i x) ∧
      (w = (D.level s j ⟨x, hx⟩ : ℝ) ↔ z = linearLevel D s j x) := by
  obtain ⟨θ, hθ, hval⟩ := exists_interpolate hz
  let f := fun k => linearLevel D s k x
  let g := fun k => (D.level s k ⟨x, hx⟩ : ℝ)
  let w' := interpolate (g i) (g j) θ
  have hgr : (x, z, w') ∈ cylinderGraph D := ⟨s, hx, i, j, hij, θ, hθ, hval, rfl⟩
  have he : w = w' := (graph_functional D hg hgr).1 rfl
  have hc : f i = f j ↔ g i = g j :=
    (level_collapse_iff D s hx i j).trans Subtype.ext_iff
  rw [he, ← hval]
  exact ⟨interpolate_mem (D.monotone_level s ⟨x, hx⟩ hij.1) hθ,
    ⟨interpolate_at_lower hc.mpr, interpolate_at_lower hc.mp⟩,
    ⟨interpolate_at_upper hc.mpr, interpolate_at_upper hc.mp⟩⟩

private theorem lifted_interior_compatible
    (e : (liftedComplex D).space ≃ₜ ↥(cylinder K a b))
    (he : ∀ p : (liftedComplex D).space, (e p).val.1 = p.val.1 ∧
      (p.val.1, p.val.2, (e p).val.2) ∈ cylinderGraph D)
    (t : Finset ((σ → ℝ) × ℝ)) (ht : t ∈ (liftedComplex D).faces) :
    let interior := intrinsicInterior ℝ (convexHull ℝ (t : Set ((σ → ℝ) × ℝ)))
    let image := (fun x : (liftedComplex D).space => (e x).val) '' (Subtype.val ⁻¹' interior)
    ∃ s : Face K,
      (∃ i, image ⊆ sectionGraph D s i) ∨ (∃ i, image ⊆ openBand D s i) := by
  classical
  obtain ⟨_, s, i, j, hij, hproj, h⟩ := (show IsLiftedFace D t from ht)
  let C := affineCoordinates t (liftedFace_indep D ht)
  have properties (p : (liftedComplex D).space)
      (hp : p.val ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set ((σ → ℝ) × ℝ)))) :
      ∃ hx : (e p).val.1 ∈ intrinsicInterior ℝ (faceHull s),
        let val (k : Fin (D.count s + 2)) :=
          (D.level s k ⟨(e p).val.1, intrinsicInterior_subset hx⟩ : ℝ)
        (e p).val.2 ∈ Icc (val i) (val j) ∧
          ((e p).val.2 = val i ↔ ∀ q ∈ t, q.2 = vertexHeight D s i q.1) ∧
          ((e p).val.2 = val j ↔ ∀ q ∈ t, q.2 = vertexHeight D s j q.1) := by
    have hpc := intrinsicInterior_subset hp
    have hpos := (C.mem_intrinsicInterior hpc).mp hp
    have hc := C.spec hpc
    obtain ⟨hint, hb, hlo, hhi⟩ := lifted_combination D hij.1 h hpos hc.2.1 hc.2.2 hproj
    obtain ⟨hproj_eq, hrel⟩ := he p
    have heint : (e p).val.1 ∈ intrinsicInterior ℝ (faceHull s) := hproj_eq.symm ▸ hint
    refine ⟨heint, ?_⟩
    obtain ⟨hout, hlo', hhi'⟩ := graph_preserves_interval D hij
      (intrinsicInterior_subset hint) hrel hb
    simp only [hproj_eq]
    exact ⟨hout, hlo'.trans hlo, hhi'.trans hhi⟩
  refine ⟨s, ?_⟩
  by_cases hlo : ∀ q ∈ t, q.2 = vertexHeight D s i q.1
  · refine Or.inl ⟨i, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hx, -, h⟩ := properties p hp
    exact ⟨hx, h.1.mpr hlo⟩
  by_cases hhi : ∀ q ∈ t, q.2 = vertexHeight D s j q.1
  · refine Or.inl ⟨j, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨hx, -, h⟩ := properties p hp
    exact ⟨hx, h.2.mpr hhi⟩
  have hne : i ≠ j := by
    intro heq
    subst j
    exact hlo (fun q hq => (h.endpoints q hq).elim id id)
  have hlt : i < j := lt_of_le_of_ne hij.1 hne
  have hstep := hij.2
  let k : Fin (D.count s + 1) := ⟨i.val, by omega⟩
  have hi : k.castSucc = i := Fin.ext rfl
  have hj : k.succ = j := Fin.ext (by dsimp [k]; omega)
  refine Or.inr ⟨k, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨hx, hb, hlo', hhi'⟩ := properties p hp
  refine ⟨hx, ?_, ?_⟩
  · rw [hi]
    exact lt_of_le_of_ne hb.1 (fun heq => hlo (hlo'.mp heq.symm))
  · rw [hj]
    exact lt_of_le_of_ne hb.2 (fun heq => hhi (hhi'.mp heq))

end Mesh

end Cylinder

universe u

/-- The finite staircase lift of the barycentrically interpolated levels, transported
fibre by fibre to the prescribed continuous levels. -/
theorem simplicialSectionBandTriangulation :
    SimplicialSectionBandTriangulationSpecs.SimplicialSectionBandTriangulation.{u} := by
  classical
  intro σ _ K hK a b _ D
  let : Fintype σ := Fintype.ofFinite σ
  let : LinearOrder (σ → ℝ) := linearOrderOfSTO WellOrderingRel
  obtain ⟨e, he⟩ := exists_cylinderHomeomorph D hK
  let m : (liftedComplex D).space ≃ₜ ↥(cylinder K a b) := Homeomorph.setCongr (lifted_space D)
  let f := m.trans e
  have hf (p : (liftedComplex D).space) :
      (f p).val.1 = p.val.1 ∧ (p.val.1, p.val.2, (f p).val.2) ∈ cylinderGraph D :=
    he (m p)
  exact ⟨liftedComplex D, f, lifted_faces_finite D hK, fun p => (hf p).1,
    lifted_interior_compatible D f hf⟩


end

end RepTheorySurvey.Geometric.SimplicialSectionBandTriangulation
