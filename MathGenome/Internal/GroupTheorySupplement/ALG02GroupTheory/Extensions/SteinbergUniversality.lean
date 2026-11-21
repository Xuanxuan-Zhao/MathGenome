import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.SteinbergCentrality

/-!
# Universality of the stable Steinberg extension

The spare-index proof of Weibel's *The K-book*, Chapter III, Proposition 5.5.1
uses only the Steinberg relations in the base. We apply it to lifts of the
elementary generators in the target central extension.
-/

namespace ALG02GroupTheory.Extensions.StableSteinberg

open scoped commutatorElement

section CentralKernel

variable {D G : Type*} [Group D] [Group G] {p : D →* G}
  (hker : p.ker ≤ Subgroup.center D)

include hker in
private theorem commutator_eq_of_map_eq_left {a a' b : D} (ha : p a = p a') :
    ⁅a, b⁆ = ⁅a', b⁆ := by
  let z := a * a'⁻¹
  have hz : z ∈ Subgroup.center D := hker (show p z = 1 by simp [z, ha])
  have hc (x : D) : Commute z x := (Subgroup.mem_center_iff.mp hz x).symm
  have hza : z * a' = a := by simp [z, mul_assoc]
  calc
    ⁅a, b⁆ = ⁅z * a', b⁆ := by rw [hza]
    _ = ⁅a', b⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, (hc b).commutator_eq,
        (hc ⁅a', b⁆).eq, mul_inv_cancel_right, mul_one]

include hker in
private theorem commutator_eq_of_map_eq {a a' b b' : D} (ha : p a = p a')
    (hb : p b = p b') : ⁅a, b⁆ = ⁅a', b'⁆ := by
  calc
    ⁅a, b⁆ = ⁅a', b⁆ := commutator_eq_of_map_eq_left hker ha
    _ = ⁅a', b'⁆ := by
      rw [← commutatorElement_inv b a', ← commutatorElement_inv b' a',
        commutator_eq_of_map_eq_left hker hb]

include hker in
private theorem commute_commutator_of_map_commute {a b c : D}
    (ha : Commute (p c) (p a)) (hb : Commute (p c) (p b)) :
    Commute c ⁅a, b⁆ := by
  have lift_conj {x : D} (h : Commute (p c) (p x)) : p (c * x * c⁻¹) = p x := by
    simp only [map_mul, map_inv, h.eq, mul_inv_cancel_right]
  apply mul_inv_eq_iff_eq_mul.mp
  rw [conjugate_commutatorElement]
  exact commutator_eq_of_map_eq hker (lift_conj ha) (lift_conj hb)

end CentralKernel

private theorem commutator_chain_assoc {D : Type*} [Group D] {a b c : D}
    (hac : Commute a c) (hde : Commute ⁅a, b⁆ ⁅b, c⁆)
    (hef : Commute ⁅b, c⁆ ⁅⁅a, b⁆, c⁆) :
    ⁅⁅a, b⁆, c⁆ = ⁅a, ⁅b, c⁆⁆ := by
  have hconj : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ * ⁅⁅a, b⁆, c⁆ := by
    rw [conjugate_commutatorElement, hac.eq, mul_inv_cancel_right,
      show a * b * a⁻¹ = ⁅a, b⁆ * b from conj_eq_commutatorElement_mul,
      commutatorElement_mul_left_eq_conj_mul, hde.eq, mul_inv_cancel_right]
  rw [commutatorElement_def a ⁅b, c⁆, hconj, hef.eq, mul_inv_cancel_right]

section LiftRelations

variable {R D G : Type*} [Ring R] [Group D] [Group G]
  {x : Generator R → G} (hx : SatisfiesRelations x) {p : D →* G}
  (hker : p.ker ≤ Subgroup.center D)

include hx hker in
private theorem commute_of_disjoint_lifts {g h : Generator R} {a b : D}
    (ha : p a = x g) (hb : p b = x h) (hjk : g.col ≠ h.row) (hil : g.row ≠ h.col)
    (hp : Function.Surjective p) : Commute a b := by
  let t := max (max g.row g.col) (max h.row h.col) + 1
  have hgt : g.row ≠ t := by dsimp [t]; omega
  have htg : t ≠ g.col := by dsimp [t]; omega
  have hht : h.row ≠ t := by dsimp [t]; omega
  have hth : t ≠ h.col := by dsimp [t]; omega
  obtain ⟨c, hc⟩ := hp (x ⟨g.row, t, hgt, 1⟩)
  obtain ⟨d, hd⟩ := hp (x ⟨t, g.col, htg, g.coeff⟩)
  have hcd : p ⁅c, d⁆ = p a := by
    rw [map_commutatorElement, hc, hd, ha,
      hx.2.2 g.row t g.col hgt htg g.distinct, one_mul]
  have hbc : Commute (p b) (p c) := by
    rw [hb, hc]
    exact (commutatorElement_eq_one_iff_commute.mp
      (hx.2.1 ⟨g.row, t, hgt, 1⟩ h hht.symm hil)).symm
  have hbd : Commute (p b) (p d) := by
    rw [hb, hd]
    exact (commutatorElement_eq_one_iff_commute.mp
      (hx.2.1 ⟨t, g.col, htg, g.coeff⟩ h hjk hth)).symm
  have h := commute_commutator_of_map_commute hker hbc hbd
  apply commutatorElement_eq_one_iff_commute.mp
  rw [commutator_eq_of_map_eq_left hker hcd.symm]
  exact h.symm.commutator_eq

variable {y : Generator R → D} (hy : ∀ g, p (y g) = x g)

include hx hy in
private theorem map_commutator_chain {i j k : ℕ}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (r s : R) :
    p ⁅y ⟨i, j, hij, r⟩, y ⟨j, k, hjk, s⟩⁆ = x ⟨i, k, hik, r * s⟩ := by
  rw [map_commutatorElement, hy, hy, hx.2.2]

include hx hker hy in
private theorem lift_chain_assoc (hp : Function.Surjective p) {i j k l : ℕ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) (r s t : R) :
    ⁅⁅y ⟨i, j, hij, r⟩, y ⟨j, k, hjk, s⟩⁆, y ⟨k, l, hkl, t⟩⁆ =
      ⁅y ⟨i, j, hij, r⟩, ⁅y ⟨j, k, hjk, s⟩, y ⟨k, l, hkl, t⟩⁆⁆ := by
  apply commutator_chain_assoc
  · exact commute_of_disjoint_lifts hx hker (hy _) (hy _) hjk hil hp
  · exact commute_of_disjoint_lifts hx hker
      (map_commutator_chain hx hy hij hjk hik r s)
      (map_commutator_chain hx hy hjk hkl hjl s t) hjk.symm hil hp
  · have h := map_commutator_chain hx hy hij hjk hik r s
    have hf : p ⁅⁅y ⟨i, j, hij, r⟩, y ⟨j, k, hjk, s⟩⁆, y ⟨k, l, hkl, t⟩⁆ =
        x ⟨i, l, hil, (r * s) * t⟩ := by
      rw [map_commutatorElement, h, hy, hx.2.2]
    exact commute_of_disjoint_lifts hx hker
      (map_commutator_chain hx hy hjk hkl hjl s t) hf hil.symm hjl hp

private def commutatorLift (y : Generator R → D) (g : Generator R) : D :=
  let t := max g.row g.col + 1
  ⁅y ⟨g.row, t, by dsimp [t]; omega, 1⟩, y ⟨t, g.col, by dsimp [t]; omega, g.coeff⟩⁆

include hx hy in
private theorem map_commutatorLift (g : Generator R) : p (commutatorLift y g) = x g := by
  obtain ⟨i, j, hij, r⟩ := g
  unfold commutatorLift
  rw [map_commutator_chain hx hy _ _ hij, one_mul]

include hx hker hy in
private theorem commutatorLift_eq (hp : Function.Surjective p) {i j t : ℕ}
    (hij : i ≠ j) (hit : i ≠ t) (htj : t ≠ j) (r : R) :
    commutatorLift y ⟨i, j, hij, r⟩ = ⁅y ⟨i, t, hit, 1⟩, y ⟨t, j, htj, r⟩⁆ := by
  let k := max i j + 1
  have hik : i ≠ k := by dsimp [k]; omega
  have hkj : k ≠ j := by dsimp [k]; omega
  change ⁅y ⟨i, k, hik, 1⟩, y ⟨k, j, hkj, r⟩⁆ = _
  by_cases hkt : k = t
  · subst t
    rfl
  · have hleft := map_commutator_chain hx hy hik hkt hit (1 : R) 1
    have hright := map_commutator_chain hx hy hkt htj hkj (1 : R) r
    rw [one_mul] at hleft hright
    calc
      _ = ⁅y ⟨i, k, hik, 1⟩, ⁅y ⟨k, t, hkt, 1⟩, y ⟨t, j, htj, r⟩⁆⁆ :=
        commutator_eq_of_map_eq hker rfl ((hy _).trans hright.symm)
      _ = ⁅⁅y ⟨i, k, hik, 1⟩, y ⟨k, t, hkt, 1⟩⁆, y ⟨t, j, htj, r⟩⁆ :=
        (lift_chain_assoc hx hker hy hp hik hit hij hkt hkj htj 1 1 r).symm
      _ = _ := commutator_eq_of_map_eq hker (hleft.trans (hy _).symm) rfl

include hx hker hy in
private theorem commutatorLift_satisfiesRelations (hp : Function.Surjective p) :
    SatisfiesRelations (commutatorLift y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij r s
    let t := max i j + 1
    have hit : i ≠ t := by dsimp [t]; omega
    have htj : t ≠ j := by dsimp [t]; omega
    rw [commutatorLift_eq hx hker hy hp hij hit htj r,
      commutatorLift_eq hx hker hy hp hij hit htj s,
      commutatorLift_eq hx hker hy hp hij hit htj (r + s)]
    have hsum : p (y ⟨t, j, htj, r⟩ * y ⟨t, j, htj, s⟩) = p (y ⟨t, j, htj, r + s⟩) := by
      rw [map_mul, hy, hy, hy, hx.1]
    have hc := commute_of_disjoint_lifts hx hker (hy ⟨t, j, htj, r⟩)
      (map_commutator_chain hx hy hit htj hij 1 s) hij.symm htj hp
    rw [← commutator_eq_of_map_eq hker rfl hsum, commutatorElement_mul_right_eq_mul_conj]
    have hconj := mul_inv_eq_iff_eq_mul.mpr hc.eq
    simpa only [mul_assoc] using
      congrArg (⁅y ⟨i, t, hit, 1⟩, y ⟨t, j, htj, r⟩⁆ * ·) hconj.symm
  · intro g h hjk hil
    exact (commute_of_disjoint_lifts hx hker (map_commutatorLift hx hy g)
      (map_commutatorLift hx hy h) hjk hil hp).commutator_eq
  · intro i j k hij hjk hik r s
    let t := max (max i j) k + 1
    have hit : i ≠ t := by dsimp [t]; omega
    have htj : t ≠ j := by dsimp [t]; omega
    have htk : t ≠ k := by dsimp [t]; omega
    rw [commutatorLift_eq hx hker hy hp hij hit htj r,
      commutatorLift_eq hx hker hy hp hik hit htk (r * s)]
    calc
      _ = ⁅⁅y ⟨i, t, hit, 1⟩, y ⟨t, j, htj, r⟩⁆, y ⟨j, k, hjk, s⟩⁆ :=
        commutator_eq_of_map_eq hker rfl ((map_commutatorLift hx hy _).trans (hy _).symm)
      _ = ⁅y ⟨i, t, hit, 1⟩, ⁅y ⟨t, j, htj, r⟩, y ⟨j, k, hjk, s⟩⁆⁆ :=
        lift_chain_assoc hx hker hy hp hit hij hik htj htk hjk 1 r s
      _ = _ := commutator_eq_of_map_eq hker rfl
        ((map_commutator_chain hx hy htj hjk htk r s).trans (hy _).symm)

end LiftRelations

universe u v w t

/-- The uniquely determined lift to any central extension of the stable elementary group. -/
theorem existsUnique_steinbergHomOver (R : Type u) [Ring R]
    {N : Type v} {D : Type w} [Group N] [Group D]
    (T : GroupExtension N D (Elementary R)) (hT : IsCentralExtension T) :
    ∃! f : Steinberg R →* D, T.rightHom.comp f = toElementary := by
  have hker := (isCentralExtension_iff_ker_le_center T).mp hT
  choose y hy using fun g : Generator R => T.rightHom_surjective (elementary g)
  let h := commutatorLift_satisfiesRelations elementary_satisfiesRelations hker hy
    T.rightHom_surjective
  let f := lift h
  refine ⟨f, hom_ext (fun g => ?_), fun φ hφ => ?_⟩
  · change T.rightHom (lift h (generator g)) = toElementary (generator g)
    rw [lift_generator, toElementary_generator]
    exact map_commutatorLift elementary_satisfiesRelations hy g
  · apply hom_ext
    rintro ⟨i, j, hij, r⟩
    let k := max i j + 1
    have hik : i ≠ k := by dsimp [k]; omega
    have hkj : k ≠ j := by dsimp [k]; omega
    have hgen := (steinberg_satisfiesRelations (R := R)).2.2 i k j hik hkj hij 1 r
    rw [one_mul] at hgen
    have hφg (g : Generator R) : T.rightHom (φ (generator g)) = T.rightHom (y g) := by
      rw [hy, ← toElementary_generator]
      exact DFunLike.congr_fun hφ (generator g)
    change φ (generator ⟨i, j, hij, r⟩) = lift h (generator ⟨i, j, hij, r⟩)
    rw [lift_generator, ← hgen, map_commutatorElement]
    exact commutator_eq_of_map_eq hker (hφg _) (hφg _)

/-- The stable Steinberg extension is the universal central extension of the stable
elementary group over any associative unital ring. -/
theorem steinbergExtension_isUniversal (R : Type u) [Ring R] :
    IsUniversalCentralExtension.{u, u, u, t} (steinbergExtension R) := by
  refine ⟨steinbergExtension_isCentral R, fun T hT => ?_⟩
  exact existsUnique_steinbergHomOver R T hT

end ALG02GroupTheory.Extensions.StableSteinberg
