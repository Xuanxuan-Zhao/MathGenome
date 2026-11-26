import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Geometry.AxisSplitting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Geometry.GeometricSemisimplicity
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Geometry.FlatTorus

namespace LinearAlgebraicGroups.Geometry

open Set
open scoped Pointwise

universe u v

noncomputable section

private def ProperIsometryAction {G : Type*} [Group G] {X : Type*} [MetricSpace X]
    (ρ : G →* (X ≃ᵢ X)) : Prop :=
  ∀ K : Set X, IsCompact K → {g : G | ∃ x ∈ K, ρ g x ∈ K}.Finite

private theorem minset_iff_minimizes {X : Type*} [MetricSpace X] {a : X ≃ᵢ X} {x : X} :
    x ∈ minset a ↔ ∀ y : X, dist x (a x) ≤ dist y (a y) := by
  let : Nonempty X := ⟨x⟩
  have hb : BddBelow (range fun y : X => dist y (a y)) := ⟨0, by
    rintro _ ⟨y, rfl⟩
    exact dist_nonneg⟩
  change dist x (a x) = (⨅ y : X, dist y (a y)) ↔ _
  exact ⟨fun h y => h.le.trans (ciInf_le hb y),
    fun h => le_antisymm (le_ciInf h) (ciInf_le hb x)⟩

private theorem eq_one_of_fixed {G : Type*} [Group G] [IsMulTorsionFree G]
    {X : Type*} [MetricSpace X] {ρ : G →* (X ≃ᵢ X)} (hp : ProperIsometryAction ρ)
    {a : G} {x : X} (hx : ρ a x = x) : a = 1 := by
  by_contra ha
  have hi : Function.Injective (fun n : ℤ => a ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr (mt (isOfFinOrder_iff_eq_one a).mp ha)
  have hs := hp {x} (isCompact_singleton (x := x))
  let S : Subgroup G :=
    { carrier := {g | ρ g x = x}
      one_mem' := by simp
      mul_mem' := by
        intro b c hb hc
        change ρ (b * c) x = x
        rw [map_mul, IsometryEquiv.mul_apply, show ρ c x = x from hc]
        exact hb
      inv_mem' := by
        intro b hb
        change ρ b⁻¹ x = x
        rw [map_inv]
        calc
          (ρ b)⁻¹ x = (ρ b)⁻¹ (ρ b x) := congrArg (fun e => (ρ b)⁻¹ e) (Eq.symm hb)
          _ = x := (ρ b).symm_apply_apply x }
  have hf (n : ℤ) : ρ (a ^ n) x = x := S.zpow_mem (show a ∈ S from hx) n
  have hsubset : range (fun n : ℤ => a ^ n) ⊆ {g : G | ∃ y ∈ ({x} : Set X), ρ g y ∈ ({x} : Set X)} := by
    rintro _ ⟨n, rfl⟩
    exact ⟨x, mem_singleton _, mem_singleton_iff.mpr (hf n)⟩
  exact (infinite_range_of_injective hi) (hs.subset hsubset)

/-- Action coordinates obtained from the axis centralizer splitting. -/
private theorem axisActionCoordinates {G : Type*} [CommGroup G]
    {X Z : Type*} [MetricSpace X] [MetricSpace Z] [Nonempty Z]
    (ρ : G →* (X ≃ᵢ X)) (a : G)
    (e : EuclideanProduct Z ℝ ≃ᵢ minset (ρ a))
    (he : ∀ (b : X ≃ᵢ X), Function.Commute (ρ a) b →
      ∃ (f : Z ≃ᵢ Z) (t : ℝ), ∀ p,
        b (e p) = (e (WithLp.toLp 2 (f p.fst, p.snd + t)) : X)) :
    ∃ (φ : G →* (Z ≃ᵢ Z)) (τ : G →* Multiplicative ℝ), ∀ g z t,
      ρ g (e (WithLp.toLp 2 (z, t))) =
        (e (WithLp.toLp 2 (φ g z, t + (τ g).toAdd)) : X) := by
  have h g := he (ρ g) (fun x => by
    change (ρ a * ρ g) x = (ρ g * ρ a) x
    rw [← map_mul, ← map_mul, mul_comm a g])
  choose f t ht using h
  have heq {g : G} {f' : Z ≃ᵢ Z} {t' : ℝ}
      (h' : ∀ z, ρ g (e (WithLp.toLp 2 (z, 0))) =
          (e (WithLp.toLp 2 (f' z, t')) : X)) : f g = f' ∧ t g = t' := by
    have hp (z : Z) : WithLp.toLp 2 (f g z, t g) = WithLp.toLp 2 (f' z, t') := by
      have hz : ρ g (e (WithLp.toLp 2 (z, 0))) =
          (e (WithLp.toLp 2 (f g z, t g)) : X) := by
        simpa using ht g (WithLp.toLp 2 (z, 0))
      exact e.injective (Subtype.ext (hz.symm.trans (h' z)))
    exact ⟨IsometryEquiv.ext fun z => congrArg WithLp.fst (hp z),
      congrArg WithLp.snd (hp (Classical.choice ‹Nonempty Z›))⟩
  have h1 := heq (g := 1) (f' := 1) (t' := 0) (by simp)
  have hmul (g k : G) : f (g * k) = f g * f k ∧ t (g * k) = t k + t g := by
    apply heq
    intro z
    rw [map_mul, IsometryEquiv.mul_apply]
    have hk := ht k (WithLp.toLp 2 (z, 0))
    have hg := ht g (WithLp.toLp 2 (f k z, t k))
    simpa using (congrArg (ρ g) (show ρ k (e (WithLp.toLp 2 (z, 0))) =
      (e (WithLp.toLp 2 (f k z, t k)) : X) by simpa using hk)).trans hg
  exact ⟨{ toFun := f, map_one' := h1.1, map_mul' := fun g k => (hmul g k).1 },
    { toFun := fun g => Multiplicative.ofAdd (t g), map_one' := h1.2,
      map_mul' := fun g k => (hmul g k).2.trans (add_comm _ _) },
    fun g z s => ht g (WithLp.toLp 2 (z, s))⟩

private theorem minset_axisCoordinates {G : Type*} [CommGroup G]
    {X Z : Type*} [MetricSpace X] [CompleteSpace X] [MetricSpace Z] (hX : CAT0 X)
    (ρ : G →* (X ≃ᵢ X)) (a : G) (ha : IsSemisimple (ρ a))
    (e : EuclideanProduct Z ℝ ≃ᵢ minset (ρ a))
    (φ : G →* (Z ≃ᵢ Z)) (τ : G →* Multiplicative ℝ)
    (he : ∀ g z t, ρ g (e (WithLp.toLp 2 (z, t))) =
      (e (WithLp.toLp 2 (φ g z, t + (τ g).toAdd)) : X))
    (hs : ∀ g, IsSemisimple (ρ g)) (g : G) :
    (∀ z t, (e (WithLp.toLp 2 (z, t)) : X) ∈ minset (ρ g) ↔ z ∈ minset (φ g)) ∧
      IsSemisimple (φ g) := by
  have hd (z z' : Z) (t t' : ℝ) :
      dist (e (WithLp.toLp 2 (z, t)) : X) (ρ g (e (WithLp.toLp 2 (z, t)))) ≤
        dist (e (WithLp.toLp 2 (z', t')) : X) (ρ g (e (WithLp.toLp 2 (z', t')))) ↔
      dist z (φ g z) ≤ dist z' (φ g z') := by
    simp only [he, ← Subtype.dist_eq, e.isometry.dist_eq, euclideanProduct_dist,
      WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sub_add_cancel_left,
      abs_neg, Real.sqrt_le_sqrt_iff (add_nonneg (sq_nonneg _) (sq_nonneg _)),
      add_le_add_iff_right]
    exact ⟨fun h => le_of_sq_le_sq h dist_nonneg, fun h => pow_le_pow_left₀ dist_nonneg h 2⟩
  obtain ⟨x, hx⟩ := hs g
  have hcomm : Function.Commute (ρ a) (ρ g) := fun x => by
    change (ρ a * ρ g) x = (ρ g * ρ a) x
    rw [← map_mul, ← map_mul, mul_comm a g]
  obtain ⟨hp, hq⟩ := hX.nearestPoint_minset_mem_minset (ρ a) (ρ g) ha hcomm hx
  obtain ⟨p, hp'⟩ := e.surjective ⟨nearestPoint (minset (ρ a)) x, hp⟩
  have hq' : (e (WithLp.toLp 2 (p.fst, p.snd)) : X) ∈ minset (ρ g) := by
    have hpe : WithLp.toLp 2 (p.fst, p.snd) = p := rfl
    rwa [hpe, hp']
  have hf (z : Z) (t : ℝ) (hz : (e (WithLp.toLp 2 (z, t)) : X) ∈ minset (ρ g)) :
      z ∈ minset (φ g) :=
    minset_iff_minimizes.mpr fun z' =>
      (hd z z' t 0).mp (minset_iff_minimizes.mp hz _)
  refine ⟨fun z t => ⟨hf z t, fun hz => ?_⟩, ⟨p.fst, hf _ _ hq'⟩⟩
  refine minset_iff_minimizes.mpr fun y => ?_
  exact ((hd z p.fst t p.snd).mpr (minset_iff_minimizes.mp hz _)).trans
    (minset_iff_minimizes.mp hq' y)

/-- Normalize the line coordinate of each lift into a single compact interval. -/
private theorem proper_axisQuotient {G H : Type*} [Group G] [Group H]
    {X Z : Type*} [MetricSpace X] [MetricSpace Z]
    (ρ : G →* (X ≃ᵢ X)) (hρ : ProperIsometryAction ρ)
    (a : G) (e : EuclideanProduct Z ℝ ≃ᵢ minset (ρ a))
    (φ : G →* (Z ≃ᵢ Z)) (τ : G →* Multiplicative ℝ)
    (he : ∀ g z t, ρ g (e (WithLp.toLp 2 (z, t))) =
      (e (WithLp.toLp 2 (φ g z, t + (τ g).toAdd)) : X))
    (ha : φ a = 1) (hL : 0 < (τ a).toAdd)
    (π : G →* H) (σ : H →* G) (hπa : π a = 1)
    (hπσ : ∀ g, π (σ g) = g) :
    ProperIsometryAction (φ.comp σ) := by
  intro K hK
  let L : ℝ := (τ a).toAdd
  let lift (g : H) : G := σ g * a ^ (-⌊(τ (σ g)).toAdd / L⌋ : ℤ)
  have hleft (g) : π (lift g) = g := by simp [lift, hπσ, hπa]
  have hφ (g) : φ (lift g) = φ (σ g) := by simp [lift, ha]
  have ht (g) : (τ (lift g)).toAdd = (τ (σ g)).toAdd - (↑⌊(τ (σ g)).toAdd / L⌋ : ℝ) * L := by
    simp only [lift, map_mul, map_zpow]
    change (τ (σ g)).toAdd + ((-⌊(τ (σ g)).toAdd / L⌋ : ℤ) • L) = _
    simp [zsmul_eq_mul, sub_eq_add_neg]
  let F : Z × ℝ → X := fun p => e (WithLp.toLp 2 p)
  have hF : Continuous F := isometry_subtype_coe.continuous.comp
    (e.isometry.continuous.comp (WithLp.prod_continuous_toLp 2 Z ℝ))
  let C := F '' (K ×ˢ Icc 0 L)
  have hC : IsCompact C := (hK.prod isCompact_Icc).image hF
  apply (hρ C hC |>.image π).subset
  rintro g ⟨z, hz, hz'⟩
  refine ⟨lift g, ⟨F (z, 0), ⟨(z, 0), ⟨hz, ⟨le_rfl, hL.le⟩⟩, rfl⟩, ?_⟩, hleft g⟩
  have ht' : (τ (lift g)).toAdd ∈ Icc 0 L := by
    rw [ht]
    exact ⟨Int.sub_floor_div_mul_nonneg _ hL, (Int.sub_floor_div_mul_lt _ hL).le⟩
  refine ⟨(φ (σ g) z, (τ (lift g)).toAdd), ⟨hz', ht'⟩, ?_⟩
  simp only [F, he, hφ, zero_add]

private abbrev vectorCons {R : Type*} {r : ℕ} (x : R) (v : Fin r → R) :
    Fin (r + 1) → R := Fin.cons x v

private abbrev IntegerGroup (r : ℕ) := Multiplicative (Fin r → ℤ)
private abbrev Euclidean (r : ℕ) := EuclideanSpace ℝ (Fin r)

private def headGenerator (r : ℕ) : IntegerGroup (r + 1) :=
  Multiplicative.ofAdd (vectorCons 1 0)

private def tailHom (r : ℕ) : IntegerGroup (r + 1) →* IntegerGroup r where
  toFun g := Multiplicative.ofAdd (Fin.tail g.toAdd)
  map_one' := rfl
  map_mul' _ _ := rfl

private def tailSection (r : ℕ) : IntegerGroup r →* IntegerGroup (r + 1) where
  toFun g := Multiplicative.ofAdd (vectorCons 0 g.toAdd)
  map_one' := by
    change vectorCons (0 : ℤ) (0 : Fin r → ℤ) = 0
    ext i
    exact Fin.cases rfl (fun _ => rfl) i
  map_mul' g h := by
    change vectorCons (0 : ℤ) (g.toAdd + h.toAdd) = vectorCons 0 g.toAdd + vectorCons 0 h.toAdd
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

private theorem headGenerator_ne_one (r : ℕ) : headGenerator r ≠ 1 := by
  intro h
  have := congrArg (fun g : IntegerGroup (r + 1) => g.toAdd 0) h
  simp [headGenerator] at this

private theorem tailHom_headGenerator (r : ℕ) : tailHom r (headGenerator r) = 1 := by
  change Fin.tail (vectorCons (1 : ℤ) (0 : Fin r → ℤ)) = 0
  funext i
  simp

private theorem tailHom_tailSection (r : ℕ) (g : IntegerGroup r) :
    tailHom r (tailSection r g) = g := by
  change Fin.tail (vectorCons (0 : ℤ) g.toAdd) = g.toAdd
  simp

private theorem head_tail_decomposition (r : ℕ) (g : IntegerGroup (r + 1)) :
    headGenerator r ^ (g.toAdd 0) * tailSection r (tailHom r g) = g := by
  change g.toAdd 0 • (vectorCons (1 : ℤ) (0 : Fin r → ℤ)) + vectorCons 0 (Fin.tail g.toAdd) = g.toAdd
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.tail]

private def euclideanHead (r : ℕ) :
    EuclideanProduct (Euclidean r) ℝ ≃ᵢ Euclidean (r + 1) where
  toFun p := WithLp.toLp 2 (vectorCons p.snd (WithLp.ofLp p.fst))
  invFun x := WithLp.toLp 2 (WithLp.toLp 2 (Fin.tail (WithLp.ofLp x)), x 0)
  left_inv p := by
    change WithLp.toLp 2 (WithLp.toLp 2 (Fin.tail (vectorCons p.snd (WithLp.ofLp p.fst))),
      vectorCons p.snd (WithLp.ofLp p.fst) 0) = p
    simp only [vectorCons, Fin.tail_cons, Fin.cons_zero]
    rfl
  right_inv x := congrArg (WithLp.toLp 2) (Fin.cons_self_tail (WithLp.ofLp x))
  isometry_toFun := Isometry.of_dist_eq fun p q => by
    rw [euclideanProduct_dist]
    apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
      EuclideanSpace.dist_sq_eq, Fin.sum_univ_succ, EuclideanSpace.dist_sq_eq, Real.dist_eq]
    simp only [Fin.cons_zero, Fin.cons_succ, Real.dist_eq, sq_abs]
    exact add_comm _ _

private theorem euclideanHead_add (r : ℕ) (p q : EuclideanProduct (Euclidean r) ℝ) :
    euclideanHead r (p + q) = euclideanHead r p + euclideanHead r q := by
  apply (WithLp.equiv 2 (Fin (r + 1) → ℝ)).injective
  change vectorCons (p.snd + q.snd) (WithLp.ofLp p.fst + WithLp.ofLp q.fst) =
    vectorCons p.snd (WithLp.ofLp p.fst) + vectorCons q.snd (WithLp.ofLp q.fst)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

private def euclideanTranslationHom {G : Type*} [Group G] (r : ℕ)
    (f : G →* Multiplicative (Euclidean r)) (t : G →* Multiplicative ℝ) :
    G →* Multiplicative (Euclidean (r + 1)) where
  toFun g := Multiplicative.ofAdd (euclideanHead r (WithLp.toLp 2 ((f g).toAdd, (t g).toAdd)))
  map_one' := by
    simp only [map_one]
    change euclideanHead r 0 = 0
    have h := euclideanHead_add r 0 0
    rw [zero_add] at h
    exact (add_left_cancel (h.symm.trans (add_zero _).symm) : euclideanHead r 0 = 0)
  map_mul' g h := by
    simp only [map_mul]
    change euclideanHead r (WithLp.toLp 2 ((f g).toAdd, (t g).toAdd) +
        WithLp.toLp 2 ((f h).toAdd, (t h).toAdd)) = _
    exact euclideanHead_add _ _ _

private theorem flatTorus_splitting (r : ℕ) {X : Type u} [MetricSpace X] [CompleteSpace X]
    (hX : CAT0 X) (ρ : IntegerGroup r →* (X ≃ᵢ X)) (hρ : ProperIsometryAction ρ)
    (hs : ∀ g, IsSemisimple (ρ g)) :
    ∃ (Y : Type u) (_ : MetricSpace Y), CAT0 Y ∧ CompleteSpace Y ∧
      ∃ (e : EuclideanProduct Y (Euclidean r) ≃ᵢ commonMinset ρ)
        (τ : IntegerGroup r →* Multiplicative (Euclidean r)),
        ∀ g y t, ρ g (e (WithLp.toLp 2 (y, t))) =
          (e (WithLp.toLp 2 (y, t + (τ g).toAdd)) : X) := by
  induction r generalizing X with
  | zero =>
    have hg (g : IntegerGroup 0) : g = 1 := Subsingleton.elim _ _
    have hbase : commonMinset ρ = univ := by
      ext x
      simp only [commonMinset, mem_iInter, mem_univ, iff_true]
      intro g
      rw [hg g, map_one]
      apply minset_iff_minimizes.mpr
      intro y
      simp
    let h : X ≃ᵢ commonMinset ρ :=
      { toFun x := ⟨x, hbase.symm ▸ mem_univ x⟩
        invFun := Subtype.val
        left_inv _ := rfl
        right_inv _ := Subtype.ext rfl
        isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
    refine ⟨X, inferInstance, hX, inferInstance,
      (IsometryEquiv.withLpProdUnique 2 X (Euclidean 0)).trans h, 1, ?_⟩
    intro g y t
    simp [hg g]
  | succ r ih =>
    let a := headGenerator r
    have hL : 0 < translationLength (ρ a) := by
      obtain ⟨x, hx⟩ := hs a
      change dist x (ρ a x) = translationLength (ρ a) at hx
      rw [← hx, dist_pos]
      exact fun h => headGenerator_ne_one r (eq_one_of_fixed hρ h.symm)
    obtain ⟨c, _, _, _, hZ, hcomplete, e, _, _, _, ha, he⟩ :=
      hX.axis_minset_splitting (ρ a) (hs a) hL
    let Z := axisCrossSection (ρ a) c
    let : CompleteSpace Z := hcomplete
    let : Nonempty Z := hZ.1.1
    obtain ⟨φ, τ, hact⟩ := axisActionCoordinates ρ a e he
    have hgen (z : Z) :
        WithLp.toLp 2 (φ a z, (τ a).toAdd) = WithLp.toLp 2 (z, translationLength (ρ a)) := by
      apply e.injective
      apply Subtype.ext
      have h := (hact a z 0).symm.trans (ha (WithLp.toLp 2 (z, 0)))
      simpa only [WithLp.toLp_fst, WithLp.toLp_snd, zero_add] using h
    have hφa : φ a = 1 := IsometryEquiv.ext fun z => congrArg WithLp.fst (hgen z)
    have hτa : (τ a).toAdd = translationLength (ρ a) :=
      congrArg WithLp.snd (hgen (Classical.choice ‹Nonempty Z›))
    let π := tailHom r
    let σ := tailSection r
    let ψ := φ.comp σ
    have hφ (g) : φ g = ψ (π g) := by
      calc
        φ g = φ (a ^ (g.toAdd 0) * σ (π g)) := congrArg φ (head_tail_decomposition r g).symm
        _ = ψ (π g) := by simp [hφa, ψ]
    have hm := minset_axisCoordinates hX ρ a (hs a) e φ τ hact hs
    have hψ : ProperIsometryAction ψ :=
      proper_axisQuotient ρ hρ a e φ τ hact hφa (hτa ▸ hL) π σ
        (tailHom_headGenerator r) (tailHom_tailSection r)
    obtain ⟨Y, mY, hY, hYcomplete, d, υ, hd⟩ :=
      ih hZ ψ hψ (fun g => (hm (σ g)).2)
    have hmem (z : Z) (t : ℝ) :
        (e (WithLp.toLp 2 (z, t)) : X) ∈ commonMinset ρ ↔ z ∈ commonMinset ψ := by
      simp only [commonMinset, mem_iInter]
      exact ⟨fun h g => (hm (σ g)).1 z t |>.mp (h (σ g)),
        fun h g => (hm g).1 z t |>.mpr (hφ g ▸ h (π g))⟩
    let F (p : EuclideanProduct (commonMinset ψ) ℝ) : commonMinset ρ :=
      ⟨e (WithLp.toLp 2 ((p.fst : Z), p.snd)), (hmem _ _).mpr p.fst.2⟩
    have hF : Isometry F := Isometry.of_dist_eq fun p q => by
      change dist (e (WithLp.toLp 2 ((p.fst : Z), p.snd))) (e (WithLp.toLp 2 ((q.fst : Z), q.snd))) = _
      rw [e.isometry.dist_eq, euclideanProduct_dist, euclideanProduct_dist]
      rfl
    have hFs : Function.Surjective F := by
      intro x
      obtain ⟨p, hp⟩ := e.surjective ⟨x, mem_iInter.mp x.2 a⟩
      have hpx : (e (WithLp.toLp 2 (p.fst, p.snd)) : X) = x := congrArg Subtype.val hp
      have hpZ := (hmem p.fst p.snd).mp (hpx.symm ▸ x.2)
      exact ⟨WithLp.toLp 2 (⟨p.fst, hpZ⟩, p.snd), Subtype.ext hpx⟩
    let m : EuclideanProduct (commonMinset ψ) ℝ ≃ᵢ commonMinset ρ :=
      ⟨Equiv.ofBijective F ⟨hF.injective, hFs⟩, hF⟩
    let E : EuclideanProduct Y (Euclidean (r + 1)) ≃ᵢ commonMinset ρ :=
      (IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl Y) (euclideanHead r).symm).trans
        ((IsometryEquiv.withLpProdAssoc 2 Y (Euclidean r) ℝ).symm.trans
          ((IsometryEquiv.withLpProdCongr 2 d (IsometryEquiv.refl ℝ)).trans m))
    let w := euclideanTranslationHom r (υ.comp π) τ
    refine ⟨Y, mY, hY, hYcomplete, E, w, ?_⟩
    intro g y q
    obtain ⟨p, rfl⟩ := (euclideanHead r).surjective q
    have hE (x : Euclidean r) (t : ℝ) :
        (E (WithLp.toLp 2 (y, euclideanHead r (WithLp.toLp 2 (x, t)))) : X) =
          (e (WithLp.toLp 2 (((d (WithLp.toLp 2 (y, x))) : Z), t)) : X) := by
      simp [E, F, m, IsometryEquiv.trans_apply]
      rfl
    have hw :
        euclideanHead r (WithLp.toLp 2 (p.fst, p.snd)) + (w g).toAdd =
          euclideanHead r (WithLp.toLp 2
            (p.fst + (υ (π g)).toAdd, p.snd + (τ g).toAdd)) :=
      (euclideanHead_add r p (WithLp.toLp 2 ((υ (π g)).toAdd, (τ g).toAdd))).symm
    change ρ g (E (WithLp.toLp 2 (y, euclideanHead r (WithLp.toLp 2 (p.fst, p.snd))))) =
      (E (WithLp.toLp 2 (y, euclideanHead r (WithLp.toLp 2 (p.fst, p.snd)) + (w g).toAdd)) : X)
    rw [hE, hw, hE, hact, hφ, hd]

open Metric

/-- A locally finite integer translation group of the full rank is generated by
a real basis over the integers. -/
private theorem lattice_basis (r : ℕ) (τ : IntegerGroup r →* Multiplicative (Euclidean r))
    (hτ : Function.Injective τ) (hfinite : {g | (τ g).toAdd ∈ closedBall 0 1}.Finite) :
    ∃ b : Module.Basis (Fin r) ℝ (Euclidean r),
      range (fun g => (τ g).toAdd) = (Submodule.span ℤ (range b) : Set (Euclidean r)) := by
  let T : (Fin r → ℤ) →+ Euclidean r := MonoidHom.toAdditiveRight τ
  let L := T.range.toIntSubmodule
  have hL : (L : Set (Euclidean r)) = range (fun g => (τ g).toAdd) := rfl
  have hfL : ((L : Set (Euclidean r)) ∩ closedBall 0 1).Finite := by
    rw [hL]
    apply (hfinite.image fun g => (τ g).toAdd).subset
    rintro _ ⟨⟨g, rfl⟩, hg⟩
    exact ⟨g, hg, rfl⟩
  let S := ((L : Set (Euclidean r)) ∩ closedBall 0 1) \ {0}
  have hS : S.Finite := hfL.sdiff
  have hdisc : DiscreteTopology L := by
    apply discreteTopology_iff_isOpen_singleton_zero.mpr
    refine ⟨ball 0 1 \ S, isOpen_ball.sdiff hS.isClosed, ?_⟩
    ext x
    change ((x : Euclidean r) ∈ ball 0 1 ∧ (x : Euclidean r) ∉ S) ↔ x ∈ ({0} : Set L)
    rw [mem_singleton_iff]
    constructor
    · rintro ⟨hb, hx⟩
      by_contra hn
      exact hx ⟨⟨x.2, ball_subset_closedBall hb⟩, fun h => hn (Subtype.ext h)⟩
    · rintro rfl
      simp [S]
  let f : (Fin r → ℤ) →+ L := T.codRestrict L fun g => ⟨g, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun g k h => hτ (congrArg Subtype.val h), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := (show x ∈ T.range from hx)
    exact ⟨g, rfl⟩
  let F : (Fin r → ℤ) ≃ₗ[ℤ] L := (AddEquiv.ofBijective f hf).toIntLinearEquiv
  have hfull : Submodule.span ℝ (L : Set (Euclidean r)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Real.finrank_eq_int_finrank_of_discrete (s := (L : Set (Euclidean r)))
      ((congrArg (fun M : Submodule ℤ (Euclidean r) => DiscreteTopology M)
        (Submodule.span_eq L)).mpr hdisc)
    change Module.finrank ℝ (Submodule.span ℝ (L : Set (Euclidean r))) =
      Module.finrank ℤ (Submodule.span ℤ (L : Set (Euclidean r))) at h
    rw [h, Submodule.span_eq, ← F.finrank_eq, Module.finrank_pi,
      Fintype.card_fin, finrank_euclideanSpace_fin]
  let : IsZLattice ℝ L := ⟨hfull⟩
  let b := (Pi.basisFun ℤ (Fin r)).map F
  exact ⟨b.ofZLatticeBasis ℝ L, hL.symm.trans (congrArg SetLike.coe (b.ofZLatticeBasis_span ℝ L)).symm⟩

private theorem compact_latticeQuotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ E) :
    CompactSpace (E ⧸ (Submodule.span ℤ (range b)).toAddSubgroup) := by
  let L := Submodule.span ℤ (range b)
  let q := QuotientAddGroup.mk' L.toAddSubgroup
  have hq : Continuous q := QuotientAddGroup.continuous_mk
  have hc := IsZLattice.isCompact_range_of_periodic L q hq (fun z w hw => by
    have hw' : q w = 0 := by
      change (↑w : E ⧸ L.toAddSubgroup) = ↑(0 : E)
      rw [QuotientAddGroup.eq, add_zero]
      exact L.neg_mem hw
    rw [map_add, hw', add_zero])
  have hu : range q = univ := range_eq_univ.mpr (QuotientAddGroup.mk'_surjective L.toAddSubgroup)
  exact ⟨hu ▸ hc⟩

/-- A subgroup quotient has the infimum distance over translates of the second point. -/
private theorem quotient_dist_eq_iInf {E : Type*} [NormedAddCommGroup E]
    (L : AddSubgroup E) [IsClosed (L : Set E)]
    {A : Type*} (t : A → E) (ht : range t = (L : Set E)) (x y : E) :
    dist (QuotientAddGroup.mk' L x) (QuotientAddGroup.mk' L y) =
      ⨅ a, dist x (y + t a) := by
  let q := QuotientAddGroup.mk' L
  change dist (q x) (q y) = _
  rw [dist_eq_norm, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.norm_mk,
    Metric.infDist_eq_iInf]
  let f (a : A) : L := ⟨t a, show t a ∈ (L : Set E) from ht ▸ mem_range_self a⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := (show z ∈ range t from ht.symm ▸ (show z ∈ (L : Set E) from hz))
    exact ⟨a, rfl⟩
  symm
  apply hf.iInf_congr f
  intro a
  change dist (x - y) (t a) = dist x (y + t a)
  rw [dist_eq_norm, dist_eq_norm, sub_sub]

private def smulIsometryHom (A X : Type*) [Group A] [MetricSpace X]
    [MulAction A X] [IsIsometricSMul A X] : A →* (X ≃ᵢ X) where
  toFun := IsometryEquiv.constSMul
  map_one' := IsometryEquiv.ext (one_smul _)
  map_mul' a b := IsometryEquiv.ext (mul_smul a b)

private theorem isometry_euclideanSlice {X Y E : Type*}
    [MetricSpace X] [MetricSpace Y] [MetricSpace E] (M : Set X)
    (e : EuclideanProduct Y E ≃ᵢ M) (y : Y) :
    Isometry (fun x : E => (e (WithLp.toLp 2 (y, x)) : X)) := by
  apply isometry_subtype_coe.comp
  apply e.isometry.comp
  apply Isometry.of_dist_eq
  intro x x'
  rw [euclideanProduct_dist]
  simp

/-- For isometric actions the local finite-translate condition implies the
compact-set condition, even when compact balls are unavailable. -/
theorem isProperAction_of_locallyFiniteBalls : FlatTorusSpec.properActionOfLocalType := by
  classical
  intro A X _ _ _ _ h K hK
  choose δ hδ hfinite using h
  let U (p : X × X) := ball p.1 (δ p.1 / 4) ×ˢ ball p.2 (δ p.1 / 4)
  let S (p : X × X) := {a : A | ∃ z : X, (z, a • z) ∈ U p}
  have hS (p : X × X) : (S p).Finite := by
    by_cases hp : (S p).Nonempty
    · obtain ⟨a₀, ha₀⟩ := hp
      have hdist (a : A) (ha : a ∈ S p) : dist (a • p.1) p.2 < δ p.1 / 2 := by
        rcases ha with ⟨z, hz, haz⟩
        have h₁ : dist (a • p.1) (a • z) < δ p.1 / 4 := by
          rw [dist_smul, dist_comm]
          exact hz
        have h₂ : dist (a • z) p.2 < δ p.1 / 4 := haz
        linarith [dist_triangle (a • p.1) (a • z) p.2]
      let f (a : A) := a₀⁻¹ * a
      have hf : Function.Injective f := fun a b hab => mul_left_cancel hab
      apply ((hfinite p.1).preimage (f := f) hf.injOn).subset
      intro a ha
      refine ⟨p.1, mem_ball_self (hδ p.1), ?_⟩
      have he : dist (f a • p.1) p.1 = dist (a • p.1) (a₀ • p.1) := by
        rw [← dist_smul a₀, ← mul_smul]
        simp [f]
      rw [mem_ball, he]
      linarith [dist_triangle_right (a • p.1) (a₀ • p.1) p.2, hdist a ha, hdist a₀ ha₀]
    · rw [not_nonempty_iff_eq_empty.mp hp]
      exact finite_empty
  obtain ⟨J, hJ⟩ := (hK.prod hK).elim_finite_subcover U
    (fun _ => isOpen_ball.prod isOpen_ball) (fun p _ => by
      have hrad : 0 < δ p.1 / 4 := div_pos (hδ p.1) (by norm_num)
      exact mem_iUnion.mpr ⟨p, mem_ball_self hrad, mem_ball_self hrad⟩)
  refine (J.finite_toSet.biUnion (fun p _ => hS p)).subset ?_
  rintro a ⟨z, hz, haz⟩
  obtain ⟨p, hp, hp'⟩ := mem_iUnion₂.mp (hJ (show (z, a • z) ∈ K ×ˢ K from ⟨hz, haz⟩))
  exact mem_iUnion₂.mpr ⟨p, hp, z, hp'⟩

/-- A proper semisimple action of a free abelian group on a complete CAT(0) space
splits its common minimum set, with flat tori as the slice quotients. -/
theorem CAT0.flatTorus : FlatTorusSpec.flatTorusType := by
  intro A X _ _ _ _ _ r hA hX hp hs
  obtain ⟨i⟩ := hA
  let ρ := (smulIsometryHom A X).comp i.symm.toMonoidHom
  have hρ : ProperIsometryAction ρ := fun K hK =>
    (hp K hK).preimage (f := i.symm) i.symm.injective.injOn
  have hmin : CAT0SpacesSpec.actionMinsetValue A X = commonMinset ρ := by
    ext x
    simp only [CAT0SpacesSpec.actionMinsetValue, CAT0SpacesSpec.commonMinsetValue,
      commonMinset, mem_iInter]
    exact ⟨fun h g => h (i.symm g), fun h a => by
      have hg := h (i a)
      change x ∈ minset (IsometryEquiv.constSMul a)
      simpa [ρ, smulIsometryHom] using hg⟩
  rw [hmin]
  obtain ⟨Y, mY, hY, hYcomplete, e, τ, he⟩ :=
    flatTorus_splitting r hX ρ hρ (fun g => hs (i.symm g))
  obtain ⟨y₀⟩ := hY.1.1
  let F (x : Euclidean r) : X := e (WithLp.toLp 2 (y₀, x))
  have hF := isometry_euclideanSlice _ e y₀
  have hτ : Function.Injective τ := by
    intro g k h
    apply mul_inv_eq_one.mp
    apply eq_one_of_fixed hρ (x := F 0)
    have hz : τ (g * k⁻¹) = 1 := by simp [h]
    change ρ (g * k⁻¹) (e (WithLp.toLp 2 (y₀, 0))) = F 0
    rw [he, hz]
    change (e (WithLp.toLp 2 (y₀, 0 + 0)) : X) = F 0
    rw [zero_add]
  have hfinite : {g | (τ g).toAdd ∈ closedBall (0 : Euclidean r) 1}.Finite := by
    let C := F '' closedBall 0 1
    have hC : IsCompact C := (isCompact_closedBall _ _).image hF.continuous
    refine (hρ C hC).subset fun g hg => ⟨F 0, mem_image_of_mem F (mem_closedBall_self zero_le_one), ?_⟩
    refine ⟨(τ g).toAdd, hg, ?_⟩
    change F (τ g).toAdd = ρ g (e (WithLp.toLp 2 (y₀, 0)))
    rw [he, zero_add]
  obtain ⟨b, hb⟩ := lattice_basis r τ hτ hfinite
  let T := τ.comp i.toMonoidHom
  have hact (a : A) (y : Y) (x : Euclidean r) :
      a • (e (WithLp.toLp 2 (y, x)) : X) =
        (e (WithLp.toLp 2 (y, x + (T a).toAdd)) : X) := by
    simpa [ρ, smulIsometryHom, T] using he (i a) y x
  let L := (Submodule.span ℤ (range b)).toAddSubgroup
  have hL : range (fun a => (T a).toAdd) = (L : Set (Euclidean r)) := by
    change range ((fun g => (τ g).toAdd) ∘ i) = _
    rw [i.surjective.range_comp]
    exact hb
  refine ⟨⟨F 0, (e (WithLp.toLp 2 (y₀, 0))).2⟩, Y, mY, hY, hYcomplete, e, T, b,
    hτ.comp i.injective, hact, hL, inferInstance, compact_latticeQuotient b, ?_⟩
  intro y x x'
  let q := QuotientAddGroup.mk' L
  have hx : q x = q x' ↔ x - x' ∈ L := by
    rw [eq_comm, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq]
    rw [sub_eq_neg_add]
  refine ⟨?_, ?_⟩
  · rw [hx]
    change (x - x' ∈ (L : Set (Euclidean r))) ↔ _
    rw [← hL]
    refine exists_congr fun a => ?_
    rw [hact]
    constructor
    · intro ha
      change (T a).toAdd = x - x' at ha
      rw [ha, add_sub_cancel]
    · intro ha
      have hcoords := e.injective (Subtype.ext ha)
      exact eq_sub_of_add_eq (by simpa [add_comm] using congrArg WithLp.snd hcoords)
  · let : IsClosed (L : Set (Euclidean r)) := AddSubgroup.isClosed_of_discreteTopology
    rw [quotient_dist_eq_iInf L _ hL]
    congr 1
    funext a
    rw [hact]
    exact ((isometry_euclideanSlice _ e y).dist_eq _ _).symm

/-- Restricting a geometric action to an embedded rank-two lattice gives a plane. -/
theorem IsGeometricAction.exists_isometricPlane : FlatTorusSpec.geometricActionPlaneType := by
  intro G X _ _ _ h hX i hi
  change IsGeometricAction G X at h
  let : IsIsometricSMul G X := h.1
  let : CompleteSpace X := h.completeSpace hX
  let : MulAction (IntegerGroup 2) X := MulAction.compHom X i
  let : IsIsometricSMul (IntegerGroup 2) X := ⟨fun a => isometry_smul X (i a)⟩
  have hp : IsProperAction (IntegerGroup 2) X := fun K hK =>
    (h.2.1 K hK).preimage (f := i) hi.injOn
  have hs (a : IntegerGroup 2) :
      IsSemisimple (IsometryEquiv.constSMul a : X ≃ᵢ X) :=
    h.isSemisimple hX (i a)
  obtain ⟨_, Y, _, hY, _, e, _⟩ :=
    CAT0.flatTorus 2 ⟨MulEquiv.refl _⟩ hX hp hs
  obtain ⟨y⟩ := hY.1.1
  exact ⟨_, isometry_euclideanSlice _ e y⟩

end

end LinearAlgebraicGroups.Geometry
