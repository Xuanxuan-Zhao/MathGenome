import Specs.LinearAlgebraicGroups.Cohomology.ProjectiveFiniteChartPresentations
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Pi

open CategoryTheory Opposite
open LinearAlgebraicGroups.Specs.ProjectiveFiniteChartPresentations

universe u v w

namespace LinearAlgebraicGroups.ProjectiveFiniteChartPresentations

variable {k : Type u} [CommRing k] {ι : Type v} [DecidableEq ι]
  {D : ChartRings k ι}

private noncomputable def restrict (M : D.Modules) {S T : Chart ι} (f : S ⟶ T)
    (x : M.obj S) : M.obj T := M.map f x

private theorem restrict_smul (M : D.Modules) {S T : Chart ι} (f : S ⟶ T)
    (r : D.rings.obj S) (x : M.obj S) :
    restrict M f (r • x) = D.rings.map f r • restrict M f x :=
  M.map_smul f r x

private theorem restrict_sub (M : D.Modules) {S T : Chart ι} (f : S ⟶ T)
    (x y : M.obj S) :
    restrict M f (x - y) = restrict M f x - restrict M f y :=
  map_sub (M.map f).hom x y

private theorem restrict_comp {M : D.Modules} {S T U : Chart ι}
    (f : S ⟶ T) (g : T ⟶ U) (h : S ⟶ U) (x : M.obj S) :
    restrict M g (restrict M f x) = restrict M h x := by
  unfold restrict
  rw [← M.map_comp_apply, Subsingleton.elim (f ≫ g) h]

private theorem restrict_self {M : D.Modules} {S : Chart ι} (f : S ⟶ S) (x : M.obj S) :
    restrict M f x = x := by
  unfold restrict
  rw [Subsingleton.elim f (𝟙 S), PresheafOfModules.map_id]
  rfl

private theorem restrict_injective_of_eq {M : D.Modules} {S T : Chart ι}
    (f : S ⟶ T) (h : S = T) : Function.Injective (restrict M f) := by
  subst T
  intro x y hxy
  simpa only [restrict_self] using hxy

private theorem exists_uniform {A : Type w} [Finite A] (p : A → ℕ → Prop)
    (hex : ∀ a, ∃ n, p a n) (hmono : ∀ a, Monotone (p a)) : ∃ n, ∀ a, p a n := by
  classical
  let := Fintype.ofFinite A
  choose n hn using hex
  exact ⟨Finset.univ.sup n, fun a => hmono a (Finset.le_sup (Finset.mem_univ a)) (hn a)⟩

private theorem unit_ratio_image (S : Chart ι) (i j : ι) (hj : j ∈ S.indices) :
    IsUnit (D.rings.map (S.toAdjoin i) (D.ratio S i j hj)) := by
  rw [D.ratio_map]
  exact (D.ratioUnit (S.adjoin i) (S.mem_adjoin i) (Chart.subset (S.toAdjoin i) hj)).isUnit

private theorem lift_power {M : D.Modules} (hM : D.Localizes M) (S : Chart ι)
    (i j : ι) (hj : j ∈ S.indices) (y : M.obj (S.adjoin i)) :
    ∃ (n : ℕ) (x : M.obj S),
      (D.rings.map (S.toAdjoin i) (D.ratio S i j hj)) ^ n • y = restrict M (S.toAdjoin i) x := by
  let f := (M.map (S.toAdjoin i)).hom
  let : IsLocalizedModule.Away (D.ratio S i j hj) f := hM S i j hj
  let y' : (ModuleCat.restrictScalars (D.rings.map (S.toAdjoin i)).hom).obj
      (M.obj (S.adjoin i)) := y
  obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj f (D.ratio S i j hj) y'
  refine ⟨n, x, ?_⟩
  rw [← map_pow]
  exact hx

private theorem kill_power {M : D.Modules} (hM : D.Localizes M) (S : Chart ι)
    (i j : ι) (hj : j ∈ S.indices) (x : M.obj S) (h : restrict M (S.toAdjoin i) x = 0) :
    ∃ n : ℕ, D.ratio S i j hj ^ n • x = 0 := by
  let f := (M.map (S.toAdjoin i)).hom
  let : IsLocalizedModule.Away (D.ratio S i j hj) f := hM S i j hj
  have he : f x = f 0 := h.trans f.map_zero.symm
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (D.ratio S i j hj) he
  exact ⟨n, hn.trans (smul_zero _)⟩

private def adjoinMap {S T : Chart ι} (f : S ⟶ T) (i : ι) : S.adjoin i ⟶ T.adjoin i :=
  Chart.hom (Finset.insert_subset_insert _ (Chart.subset f))

private theorem basis_apply (L : Twists D) (d : ℤ) (S : Chart ι) (i : ι)
    (hi : i ∈ S.indices) (r : D.rings.obj S) :
    L.basis d S i hi r = r • L.basis d S i hi 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

private def onBasis (L : Twists D) (d : ℤ) {M : D.Modules} (S : Chart ι) (j : ι)
    (hj : j ∈ S.indices) (x : M.obj S) : (L.diagram d).obj S ⟶ M.obj S :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton _ _ x).comp (L.basis d S j hj).symm.toLinearMap)

@[simp] private theorem onBasis_apply (L : Twists D) (d : ℤ) {M : D.Modules}
    (S : Chart ι) (j : ι) (hj : j ∈ S.indices) (x : M.obj S) (r : D.rings.obj S) :
    onBasis L d S j hj x (L.basis d S j hj r) = r • x := by
  change (L.basis d S j hj).symm (L.basis d S j hj r) • x = r • x
  rw [LinearEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Clearing a common denominator extends a single local generator. A second
common power kills the discrepancies on every restriction. -/
private theorem extends_generator [Fintype ι] (L : Twists D) {M : D.Modules}
    (hM : D.Localizes M) (i : ι) (x : M.obj (Chart.single i)) :
    ∃ (d : ℤ) (q : L.diagram d ⟶ M),
      q.app (Chart.single i) (L.basis d (Chart.single i) i (Chart.mem_single i) 1) = x := by
  classical
  let : Finite (Chart ι) := Finite.of_injective Chart.indices
    (Subtype.val_injective.comp (OrderDual.ofDual.injective.comp Opposite.unop_injective))
  let j (S : Chart ι) : ι := S.nonempty.choose
  have hj (S : Chart ι) : j S ∈ S.indices := S.nonempty.choose_spec
  let r (S : Chart ι) : D.rings.obj S := D.ratio S i (j S) (hj S)
  let xOn (S : Chart ι) : M.obj (S.adjoin i) :=
    restrict M (Chart.fromSingle (S.mem_adjoin i)) x
  have xOn_map {S T : Chart ι} (f : S ⟶ T) :
      restrict M (adjoinMap f i) (xOn S) = xOn T :=
    restrict_comp _ _ _ x
  obtain ⟨d, hd⟩ := exists_uniform (fun (S : Chart ι) n => ∃ v : M.obj S,
      restrict M (S.toAdjoin i) v = (D.rings.map (S.toAdjoin i) (r S)) ^ n • xOn S)
    (fun S => by
      obtain ⟨n, v, hv⟩ := lift_power hM S i (j S) (hj S) (xOn S)
      exact ⟨n, v, hv.symm⟩)
    (fun S n m hnm ⟨v, hv⟩ => by
      refine ⟨r S ^ (m - n) • v, ?_⟩
      rw [restrict_smul M, map_pow, hv, smul_smul, ← pow_add, Nat.sub_add_cancel hnm])
  choose v hv using hd
  let b {S T : Chart ι} (f : S ⟶ T) : D.rings.obj T :=
    D.ratio T (j S) (j T) (hj T)
  let diff {S T : Chart ι} (f : S ⟶ T) : M.obj T := v T - b f ^ d • restrict M f (v S)
  have diff_vanishes {S T : Chart ι} (f : S ⟶ T) :
      restrict M (T.toAdjoin i) (diff f) = 0 := by
    have hsq : restrict M (T.toAdjoin i) (restrict M f (v S)) =
        restrict M (adjoinMap f i) (restrict M (S.toAdjoin i) (v S)) := by
      rw [restrict_comp f (T.toAdjoin i) (f ≫ T.toAdjoin i),
        restrict_comp (S.toAdjoin i) (adjoinMap f i) (f ≫ T.toAdjoin i)]
    have hr : D.rings.map (adjoinMap f i) (D.rings.map (S.toAdjoin i) (r S)) *
        D.rings.map (T.toAdjoin i) (b f) = D.rings.map (T.toAdjoin i) (r T) := by
      dsimp only [r, b]
      rw [D.ratio_map, D.ratio_map, D.ratio_map, D.ratio_map, D.ratio_mul]
    unfold diff
    rw [restrict_sub M, restrict_smul M, hsq, hv T, hv S,
      restrict_smul M, map_pow, map_pow, xOn_map, smul_smul, mul_comm, ← mul_pow, hr, sub_self]
  let Arrows := Σ S : Chart ι, Σ T : Chart ι, S ⟶ T
  let : Finite Arrows := by
    dsimp [Arrows]
    infer_instance
  obtain ⟨m, hm⟩ := exists_uniform (A := Arrows) (fun a n =>
      r a.2.1 ^ n • diff a.2.2 = 0)
    (fun a => kill_power hM a.2.1 i (j a.2.1) (hj a.2.1) _ (diff_vanishes a.2.2))
    (fun a n m hnm hn => by
      change r a.2.1 ^ n • diff a.2.2 = 0 at hn
      rw [← Nat.sub_add_cancel hnm, pow_add, mul_smul, hn, smul_zero])
  let z (S : Chart ι) : M.obj S := r S ^ m • v S
  have z_map {S T : Chart ι} (f : S ⟶ T) :
      b f ^ (d + m) • restrict M f (z S) = z T := by
    have h : r T ^ m • v T = r T ^ m • (b f ^ d • restrict M f (v S)) := by
      simpa only [diff, smul_sub, sub_eq_zero] using hm ⟨S, T, f⟩
    have hr : D.rings.map f (r S) * b f = r T := by
      dsimp only [r, b]
      rw [D.ratio_map, D.ratio_mul]
    rw [show z S = r S ^ m • v S from rfl, show z T = r T ^ m • v T from rfl,
      restrict_smul M, map_pow, smul_smul, h, smul_smul, ← hr, mul_pow, pow_add]
    congr 1
    rw [mul_comm (b f ^ d) (b f ^ m), mul_comm (b f ^ m * b f ^ d), mul_assoc]
  let e : ℤ := -((d + m : ℕ) : ℤ)
  have z_compatible {S T : Chart ι} (f : S ⟶ T) :
      restrict M f (z S) =
        ((D.ratioUnit T (Chart.subset f (hj S)) (hj T) ^ e : (D.rings.obj T)ˣ) :
          D.rings.obj T) • z T := by
    let u₀ := D.ratioUnit T (Chart.subset f (hj S)) (hj T)
    change _ = ((u₀ ^ e : (D.rings.obj T)ˣ) : D.rings.obj T) • z T
    rw [← z_map f, smul_smul]
    have h : ((u₀ ^ e : (D.rings.obj T)ˣ) : D.rings.obj T) * b f ^ (d + m) = 1 := by
      change _ * (u₀ : D.rings.obj T) ^ (d + m) = _
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
      simp [e]
    rw [h, one_smul]
  let q : L.diagram e ⟶ M :=
    { app := fun S => onBasis L e S (j S) (hj S) (z S)
      naturality := by
        intro S T f
        ext a
        obtain ⟨c, rfl⟩ := (L.basis e S (j S) (hj S)).surjective a
        change onBasis L e T (j T) (hj T) (z T)
            (restrict (L.diagram e) f (L.basis e S (j S) (hj S) c)) =
          restrict M f (onBasis L e S (j S) (hj S) (z S) (L.basis e S (j S) (hj S) c))
        have hbasis : restrict (L.diagram e) f (L.basis e S (j S) (hj S) 1) =
            L.basis e T (j S) (Chart.subset f (hj S)) 1 := L.basis_map e f (j S) (hj S)
        rw [onBasis_apply, basis_apply L e S (j S) (hj S), restrict_smul (L.diagram e), hbasis,
          L.basis_transition e T (j S) (j T) (Chart.subset f (hj S)) (hj T),
          map_smul (onBasis L e T (j T) (hj T) (z T)).hom,
          map_smul (onBasis L e T (j T) (hj T) (z T)).hom,
          onBasis_apply, one_smul, restrict_smul M, z_compatible] }
  refine ⟨e, q, ?_⟩
  let S := Chart.single i
  have ha : S.adjoin i = S := by
    change Chart.ofFinset (insert i ({i} : Finset ι)) _ = Chart.ofFinset {i} _
    simp [Finset.insert_eq_of_mem (Finset.mem_singleton_self i)]
  have hr₀ (a : ι) (ha : a ∈ S.indices) : D.ratio S i a ha = 1 := by
    have he : a = i := Finset.mem_singleton.mp ha
    subst a
    exact D.ratio_self S i ha
  have hr : r S = 1 := hr₀ (j S) (hj S)
  have hvx : v S = x := by
    apply restrict_injective_of_eq (S.toAdjoin i) ha.symm
    rw [hv S, hr, map_one, one_pow, one_smul]
    exact M.congr_map_apply (Subsingleton.elim _ _) x
  have hz : z S = x := by dsimp only [z]; rw [hr, one_pow, one_smul, hvx]
  have hb (a : ι) (ha : a ∈ S.indices) :
      L.basis e S i (Chart.mem_single i) 1 = L.basis e S a ha 1 := by
    have he : a = i := Finset.mem_singleton.mp ha
    subst a
    rfl
  change onBasis L e S (j S) (hj S) (z S) (L.basis e S i (Chart.mem_single i) 1) = x
  rw [hb (j S) (hj S), onBasis_apply, one_smul, hz]

set_option backward.isDefEq.respectTransparency false in
private theorem localizes_of_lift_and_kill (M : D.Modules)
    (lift : ∀ (S : Chart ι) (i j : ι) (hj : j ∈ S.indices) (y : M.obj (S.adjoin i)),
      ∃ (n : ℕ) (x : M.obj S),
        (D.rings.map (S.toAdjoin i) (D.ratio S i j hj)) ^ n • y =
          restrict M (S.toAdjoin i) x)
    (kill : ∀ (S : Chart ι) (i j : ι) (hj : j ∈ S.indices) (x : M.obj S),
      restrict M (S.toAdjoin i) x = 0 → ∃ n : ℕ, D.ratio S i j hj ^ n • x = 0) :
    D.Localizes M := by
  intro S i j hj
  let f := (M.map (S.toAdjoin i)).hom
  change IsLocalizedModule.Away (D.ratio S i j hj) f
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · rw [Module.End.isUnit_iff]
    change Function.Bijective (fun y : M.obj (S.adjoin i) =>
      D.rings.map (S.toAdjoin i) (D.ratio S i j hj) • y)
    exact (unit_ratio_image (D := D) S i j hj).smul_bijective
  · intro y
    obtain ⟨n, x, hx⟩ := lift S i j hj y
    rw [← map_pow] at hx
    exact ⟨n, x, hx⟩
  · intro x hx
    exact kill S i j hj x hx

set_option backward.isDefEq.respectTransparency false in
private theorem product_localizes {n : ℕ} (P : Fin n → D.Modules)
    (hP : ∀ a, D.Localizes (P a)) : D.Localizes (product P) := by
  apply localizes_of_lift_and_kill
  · intro S i j hj y
    let f := S.toAdjoin i
    let r := D.ratio S i j hj
    obtain ⟨m, hm⟩ := exists_uniform (fun a p => ∃ x : (P a).obj S,
        (D.rings.map f r) ^ p • y a = restrict (P a) f x)
      (fun a => lift_power (hP a) S i j hj (y a))
      (fun a p q hpq ⟨x, hx⟩ => by
        refine ⟨r ^ (q - p) • x, ?_⟩
        rw [restrict_smul, map_pow, ← hx, smul_smul, ← pow_add, Nat.sub_add_cancel hpq])
    choose x hx using hm
    exact ⟨m, x, funext hx⟩
  · intro S i j hj x h
    let f := S.toAdjoin i
    let r := D.ratio S i j hj
    have hzero (a : Fin n) : restrict (P a) f (x a) = 0 := congrFun h a
    obtain ⟨m, hm⟩ := exists_uniform (fun a p => r ^ p • x a = 0)
      (fun a => kill_power (hP a) S i j hj (x a) (hzero a))
      (fun a p q hpq hp => by
        change r ^ p • x a = 0 at hp
        rw [← Nat.sub_add_cancel hpq, pow_add, mul_smul, hp, smul_zero])
    exact ⟨m, funext hm⟩

private theorem restrict_natural {P M : D.Modules} (q : P ⟶ M) {S T : Chart ι}
    (f : S ⟶ T) (x : P.obj S) :
    q.app T (restrict P f x) = restrict M f (q.app S x) :=
  PresheafOfModules.naturality_apply q f x

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_localizes {P M : D.Modules} (q : P ⟶ M)
    (hP : D.Localizes P) (hM : D.Localizes M) : D.Localizes (kernel q) := by
  apply localizes_of_lift_and_kill
  · intro S i j hj y
    let f := S.toAdjoin i
    let r := D.ratio S i j hj
    obtain ⟨n, x, hx⟩ := lift_power hP S i j hj y.1
    have hy : q.app (S.adjoin i) y.1 = 0 := y.2
    have hqx : restrict M f (q.app S x) = 0 := by
      rw [← restrict_natural q, ← hx, map_smul (q.app _).hom, hy, smul_zero]
    obtain ⟨m, hm⟩ := kill_power hM S i j hj (q.app S x) hqx
    have hx' : q.app S (r ^ m • x) = 0 := by
      rw [map_smul (q.app S).hom]
      exact hm
    refine ⟨m + n, ⟨r ^ m • x, hx'⟩, Subtype.ext ?_⟩
    change (D.rings.map f r) ^ (m + n) • y.1 = restrict P f (r ^ m • x)
    rw [pow_add, mul_smul, hx, restrict_smul, map_pow]
  · intro S i j hj x h
    have hx : restrict P (S.toAdjoin i) x.1 = 0 := congrArg Subtype.val h
    obtain ⟨n, hn⟩ := kill_power hP S i j hj x.1 hx
    exact ⟨n, Subtype.ext hn⟩

set_option backward.isDefEq.respectTransparency false in
private def sumMorphisms {M : D.Modules} {n : ℕ} {P : Fin n → D.Modules}
    (q : ∀ a, P a ⟶ M) : product P ⟶ M where
  app S := ModuleCat.ofHom
    (LinearMap.lsum (D.rings.obj S) (fun a => (P a).obj S) (D.rings.obj S)
      (fun a => (q a).app S |>.hom))
  naturality {S T} f := by
    ext x
    change (LinearMap.lsum (D.rings.obj T) (fun a => (P a).obj T) (D.rings.obj T)
        (fun a => ((q a).app T).hom)) (restrict (product P) f x) =
      restrict M f ((LinearMap.lsum (D.rings.obj S) (fun a => (P a).obj S) (D.rings.obj S)
        (fun a => ((q a).app S).hom)) x)
    simp only [LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    change (∑ a, (q a).app T (restrict (P a) f (x a))) =
      restrict M f (∑ a, (q a).app S (x a))
    calc
      _ = ∑ a, restrict M f ((q a).app S (x a)) :=
        Finset.sum_congr rfl (fun a _ => restrict_natural (q a) f (x a))
      _ = _ := (map_sum (M.map f).hom _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem sumMorphisms_single {M : D.Modules} {n : ℕ} {P : Fin n → D.Modules}
    (q : ∀ a, P a ⟶ M) (S : Chart ι) (a : Fin n) (x : (P a).obj S) :
    (sumMorphisms q).app S (Pi.single a x) = (q a).app S x :=
  LinearMap.lsum_piSingle (D.rings.obj S) (fun a => (P a).obj S) (D.rings.obj S) (fun b => ((q b).app S).hom) a x

set_option backward.isDefEq.respectTransparency false in
private theorem surjective_on_charts {P M : D.Modules} (q : P ⟶ M) (hM : D.Localizes M)
    (hsingle : ∀ i, Function.Surjective (q.app (Chart.single i))) :
    ∀ S, Function.Surjective (q.app S) := by
  classical
  have step (S : Chart ι) (i : ι) (hs : Function.Surjective (q.app S)) :
      Function.Surjective (q.app (S.adjoin i)) := by
    intro y
    obtain ⟨j, hj⟩ := S.nonempty
    obtain ⟨n, x, hx⟩ := lift_power hM S i j hj y
    obtain ⟨z, hz⟩ := hs x
    let r := (D.rings.map (S.toAdjoin i) (D.ratio S i j hj)) ^ n
    have hr : IsUnit r := (unit_ratio_image (D := D) S i j hj).pow n
    obtain ⟨w, hw⟩ := hr.smul_bijective.2 (restrict P (S.toAdjoin i) z)
    change r • w = restrict P (S.toAdjoin i) z at hw
    refine ⟨w, hr.smul_left_cancel.mp ?_⟩
    calc
      r • q.app (S.adjoin i) w = q.app (S.adjoin i) (r • w) :=
        (map_smul (q.app (S.adjoin i)).hom r w).symm
      _ = r • y := by
        rw [hw, restrict_natural, hz]
        exact hx.symm
  have all (s : Finset ι) : ∀ hs : s.Nonempty,
      Function.Surjective (q.app (Chart.ofFinset s hs)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s _ ih =>
      intro hs
      by_cases h : s.Nonempty
      · exact step (Chart.ofFinset s h) i (ih h)
      · obtain rfl : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        have he : Chart.ofFinset (insert i (∅ : Finset ι)) hs = Chart.single i := by
          simp [Chart.single]
        exact he.symm ▸ hsingle i
  intro S
  exact all (Chart.indices S) (Chart.nonempty S)

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_finite {n : ℕ} (L : Twists D) (d : Fin n → ℤ) {M : D.Modules}
    (q : product (fun a => L.diagram (d a)) ⟶ M) :
    D.FiniteOnSingletons (kernel q) := by
  intro i
  let S := Chart.single i
  let : IsNoetherianRing (D.rings.obj S) := D.noetherian i
  let : ∀ a, Module.Finite (D.rings.obj S) ((L.diagram (d a)).obj S) :=
    fun a => Module.Finite.equiv (L.basis (d a) S i (Chart.mem_single i))
  let : Module.Finite (D.rings.obj S) ((product (fun a => L.diagram (d a))).obj S) :=
    Module.Finite.pi
  change Module.Finite (D.rings.obj S) (LinearMap.ker (q.app S).hom)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Termwise finite twist quotients and their localizing kernels. -/
theorem finiteChartPresentations : FiniteChartPresentations.{u, v} := by
  intro k _ ι _ _ _ D L M hfinite hM
  classical
  have generators (i : ι) :
      ∃ (n : ℕ) (g : Fin n → M.obj (Chart.single i)),
        Submodule.span (D.rings.obj (Chart.single i)) (Set.range g) = ⊤ := by
    let := hfinite i
    exact Module.Finite.exists_fin
  choose n g hg using generators
  let A := Σ i : ι, Fin (n i)
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  choose degree maps hm using
    (fun a : A => extends_generator L hM a.1 (g a.1 a.2))
  let d (a : Fin (Fintype.card A)) := degree (e a)
  let qs (a : Fin (Fintype.card A)) : L.diagram (d a) ⟶ M := maps (e a)
  let q := sumMorphisms qs
  have hsingle (i : ι) : Function.Surjective (q.app (Chart.single i)) := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hg i, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hgen (a : A) : g a.1 a.2 ∈ LinearMap.range (q.app (Chart.single a.1)).hom := by
      let c := e.symm a
      have hc : e c = a := e.apply_symm_apply a
      have hval (t : Fin (Fintype.card A)) :
          (qs t).app (Chart.single (e t).1)
            (L.basis (d t) _ _ (Chart.mem_single (e t).1) 1) = g (e t).1 (e t).2 :=
        hm (e t)
      have hmem : g (e c).1 (e c).2 ∈ LinearMap.range (q.app (Chart.single (e c).1)).hom := by
        refine ⟨Pi.single c (L.basis (d c) _ _ (Chart.mem_single (e c).1) 1), ?_⟩
        exact (sumMorphisms_single qs _ c _).trans (hval c)
      exact Eq.mp (congrArg (fun a : A =>
        g a.1 a.2 ∈ LinearMap.range (q.app (Chart.single a.1)).hom) hc) hmem
    exact hgen ⟨i, b⟩
  refine ⟨_, d, q, surjective_on_charts q hM hsingle, ?_, ?_, kernel_finite L d q, ?_⟩
  · intro S
    exact Subtype.val_injective
  · intro S x
    exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩
  · exact kernel_localizes q (product_localizes _ (fun a => L.localizes (d a))) hM

end LinearAlgebraicGroups.ProjectiveFiniteChartPresentations
