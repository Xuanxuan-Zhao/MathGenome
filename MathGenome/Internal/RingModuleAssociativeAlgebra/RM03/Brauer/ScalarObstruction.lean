import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ScalarObstruction
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.BaseChange
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification
import Mathlib.Tactic.Group
import Batteries.Tactic.OpenPrivate

open scoped TensorProduct MatrixGroups Kronecker

namespace RM03.Brauer.ScalarObstruction

open Matrix ProjectiveClassification SemilinearDescent groupCohomology
open Specs.RM03.Brauer.ScalarObstruction

universe u v w x

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable {n : ℕ}

theorem coefficientAction_formula (g : Gal(K/k)) (a : Kˣ) :
    ((g • a : Kˣ) : K) = g (a : K) := rfl

theorem cocycleClass_eq_iff (a b : ScalarCocycle k K) :
    cocycleClass k K a = cocycleClass k K b ↔
      IsMulCoboundary₂ (fun p => b.val p / a.val p) := by
  rw [eq_comm]
  change ((b : H2 k K) = a) ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, fun g h => congrArg (fun c : ScalarCocycle k K => c.val (g,h)) ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, Subtype.ext (funext fun p => ht p.1 p.2)⟩

theorem cocycleClass_eq_one_iff (a : ScalarCocycle k K) :
    cocycleClass k K a = 1 ↔ IsMulCoboundary₂ a.val := by
  rw [← map_one (cocycleClass k K), eq_comm, cocycleClass_eq_iff]
  change IsMulCoboundary₂ (fun p => a.val p / 1) ↔ _
  simp only [div_one]

theorem cocycleClass_surjective :
    Function.Surjective (cocycleClass k K) :=
  QuotientGroup.mk_surjective

private theorem scalar_injective (hn : 0 < n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Kˣ → GL (Fin n) K) := by
  intro a b h
  let i : Fin n := ⟨0, hn⟩
  apply Units.ext
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using
    congrArg (fun G : GL (Fin n) K => (G : Mat K n) i i) h

private theorem scalar_commute (a : Kˣ) (G : GL (Fin n) K) :
    Commute (GeneralLinearGroup.scalar (Fin n) a) G := by
  have h : GeneralLinearGroup.scalar (Fin n) a ∈ Subgroup.center (GL (Fin n) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨a, rfl⟩
  exact ((Subgroup.mem_center_iff.mp h) G).symm

@[simp] theorem mapGL_scalar (g : Gal(K/k)) (a : Kˣ) :
    mapGL g (GeneralLinearGroup.scalar (Fin n) a) =
      GeneralLinearGroup.scalar (Fin n) (g • a) :=
  GeneralLinearGroup.map_scalar g.toRingHom a

theorem mapGL_mul_apply (g h : Gal(K/k)) (G : GL (Fin n) K) :
    mapGL (g*h) G = mapGL g (mapGL h G) := rfl

@[simp] theorem mk_mapGL (g : Gal(K/k)) (G : GL (Fin n) K) :
    ProjGenLinGroup.mk (mapGL g G) = projectiveAction k K n g (ProjGenLinGroup.mk G) := rfl

private theorem scalarDefect_eq (p : Cocycle k K n)
    (G : Gal(K/k) → GL (Fin n) K) (hG : IsLift p G) (g h : Gal(K/k)) :
    GeneralLinearGroup.scalar (Fin n) (scalarDefect G (g,h)) =
      G g * mapGL g (G h) * (G (g*h))⁻¹ := by
  apply Function.invFun_eq
  have hp : ProjGenLinGroup.mk (G g * mapGL g (G h) * (G (g*h))⁻¹) = 1 := by
    simp only [map_mul, mk_mapGL, map_inv, hG g, hG h, hG (g*h)]
    rw [← p.law, mul_inv_cancel]
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  exact hp

private theorem lift_mul (p : Cocycle k K n) (G : Gal(K/k) → GL (Fin n) K)
    (hG : IsLift p G) (g h : Gal(K/k)) :
    G g * mapGL g (G h) =
      GeneralLinearGroup.scalar (Fin n) (scalarDefect G (g,h)) * G (g*h) := by
  rw [scalarDefect_eq p G hG, inv_mul_cancel_right]

theorem lift_defect (hn : 0 < n) (p : Cocycle k K n)
    (G : Gal(K/k) → GL (Fin n) K) (hG : IsLift p G) :
    (∀ g h, GeneralLinearGroup.scalar (Fin n) (scalarDefect G (g,h)) =
      G g * mapGL g (G h) * (G (g*h))⁻¹) ∧ IsMulCocycle₂ (scalarDefect G) := by
  refine ⟨scalarDefect_eq p G hG, fun g h j => ?_⟩
  let S := GeneralLinearGroup.scalar (Fin n) (R := K)
  let d := scalarDefect G
  apply scalar_injective hn
  apply mul_right_cancel (b := G (g * h * j))
  change S (d (g*h,j) * d (g,h)) * G (g*h*j) =
    S (g • d (h,j) * d (g,h*j)) * G (g*h*j)
  calc
    S (d (g*h,j) * d (g,h)) * G (g*h*j) =
        S (d (g,h)) * (S (d (g*h,j)) * G (g*h*j)) := by
      rw [mul_comm (d (g*h,j)), map_mul, mul_assoc]
    _ = (G g * mapGL g (G h)) * mapGL (g*h) (G j) := by
      rw [← lift_mul p G hG, ← mul_assoc, ← lift_mul p G hG]
    _ = G g * mapGL g (G h * mapGL h (G j)) := by
      rw [mapGL_mul_apply, map_mul, mul_assoc]
    _ = S (g • d (h,j) * d (g,h*j)) * G (g*h*j) := by
      rw [lift_mul p G hG h j, map_mul, mapGL_scalar,
        ← mul_assoc, (scalar_commute (g • d (h,j)) (G g)).eq.symm, mul_assoc,
        lift_mul p G hG g (h*j), ← mul_assoc, ← map_mul, mul_assoc g h j]

theorem lift_cocycle_law (hn : 0 < n) (p : Cocycle k K n)
    (G : Gal(K/k) → GL (Fin n) K) (hG : IsLift p G) (g h j : Gal(K/k)) :
    scalarDefect G (g,h) * scalarDefect G (g*h,j) =
      g • scalarDefect G (h,j) * scalarDefect G (g,h*j) :=
  (mul_comm _ _).trans ((lift_defect hn p G hG).2 g h j)

theorem stacks_inverse (_hn : 0 < n) (p : Cocycle k K n)
    (G : Gal(K/k) → GL (Fin n) K) (hG : IsLift p G) (g h : Gal(K/k)) :
    (G g)⁻¹ * G (g*h) * mapGL g (G h)⁻¹ =
      GeneralLinearGroup.scalar (Fin n) ((scalarDefect G (g,h))⁻¹) := by
  let D := G g * mapGL g (G h) * (G (g*h))⁻¹
  calc
    (G g)⁻¹ * G (g*h) * mapGL g (G h)⁻¹ = (G g)⁻¹ * D⁻¹ * G g := by
      dsimp [D]
      rw [map_inv]
      group
    _ = _ := by
      rw [show D = _ from (scalarDefect_eq p G hG g h).symm, ← map_inv,
        ← (scalar_commute ((scalarDefect G (g,h))⁻¹) (G g)⁻¹).eq,
        mul_assoc, inv_mul_cancel, mul_one]

/-- The actual scalar cocycle of the indicated lift. -/
noncomputable def liftCocycle (hn : 0 < n) (p : Cocycle k K n)
    (G : Gal(K/k) → GL (Fin n) K) (hG : IsLift p G) : ScalarCocycle k K :=
  ⟨scalarDefect G, (lift_defect hn p G hG).2⟩

theorem liftCocycle_records (hn : 0 < n) (p : Cocycle k K n)
    (G : Gal(K/k) → GL (Fin n) K) (hG : IsLift p G) :
    RecordsDefect G (liftCocycle hn p G hG) :=
  scalarDefect_eq p G hG

private theorem records_mul {G : Gal(K/k) → GL (Fin n) K} {c : ScalarCocycle k K}
    (hc : RecordsDefect G c) (g h : Gal(K/k)) :
    G g * mapGL g (G h) = GeneralLinearGroup.scalar (Fin n) (c.val (g,h)) * G (g*h) := by
  rw [hc, inv_mul_cancel_right]

theorem recordsDefect_unique (hn : 0 < n) {G : Gal(K/k) → GL (Fin n) K}
    {a b : ScalarCocycle k K} (ha : RecordsDefect G a) (hb : RecordsDefect G b) : a = b := by
  apply Subtype.ext
  funext p
  exact scalar_injective hn ((ha p.1 p.2).trans (hb p.1 p.2).symm)


private theorem same_projective_lift_class (hn : 0 < n) (p : Cocycle k K n)
    (G H : Gal(K/k) → GL (Fin n) K) (hG : IsLift p G) (hH : IsLift p H)
    (a b : ScalarCocycle k K) (ha : RecordsDefect G a) (hb : RecordsDefect H b) :
    cocycleClass k K a = cocycleClass k K b := by
  let S := GeneralLinearGroup.scalar (Fin n) (R := K)
  have hex (g : Gal(K/k)) : ∃ t : Kˣ, H g = S t * G g := by
    obtain ⟨t, ht⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp ((hG g).trans (hH g).symm)
    exact ⟨t, ht.symm.trans (scalar_commute t (G g)).eq.symm⟩
  choose t ht using hex
  apply (cocycleClass_eq_iff a b).2
  refine ⟨t, fun g h => ?_⟩
  have hmul : b.val (g,h) * t (g*h) = t g * (g • t h) * a.val (g,h) := by
    apply scalar_injective hn
    apply mul_right_cancel (b := G (g*h))
    change S (b.val (g,h) * t (g*h)) * G (g*h) =
      S (t g * (g • t h) * a.val (g,h)) * G (g*h)
    simp only [map_mul]
    rw [mul_assoc, ← ht, ← records_mul hb, ht g, ht h, map_mul, mapGL_scalar]
    calc
      (S (t g) * G g) * (S (g • t h) * mapGL g (G h)) =
          (S (t g) * S (g • t h)) * (G g * mapGL g (G h)) := by
        rw [mul_assoc, ← mul_assoc (G g), ← (scalar_commute (g • t h) (G g)).eq]
        simp only [S, mul_assoc]
      _ = _ := by simp only [records_mul ha, S, mul_assoc]
  have hb' : b.val (g,h) = t g * (g • t h) * a.val (g,h) / t (g*h) :=
    (eq_div_iff_mul_eq').2 hmul
  change g • t h / t (g*h) * t g = b.val (g,h) / a.val (g,h)
  rw [hb']
  simp only [div_eq_mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cohomologous_lift_classes (hn : 0 < n) (p q : Cocycle k K n)
    (hpq : Cohomologous k K n p q)
    (G H : Gal(K/k) → GL (Fin n) K) (hG : IsLift p G) (hH : IsLift q H)
    (a b : ScalarCocycle k K) (ha : RecordsDefect G a) (hb : RecordsDefect H b) :
    cocycleClass k K a = cocycleClass k K b := by
  obtain ⟨u, hu⟩ := hpq
  obtain ⟨U, rfl⟩ := ProjGenLinGroup.mk_surjective u
  let T (g : Gal(K/k)) := U⁻¹ * G g * mapGL g U
  have hT : IsLift q T := by
    intro g
    simp only [T, map_mul, map_inv, mk_mapGL, hG g, hu]
  have ht : RecordsDefect T a := by
    intro g h
    apply eq_mul_inv_iff_mul_eq.mpr
    symm
    calc
      T g * mapGL g (T h) =
          U⁻¹ * (G g * mapGL g (G h)) * mapGL (g*h) U := by
        simp only [T, map_mul, map_inv, mapGL_mul_apply]
        group
      _ = _ := by
        rw [records_mul ha, ← mul_assoc U⁻¹, ← (scalar_commute (a.val (g,h)) U⁻¹).eq]
        simp only [T, mul_assoc]
  exact same_projective_lift_class hn q T H hT hH a b ht hb


section Splittings

open Algebra.TensorProduct

open private coefficient unitConj conjugation conjugation_mk
  conjugation_injective conjugation_surjective from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification

variable {A : Type w} [Ring A] [Algebra k A]
variable {B : Type x} [Ring B] [Algebra k B]

private theorem presents_apply {s : (K ⊗[k] A) ≃ₐ[K] Mat K n}
    {G : Gal(K/k) → GL (Fin n) K} (hG : Presents s G) (g : Gal(K/k)) (a : K) (x : A) :
    (G g : Mat K n) * (s (a ⊗ₜ[k] x)).map g * (↑(G g)⁻¹ : Mat K n) =
      s (g a ⊗ₜ[k] x) := by
  obtain ⟨ρ, p, hρ, hp, hG⟩ := hG
  rw [← hp g (G g) (hG g), hρ]

private theorem presents_of_formula (hn : 0 < n) (s : (K ⊗[k] A) ≃ₐ[K] Mat K n)
    (G : Gal(K/k) → GL (Fin n) K)
    (h : ∀ (g : Gal(K/k)) (a : K) (x : A),
      (G g : Mat K n) * (s (a ⊗ₜ[k] x)).map g * (↑(G g)⁻¹ : Mat K n) =
        s (g a ⊗ₜ[k] x)) : Presents s G := by
  obtain ⟨ρ, hρ, p, hp⟩ := transported_cocycle hn s
  refine ⟨ρ, p, hρ, hp, fun g => ?_⟩
  obtain ⟨H, hH⟩ := ProjGenLinGroup.mk_surjective (p.val g)
  rw [← hH]
  apply conjugation_injective
  apply AlgEquiv.ext
  intro X
  obtain ⟨Y, rfl⟩ := (coefficient g).surjective X
  have he : unitConj (G g) (coefficient g Y) = ρ.act g Y := by
    obtain ⟨y, rfl⟩ := s.surjective Y
    induction y using TensorProduct.inductionOn with
    | tmul a x =>
      rw [hρ]
      exact h g a x
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [conjugation_mk, conjugation_mk]
  exact he.trans (hp g H hH Y)

theorem exists_presentation (hn : 0 < n) (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) :
    ∃ G : Gal(K/k) → GL (Fin n) K, Presents s G := by
  obtain ⟨ρ, hρ, p, hp⟩ := transported_cocycle hn s
  choose G hG using fun g : Gal(K/k) => ProjGenLinGroup.mk_surjective (p.val g)
  exact ⟨G, ρ, p, hρ, hp, hG⟩

theorem exists_recorded_defect (hn : 0 < n)
    {s : (K ⊗[k] A) ≃ₐ[K] Mat K n} {G : Gal(K/k) → GL (Fin n) K}
    (hG : Presents s G) : ∃ c : ScalarCocycle k K, RecordsDefect G c := by
  obtain ⟨ρ, p, hρ, hp, hG⟩ := hG
  exact ⟨liftCocycle hn p G hG, liftCocycle_records hn p G hG⟩

theorem splitting_lift_classes (hn : 0 < n) (s t : (K ⊗[k] A) ≃ₐ[K] Mat K n)
    (G H : Gal(K/k) → GL (Fin n) K) (hG : Presents s G) (hH : Presents t H)
    (a b : ScalarCocycle k K) (ha : RecordsDefect G a) (hb : RecordsDefect H b) :
    cocycleClass k K a = cocycleClass k K b := by
  obtain ⟨ρ, p, hρ, hp, hG⟩ := hG
  obtain ⟨τ, q, hτ, hq, hH⟩ := hH
  obtain ⟨V, hV⟩ := conjugation_surjective hn (t.symm.trans s)
  obtain ⟨U, rfl⟩ := ProjGenLinGroup.mk_surjective V
  have hU (y : K ⊗[k] A) :
      t y = (↑U⁻¹ : Mat K n) * s y * (U : Mat K n) := by
    have he := DFunLike.congr_fun hV (t y)
    rw [conjugation_mk, AlgEquiv.trans_apply, t.symm_apply_apply] at he
    rw [← he]
    simp [mul_assoc]
  exact cohomologous_lift_classes hn p q
    ⟨ProjGenLinGroup.mk U, change_splitting s t U hU ρ τ p q hρ hτ hp hq⟩
    G H hG hH a b ha hb

private theorem kroneckerLift_mul {m : ℕ}
    (G G' : GL (Fin m) K) (H H' : GL (Fin n) K) :
    kroneckerLift (G * G') (H * H') = kroneckerLift G H * kroneckerLift G' H' := by
  unfold kroneckerLift
  rw [← map_mul]
  congr 1
  apply Units.ext
  exact mul_kronecker_mul _ _ _ _

private theorem mapGL_kroneckerLift {m : ℕ} (g : Gal(K/k))
    (G : GL (Fin m) K) (H : GL (Fin n) K) :
    mapGL g (kroneckerLift G H) = kroneckerLift (mapGL g G) (mapGL g H) := by
  apply Units.ext
  ext i j
  let e : Fin m × Fin n ≃ Fin (m*n) := finProdFinEquiv
  change g (G.val (e.symm i).1 (e.symm j).1 * H.val (e.symm i).2 (e.symm j).2) =
    g (G.val (e.symm i).1 (e.symm j).1) * g (H.val (e.symm i).2 (e.symm j).2)
  exact map_mul g _ _

private theorem kroneckerLift_scalar (m n : ℕ) (a b : Kˣ) :
    kroneckerLift (GeneralLinearGroup.scalar (Fin m) a)
        (GeneralLinearGroup.scalar (Fin n) b) = GeneralLinearGroup.scalar (Fin (m*n)) (a*b) := by
  apply Units.ext
  unfold kroneckerLift
  change Matrix.reindexAlgEquiv K K finProdFinEquiv
    ((GeneralLinearGroup.scalar (Fin m) a).val ⊗ₖ (GeneralLinearGroup.scalar (Fin n) b).val) =
      (GeneralLinearGroup.scalar (Fin (m*n)) (a*b)).val
  change Matrix.reindexAlgEquiv K K finProdFinEquiv
    (Matrix.diagonal (fun _ : Fin m => (a : K)) ⊗ₖ Matrix.diagonal (fun _ : Fin n => (b : K))) =
      Matrix.diagonal (fun _ : Fin (m*n) => (a : K) * (b : K))
  rw [diagonal_kronecker_diagonal]
  ext i j
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Equiv.apply_eq_iff_eq]

private def flatten {m : ℕ} (X : Matrix (Fin m × Fin n) (Fin m × Fin n) K) : Mat K (m*n) :=
  Matrix.reindexAlgEquiv K K finProdFinEquiv X

private theorem flatten_map {m : ℕ} (g : Gal(K/k))
    (X : Matrix (Fin m × Fin n) (Fin m × Fin n) K) :
    (flatten X).map g = flatten (X.map g) := rfl

private theorem flatten_mul {m : ℕ} (X Y : Matrix (Fin m × Fin n) (Fin m × Fin n) K) :
    flatten (X * Y) = flatten X * flatten Y :=
  map_mul (Matrix.reindexAlgEquiv K K finProdFinEquiv) X Y

private theorem kronecker_map {m : ℕ} (g : Gal(K/k)) (X : Mat K m) (Y : Mat K n) :
    (X ⊗ₖ Y).map g = X.map g ⊗ₖ Y.map g := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  exact map_mul g _ _

private def tensorSplitting {m : ℕ} (s : (K ⊗[k] A) ≃ₐ[K] Mat K m)
    (t : (K ⊗[k] B) ≃ₐ[K] Mat K n) : (K ⊗[k] (A ⊗[k] B)) ≃ₐ[K] Mat K (m*n) :=
  (baseChangeTensor k K A B).trans <|
    (Algebra.TensorProduct.congr s t).trans <|
      (Matrix.kroneckerAlgEquiv (Fin m) (Fin n) K).trans (Matrix.reindexAlgEquiv K K finProdFinEquiv)

private theorem tensorSplitting_tmul {m : ℕ} (s : (K ⊗[k] A) ≃ₐ[K] Mat K m)
    (t : (K ⊗[k] B) ≃ₐ[K] Mat K n) (a : K) (x : A) (y : B) :
    tensorSplitting s t (a ⊗ₜ[k] (x ⊗ₜ[k] y)) =
      flatten (s (a ⊗ₜ[k] x) ⊗ₖ t (1 ⊗ₜ[k] y)) := rfl

theorem tensor_lift_defect {m : ℕ} (hm : 0 < m) (hn : 0 < n)
    (s : (K ⊗[k] A) ≃ₐ[K] Mat K m) (t : (K ⊗[k] B) ≃ₐ[K] Mat K n)
    (G : Gal(K/k) → GL (Fin m) K) (H : Gal(K/k) → GL (Fin n) K)
    (hG : Presents s G) (hH : Presents t H)
    (a b : ScalarCocycle k K) (ha : RecordsDefect G a) (hb : RecordsDefect H b) :
    ∃ st : (K ⊗[k] (A ⊗[k] B)) ≃ₐ[K] Mat K (m*n),
      Presents st (fun g => kroneckerLift (G g) (H g)) ∧
        RecordsDefect (fun g => kroneckerLift (G g) (H g)) (a*b) := by
  refine ⟨tensorSplitting s t, presents_of_formula (Nat.mul_pos hm hn) _ _ ?_, ?_⟩
  · intro g l z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      rw [tensorSplitting_tmul, tensorSplitting_tmul, flatten_map, kronecker_map]
      change flatten ((G g).val ⊗ₖ (H g).val) *
          flatten ((s (l ⊗ₜ[k] x)).map g ⊗ₖ (t (1 ⊗ₜ[k] y)).map g) *
          flatten (((G g)⁻¹).val ⊗ₖ ((H g)⁻¹).val) = _
      rw [← flatten_mul, ← flatten_mul, ← mul_kronecker_mul, ← mul_kronecker_mul,
        presents_apply hG, presents_apply hH, map_one]
    | add z z' hz hz' =>
      change _ * coefficient g (tensorSplitting s t (l ⊗ₜ[k] z)) * _ = _ at hz
      change _ * coefficient g (tensorSplitting s t (l ⊗ₜ[k] z')) * _ = _ at hz'
      change _ * coefficient g (tensorSplitting s t (l ⊗ₜ[k] (z + z'))) * _ = _
      simp only [TensorProduct.tmul_add, map_add, mul_add, add_mul, hz, hz']
  · intro g h
    apply eq_mul_inv_iff_mul_eq.mpr
    symm
    change kroneckerLift (G g) (H g) * mapGL g (kroneckerLift (G h) (H h)) =
      GeneralLinearGroup.scalar (Fin (m*n)) (a.val (g,h) * b.val (g,h)) *
        kroneckerLift (G (g*h)) (H (g*h))
    rw [mapGL_kroneckerLift, ← kroneckerLift_mul, records_mul ha, records_mul hb,
      kroneckerLift_mul, kroneckerLift_scalar]


private def splittingOfEquiv (e : A ≃ₐ[k] B) (t : (K ⊗[k] B) ≃ₐ[K] Mat K n) :
    (K ⊗[k] A) ≃ₐ[K] Mat K n :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e).trans t

private theorem presents_of_equiv (hn : 0 < n) (e : A ≃ₐ[k] B)
    {t : (K ⊗[k] B) ≃ₐ[K] Mat K n} {G : Gal(K/k) → GL (Fin n) K}
    (hG : Presents t G) : Presents (splittingOfEquiv e t) G :=
  presents_of_formula hn _ G fun g a x => presents_apply hG g a (e x)

private noncomputable def splitMatrix (m : ℕ) : (K ⊗[k] Mat k m) ≃ₐ[K] Mat K m :=
  (baseChangeMatrix k K m k).trans (Algebra.TensorProduct.rid k K K).mapMatrix

private theorem splitMatrix_tmul (m : ℕ) (a : K) (M : Mat k m) (i j : Fin m) :
    splitMatrix m (a ⊗ₜ[k] M) i j = algebraMap k K (M i j) * a := by
  simp only [splitMatrix, AlgEquiv.trans_apply, AlgEquiv.mapMatrix_apply, Matrix.map_apply,
    baseChangeMatrix_tmul, Algebra.TensorProduct.rid_tmul, Algebra.smul_def]

private theorem splitMatrix_presents {m : ℕ} (hm : 0 < m) :
    Presents (splitMatrix (k := k) (K := K) m) (fun _ => 1) := by
  apply presents_of_formula hm
  intro g a M
  simp only [Units.val_one, inv_one, one_mul, mul_one]
  ext i j
  simp [splitMatrix_tmul, map_mul]

private theorem one_records (m : ℕ) :
    RecordsDefect (fun _ : Gal(K/k) => (1 : GL (Fin m) K)) (1 : ScalarCocycle k K) := by
  intro g h
  change GeneralLinearGroup.scalar (Fin m) (1 : Kˣ) = 1 * mapGL g 1 * (1 : GL (Fin m) K)⁻¹
  simp

theorem enlargement_lift_defect {m : ℕ} (hm : 0 < m) (hn : 0 < n)
    (s : (K ⊗[k] A) ≃ₐ[K] Mat K n) (G : Gal(K/k) → GL (Fin n) K) (hG : Presents s G)
    (a : ScalarCocycle k K) (ha : RecordsDefect G a) :
    ∃ t : (K ⊗[k] Matrix (Fin m) (Fin m) A) ≃ₐ[K] Mat K (m*n),
      Presents t (fun g => kroneckerLift (1 : GL (Fin m) K) (G g)) ∧
      RecordsDefect (fun g => kroneckerLift (1 : GL (Fin m) K) (G g)) a := by
  obtain ⟨st, hp, hd⟩ := tensor_lift_defect hm hn (splitMatrix m) s (fun _ => 1) G
    (splitMatrix_presents hm) hG 1 a (one_records m) ha
  let e : Matrix (Fin m) (Fin m) A ≃ₐ[k] Mat k m ⊗[k] A :=
    (matrixEquivTensor (Fin m) k A).trans
      (Algebra.TensorProduct.comm k A (Mat k m))
  exact ⟨splittingOfEquiv e st, presents_of_equiv (Nat.mul_pos hm hn) e hp, by simpa using hd⟩

private theorem isomorphic_lift_classes {m : ℕ} (hm : 0 < m) (hn : 0 < n) (e : A ≃ₐ[k] B)
    (s : (K ⊗[k] A) ≃ₐ[K] Mat K m) (t : (K ⊗[k] B) ≃ₐ[K] Mat K n)
    (G : Gal(K/k) → GL (Fin m) K) (H : Gal(K/k) → GL (Fin n) K)
    (hG : Presents s G) (hH : Presents t H)
    (a b : ScalarCocycle k K) (ha : RecordsDefect G a) (hb : RecordsDefect H b) :
    cocycleClass k K a = cocycleClass k K b := by
  have hmn : m = n := by
    apply Nat.mul_self_inj.mp
    simpa [Module.finrank_matrix] using (s.symm.trans (splittingOfEquiv e t)).toLinearEquiv.finrank_eq
  subst n
  exact splitting_lift_classes hm s (splittingOfEquiv e t) G H hG
    (presents_of_equiv hm e hH) a b ha hb

theorem equivalent_lift_classes {m : ℕ} (hm : 0 < m) (hn : 0 < n)
    (e : RM03.Brauer.Equivalent k A B)
    (s : (K ⊗[k] A) ≃ₐ[K] Mat K m) (t : (K ⊗[k] B) ≃ₐ[K] Mat K n)
    (G : Gal(K/k) → GL (Fin m) K) (H : Gal(K/k) → GL (Fin n) K)
    (hG : Presents s G) (hH : Presents t H)
    (a b : ScalarCocycle k K) (ha : RecordsDefect G a) (hb : RecordsDefect H b) :
    cocycleClass k K a = cocycleClass k K b := by
  obtain ⟨p, q, hp, hq, ⟨e⟩⟩ := e
  obtain ⟨s', hs', ha'⟩ := enlargement_lift_defect hp hm s G hG a ha
  obtain ⟨t', ht', hb'⟩ := enlargement_lift_defect hq hn t H hH b hb
  exact isomorphic_lift_classes (Nat.mul_pos hp hm) (Nat.mul_pos hq hn) e s' t' _ _ hs' ht' a b ha' hb'

end Splittings


open private csa_eq_of_toAlgCat_eq from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.BaseChange

section BrauerMap

private def SplitDefect (A : Type x) [Ring A] [Algebra k A] (c : ScalarCocycle k K) : Prop :=
  ∃ (n : ℕ) (_ : 0 < n) (s : (K ⊗[k] A) ≃ₐ[K] Mat K n)
    (G : Gal(K/k) → GL (Fin n) K), Presents s G ∧ RecordsDefect G c

private theorem exists_split_defect {A : Type x} [Ring A] [Algebra k A]
    (hA : RM03.CSA.Splits k K A) : ∃ c : ScalarCocycle k K, SplitDefect A c := by
  obtain ⟨n, hn, ⟨s⟩⟩ := hA
  obtain ⟨G, hG⟩ := exists_presentation hn s
  obtain ⟨a, ha⟩ := exists_recorded_defect hn hG
  exact ⟨a, n, hn, s, G, hG, ha⟩

variable [AddCommGroup (BrauerGroup.{u, max u v w} k)]
  [AddCommGroup (BrauerGroup.{v, max u v w} K)]
variable (f : BrauerGroup.{u, max u v w} k →+ BrauerGroup.{v, max u v w} K)
variable (hSplit : ∀ A : _root_.CSA.{u, max u v w} k,
  classOf A ∈ relativeSubgroup f ↔ RM03.CSA.Splits k K A)

include hSplit in
private theorem relative_defect (q : relativeSubgroup f) :
    ∃ a : ScalarCocycle k K, ∃ A : _root_.CSA.{u, max u v w} k,
      classOf A = q.val ∧ SplitDefect A a := by
  obtain ⟨A, hA⟩ := Quotient.exists_rep q.val
  change classOf A = q.val at hA
  have hq : classOf A ∈ relativeSubgroup f := by
    rw [hA]
    exact q.property
  obtain ⟨a, ha⟩ := exists_split_defect ((hSplit A).1 hq)
  exact ⟨a, A, hA, ha⟩

private noncomputable def obstructionValue (q : relativeSubgroup f) : Additive (H2 k K) :=
  Additive.ofMul (cocycleClass k K (relative_defect f hSplit q).choose)

private theorem obstructionValue_formula (q : relativeSubgroup f)
    (A : _root_.CSA.{u, max u v w} k) (hA : classOf A = q.val)
    (a : ScalarCocycle k K) (ha : SplitDefect A a) :
    obstructionValue f hSplit q = Additive.ofMul (cocycleClass k K a) := by
  obtain ⟨B, hB, hb⟩ := (relative_defect f hSplit q).choose_spec
  obtain ⟨m, hm, t, H, hH, hb⟩ := hb
  obtain ⟨n, hn, s, G, hG, ha⟩ := ha
  apply congrArg Additive.ofMul
  exact equivalent_lift_classes hm hn ((classOf_eq_iff k B A).mp (hB.trans hA.symm))
    t s H G hH hG _ a hb ha

variable (hAdd : ∀ A B : _root_.CSA.{u, max u v w} k,
  classOf A + classOf B = classOf (tensorCSA A B))

include hAdd in
private theorem obstructionValue_add (x y : relativeSubgroup f) :
    obstructionValue f hSplit (x+y) =
      obstructionValue f hSplit x + obstructionValue f hSplit y := by
  obtain ⟨a, A, hA, m, hm, s, G, hG, ha⟩ := relative_defect f hSplit x
  obtain ⟨b, B, hB, n, hn, t, H, hH, hb⟩ := relative_defect f hSplit y
  obtain ⟨st, hst, hab⟩ := tensor_lift_defect hm hn s t G H hG hH a b ha hb
  have he : classOf (tensorCSA A B) = (x+y).val := by
    rw [← hAdd, hA, hB]
    rfl
  rw [obstructionValue_formula f hSplit x A hA a ⟨m, hm, s, G, hG, ha⟩,
    obstructionValue_formula f hSplit y B hB b ⟨n, hn, t, H, hH, hb⟩,
    obstructionValue_formula f hSplit (x+y) (tensorCSA A B) he (a*b)
      ⟨m*n, Nat.mul_pos hm hn, st, _, hst, hab⟩, map_mul, ofMul_mul]

private noncomputable def obstructionFor :
    relativeSubgroup f →+ Additive (H2 k K) where
  toFun := obstructionValue f hSplit
  map_zero' := by
    have h := obstructionValue_add f hSplit hAdd 0 0
    rw [zero_add] at h
    let z : H2 k K := (obstructionValue f hSplit 0).toMul
    change z = z * z at h
    change z = 1
    calc
      z = z⁻¹ * (z * z) := (inv_mul_cancel_left z z).symm
      _ = z⁻¹ * z := congrArg (z⁻¹ * ·) h.symm
      _ = 1 := inv_mul_cancel z
  map_add' := obstructionValue_add f hSplit hAdd

private theorem obstructionFor_formula :
    IsObstructionHom.{u,v,w} f (obstructionFor f hSplit hAdd) := by
  intro A hA n hn s G hG a ha
  exact obstructionValue_formula f hSplit _ A rfl a ⟨n, hn, s, G, hG, ha⟩

end BrauerMap

/-- The scalar obstruction homomorphism on the relative Brauer group. -/
noncomputable def obstruction (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] :
    relativeBrauerGroup.{u,v,w} k K →+ Additive (H2 k K) :=
  obstructionFor (baseChange.{u,v,w} k K) (classOf_mem_relativeBrauerGroup_iff k K) classOf_add.{u, max v w}

/-- Every splitting and every lift computes the same value of the homomorphism. -/
theorem obstruction_formula (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] :
    IsObstructionHom.{u,v,w} (baseChange.{u,v,w} k K) (obstruction.{u,v,w} k K) :=
  obstructionFor_formula (baseChange.{u,v,w} k K)
    (classOf_mem_relativeBrauerGroup_iff k K) classOf_add.{u, max v w}

theorem obstruction_hom : ObstructionHom.{u,v,w} := by
  intro k K _ _ _ _ _ gk gK hk hK
  let _ := gk
  let _ := gK
  intro f hf
  have hSplit (A : _root_.CSA.{u, max u v w} k) :
      classOf A ∈ relativeSubgroup f ↔ RM03.CSA.Splits k K A := by
    obtain ⟨B, hB, hF⟩ := hf A
    have he : B = baseChangeCSA k K A := csa_eq_of_toAlgCat_eq hB
    change f (Specs.RM03.Brauer.classOf A) = 0 ↔ _
    rw [hF, he]
    exact hK.2.2.2 (baseChangeCSA k K A)
  have hAdd (A B : _root_.CSA.{u, max u v w} k) :
      classOf A + classOf B = classOf (tensorCSA A B) := by
    obtain ⟨C, hC, hEq⟩ := hk.2.1 A B
    have he : C = tensorCSA A B := csa_eq_of_toAlgCat_eq hC
    exact hEq.trans (congrArg classOf he)
  refine ⟨obstructionFor f hSplit hAdd, obstructionFor_formula f hSplit hAdd, fun φ hφ => ?_⟩
  apply AddMonoidHom.ext
  intro q
  obtain ⟨a, A, hA, n, hn, s, G, hG, ha⟩ := relative_defect f hSplit q
  have hA' : classOf A ∈ relativeSubgroup f := by
    rw [hA]
    exact q.property
  have hq : (⟨classOf A, hA'⟩ : relativeSubgroup f) = q := Subtype.ext hA
  rw [← hq]
  exact (hφ A hA' hn s G hG a ha).trans
    (obstructionFor_formula f hSplit hAdd A hA' hn s G hG a ha).symm

end RM03.Brauer.ScalarObstruction
