import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GroupBarResolution

noncomputable section
open CategoryTheory
open scoped MonoidAlgebra
namespace GroupBar
universe u
variable (k G : Type u) [CommRing k] [Group G]

lemma diagonal_action (n : ℕ) (g : G) (c : Fin (n + 1) → G) (r : k) :
    (B k G n).ρ g (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (fun i => g * c i) r := by
  exact Representation.ofMulAction_single g c r

lemma boundary_single (n : ℕ) (c : Fin (n + 2) → G) (r : k) :
    d k G n (MonoidAlgebra.single c r) =
      ∑ i : Fin (n + 2), MonoidAlgebra.single (c ∘ i.succAbove) (r * (-1 : k) ^ i.val) := by
  change ((Rep.standardComplex k G).d (n + 1) n).hom.toLinearMap _ = _
  rw [Rep.standardComplex.d_eq]
  exact Rep.standardComplex.d_single c r

@[simp] lemma augmentation_single (c : Fin 1 → G) (r : k) :
    ε k G (MonoidAlgebra.single c r) = r := by
  simp [ε, augmentation, Rep.standardComplex.ε]

lemma degree_free (n : ℕ) : Module.Free k[G] (B k G n).ρ.asModule := by
  let e := (Rep.toModuleMonoidAlgebra.mapIso (Rep.diagonalSuccIsoFree k G n)).toLinearEquiv
  exact Module.Free.of_basis ((Representation.freeAsModuleBasis k G (Fin n → G)).map e.symm)

@[simp] lemma s_single (n : ℕ) (c : Fin (n + 1) → G) (r : k) :
    s k G n (MonoidAlgebra.single c r) = MonoidAlgebra.single (Fin.cons 1 c) r := by
  simp [s]

@[simp] lemma sAug_apply (r : k) :
    sAug k G r = MonoidAlgebra.single (fun _ : Fin 1 => (1 : G)) r := by
  simp [sAug, MonoidAlgebra.smul_single]

lemma prepend_boundary_single (n : ℕ) (c : Fin (n + 1) → G) (r : k) :
    Rep.standardComplex.d k G (n + 1) (MonoidAlgebra.single (Fin.cons 1 c) r) +
      MonoidAlgebra.mapDomainLinearMap k k (fun c : Fin n → G => Fin.cons (1 : G) c)
        (Rep.standardComplex.d k G n (MonoidAlgebra.single c r)) =
      MonoidAlgebra.single c r := by
  rw [Rep.standardComplex.d_single, Rep.standardComplex.d_single, map_sum,
    Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.succAbove_zero, Fin.cons_comp_succ,
    Fin.cons_comp_succ_succAbove, Fin.val_succ, pow_succ, mul_neg, mul_one,
    MonoidAlgebra.single_neg, MonoidAlgebra.mapDomainLinearMap_single]
  have h (i : Fin (n + 1)) : i.removeNth c = c ∘ i.succAbove := rfl
  simp_rw [h]
  rw [Finset.sum_neg_distrib]
  simp [add_assoc]

lemma d_eq (n : ℕ) : d k G n = Rep.standardComplex.d k G (n + 1) :=
  Rep.standardComplex.d_eq k G n

lemma contraction_succ (n : ℕ) :
    d k G (n + 1) ∘ₗ s k G (n + 1) + s k G n ∘ₗ d k G n = LinearMap.id := by
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change d k G (n + 1) (s k G (n + 1) (MonoidAlgebra.single c 1)) +
    s k G n (d k G n (MonoidAlgebra.single c 1)) = MonoidAlgebra.single c 1
  rw [s_single, d_eq, d_eq]
  exact prepend_boundary_single k G (n + 1) c 1

lemma contraction_zero :
    d k G 0 ∘ₗ s k G 0 + sAug k G ∘ₗ ε k G = LinearMap.id := by
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change d k G 0 (s k G 0 (MonoidAlgebra.single c 1)) +
    sAug k G (ε k G (MonoidAlgebra.single c 1)) = MonoidAlgebra.single c 1
  rw [s_single, augmentation_single, sAug_apply, d_eq]
  have h := prepend_boundary_single k G 0 c 1
  have hc : Fin.cons (1 : G) (c ∘ Fin.succ) = (fun _ : Fin 1 => (1 : G)) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  simpa [Rep.standardComplex.d_single, hc] using h

lemma contraction_aug : ε k G ∘ₗ sAug k G = LinearMap.id := by
  apply LinearMap.ext
  intro r
  change ε k G (sAug k G r) = r
  rw [sAug_apply, augmentation_single]

lemma boundary_squared (n : ℕ) : boundary k G (n + 1) ≫ boundary k G n = 0 :=
  (complex k G).d_comp_d (n + 2) (n + 1) n

lemma boundary_augmentation : boundary k G 0 ≫ augmentation k G = 0 :=
  Rep.standardComplex.d_comp_ε k G

lemma augmentation_surjective : Function.Surjective (ε k G) := by
  intro r
  exact ⟨sAug k G r, LinearMap.congr_fun (contraction_aug k G) r⟩

lemma exact_zero (x : B k G 0) :
    ε k G x = 0 ↔ ∃ y : B k G 1, d k G 0 y = x := by
  constructor
  · intro hx
    refine ⟨s k G 0 x, ?_⟩
    have h := LinearMap.congr_fun (contraction_zero k G) x
    change d k G 0 (s k G 0 x) + sAug k G (ε k G x) = x at h
    rw [hx, map_zero, add_zero] at h
    exact h
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : B k G 1 ⟶ Rep.trivial k G k => f.hom.toLinearMap)
      (boundary_augmentation k G)
    exact LinearMap.congr_fun h y

lemma exact_succ (n : ℕ) (x : B k G (n + 1)) :
    d k G n x = 0 ↔ ∃ y : B k G (n + 2), d k G (n + 1) y = x := by
  constructor
  · intro hx
    refine ⟨s k G (n + 1) x, ?_⟩
    have h := LinearMap.congr_fun (contraction_succ k G n) x
    change d k G (n + 1) (s k G (n + 1) x) + s k G n (d k G n x) = x at h
    rw [hx, map_zero, add_zero] at h
    exact h
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f : B k G (n + 2) ⟶ B k G n => f.hom.toLinearMap)
      (boundary_squared k G n)
    exact LinearMap.congr_fun h y

/-- HA-A02: the homogeneous bar complex is a free augmented resolution,
contracted over k by prepending the identity element. -/
theorem resolution : Resolution k G := by
  exact ⟨diagonal_action k G, boundary_single k G, augmentation_single k G,
    boundary_squared k G, boundary_augmentation k G, degree_free k G,
    s_single k G, sAug_apply k G, contraction_aug k G, contraction_zero k G,
    contraction_succ k G, augmentation_surjective k G, exact_zero k G, exact_succ k G⟩

end GroupBar

namespace GroupBar.Large

universe u v w
variable (k : Type u) (G : Type v) [CommRing k] [Group G]

@[simp] lemma originalBasis_single (n : ℕ) (c : Fin (n + 1) → G) (r : k) :
    originalBasis.{u,v,w} k G n (single k G c r) = MonoidAlgebra.single c r := by
  simp [originalBasis, single]

lemma diagonal_action (n : ℕ) (g : G) (c : Fin (n + 1) → G) (r : k) :
    (B.{u,v,w} k G n).ρ g (single k G c r) = single k G (fun i => g * c i) r :=
  Representation.ofMulAction_single g (ULift.up c) r

set_option backward.isDefEq.respectTransparency false in
lemma boundary_single (n : ℕ) (c : Fin (n + 2) → G) (r : k) :
    d.{u,v,w} k G n (single k G c r) =
      ∑ i : Fin (n + 2), single k G (c ∘ i.succAbove) (r * (-1 : k) ^ i.val) := by
  simp only [d, boundary, complex, AlgebraicTopology.alternatingFaceMapComplex,
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
    ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : ℤ), Int.cast_pow, Int.cast_neg, Int.cast_one,
    SimplicialObject.δ, Functor.comp_map, Rep.sum_hom, Rep.smul_hom, Rep.hom_ofHom,
    Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ((-1 : k) ^ i.val) •
    (Representation.linearizeMap
      ((liftedCover.{v,w} G).map (SimplexCategory.δ i).op)) (single k G c r) = _
  rw [Representation.linearizeMap_single]
  change ((-1 : k) ^ i.val) • single k G (c ∘ i.succAbove) r = _
  rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_comm]

@[simp] lemma augmentation_single (c : Fin 1 → G) (r : k) :
    ε.{u,v,w} k G (single k G c r) = r := by
  simp [ε, single]

@[simp] lemma s_single (n : ℕ) (c : Fin (n + 1) → G) (r : k) :
    s.{u,v,w} k G n (single k G c r) = single k G (Fin.cons 1 c) r := by
  simp [s, single]

@[simp] lemma sAug_apply (r : k) :
    sAug.{u,v,w} k G r = single k G (fun _ : Fin 1 => 1) r := by
  simp [sAug, single, MonoidAlgebra.smul_single]

lemma contraction_aug : ε.{u,v,w} k G ∘ₗ sAug k G = LinearMap.id := by
  apply LinearMap.ext
  intro r
  change ε.{u,v,w} k G (sAug k G r) = r
  rw [sAug_apply, augmentation_single]

private lemma tail_after_prepend (c : Fin 1 → G) :
    Fin.cons (1 : G) (Fin.tail c) = (fun _ : Fin 1 => (1 : G)) := by
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

lemma contraction_zero :
    d.{u,v,w} k G 0 ∘ₗ s k G 0 + sAug k G ∘ₗ ε k G = LinearMap.id := by
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  apply LinearMap.ext_ring
  change d.{u,v,w} k G 0 (s k G 0 (single k G c 1)) +
    sAug k G (ε k G (single k G c 1)) = single k G c 1
  rw [s_single, augmentation_single, sAug_apply, boundary_single, Fin.sum_univ_succ]
  simp [Fin.succAbove_zero, Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove,
    tail_after_prepend, single, add_assoc]

lemma contraction_succ (n : ℕ) :
    d.{u,v,w} k G (n + 1) ∘ₗ s k G (n + 1) + s k G n ∘ₗ d k G n = LinearMap.id := by
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  apply LinearMap.ext_ring
  change d.{u,v,w} k G (n + 1) (s k G (n + 1) (single k G c 1)) +
    s k G n (d k G n (single k G c 1)) = single k G c 1
  rw [s_single, boundary_single, boundary_single, map_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.succAbove_zero, Fin.cons_comp_succ,
    Fin.cons_comp_succ_succAbove, Fin.val_succ, pow_succ, mul_neg]
  simp_rw [s_single.{u,v,w} k G n]
  have h (i : Fin (n + 2)) : i.removeNth c = c ∘ i.succAbove := rfl
  simp_rw [h]
  simp only [single, one_mul, MonoidAlgebra.single_neg, Finset.sum_neg_distrib]
  simp [add_assoc]

lemma boundary_squared (n : ℕ) : boundary.{u,v,w} k G (n + 1) ≫ boundary k G n = 0 :=
  (complex.{u,v,w} k G).d_comp_d (n + 2) (n + 1) n

lemma boundary_augmentation : boundary.{u,v,w} k G 0 ≫ augmentation k G = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.toLinearMap_injective
  apply MonoidAlgebra.lhom_ext'
  rintro ⟨c⟩
  apply LinearMap.ext_ring
  change ULift.up (ε.{u,v,w} k G (d k G 0 (single k G c 1))) = ULift.up 0
  congr 1
  rw [boundary_single, map_sum]
  simp only [augmentation_single.{u,v,w} k G, one_mul]
  simp [Fin.sum_univ_succ]

lemma augmentation_surjective : Function.Surjective (ε.{u,v,w} k G) := by
  intro r
  exact ⟨sAug k G r, LinearMap.congr_fun (contraction_aug k G) r⟩

lemma exact_zero (x : B.{u,v,w} k G 0) :
    ε k G x = 0 ↔ ∃ y : B.{u,v,w} k G 1, d k G 0 y = x := by
  constructor
  · intro hx
    refine ⟨s k G 0 x, ?_⟩
    have h := LinearMap.congr_fun (contraction_zero k G) x
    change d k G 0 (s k G 0 x) + sAug k G (ε k G x) = x at h
    simpa [hx] using h
  · rintro ⟨y, rfl⟩
    exact congrArg (fun f : B.{u,v,w} k G 1 ⟶ trivial.{u,v,w} k G =>
      (f.hom y : ULift.{max v w} k).down) (boundary_augmentation k G)

lemma exact_succ (n : ℕ) (x : B.{u,v,w} k G (n + 1)) :
    d k G n x = 0 ↔ ∃ y : B.{u,v,w} k G (n + 2), d k G (n + 1) y = x := by
  constructor
  · intro hx
    refine ⟨s k G (n + 1) x, ?_⟩
    have h := LinearMap.congr_fun (contraction_succ k G n) x
    change d k G (n + 1) (s k G (n + 1) x) + s k G n (d k G n x) = x at h
    simpa [hx] using h
  · rintro ⟨y, rfl⟩
    exact congrArg (fun f : B.{u,v,w} k G (n + 2) ⟶ B.{u,v,w} k G n => f.hom y)
      (boundary_squared k G n)

/-- Separate the first coordinate of a tuple and translate its tail so that
the first coordinate becomes the identity. -/
private def tupleEquiv (n : ℕ) :
    ULift.{w} (Fin (n + 1) → G) ≃ ULift.{max u w} (Fin n → G) × G where
  toFun c := (ULift.up (fun i => (c.down 0)⁻¹ * c.down i.succ), c.down 0)
  invFun p := ULift.up (Fin.cons p.2 (fun i => p.2 * p.1.down i))
  left_inv c := by
    apply ULift.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv p := by
    apply Prod.ext
    · apply ULift.ext
      funext i
      simp
    · rfl

/-- The signed deletion complex is free over the original group algebra in every degree. -/
lemma degree_free (n : ℕ) : Module.Free k[G] (B.{u,v,w} k G n).ρ.asModule := by
  let α := ULift.{max u w} (Fin n → G)
  let e : B.{u,v,w} k G n ≃ₗ[k] (α →₀ k[G]) :=
    (MonoidAlgebra.mapDomainLinearEquiv k k (tupleEquiv.{u,v,w} G n)).trans
      ((MonoidAlgebra.coeffLinearEquiv k).trans
        ((Finsupp.curryLinearEquiv k).trans
          (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv k).symm)))
  have e_single (c : Fin (n + 1) → G) (r : k) :
      e (single k G c r) =
        Finsupp.single (ULift.up (fun i => (c 0)⁻¹ * c i.succ))
          (MonoidAlgebra.single (c 0) r) := by
    simp [e, single, tupleEquiv, Finsupp.curryLinearEquiv]
  -- Left translation acts on the first coordinate and fixes the normalized tail.
  let iso : B.{u,v,w} k G n ≅ Rep.free k G α :=
    Rep.mkIso (Representation.Equiv.mk e (fun g => by
      apply MonoidAlgebra.lhom_ext'
      rintro ⟨c⟩
      apply LinearMap.ext_ring
      change e ((B.{u,v,w} k G n).ρ g (single k G c 1)) =
        Representation.free k G α g (e (single k G c 1))
      rw [diagonal_action, e_single, e_single, Representation.free_single_single]
      simp [mul_inv_rev, mul_assoc]))
  let linearIso := (Rep.toModuleMonoidAlgebra.mapIso iso).toLinearEquiv
  exact Module.Free.of_basis ((Representation.freeAsModuleBasis k G α).map linearIso.symm)

/-- The homogeneous bar resolution over independently sized rings and groups. -/
theorem resolution : Resolution.{u,v,w} k G :=
  ⟨originalBasis_single k G, diagonal_action k G, boundary_single k G, augmentation_single k G,
    boundary_squared k G, boundary_augmentation k G, degree_free k G, s_single k G,
    sAug_apply k G, contraction_aug k G, contraction_zero k G, contraction_succ k G,
    augmentation_surjective k G, exact_zero k G, exact_succ k G⟩

end GroupBar.Large
