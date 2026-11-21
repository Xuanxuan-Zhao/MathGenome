import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergGraded
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.PBWGraded
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Pure tensors from the specified word-length step belong to the weight step. -/
theorem tmul_mem_weight (a : ℤ) (n : ℕ) (u : U k g) (z : W k g n)
    (hu : u ∈ Shared.Lie.filtration k g (a-n)) :
    u ⊗ₜ[k] z ∈ weight k g a n :=
  ⟨⟨u, hu⟩ ⊗ₜ[k] z, rfl⟩

/-- The image definition is exactly the span of tensors from the step. -/
theorem weight_eq_span (a : ℤ) (n : ℕ) : weight k g a n =
    Submodule.span k {t | ∃ u : U k g, ∃ z : W k g n,
      u ∈ Shared.Lie.filtration k g (a-n) ∧ u ⊗ₜ[k] z = t} := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul u z => exact Submodule.subset_span ⟨u.val, z, u.property, rfl⟩
    | add t s ht hs => simpa using Submodule.add_mem _ ht hs
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, z, hu, rfl⟩
    exact tmul_mem_weight k g a n u z hu

theorem weight_mono (n : ℕ) : Monotone (fun a => weight k g a n) := by
  intro a b hab
  change weight k g a n ≤ weight k g b n
  rw [weight_eq_span, weight_eq_span]
  apply Submodule.span_mono
  rintro _ ⟨u, z, hu, rfl⟩
  exact ⟨u, z, Shared.Lie.filtration_mono k g (by omega) hu, rfl⟩

theorem weight_below (a : ℤ) (n : ℕ) (ha : a < (n : ℤ)) : weight k g a n = ⊥ := by
  apply le_antisymm _ bot_le
  rw [weight_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨u, z, hu, rfl⟩
  rw [Shared.Lie.filtration_negative k g _ (by omega), Submodule.mem_bot] at hu
  simp [hu]

theorem weight_exhaustive (n : ℕ) (z : V k g n) : ∃ a, z ∈ weight k g a n := by
  induction z using TensorProduct.inductionOn with
  | tmul u z =>
    obtain ⟨m, hm⟩ := Shared.Lie.filtration_exhaustive k g u
    exact ⟨m+n, tmul_mem_weight k g (m+n) n u z (by simpa using hm)⟩
  | add z w hz hw =>
    obtain ⟨a, ha⟩ := hz
    obtain ⟨b, hb⟩ := hw
    exact ⟨max a b, (weight k g (max a b) n).add_mem
      (weight_mono k g n (le_max_left a b) ha)
      (weight_mono k g n (le_max_right a b) hb)⟩

/-- Exterior generators suffice for membership under an arbitrary linear map. -/
theorem map_tmul_mem_of_wedge {n : ℕ} {P : Type*} [AddCommGroup P] [Module k P]
    (f : V k g n →ₗ[k] P) (S : Submodule k P) (u : U k g)
    (h : ∀ x, f (u ⊗ₜ[k] wedge k g n x) ∈ S) (z : W k g n) :
    f (u ⊗ₜ[k] z) ∈ S := by
  have hz : z ∈ Submodule.span k (Set.range (wedge k g n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨x, rfl⟩ := hz; exact h x
  | zero => simp
  | add z w hz hw ihz ihw => simpa only [TensorProduct.tmul_add, map_add] using S.add_mem ihz ihw
  | smul r z hz ih => simpa only [TensorProduct.tmul_smul, map_smul] using S.smul_mem r ih

/-- The multiplication term keeps total weight. -/
theorem actionSum_mem (a : ℤ) (n : ℕ) (u : U k g) (x : Fin (n+1) → g)
    (hu : u ∈ Shared.Lie.filtration k g (a-(n+1 : ℕ))) :
    actionSum k g n u x ∈ weight k g a n := by
  unfold actionSum
  apply Submodule.sum_mem
  intro i hi
  apply (weight k g a n).toAddSubgroup.zsmul_mem
  apply tmul_mem_weight
  have h := Shared.Lie.mul_mem_filtration k g (a-(n+1 : ℕ)) 1 u
    (Shared.Lie.inclusion k g (x i)) hu (Shared.Lie.inclusion_mem_filtration k g (x i))
  convert h using 1 <;> push_cast
  congr 1 <;> omega

/-- The bracket term has weight one less, including the zero degree-one case. -/
theorem bracketSum_mem (a : ℤ) (n : ℕ) (u : U k g) (x : Fin (n+1) → g)
    (hu : u ∈ Shared.Lie.filtration k g (a-(n+1 : ℕ))) :
    bracketSum k g n u x ∈ weight k g (a-1) n := by
  cases n with
  | zero => exact (weight k g (a-1) 0).zero_mem
  | succ n =>
    unfold bracketSum
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.sum_mem
    intro j hj
    apply (weight k g (a-1) (n+1)).toAddSubgroup.zsmul_mem
    apply tmul_mem_weight
    convert hu using 1 <;> push_cast
    congr 1 <;> omega

/-- Extension from exterior pure tensors to every element in a weight step. -/
theorem map_weight_mem {n : ℕ} {P : Type*} [AddCommGroup P] [Module k P]
    (f : V k g n →ₗ[k] P) (S : Submodule k P) (a : ℤ)
    (h : ∀ u, u ∈ Shared.Lie.filtration k g (a-n) →
      ∀ x, f (u ⊗ₜ[k] wedge k g n x) ∈ S)
    (z : V k g n) (hz : z ∈ weight k g a n) : f z ∈ S := by
  rw [weight_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, w, hu, rfl⟩ := hz
    exact map_tmul_mem_of_wedge k g f S u (h u hu) w
  | zero => simpa using S.zero_mem
  | add z w hz hw ihz ihw => simpa using S.add_mem ihz ihw
  | smul r z hz ih => simpa using S.smul_mem r ih

theorem action_preserves (A : BoundaryFamily k g)
    (hA : ∀ n a x, A n (a ⊗ₜ[k] wedge k g (n+1) x) = actionSum k g n a x)
    (a : ℤ) (n : ℕ) (z : V k g (n+1)) (hz : z ∈ weight k g a (n+1)) :
    A n z ∈ weight k g a n := by
  apply map_weight_mem k g ((A n).restrictScalars k) (weight k g a n) a _ z hz
  intro u hu x
  change A n _ ∈ _
  rw [hA]
  exact actionSum_mem k g a n u x hu

theorem bracket_lowers (B : BoundaryFamily k g)
    (hB : ∀ n a x, B n (a ⊗ₜ[k] wedge k g (n+1) x) = bracketSum k g n a x)
    (a : ℤ) (n : ℕ) (z : V k g (n+1)) (hz : z ∈ weight k g a (n+1)) :
    B n z ∈ weight k g (a-1) n := by
  apply map_weight_mem k g ((B n).restrictScalars k) (weight k g (a-1) n) a _ z hz
  intro u hu x
  change B n _ ∈ _
  rw [hB]
  exact bracketSum_mem k g a n u x hu

theorem filtration_spec : Specs.AdvancedHomologicalAlgebra.CE.Graded.filtrationExpected.{u,v} := by
  intro k g _ _ _
  refine ⟨weight_mono k g, weight_below k g, weight_exhaustive k g, ?_⟩
  intro A B hA hB
  refine ⟨action_preserves k g A hA, bracket_lowers k g B hB, ?_⟩
  intro a n z hz
  exact (weight k g a n).add_mem (action_preserves k g A hA a n z hz)
    (weight_mono k g n (by omega) (bracket_lowers k g B hB a n z hz))

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded.TensorFiltration
open scoped TensorProduct
universe u v w t
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {M' : Type t} [AddCommGroup M'] [Module R M']

/-- Coordinatewise proof that tensoring with a free module preserves injections.
No flatness certificate is assumed, and the basis may have arbitrary rank. -/
theorem map_id_injective [Module.Free R N] (f : M →ₗ[R] M') (hf : Function.Injective f) :
    Function.Injective (TensorProduct.map f (LinearMap.id : N →ₗ[R] N)) := by
  classical
  let b := Module.Free.chooseBasis R N
  have hnat : ∀ (z : M ⊗[R] N) i,
      TensorProduct.equivFinsuppOfBasisRight (M := M') b
        (TensorProduct.map f LinearMap.id z) i =
      f (TensorProduct.equivFinsuppOfBasisRight (M := M) b z i) := by
    intro z i
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp
    | add z s hz hs => simp [hz, hs]
  intro z s h
  apply (TensorProduct.equivFinsuppOfBasisRight (M := M) b).injective
  ext i
  apply hf
  rw [← hnat, ← hnat, h]

/-- The actual image of a submodule tensored into an ambient tensor product. -/
def tensorImage (P : Submodule R M) : Submodule R (M ⊗[R] N) :=
  LinearMap.range (TensorProduct.map P.subtype (LinearMap.id : N →ₗ[R] N))

noncomputable def imageEquiv [Module.Free R N] (P : Submodule R M) :
    (P ⊗[R] N) ≃ₗ[R] tensorImage (N := N) P :=
  LinearEquiv.ofInjective (TensorProduct.map P.subtype LinearMap.id)
    (map_id_injective P.subtype P.injective_subtype)

@[simp] theorem imageEquiv_val [Module.Free R N] (P : Submodule R M) (z : P ⊗[R] N) :
    (imageEquiv (N := N) P z).val = TensorProduct.map P.subtype LinearMap.id z := rfl

/-- Inclusion of the lower step, viewed as a submodule of the upper step. -/
def lowerInclusion (P Q : Submodule R M) (hQP : Q ≤ P) :
    Q →ₗ[R] Q.comap P.subtype where
  toFun q := ⟨⟨q.val, hQP q.property⟩, q.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lower_image [Module.Free R N] (P Q : Submodule R M) (hQP : Q ≤ P) :
    (LinearMap.range (TensorProduct.map (Q.comap P.subtype).subtype
      (LinearMap.id : N →ₗ[R] N))).map (imageEquiv (N := N) P).toLinearMap =
      (tensorImage (N := N) Q).comap (tensorImage (N := N) P).subtype := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    change TensorProduct.map P.subtype LinearMap.id
      (TensorProduct.map (Q.comap P.subtype).subtype LinearMap.id t) ∈ tensorImage (N := N) Q
    let f : Q.comap P.subtype →ₗ[R] Q :=
      { toFun := fun q => ⟨q.val.val, q.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨TensorProduct.map f LinearMap.id t, ?_⟩
    have he : (TensorProduct.map Q.subtype (LinearMap.id : N →ₗ[R] N)).comp
        (TensorProduct.map f LinearMap.id) =
        (TensorProduct.map P.subtype LinearMap.id).comp
          (TensorProduct.map (Q.comap P.subtype).subtype LinearMap.id) := by
      ext q z
      rfl
    exact DFunLike.congr_fun he t
  · intro z hz
    obtain ⟨t, ht⟩ := hz
    let s := TensorProduct.map (lowerInclusion P Q hQP) (LinearMap.id : N →ₗ[R] N) t
    refine ⟨TensorProduct.map (Q.comap P.subtype).subtype LinearMap.id s, ⟨s, rfl⟩, ?_⟩
    apply Subtype.ext
    change TensorProduct.map P.subtype LinearMap.id
      (TensorProduct.map (Q.comap P.subtype).subtype LinearMap.id
        (TensorProduct.map (lowerInclusion P Q hQP) LinearMap.id t)) = z.val
    change TensorProduct.map Q.subtype LinearMap.id t = z.val at ht
    rw [← ht]
    have he : (TensorProduct.map P.subtype (LinearMap.id : N →ₗ[R] N)).comp
        ((TensorProduct.map (Q.comap P.subtype).subtype LinearMap.id).comp
          (TensorProduct.map (lowerInclusion P Q hQP) LinearMap.id)) =
        TensorProduct.map Q.subtype LinearMap.id := by
      ext q z
      rfl
    exact DFunLike.congr_fun he t

/-- The successive quotient/tensor comparison, proved using the free basis.
The quotient-tensor equivalence itself is right-exact for all modules; freeness
is used precisely to identify a tensored step with its actual ambient image. -/
noncomputable def subquotientEquiv [Module.Free R N] (P Q : Submodule R M) (hQP : Q ≤ P) :
    (P ⧸ Q.comap P.subtype) ⊗[R] N ≃ₗ[R]
      tensorImage (N := N) P ⧸
        (tensorImage (N := N) Q).comap (tensorImage (N := N) P).subtype :=
  TensorProduct.quotientTensorEquiv N (Q.comap P.subtype) ≪≫ₗ
    Submodule.Quotient.equiv _ _ (imageEquiv (N := N) P) (lower_image P Q hQP)

@[simp] theorem subquotientEquiv_tmul [Module.Free R N]
    (P Q : Submodule R M) (hQP : Q ≤ P) (p : P) (z : N) :
    subquotientEquiv (N := N) P Q hQP (Submodule.Quotient.mk p ⊗ₜ[R] z) =
      Submodule.Quotient.mk (imageEquiv (N := N) P (p ⊗ₜ[R] z)) := rfl

end AdvancedHomologicalAlgebra.CE.Graded.TensorFiltration


namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g]

/-- PBW coefficient grade m becomes CE weight m+n in chain degree n. -/
noncomputable def tensorComparison (m n : ℕ) :
    (Shared.Lie.PBW.Graded.Piece k g m ⊗[k] W k g n) ≃ₗ[k]
      Piece k g ((m : ℤ)+n) n := by
  let P := Shared.Lie.filtration k g (m : ℤ)
  let Q := Shared.Lie.filtration k g ((m : ℤ)-1)
  have hQP : Q ≤ P := Shared.Lie.filtration_mono k g (by omega)
  have hp : TensorFiltration.tensorImage (N := W k g n) P =
      weight k g ((m : ℤ)+n) n := by
    unfold TensorFiltration.tensorImage weight P
    rw [add_sub_cancel_right]
  have hq : TensorFiltration.tensorImage (N := W k g n) Q =
      weight k g ((m : ℤ)+n-1) n := by
    unfold TensorFiltration.tensorImage weight Q
    rw [show (m : ℤ) + n - 1 - n = (m : ℤ)-1 from by omega]
  let e := LinearEquiv.ofEq _ _ hp
  have hlower : ((TensorFiltration.tensorImage (N := W k g n) Q).comap
      (TensorFiltration.tensorImage (N := W k g n) P).subtype).map e.toLinearMap =
      lower k g ((m : ℤ)+n) n := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext z
    change (e.symm z).val ∈ TensorFiltration.tensorImage (N := W k g n) Q ↔
      z.val ∈ weight k g ((m : ℤ)+n-1) n
    simp only [e, LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply, hq]
  exact (TensorFiltration.subquotientEquiv (N := W k g n) P Q hQP).trans
    (Submodule.Quotient.equiv _ _ e hlower)

@[simp] theorem tensorComparison_tmul (m n : ℕ)
    (a : Shared.Lie.PBW.Graded.Step k g m) (z : W k g n)
    (h : a.val ⊗ₜ[k] z ∈ weight k g ((m : ℤ)+n) n) :
    tensorComparison k g m n (Shared.Lie.PBW.Graded.principal k g m a ⊗ₜ[k] z) =
      principal k g ((m : ℤ)+n) n ⟨a.val ⊗ₜ[k] z, h⟩ := by
  rfl

theorem tensorComparison_spec :
    Specs.AdvancedHomologicalAlgebra.CE.Graded.tensorComparisonExpected.{u,v} := by
  intro k g _ _ _ _ m n
  exact ⟨tensorComparison k g m n, tensorComparison_tmul k g m n⟩

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct DirectSum
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]

/-- Homogeneous PBW lands entirely in its prescribed graded summand. -/
theorem homogeneousPBW_lof (m : ℕ)
    (p : Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m) :
    DirectSum.lof k ℕ (Shared.Lie.PBW.Graded.Piece k g) m (homogeneousPBW k g m p) =
      Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g) p.val := by
  classical
  letI : LinearOrder (Module.Free.ChooseBasisIndex k g) :=
    IsWellOrder.linearOrder WellOrderingRel
  have hp : Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g) p.val ∈
      LinearMap.range (DirectSum.lof k ℕ (Shared.Lie.PBW.Graded.Piece k g) m) := by
    rw [← Shared.Lie.PBW.Graded.canonicalMap_degree (Module.Free.chooseBasis k g)]
    exact ⟨p.val, p.property, rfl⟩
  obtain ⟨q, hq⟩ := hp
  change DirectSum.lof k ℕ (Shared.Lie.PBW.Graded.Piece k g) m
    (DirectSum.component k ℕ (Shared.Lie.PBW.Graded.Piece k g) m
      (Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g) p.val)) = _
  rw [← hq]
  simp

/-- Restricting the canonical PBW isomorphism gives each homogeneous isomorphism. -/
theorem homogeneousPBW_bijective (m : ℕ) : Function.Bijective (homogeneousPBW k g m) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Shared.Lie.PBW.Graded.canonicalMap_bijective.1
    rw [← homogeneousPBW_lof k g m p, ← homogeneousPBW_lof k g m q, hpq]
  · classical
    intro q
    letI : LinearOrder (Module.Free.ChooseBasisIndex k g) :=
      IsWellOrder.linearOrder WellOrderingRel
    have hq : DirectSum.lof k ℕ (Shared.Lie.PBW.Graded.Piece k g) m q ∈
        Submodule.map (Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g)).toLinearMap
          (Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m) := by
      rw [Shared.Lie.PBW.Graded.canonicalMap_degree (Module.Free.chooseBasis k g)]
      exact ⟨q, rfl⟩
    obtain ⟨p, hp, hpeq⟩ := hq
    refine ⟨⟨p, hp⟩, ?_⟩
    change DirectSum.component k ℕ (Shared.Lie.PBW.Graded.Piece k g) m
      (Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g) p) = q
    rw [show Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g) p =
      DirectSum.lof k ℕ (Shared.Lie.PBW.Graded.Piece k g) m q from hpeq]
    simp

noncomputable def homogeneousEquiv (m : ℕ) :
    Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m ≃ₗ[k]
      Shared.Lie.PBW.Graded.Piece k g m :=
  LinearEquiv.ofBijective (homogeneousPBW k g m) (homogeneousPBW_bijective k g m)

@[simp] theorem homogeneousEquiv_apply (m : ℕ)
    (p : Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m) :
    homogeneousEquiv k g m p = homogeneousPBW k g m p := rfl

/-- Canonical identification of a weightwise CE term with a symmetric Koszul term. -/
noncomputable def koszulComparison (m n : ℕ) :
    KoszulPiece k g m n ≃ₗ[k] Piece k g ((m : ℤ)+n) n :=
  ((homogeneousEquiv k g m).rTensor (W k g n)).trans (tensorComparison k g m n)

theorem homogeneousComparison_spec :
    Specs.AdvancedHomologicalAlgebra.CE.Graded.homogeneousComparisonExpected.{u,v} := by
  intro k g _ _ _ _
  refine ⟨Shared.Lie.filtration_properties k g, ?_⟩
  exact ⟨homogeneousEquiv k g, fun _ _ => rfl⟩

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g]

/-- The accepted CE boundary preserves the total-weight filtration. -/
theorem boundary_preserves (a : ℤ) (n : ℕ) (z : V k g (n+1))
    (hz : z ∈ weight k g a (n+1)) : boundary k g n z ∈ weight k g a n := by
  exact (filtration_spec k g).2.2.2 (actionBoundary k g) (bracketBoundary k g)
    (actionBoundary_tmul k g) (bracketBoundary_tmul k g) |>.2.2 a n z hz

/-- Restriction of the CE differential to a weight step. -/
noncomputable def boundaryOnStep (a : ℤ) (n : ℕ) :
    Step k g a (n+1) →ₗ[k] Step k g a n :=
  (((boundary k g n).restrictScalars k).comp (weight k g a (n+1)).subtype).codRestrict _
    (fun z => boundary_preserves k g a n z.val z.property)

/-- The CE boundary on the actual successive quotients. -/
noncomputable def gradedBoundary (a : ℤ) (n : ℕ) :
    Piece k g a (n+1) →ₗ[k] Piece k g a n :=
  (lower k g a (n+1)).liftQ ((principal k g a n).comp (boundaryOnStep k g a n)) (by
    intro z hz
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact boundary_preserves k g (a-1) n z.val hz)

@[simp] theorem gradedBoundary_principal (a : ℤ) (n : ℕ)
    (z : Step k g a (n+1)) (h : boundary k g n z.val ∈ weight k g a n) :
    gradedBoundary k g a n (principal k g a (n+1) z) =
      principal k g a n ⟨boundary k g n z.val, h⟩ := rfl

/-- Square zero descends to every weight, including negative weights. -/
theorem gradedBoundary_squared (a : ℤ) (n : ℕ) :
    (gradedBoundary k g a n).comp (gradedBoundary k g a (n+1)) = 0 := by
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
    change principal k g a n
      ⟨boundary k g n (boundary k g (n+1) z.val), _⟩ = 0
    have hz : boundary k g n (boundary k g (n+1) z.val) = 0 :=
      DFunLike.congr_fun (boundary_squared k g n) z.val
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change boundary k g n (boundary k g (n+1) z.val) ∈ weight k g (a-1) n
    rw [hz]
    exact (weight k g (a-1) n).zero_mem

/-- The bracket term becomes zero in the same-weight associated graded. -/
theorem bracket_symbol_zero (a : ℤ) (n : ℕ) (z : Step k g a (n+1)) :
    principal k g a n
      ⟨bracketBoundary k g n z.val, weight_mono k g n (by omega)
        (bracket_lowers k g (bracketBoundary k g) (bracketBoundary_tmul k g)
          a n z.val z.property)⟩ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact bracket_lowers k g (bracketBoundary k g) (bracketBoundary_tmul k g)
    a n z.val z.property

/-- Only multiplication survives on the associated graded CE complex. -/
theorem gradedBoundary_eq_action (a : ℤ) (n : ℕ) (z : Step k g a (n+1)) :
    gradedBoundary k g a n (principal k g a (n+1) z) =
      principal k g a n ⟨actionBoundary k g n z.val,
        action_preserves k g (actionBoundary k g) (actionBoundary_tmul k g)
          a n z.val z.property⟩ := by
  rw [gradedBoundary_principal k g a n z (boundary_preserves k g a n z.val z.property)]
  apply (Submodule.Quotient.eq _).mpr
  change boundary k g n z.val - actionBoundary k g n z.val ∈ weight k g (a-1) n
  have he : boundary k g n z.val - actionBoundary k g n z.val =
      bracketBoundary k g n z.val := by simp [boundary]
  rw [he]
  exact bracket_lowers k g (bracketBoundary k g) (bracketBoundary_tmul k g)
    a n z.val z.property

theorem inducedBoundary_spec :
    Specs.AdvancedHomologicalAlgebra.CE.Graded.inducedBoundaryExpected.{u,v} := by
  intro k g _ _ _ _ d hd hc
  have he : d = boundary k g := boundary_unique k g hd (boundary_formula k g)
  subst d
  exact ⟨boundary_preserves k g, gradedBoundary k g,
    gradedBoundary_principal k g, gradedBoundary_squared k g⟩

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Transport of the same quotient along an equality of weight indices. -/
noncomputable def pieceWeightEquiv (a b : ℤ) (n : ℕ) (h : a = b) :
    Piece k g a n ≃ₗ[k] Piece k g b n := by
  subst b
  exact LinearEquiv.refl _ _

@[simp] theorem pieceWeightEquiv_principal (a b : ℤ) (n : ℕ) (h : a = b)
    (z : Step k g a n) (hz : z.val ∈ weight k g b n) :
    pieceWeightEquiv k g a b n h (principal k g a n z) =
      principal k g b n ⟨z.val, hz⟩ := by
  subst b
  rfl

variable [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]

/-- The associated graded CE differential, expressed on the actual symmetric
homogeneous tensor terms through canonical PBW. -/
noncomputable def koszulDifferential (m n : ℕ) :
    KoszulPiece k g m (n+1) →ₗ[k] KoszulPiece k g (m+1) n :=
  (koszulComparison k g (m+1) n).symm.toLinearMap.comp
    ((pieceWeightEquiv k g ((m : ℤ)+(n+1 : ℕ)) ((m+1 : ℕ)+n) n (by push_cast; omega)).toLinearMap.comp
      ((gradedBoundary k g ((m : ℤ)+(n+1 : ℕ)) n).comp
        (koszulComparison k g m (n+1)).toLinearMap))

/-- The transported map is induced by the original CE boundary on every
representative, including representatives with nonhomogeneous U-factor. -/
theorem koszulDifferential_principal (m n : ℕ)
    (z : Step k g ((m : ℤ)+(n+1 : ℕ)) (n+1))
    (h : boundary k g n z.val ∈ weight k g ((m+1 : ℕ)+n) n) :
    koszulComparison k g (m+1) n
      (koszulDifferential k g m n ((koszulComparison k g m (n+1)).symm
        (principal k g ((m : ℤ)+(n+1 : ℕ)) (n+1) z))) =
      principal k g ((m+1 : ℕ)+n) n ⟨boundary k g n z.val, h⟩ := by
  simp only [koszulDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [gradedBoundary_principal k g _ n z
    (boundary_preserves k g _ n z.val z.property)]
  exact pieceWeightEquiv_principal k g _ _ n _ _ h

/-- No additional Koszul square-zero assumption is needed after transport. -/
theorem koszulDifferential_squared (m n : ℕ) :
    (koszulDifferential k g (m+1) n).comp (koszulDifferential k g m (n+1)) = 0 := by
  apply LinearMap.ext
  intro p
  apply (koszulComparison k g (m+1+1) n).injective
  obtain ⟨q, rfl⟩ := (koszulComparison k g m (n+1+1)).symm.surjective p
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
    have h₁ : boundary k g (n+1) z.val ∈ weight k g ((m+1 : ℕ)+(n+1 : ℕ)) (n+1) := by
      apply weight_mono k g (n+1) (show (m : ℤ)+(n+1+1 : ℕ) ≤
        (m+1 : ℕ)+(n+1 : ℕ) by push_cast; omega)
      exact boundary_preserves k g _ (n+1) z.val z.property
    have h₂ : boundary k g n (boundary k g (n+1) z.val) ∈
        weight k g ((m+1+1 : ℕ)+n) n := by
      apply weight_mono k g n (show ((m+1 : ℕ)+(n+1 : ℕ) : ℤ) ≤
        (m+1+1 : ℕ)+n by push_cast; omega)
      exact boundary_preserves k g _ n _ h₁
    have he₁ := koszulDifferential_principal k g m (n+1) z h₁
    have he₂ := koszulDifferential_principal k g (m+1) n
      ⟨boundary k g (n+1) z.val, h₁⟩ h₂
    have he₁' := (koszulComparison k g (m+1) (n+1)).eq_symm_apply.mpr he₁
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero]
    simp only [principal, Submodule.mkQ_apply] at he₁' he₂ ⊢
    rw [he₁', he₂]
    have hz : boundary k g n (boundary k g (n+1) z.val) = 0 :=
      DFunLike.congr_fun (boundary_squared k g n) z.val
    have hezero : (⟨boundary k g n (boundary k g (n+1) z.val), h₂⟩ :
        Step k g ((m+1+1 : ℕ)+n) n) = 0 := Subtype.ext hz
    rw [hezero]
    simp

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- A homogeneous symmetric word, with its degree recorded. -/
def homogeneousWord (m : ℕ) (xs : List g) (h : xs.length = m) :
    Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m :=
  ⟨Shared.Lie.PBW.Graded.symmetricWord xs, Submodule.subset_span ⟨xs, h, rfl⟩⟩

variable [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]

@[simp] theorem homogeneousEquiv_word (m : ℕ) (xs : List g) (h : xs.length = m) :
    homogeneousEquiv k g m (homogeneousWord k g m xs h) =
      Shared.Lie.PBW.Graded.principal k g m
        ⟨Shared.Lie.word k g xs, Shared.Lie.word_mem k g xs (by omega)⟩ := by
  subst m
  change DirectSum.component k ℕ (Shared.Lie.PBW.Graded.Piece k g) xs.length
    (Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g)
      (Shared.Lie.PBW.Graded.symmetricWord xs)) = _
  rw [Shared.Lie.PBW.Graded.canonicalMap_word]
  simp [Shared.Lie.PBW.Graded.symbol]

@[simp] theorem koszulComparison_word (m n : ℕ) (xs : List g) (hm : xs.length = m)
    (z : W k g n) (h : Shared.Lie.word k g xs ⊗ₜ[k] z ∈ weight k g ((m : ℤ)+n) n) :
    koszulComparison k g m n (homogeneousWord k g m xs hm ⊗ₜ[k] z) =
      principal k g ((m : ℤ)+n) n ⟨Shared.Lie.word k g xs ⊗ₜ[k] z, h⟩ := by
  simp only [koszulComparison, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    homogeneousEquiv_word]
  exact tensorComparison_tmul k g m n _ z h

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]

/-- The leading CE boundary on a symmetric word is signed deletion with
multiplication by the deleted variable. No basis order is needed for this step. -/
theorem koszulDifferential_word (m n : ℕ) (xs : List g) (hm : xs.length = m)
    (x : Fin (n+1) → g) :
    koszulInclusion k g (m+1) n
      (koszulDifferential k g m n
        (homogeneousWord k g m xs hm ⊗ₜ[k] wedge k g (n+1) x)) =
      koszulSum k g n (Shared.Lie.PBW.Graded.symmetricWord xs) x := by
  classical
  let u := Shared.Lie.word k g xs
  let a : ℤ := (m+1 : ℕ) + n
  have hu : u ∈ Shared.Lie.filtration k g (m : ℤ) :=
    Shared.Lie.word_mem k g xs (by omega)
  have hu' : u ∈ Shared.Lie.filtration k g (a-(n+1 : ℕ)) := by
    convert hu using 1 <;> dsimp [a] <;> congr 1 <;> push_cast <;> omega
  have hi : ∀ i : Fin (n+1),
      (u * Shared.Lie.inclusion k g (x i)) ⊗ₜ[k] wedge k g n (i.removeNth x) ∈ weight k g a n := by
    intro i
    apply tmul_mem_weight
    have hmul := Shared.Lie.mul_mem_filtration k g (m : ℤ) 1 u
      (Shared.Lie.inclusion k g (x i)) hu (Shared.Lie.inclusion_mem_filtration k g (x i))
    convert hmul using 1 <;> dsimp [a] <;> congr 1 <;> push_cast <;> omega
  let r : Fin (n+1) → Step k g a n := fun i =>
    ⟨(u * Shared.Lie.inclusion k g (x i)) ⊗ₜ[k] wedge k g n (i.removeNth x), hi i⟩
  let t : Fin (n+1) → KoszulPiece k g (m+1) n := fun i =>
    homogeneousWord k g (m+1) (xs ++ [x i]) (by simp [hm]) ⊗ₜ[k]
      wedge k g n (i.removeNth x)
  let S : KoszulPiece k g (m+1) n := ∑ i : Fin (n+1), (-1 : ℤ)^(i : ℕ) • t i
  have ht : ∀ i, koszulComparison k g (m+1) n (t i) = principal k g a n (r i) := by
    intro i
    have hword : Shared.Lie.word k g (xs ++ [x i]) = u * Shared.Lie.inclusion k g (x i) := by
      simp [Shared.Lie.word, u]
    have h := koszulComparison_word k g (m+1) n (xs ++ [x i]) (by simp [hm])
      (wedge k g n (i.removeNth x)) (by rw [hword]; exact hi i)
    simpa only [t, r, hword] using h
  have hA : actionSum k g n u x ∈ weight k g a n := actionSum_mem k g a n u x hu'
  have hS : koszulComparison k g (m+1) n S = principal k g a n ⟨actionSum k g n u x, hA⟩ := by
    have hsum : (⟨actionSum k g n u x, hA⟩ : Step k g a n) =
        ∑ i : Fin (n+1), (-1 : ℤ)^(i : ℕ) • r i := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, r, actionSum]
      apply Finset.sum_congr rfl
      intro i hi
      exact (map_zsmul (weight k g a n).subtype ((-1 : ℤ)^(i : ℕ)) (r i)).symm
    dsimp only [S]
    rw [hsum]
    simp only [map_sum, map_zsmul, ht]
  have hsrc : u ⊗ₜ[k] wedge k g (n+1) x ∈ weight k g ((m : ℤ)+(n+1 : ℕ)) (n+1) := by
    apply tmul_mem_weight
    simpa using hu
  let z : Step k g ((m : ℤ)+(n+1 : ℕ)) (n+1) := ⟨u ⊗ₜ[k] wedge k g (n+1) x, hsrc⟩
  have hb : boundary k g n z.val ∈ weight k g a n := by
    exact weight_mono k g n (by dsimp [a]; push_cast; omega)
      (boundary_preserves k g _ n z.val z.property)
  have heD := koszulDifferential_principal k g m n z hb
  have heSrc := koszulComparison_word k g m (n+1) xs hm
    (wedge k g (n+1) x) hsrc
  change koszulComparison k g m (n+1) _ = principal k g _ _ z at heSrc
  rw [← heSrc, LinearEquiv.symm_apply_apply] at heD
  have heA : principal k g a n ⟨boundary k g n z.val, hb⟩ =
      principal k g a n ⟨actionSum k g n u x, hA⟩ := by
    apply (Submodule.Quotient.eq _).mpr
    change boundary k g n (u ⊗ₜ[k] wedge k g (n+1) x) - actionSum k g n u x ∈
      weight k g (a-1) n
    rw [boundary_formula k g]
    simpa only [add_sub_cancel_left] using bracketSum_mem k g a n u x hu'
  have hDS : koszulDifferential k g m n
      (homogeneousWord k g m xs hm ⊗ₜ[k] wedge k g (n+1) x) = S :=
    (koszulComparison k g (m+1) n).injective (heD.trans (heA.trans hS.symm))
  rw [hDS]
  simp [S, t, koszulInclusion, homogeneousWord, koszulSum,
    Shared.Lie.PBW.Graded.symmetricWord, List.map_append, List.prod_append]

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]

/-- The signed Koszul formula for every homogeneous polynomial coefficient. -/
theorem koszulDifferential_formula (m n : ℕ)
    (p : Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m)
    (x : Fin (n+1) → g) :
    koszulInclusion k g (m+1) n
      (koszulDifferential k g m n (p ⊗ₜ[k] wedge k g (n+1) x)) =
      koszulSum k g n p.val x := by
  suffices ∀ q (hq : q ∈ Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m),
      koszulInclusion k g (m+1) n
        (koszulDifferential k g m n (⟨q, hq⟩ ⊗ₜ[k] wedge k g (n+1) x)) =
          koszulSum k g n q x from this p.val p.property
  intro q hq
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨xs, hm, rfl⟩ := hq
    exact koszulDifferential_word k g m n xs hm x
  | zero =>
    change koszulInclusion k g (m+1) n (koszulDifferential k g m n
      ((0 : Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m) ⊗ₜ[k] wedge k g (n+1) x)) = _
    simp [koszulSum]
  | add q r hq hr ihq ihr =>
    change koszulInclusion k g (m+1) n
      (koszulDifferential k g m n
        ((⟨q, hq⟩ + ⟨r, hr⟩) ⊗ₜ[k] wedge k g (n+1) x)) = _
    rw [TensorProduct.add_tmul, map_add, map_add, ihq, ihr]
    simp [koszulSum, add_mul, TensorProduct.add_tmul, smul_add, Finset.sum_add_distrib]
  | smul r q hq ih =>
    let p' : Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m := ⟨q, hq⟩
    change koszulInclusion k g (m+1) n
      (koszulDifferential k g m n
        ((r • p') ⊗ₜ[k] wedge k g (n+1) x)) = _
    rw [← TensorProduct.smul_tmul', map_smul, map_smul, ih]
    unfold koszulSum
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Algebra.smul_mul_assoc, ← TensorProduct.smul_tmul']
    exact smul_comm r ((-1 : ℤ)^(i : ℕ)) _

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The degree-zero augmentation on the quotient at weight zero. -/
noncomputable def gradedAugmentationZero : Piece k g 0 0 →ₗ[k] k :=
  (lower k g 0 0).liftQ ((augmentation k g).comp (weight k g 0 0).subtype) (by
    intro z hz
    have hz' : z.val = 0 := by
      change z.val ∈ weight k g (0-1) 0 at hz
      rw [weight_below k g _ 0 (by norm_num), Submodule.mem_bot] at hz
      exact hz
    change augmentation k g z.val = 0
    rw [hz', map_zero])

/-- The target k is placed in weight zero. -/
noncomputable def gradedAugmentation (m : ℕ) : Piece k g ((m : ℤ)+0) 0 →ₗ[k] k :=
  if h : m = 0 then (gradedAugmentationZero k g).comp
    (pieceWeightEquiv k g ((m : ℤ)+0) 0 0 (by omega)).toLinearMap else 0

@[simp] theorem gradedAugmentation_principal (m : ℕ) (z : Step k g ((m : ℤ)+0) 0) :
    gradedAugmentation k g m (principal k g ((m : ℤ)+0) 0 z) =
      if m = 0 then augmentation k g z.val else 0 := by
  unfold gradedAugmentation
  split_ifs with h
  · rw [LinearMap.comp_apply, LinearEquiv.coe_coe,
      pieceWeightEquiv_principal k g _ _ _ _ z (by simpa [h] using z.property)]
    rfl
  · rfl

variable [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]

/-- Augmentation compatibility of the canonical term comparison. -/
theorem koszulAugmentation_comparison (m : ℕ) :
    (koszulAugmentation k g).comp (koszulInclusion k g m 0) =
      (gradedAugmentation k g m).comp (koszulComparison k g m 0).toLinearMap := by
  apply TensorProduct.ext'
  intro p z
  suffices ∀ q (hq : q ∈ Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m),
      koszulAugmentation k g (koszulInclusion k g m 0 (⟨q, hq⟩ ⊗ₜ[k] z)) =
        gradedAugmentation k g m (koszulComparison k g m 0 (⟨q, hq⟩ ⊗ₜ[k] z))
    from this p.val p.property
  intro q hq
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨xs, hm, rfl⟩ := hq
    have hz : Shared.Lie.word k g xs ⊗ₜ[k] z ∈ weight k g ((m : ℤ)+0) 0 := by
      apply tmul_mem_weight
      simpa using Shared.Lie.word_mem k g xs (show (xs.length : ℤ) ≤ m by omega)
    change koszulAugmentation k g (koszulInclusion k g m 0
      (homogeneousWord k g m xs hm ⊗ₜ[k] z)) =
        gradedAugmentation k g m (koszulComparison k g m 0 (homogeneousWord k g m xs hm ⊗ₜ[k] z))
    rw [koszulComparison_word k g m 0 xs hm z hz]
    erw [gradedAugmentation_principal]
    cases xs with
    | nil =>
      have hm0 : m = 0 := by simpa using hm.symm
      subst m
      simp [koszulInclusion, homogeneousWord, koszulAugmentation,
        augmentation_tmul, Shared.Lie.word, Shared.Lie.PBW.Graded.symmetricWord]
    | cons y ys =>
      have hm0 : m ≠ 0 := by simp only [List.length_cons] at hm; omega
      simp [hm0, koszulInclusion, homogeneousWord, koszulAugmentation,
        Shared.Lie.PBW.Graded.symmetricWord, SymmetricAlgebra.lift_ι_apply]
  | zero =>
    change koszulAugmentation k g (koszulInclusion k g m 0
      ((0 : Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m) ⊗ₜ[k] z)) =
        gradedAugmentation k g m (koszulComparison k g m 0
          ((0 : Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m) ⊗ₜ[k] z))
    simp only [TensorProduct.zero_tmul, map_zero]
  | add q r hq hr ihq ihr =>
    change koszulAugmentation k g (koszulInclusion k g m 0
      ((⟨q, hq⟩ + ⟨r, hr⟩) ⊗ₜ[k] z)) =
        gradedAugmentation k g m (koszulComparison k g m 0 ((⟨q, hq⟩ + ⟨r, hr⟩) ⊗ₜ[k] z))
    simp only [TensorProduct.add_tmul, map_add, ihq, ihr]
  | smul r q hq ih =>
    change koszulAugmentation k g (koszulInclusion k g m 0 ((r • ⟨q, hq⟩) ⊗ₜ[k] z)) =
      gradedAugmentation k g m (koszulComparison k g m 0 ((r • ⟨q, hq⟩) ⊗ₜ[k] z))
    simp only [← TensorProduct.smul_tmul', map_smul, ih]

theorem koszulAugmentation_principal (m : ℕ) (z : Step k g ((m : ℤ)+0) 0) :
    koszulAugmentation k g (koszulInclusion k g m 0
      ((koszulComparison k g m 0).symm (principal k g ((m : ℤ)+0) 0 z))) =
      if m = 0 then augmentation k g z.val else 0 := by
  have h := DFunLike.congr_fun (koszulAugmentation_comparison k g m)
    ((koszulComparison k g m 0).symm (principal k g ((m : ℤ)+0) 0 z))
  change koszulAugmentation k g (koszulInclusion k g m 0
      ((koszulComparison k g m 0).symm (principal k g ((m : ℤ)+0) 0 z))) =
    gradedAugmentation k g m (koszulComparison k g m 0
      ((koszulComparison k g m 0).symm (principal k g ((m : ℤ)+0) 0 z))) at h
  rw [LinearEquiv.apply_symm_apply, gradedAugmentation_principal] at h
  exact h

/-- The Koszul augmentation kills the boundary because it kills each variable. -/
theorem koszulAugmentation_boundary (m : ℕ) :
    (koszulAugmentation k g).comp
      ((koszulInclusion k g (m+1) 0).comp (koszulDifferential k g m 0)) = 0 := by
  apply TensorProduct.ext'
  intro p z
  have hz : z ∈ Submodule.span k (Set.range (wedge k g 1)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    change koszulAugmentation k g
      (koszulInclusion k g (m+1) 0 (koszulDifferential k g m 0 (p ⊗ₜ[k] wedge k g 1 x))) = 0
    rw [koszulDifferential_formula]
    simp [koszulSum, koszulAugmentation, SymmetricAlgebra.lift_ι_apply]
  | zero => simp
  | add z w hz hw ihz ihw => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) ihz ihw
  | smul r z hz ih => simpa only [TensorProduct.tmul_smul, map_smul, smul_zero] using congrArg (r • ·) ih

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
universe u v

/-- HA-A07 associated graded: canonical PBW identifies every total-weight
quotient and its augmented differential with the symmetric Koszul complex. -/
theorem graded_spec : Specs.AdvancedHomologicalAlgebra.CE.Graded.gradedExpected.{u,v} := by
  intro k g _ _ _ _
  refine ⟨filtration_spec k g, Shared.Lie.filtration_properties k g, ?_⟩
  intro d hd hc
  have he : d = boundary k g := boundary_unique k g hd (boundary_formula k g)
  subst d
  refine ⟨⟨boundary_preserves k g, gradedBoundary k g,
    gradedBoundary_principal k g, gradedBoundary_squared k g⟩, ?_⟩
  refine ⟨tensorComparison k g, homogeneousEquiv k g,
    tensorComparison_tmul k g, fun _ _ => rfl, koszulDifferential k g,
    koszulDifferential_formula k g, koszulDifferential_squared k g,
    koszulDifferential_principal k g, koszulAugmentation_principal k g,
    koszulAugmentation_boundary k g⟩

end AdvancedHomologicalAlgebra.CE.Graded
