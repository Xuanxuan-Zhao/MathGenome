import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Brauer.ScalarInjective
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ScalarObstruction
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.SemilinearDescent
import Batteries.Tactic.OpenPrivate

open scoped TensorProduct MatrixGroups

namespace RM03.Brauer.ScalarInjective

open Matrix Module ProjectiveClassification ScalarObstruction
open LieAlgebrasAndRepresentations.GaloisDescent (SemilinearAction)
open Specs.RM03.Brauer Specs.RM03.Brauer.ScalarObstruction

universe u v w x

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K] {n : ℕ}

open private scalar_commute records_mul relative_defect
  from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ScalarObstruction
open private implements_iff cohomologous_iff_fixed_isomorphic trivial_fixed_equiv
  from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification
open private csa_eq_of_toAlgCat_eq from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.BaseChange

/-- A coboundary defect can be removed without changing the projected lifts. -/
private theorem rescale_lifts (p : Cocycle k K n) (G : Gal(K/k) → GL (Fin n) K)
    (hG : IsLift p G) (c : ScalarCocycle k K) (hc : RecordsDefect G c)
    (hz : cocycleClass k K c = 1) :
    ∃ H : Gal(K/k) → GL (Fin n) K, IsLift p H ∧
      ∀ g h, H g * mapGL g (H h) = H (g * h) := by
  obtain ⟨a, ha⟩ := (cocycleClass_eq_one_iff c).mp hz
  let S := GeneralLinearGroup.scalar (Fin n) (R := K)
  refine ⟨fun g => S (a g)⁻¹ * G g, ?_, ?_⟩
  · intro g
    have hs : ProjGenLinGroup.mk (S (a g)⁻¹) = 1 := by
      rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    rw [map_mul, hs, one_mul, hG g]
  · intro g h
    change (S (a g)⁻¹ * G g) * mapGL g (S (a h)⁻¹ * G h) = S (a (g * h))⁻¹ * G (g * h)
    rw [map_mul, mapGL_scalar, smul_inv', mul_assoc,
      ← mul_assoc (G g), ← (scalar_commute (g • a h)⁻¹ (G g)).eq, mul_assoc,
      ← mul_assoc (S (a g)⁻¹), records_mul hc, ← mul_assoc, ← map_mul, ← map_mul]
    congr 1
    rw [← ha g h]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

private def coefficientVector (g : Gal(K/k)) : (Fin n → K) ≃+ (Fin n → K) :=
  AddEquiv.piCongrRight (fun _ => g.toRingEquiv.toAddEquiv)

/-- The vector action of an honest cocycle of invertible matrices. -/
private def vectorAction (H : Gal(K/k) → GL (Fin n) K)
    (hH : ∀ g h, H g * mapGL g (H h) = H (g * h)) :
    SemilinearAction k K (Fin n → K) where
  act g := (coefficientVector g).trans (GeneralLinearGroup.toLin (H g)).toLinearEquiv.toAddEquiv
  one_act v := by
    have h := hH 1 1
    rw [one_mul] at h
    have hm : mapGL (1 : Gal(K/k)) (H 1) = H 1 := by
      apply GeneralLinearGroup.ext
      intro i j
      rfl
    rw [hm] at h
    have h1 : H 1 = 1 := mul_left_cancel (h.trans (mul_one _).symm)
    change (↑(H 1) : Mat K n) *ᵥ v = v
    rw [h1, GeneralLinearGroup.coe_one, one_mulVec]
  mul_act g h v := by
    change (↑(H (g * h)) : Mat K n) *ᵥ (g ∘ (h ∘ v)) =
      (↑(H g) : Mat K n) *ᵥ (g ∘ ((↑(H h) : Mat K n) *ᵥ (h ∘ v)))
    rw [← hH g h, GeneralLinearGroup.coe_mul, ← mulVec_mulVec]
    congr 1
    funext i
    exact (RingHom.map_mulVec g.toRingHom (H h) (h ∘ v) i).symm
  map_smul g a v := by
    change (↑(H g) : Mat K n) *ᵥ (g ∘ (a • v)) =
      g a • ((↑(H g) : Mat K n) *ᵥ (g ∘ v))
    rw [← mulVec_smul]
    congr 1
    funext i
    exact map_mul g a (v i)

variable [FiniteDimensional k K] [IsGalois k K]

/-- An invariant basis trivializes the honest matrix cocycle. -/
private theorem invariant_basis_matrix (H : Gal(K/k) → GL (Fin n) K)
    (hH : ∀ g h, H g * mapGL g (H h) = H (g * h)) :
    ∃ B : GL (Fin n) K, ∀ g, H g * mapGL g B = B := by
  classical
  let T := vectorAction H hH
  have hs := (SemilinearDescent.fixed_span T).ge
  let b := Basis.ofSpan hs
  let e := b.indexEquiv (Pi.basisFun K (Fin n))
  let c := b.reindex e
  have hfixed (j : Fin n) : c j ∈ T.fixed := by
    change (b.reindex e) j ∈ T.fixed
    rw [Basis.reindex_apply]
    exact Basis.ofSpan_subset hs (Set.mem_range_self (e.symm j))
  let B := GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv c.equivFun.symm)
  have hcol (j : Fin n) : (↑B : Mat K n).col j = c j := by
    have h (v : Fin n → K) : (↑B : Mat K n) *ᵥ v = c.equivFun.symm v := by
      change ((GeneralLinearGroup.toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        (Fin n → K) →ₗ[K] (Fin n → K)) v = _
      simp [B]
    simpa only [mulVec_single_one, Basis.equivFun_symm_single] using h (Pi.single j 1)
  refine ⟨B, fun g => GeneralLinearGroup.ext fun i j => ?_⟩
  have hx : (↑(H g) : Mat K n) *ᵥ (g ∘ c j) = c j := hfixed j g
  rw [← hcol j] at hx
  exact congrFun hx i

/-- A form with trivial scalar obstruction is a matrix algebra in the same
degree as the chosen splitting. -/
private theorem split_of_zero_defect {A : Type x} [Ring A] [Algebra k A]
    (hn : 0 < n) {s : (K ⊗[k] A) ≃ₐ[K] Mat K n} {G : Gal(K/k) → GL (Fin n) K}
    (hG : Presents s G) {c : ScalarCocycle k K} (hc : RecordsDefect G c)
    (hz : cocycleClass k K c = 1) : Nonempty (A ≃ₐ[k] Mat k n) := by
  obtain ⟨ρ, p, hρ, hp, hpG⟩ := hG
  obtain ⟨H, hHp, hH⟩ := rescale_lifts p G hpG c hc hz
  obtain ⟨B, hB⟩ := invariant_basis_matrix H hH
  have ht : Cohomologous k K n p (trivial k K n) := by
    refine ⟨ProjGenLinGroup.mk B, fun g => ?_⟩
    have h := congrArg ProjGenLinGroup.mk (hB g)
    rw [map_mul, hHp g, mk_mapGL] at h
    change 1 = (ProjGenLinGroup.mk B)⁻¹ * p.val g * projectiveAction k K n g
      (ProjGenLinGroup.mk B)
    rw [mul_assoc, h, inv_mul_cancel]
  obtain ⟨f, _⟩ := recover_form s ρ hρ
  obtain ⟨e⟩ := (cohomologous_iff_fixed_isomorphic hn p (trivial k K n)).mp ht
  rw [(implements_iff p ρ).mp hp] at e
  exact ⟨f.trans (e.trans trivial_fixed_equiv.symm)⟩

private theorem injective_of_formula
    [AddCommGroup (BrauerGroup.{u, max u v w} k)] [AddCommGroup (BrauerGroup.{v, max u v w} K)]
    (f : BrauerGroup.{u, max u v w} k →+ BrauerGroup.{v, max u v w} K)
    (hSplit : ∀ A : _root_.CSA.{u, max u v w} k,
      classOf A ∈ relativeSubgroup f ↔ RM03.CSA.Splits k K A)
    (hZero : ∀ A : _root_.CSA.{u, max u v w} k, classOf A = 0 ↔ RM03.CSA.IsSplit k A)
    (φ : relativeSubgroup f →+ Additive (H2 k K)) (hφ : IsObstructionHom.{u,v,w} f φ) :
    Function.Injective φ := by
  apply (AddMonoidHom.ker_eq_bot_iff φ).mp
  rw [AddSubgroup.eq_bot_iff_forall]
  intro q hq
  obtain ⟨c, A, hA, n, hn, s, G, hG, hc⟩ := relative_defect f hSplit q
  have hA' : classOf A ∈ relativeSubgroup f := hA ▸ q.property
  have he : (⟨classOf A, hA'⟩ : relativeSubgroup f) = q := Subtype.ext hA
  have hz : cocycleClass k K c = 1 := by
    have h : φ (⟨classOf A, hA'⟩ : relativeSubgroup f) =
        Additive.ofMul (cocycleClass k K c) := hφ A hA' hn s G hG c hc
    rw [he, show φ q = 0 from hq] at h
    exact (congrArg Additive.toMul h).symm
  apply Subtype.ext
  exact hA.symm.trans ((hZero A).mpr ⟨n, hn, split_of_zero_defect hn hG hc hz⟩)

/-- The map with the prescribed scalar-defect formula is injective. -/
theorem obstruction_injective : Specs.RM03.Brauer.ScalarInjective.ObstructionInjective.{u,v,w} := by
  intro k K _ _ _ _ _ gk gK hk hK
  let _ := gk
  let _ := gK
  intro f hf φ hφ
  refine injective_of_formula f ?_ hk.2.2.2 φ hφ
  intro A
  obtain ⟨B, hB, hF⟩ := hf A
  have he : B = baseChangeCSA k K A := csa_eq_of_toAlgCat_eq hB
  change f (Specs.RM03.Brauer.classOf A) = 0 ↔ _
  rw [hF, he]
  exact hK.2.2.2 (baseChangeCSA k K A)

/-- Injectivity for the canonical relative Brauer group and obstruction. -/
theorem canonical_obstruction_injective :
    Function.Injective (obstruction.{u,v,w} k K) :=
  injective_of_formula (baseChange.{u,v,w} k K)
    (classOf_mem_relativeBrauerGroup_iff k K) classOf_eq_zero_iff_split _
    (obstruction_formula k K)

end RM03.Brauer.ScalarInjective
