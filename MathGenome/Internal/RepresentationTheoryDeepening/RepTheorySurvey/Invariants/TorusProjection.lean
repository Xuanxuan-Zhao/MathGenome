import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.TorusProjection
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.RationalActionComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.TorusWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.ExactInvariants
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory LinearAlgebraicGroups Opposite
open LinearAlgebraicGroups.RationalRepresentations (invariants invariantsMap mem_invariants)
open LinearAlgebraicGroups.WeightDecomposition (weightSpace mem_weightSpace)
open RepTheorySurvey.Invariants.RationalActionComparison (contract contract_tmul)
open RepTheorySurvey.Invariants.Specs.TorusWeights (coordinates)
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace RepTheorySurvey.Invariants.TorusProjection

noncomputable section

open private linearMap_ext_weights from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.TorusWeights
open private contract_natural from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.RationalActionComparison

/-- The coefficient of the trivial character of the coaction. -/
abbrev zeroComponent := @Specs.zeroComponent

section Projection

variable {k M V W : Type u} [Field k] [CommGroup M]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

local notation "B₀" => coordinates k M

private abbrev constantCoefficient : B₀ →ₗ[k] k :=
  (Finsupp.lapply (R := k) (1 : M)).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

open scoped Classical in
private theorem zeroComponent_weight (ρ : RightComodule k B₀ V) (m : M)
    (x : weightSpace ρ m) :
    zeroComponent ρ (x : V) = if m = 1 then (x : V) else 0 := by
  classical
  change contract (constantCoefficient (k := k) (M := M)) (ρ.coaction (x : V)) = _
  rw [mem_weightSpace.mp x.property, contract_tmul]
  change Finsupp.single m (1 : k) (1 : M) • (x : V) = _
  by_cases h : m = 1 <;> simp [h]

theorem projection : Specs.Projection.{u} := by
  classical
  intro k M V _ _ _ _ ρ
  let H := coordinates k M
  let δ := Invariants.Specs.rationalTrivial H (V := invariants H ρ)
  have hmem : ∀ x, zeroComponent ρ x ∈ invariants H ρ := by
    have hd : ρ.coaction.comp (zeroComponent ρ) =
        (RationalRepresentations.trivialLinearMap H).comp (zeroComponent ρ) := by
      apply linearMap_ext_weights ρ
      intro m x
      change ρ.coaction (zeroComponent ρ (x : _)) = zeroComponent ρ (x : _) ⊗ₜ[k] (1 : H)
      rw [zeroComponent_weight]
      by_cases hm : m = 1
      · subst m
        rw [ite_eq_left rfl, mem_weightSpace.mp x.property, map_one]
      · rw [ite_eq_right hm, map_zero, TensorProduct.zero_tmul]
    intro x
    exact mem_invariants.mpr (DFunLike.congr_fun hd x)
  let R : _ →ₗ[k] invariants H ρ := (zeroComponent ρ).codRestrict _ hmem
  refine ⟨R, rfl, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hx : (x : V) ∈ weightSpace ρ 1 := TorusWeights.invariantWeight ρ ▸ x.property
    exact (zeroComponent_weight ρ 1 ⟨x, hx⟩).trans (ite_eq_left rfl)
  · change (R.rTensor H).comp ρ.coaction = δ.coaction.comp R
    apply linearMap_ext_weights ρ
    intro m x
    change (R.rTensor H) (ρ.coaction (x : _)) = R (x : _) ⊗ₜ[k] (1 : H)
    rw [mem_weightSpace.mp x.property, LinearMap.rTensor_tmul]
    by_cases hm : m = 1
    · subst m
      rw [map_one]
    · have hx : R (x : _) = 0 :=
        Subtype.ext ((zeroComponent_weight ρ m x).trans (ite_eq_right hm))
      simp [hx]

theorem naturality : Specs.Naturality.{u} := by
  intro k M V W _ _ _ _ _ _ ρ σ f hf
  apply LinearMap.ext
  intro x
  change f (contract constantCoefficient (ρ.coaction x)) =
    contract constantCoefficient (σ.coaction (f x))
  rw [contract_natural]
  exact congrArg (contract constantCoefficient) (DFunLike.congr_fun hf x)

theorem exactInvariants : Specs.ExactInvariants.{u} := by
  intro k M U V W _ _ _ _ _ _ _ _ ρ σ τ f g hf hg hi he hs
  obtain ⟨R, hR, hRid, _⟩ := projection ρ
  obtain ⟨S, hS, _, _⟩ := projection σ
  obtain ⟨T, hT, hTid, _⟩ := projection τ
  refine ⟨fun _ _ h => Subtype.ext (hi (congrArg Subtype.val h)), ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (he (y : V)).mp (congrArg Subtype.val hy)
      refine ⟨R x, Subtype.ext ?_⟩
      change f ((R x : invariants _ ρ) : U) = (y : V)
      rw [show ((R x : invariants _ ρ) : U) = zeroComponent ρ x from DFunLike.congr_fun hR x]
      rw [show f (zeroComponent ρ x) = zeroComponent σ (f x) from
        DFunLike.congr_fun (naturality ρ σ f hf) x, hx]
      have hyw : (y : V) ∈ weightSpace σ 1 := TorusWeights.invariantWeight σ ▸ y.property
      exact (zeroComponent_weight σ 1 ⟨y, hyw⟩).trans (ite_eq_left rfl)
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (he.apply_apply_eq_zero (x : U))
  · intro z
    obtain ⟨y, hy⟩ := hs (z : W)
    refine ⟨S y, Subtype.ext ?_⟩
    change g ((S y : invariants _ σ) : V) = (z : W)
    rw [show ((S y : invariants _ σ) : V) = zeroComponent σ y from DFunLike.congr_fun hS y]
    rw [show g (zeroComponent σ y) = zeroComponent τ (g y) from
      DFunLike.congr_fun (naturality σ τ g hg) y, hy]
    exact (DFunLike.congr_fun hT (z : W)).symm.trans
      (congrArg Subtype.val (DFunLike.congr_fun hTid z))

theorem reynolds : Specs.Reynolds.{u} := by
  intro k M A _ _ _ _ ρ
  let H := coordinates k M
  let σ := Invariants.Specs.rationalToRightComodule ρ
  obtain ⟨R, hR, hid, he⟩ := projection σ
  refine ⟨R, hR, he, ?_, fun a => DFunLike.congr_fun hid a⟩
  intro a x
  let f := LinearMap.mulLeft k (a : A)
  have ht : f.rTensor H = LinearMap.mulLeft k ((a : A) ⊗ₜ[k] (1 : H)) := by
    apply TensorProduct.ext'
    intro b c
    simp [f, Algebra.TensorProduct.tmul_mul_tmul]
  have hfix : ρ.coaction (a : A) = (a : A) ⊗ₜ[k] (1 : H) :=
    mem_invariants.mp (show (a : A) ∈ invariants H σ from a.property)
  have hf : Invariants.Specs.isComoduleMap σ σ f := by
    apply LinearMap.ext
    intro b
    change (f.rTensor H) (ρ.coaction b) = ρ.coaction ((a : A) * b)
    rw [ht, LinearMap.mulLeft_apply, map_mul, hfix]
  apply Subtype.ext
  change (R (f x) : A) = f (R x : A)
  exact (DFunLike.congr_fun hR (f x)).trans
    ((DFunLike.congr_fun (naturality σ σ f hf) x).symm.trans
      (congrArg f (DFunLike.congr_fun hR x).symm))

theorem stableSubspaces : Specs.StableSubspaces.{u} := by
  intro k M V _ _ _ _ ρ S hS x hx
  let H := coordinates k M
  obtain ⟨t, ht⟩ := hS ⟨x, hx⟩
  change contract constantCoefficient (ρ.coaction x) ∈ S
  change S.subtype.rTensor H t = ρ.coaction x at ht
  rw [← ht, ← contract_natural]
  exact (contract constantCoefficient t).property

end Projection

section Points

open LinearAlgebraicGroups.Specs.StandardGroups (multiplicativePowerGroup)
open RationalActionComparison (pointEvaluation)
open private isIso_unit_of_affine from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.GlobalFunctionsHopf
open private transportCoaction invariants_transportCoaction
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.ExactInvariants

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
  {A B : HopfAlgebraCategory k}

private theorem transportCoaction_inverse (e : A ≅ B) (ρ : RightComodule k A V) :
    transportCoaction e.inv.hom (transportCoaction e.hom.hom ρ) = ρ := by
  have h : (e.inv.hom.toLinearMap.lTensor V).comp (e.hom.hom.toLinearMap.lTensor V) =
      LinearMap.id := by
    apply TensorProduct.ext'
    intro v c
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.id_apply]
    exact congrArg (fun d => v ⊗ₜ[k] d) ((CommHopfAlgCat.ofIso e).symm_apply_apply c)
  have hcoaction :
      (transportCoaction e.inv.hom (transportCoaction e.hom.hom ρ)).coaction = ρ.coaction := by
    change (e.inv.hom.toLinearMap.lTensor V).comp
      ((e.hom.hom.toLinearMap.lTensor V).comp ρ.coaction) = ρ.coaction
    rw [← LinearMap.comp_assoc, h, LinearMap.id_comp]
  generalize transportCoaction e.inv.hom (transportCoaction e.hom.hom ρ) = σ at hcoaction ⊢
  cases ρ
  cases σ
  cases hcoaction
  rfl

private def transportCoactionEquiv (e : A ≅ B) :
    RightComodule k A V ≃ RightComodule k B V where
  toFun := transportCoaction e.hom.hom
  invFun := transportCoaction e.inv.hom
  left_inv := transportCoaction_inverse e
  right_inv := transportCoaction_inverse e.symm

private theorem contract_lTensor (f : A →ₗ[k] B) (p : B →ₗ[k] k) (t : V ⊗[k] A) :
    contract p (f.lTensor V t) = contract (p.comp f) t := by
  induction t <;> simp_all

set_option maxHeartbeats 500000 in
theorem pointInvariants : Specs.PointInvariants.{u} := by
  intro k I _ _ _ T B
  let D := multiplicativePowerGroup k I
  let : IsAffine T.X.left := D.property.1
  let : LocallyOfFiniteType T.X.hom := D.property.2.1
  let : QuasiCompact T.X.hom := D.property.2.2
  have hred : IsReduced T.X.left := by
    change IsReduced (Spec (CommRingCat.of (AddMonoidAlgebra k (I → ℤ))))
    infer_instance
  let : Smooth T.X.hom := smoothOfReducedOverPerfectField k T hred
  let H := GlobalFunctions.globalHopf T
  let a := GlobalFunctions.groupUnit T
  have ha : a.hom.hom = GlobalFunctions.unit T.X := GlobalFunctions.groupUnit_underlying T
  let F := hopfSpec (CommRingCat.of k)
  obtain ⟨_, ⟨splitIso⟩⟩ :=
    TorusWeights.splitTorus k (Multiplicative (I → ℤ)) I (MulEquiv.refl _)
  let s : F.obj (op B) ≅ T := splitIso
  let : IsIso a.hom.hom := by
    rw [ha]
    exact isIso_unit_of_affine T.X
  let aIso : T ≅ H.spectrum :=
    Grp.mkIso (asIso a.hom.hom) (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
  have haIso : aIso.hom = a := (Grp.forget _).map_injective rfl
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let eOp : op H.hopf ≅ op B := ff.preimageIso (aIso.symm ≪≫ s.symm)
  let e : B ≅ H.hopf := eOp.unop
  have he : F.map e.hom.op = aIso.inv ≫ s.inv := ff.map_preimage _
  refine ⟨H, a, s, e, ha, ?_, ?_⟩
  · change a ≫ F.map e.hom.op = s.inv
    rw [he, ← Category.assoc, ← haIso, aIso.hom_inv_id, Category.id_comp]
  · intro V _ _
    obtain ⟨E, hE⟩ := RationalActionComparison.linearComparison (V := V) T H a ha
    refine ⟨(transportCoactionEquiv e).trans E, fun ρ => ⟨?_, ?_⟩⟩
    · intro g v
      have h := hE (transportCoaction e.hom.hom ρ) g v
      change (E (transportCoaction e.hom.hom ρ)).1 g v =
        contract (((pointEvaluation H g).comp e.hom.hom.toAlgHom).toLinearMap) (ρ.coaction v)
      rw [h]
      exact contract_lTensor e.hom.hom.toLinearMap (pointEvaluation H g).toLinearMap (ρ.coaction v)
    · exact (RationalActionComparison.invariantSubspaces T H _ _ (hE _)).trans
        (invariants_transportCoaction e ρ)

end Points

end
end RepTheorySurvey.Invariants.TorusProjection
