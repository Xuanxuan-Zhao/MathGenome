import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LowRankCharacterChecks
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.TypeAHighestWeightModels
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SteinbergTensorMultiplicity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylDimension
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

noncomputable section

open scoped Classical TensorProduct DirectSum

namespace LieAlgebrasAndRepresentations.LowRankCharacterChecks

open Specs.LieAlgebrasAndRepresentations
open Specs.LieAlgebrasAndRepresentations.LowRankCharacterChecks
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA
local notation "matrixCoroot" => Specs.LieAlgebrasAndRepresentations.ClassicalRootsA.coroot
open Specs.LieAlgebrasAndRepresentations.TypeAHighestWeightModels
open ClassicalRootsA (coroot_apply root_apply root_injective killing_coroot cartan_isCartan)
open TypeAHighestWeightModels (positive_roots simple_roots fundamental_weights)
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.SerreRelations
open IntegrableHighestWeightQuotient (IsDominant)
open RootForm (coroot_value)
open _root_.Specs.LieAlgebrasAndRepresentations.KostantMultiplicity (Decomposition partition)
open WeylDenominatorSpecs (cartanRho cartanSign)

open private omega_apply omega_one positive_iff from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.TypeAHighestWeightModels

open FiniteModuleWeights (weightWeylGroup weightReflection corootEvaluation)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient (simpleQuotient_value)

universe u v

section RankOne

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} {φ : Direction H} (A : RankOneData (H := H) (φ := φ))


private def lonePositive : positive H φ :=
  ⟨2 • A.ω, by rw [A.positives]; exact Set.mem_singleton _⟩

private theorem eq_lonePositive (x : positive H φ) : x = lonePositive A :=
  Subtype.ext (Set.mem_singleton_iff.mp (A.positives ▸ x.property))

private theorem rho₁ (hS : (positive H φ).Finite) : cartanRho H φ hS = A.ω := by
  have h : hS.toFinset = {2 • A.ω} := by
    ext x
    simp [A.positives]
  rw [cartanRho, h, Finset.sum_singleton, two_nsmul, ← two_smul ℂ, smul_smul]
  norm_num

private theorem eval_smul_omega (z : ℂ) : (z • A.ω) A.h = z := by simp [A.omegaValue]

private theorem partition₁ (z : ℤ) :
    partition H φ ((z : ℂ) • A.ω) = if 0 ≤ z ∧ z % 2 = 0 then 1 else 0 := by
  let v := lonePositive A
  let : Subsingleton (positive H φ) := ⟨fun x y => (eq_lonePositive A x).trans (eq_lonePositive A y).symm⟩
  let := Fintype.ofFinite (positive H φ)
  have sum_eq (n : positive H φ → ℕ) : (∑ᶠ r, n r • r.val) = (2 * (n v : ℂ)) • A.ω := by
    rw [finsum_eq_sum_of_fintype, Finset.sum_eq_single v]
    · change n v • (2 • A.ω) = _
      rw [two_nsmul, ← two_smul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_comm]
    · intro x _ hx
      exact hx (eq_lonePositive A x) |>.elim
    · simp
  have char (n : positive H φ → ℕ) :
      (∑ᶠ r, n r • r.val) = (z : ℂ) • A.ω ↔ (2 : ℤ) * n v = z := by
    rw [sum_eq]
    constructor
    · intro h
      have e := congrArg (fun x : Module.Dual ℂ H => x A.h) h
      simp only [eval_smul_omega] at e
      exact_mod_cast e
    · intro h
      have e : (2 : ℂ) * n v = z := by exact_mod_cast h
      rw [e]
  let D := Decomposition H φ ((z : ℂ) • A.ω)
  have hs : Subsingleton D := ⟨fun x y => by
    apply Subtype.ext
    funext r
    rw [eq_lonePositive A r]
    have hx := (char x.val).mp x.property
    have hy := (char y.val).mp y.property
    change x.val v = y.val v
    omega⟩
  unfold partition
  split_ifs with hz
  · have he : (2 : ℤ) * (z / 2).toNat = z := by omega
    let d : D := ⟨fun _ => (z / 2).toNat, (char _).mpr he⟩
    let : Unique D := ⟨⟨d⟩, fun _ => Subsingleton.elim _ _⟩
    exact Nat.card_unique
  · let : IsEmpty D := ⟨fun x => hz (by
      have hx := (char x.val).mp x.property
      omega)⟩
    simp

private def negWeight : Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H := LinearEquiv.neg ℂ

private theorem reflection₁ :
    weightReflection H (2 • A.ω) = negWeight (H := H) := by
  have h : (2 • A.ω) (coroot_value H (2 • A.ω)) = 2 := by
    rw [A.positiveCoroot]
    norm_num [two_nsmul, A.omegaValue]
  rw [weightReflection, dite_eq_left h]
  apply LinearEquiv.ext
  intro x
  apply A.separates
  dsimp only
  rw [show (Module.reflection (f := corootEvaluation H _) h) x = _ from Module.reflection_apply _ _]
  change (x - x (coroot_value H (2 • A.ω)) • (2 • A.ω)) A.h = (-x) A.h
  rw [A.positiveCoroot]
  simp [two_nsmul, A.omegaValue]

private theorem reflection_neg₁ :
    weightReflection H (-(2 • A.ω)) = negWeight (H := H) := by
  have h : (-(2 • A.ω)) (coroot_value H (-(2 • A.ω))) = 2 := by
    rw [A.negativeCoroot]
    norm_num [two_nsmul, A.omegaValue]
  rw [weightReflection, dite_eq_left h]
  apply LinearEquiv.ext
  intro x
  apply A.separates
  dsimp only
  rw [show (Module.reflection (f := corootEvaluation H _) h) x = _ from Module.reflection_apply _ _]
  change (x - x (coroot_value H (-(2 • A.ω))) • (-(2 • A.ω))) A.h = (-x) A.h
  rw [A.negativeCoroot]
  simp [two_nsmul, A.omegaValue]

include A in
private theorem negWeight_mem : negWeight (H := H) ∈ weightWeylGroup H := by
  rw [← reflection₁ A]
  apply Subgroup.subset_closure
  exact ⟨_, by rw [A.roots]; exact Set.mem_insert _ _, rfl⟩

include A in
private theorem weyl₁ (w : weightWeylGroup H) :
    w.val = 1 ∨ w.val = negWeight (H := H) := by
  let S : Subgroup (Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H) := {
    carrier := {f | f = 1 ∨ f = negWeight (H := H)}
    one_mem' := Or.inl rfl
    mul_mem' := by
      intro f g hf hg
      rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
      · exact Or.inl (one_mul _)
      · exact Or.inr (one_mul _)
      · exact Or.inr (mul_one _)
      · left
        ext x
        simp [negWeight, LinearEquiv.mul_apply]
    inv_mem' := by
      intro f hf
      rcases hf with rfl | rfl
      · exact Or.inl inv_one
      · right
        ext x
        rfl }
  suffices h : weightWeylGroup H ≤ S from h w.property
  apply (Subgroup.closure_le S).mpr
  rintro _ ⟨x, hx, rfl⟩
  rw [A.roots] at hx
  rcases Set.mem_insert_iff.mp hx with hx | hx
  · exact Or.inr (hx.symm ▸ reflection₁ A)
  · exact Or.inr ((Set.mem_singleton_iff.mp hx).symm ▸ reflection_neg₁ A)

private def weylOrder : Fin 2 ≃ weightWeylGroup H := by
  let s : weightWeylGroup H := ⟨negWeight, negWeight_mem A⟩
  let f : Fin 2 → weightWeylGroup H := ![1, s]
  have hne : (1 : weightWeylGroup H) ≠ s := by
    intro h
    have hx := congrArg (fun g : weightWeylGroup H => g.val A.ω A.h) h
    change A.ω A.h = (-A.ω) A.h at hx
    norm_num [A.omegaValue] at hx
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hne h).elim
    · exact (hne h.symm).elim
    · rfl
  · intro w
    rcases weyl₁ A w with hw | hw
    · exact ⟨0, Subtype.ext hw.symm⟩
    · exact ⟨1, Subtype.ext hw.symm⟩

private theorem sign_negWeight :
    cartanSign H ⟨negWeight, negWeight_mem A⟩ = -1 := by
  let e : Module.Dual ℂ H ≃ₗ[ℂ] ℂ :=
    { toFun := fun x => x A.h
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun z => z • A.ω
      left_inv := fun x => A.separates (eval_smul_omega A (x A.h))
      right_inv := eval_smul_omega A }
  have hd : Module.finrank ℂ (Module.Dual ℂ H) = 1 := e.finrank_eq.trans (Module.finrank_self ℂ)
  unfold cartanSign
  have he : (negWeight (H := H)).toLinearMap =
      (-1 : ℂ) • (LinearMap.id : Module.End ℂ (Module.Dual ℂ H)) := by
    apply LinearMap.ext
    intro x
    simp [negWeight]
  change (if LinearMap.det (negWeight (H := H)).toLinearMap = 1 then (1 : ℤ) else -1) = _
  rw [he]
  norm_num [hd]

private theorem signedCount_arithmetic (a b c : ℕ) :
    let d : ℤ := (a : ℤ) + b - c
    let f (z : ℤ) : ℤ := if 0 ≤ z ∧ z % 2 = 0 then 1 else 0
    f d - f (d - 2 * ((a : ℤ) + 1)) - f (d - 2 * ((b : ℤ) + 1)) +
      f (-((a : ℤ) + b + c + 4)) =
      if ∃ j : Fin (min a b + 1), c = a + b - 2 * j.val then 1 else 0 := by
  dsimp only
  have hiff :
      (∃ j : Fin (min a b + 1), c = a + b - 2 * j.val) ↔
        (0 ≤ (a : ℤ) + b - c ∧ ((a : ℤ) + b - c) % 2 = 0 ∧
          (a : ℤ) + b - c ≤ 2 * (min a b : ℕ)) := by
    constructor
    · rintro ⟨j, rfl⟩
      have hj := j.isLt
      omega
    · intro h
      refine ⟨⟨(((a : ℤ) + b - c) / 2).toNat, by omega⟩, by dsimp; omega⟩
  simp only [hiff]
  split_ifs <;> omega

private theorem signedCount (hS : (positive H φ).Finite) (a b c : ℕ) :
    SteinbergTensorMultiplicity.signedPartitionSum H φ hS
      ((a : ℂ) • A.ω) ((b : ℂ) • A.ω) ((c : ℂ) • A.ω) =
        if ∃ j : Fin (min a b + 1), c = a + b - 2 * j.val then 1 else 0 := by
  let e := weylOrder A
  let := Fintype.ofEquiv _ e
  unfold SteinbergTensorMultiplicity.signedPartitionSum
  simp only [rho₁ A hS, finsum_eq_sum_of_fintype]
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp, Fin.sum_univ_two]
  have s₀ : cartanSign H (e 0) = 1 := by
    unfold cartanSign
    change (if LinearMap.det (LinearMap.id : Module.End ℂ (Module.Dual ℂ H)) = 1
      then (1 : ℤ) else -1) = _
    simp
  have s₁ : cartanSign H (e 1) = -1 := sign_negWeight A
  have app₀ (x : Module.Dual ℂ H) : (e 0).val x = x := rfl
  have app₁ (x : Module.Dual ℂ H) : (e 1).val x = -x := LinearEquiv.neg_apply _
  norm_num only [app₀, app₁, s₀, s₁, one_mul, mul_one, neg_one_mul, Int.reduceMul]
  let d : ℤ := (a : ℤ) + b - c
  let x := (a : ℂ) • A.ω + A.ω
  let y := (b : ℂ) • A.ω + A.ω
  let z := (c : ℂ) • A.ω + 2 • A.ω
  change (partition H φ (x + y - z) : ℤ) + -(partition H φ (x + -y - z) : ℤ) +
    (-(partition H φ (-x + y - z) : ℤ) + (partition H φ (-x + -y - z) : ℤ)) = _
  have h₀₀ : x + y - z = (d : ℂ) • A.ω := by
    apply A.separates
    push_cast
    simp [x, y, z, d, two_nsmul, A.omegaValue]
    ring
  have h₀₁ : x + -y - z = ((d - 2 * ((b : ℤ) + 1) : ℤ) : ℂ) • A.ω := by
    apply A.separates
    push_cast
    simp [x, y, z, d, two_nsmul, A.omegaValue]
    ring
  have h₁₀ : -x + y - z = ((d - 2 * ((a : ℤ) + 1) : ℤ) : ℂ) • A.ω := by
    apply A.separates
    push_cast
    simp [x, y, z, d, two_nsmul, A.omegaValue]
    ring
  have h₁₁ : -x + -y - z = ((-((a : ℤ) + b + c + 4) : ℤ) : ℂ) • A.ω := by
    apply A.separates
    push_cast
    simp [x, y, z, two_nsmul, A.omegaValue]
    ring
  rw [h₀₀, h₀₁, h₁₀, h₁₁]
  simp only [partition₁, apply_ite (Nat.cast : ℕ → ℤ), Nat.cast_one, Nat.cast_zero]
  convert signedCount_arithmetic a b c using 1
  abel

end RankOne

theorem rankOneSignedSum : rankOneSignedSumType.{u} := by
  intro L _ _ _ H φ A hS a b c
  exact signedCount A hS a b c

private def directSumEquiv {L : Type*} [LieRing L] [LieAlgebra ℂ L] {ι κ : Type*}
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, LieRingModule L (V i)] [∀ i, LieModule ℂ L (V i)]
    {W : κ → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, LieRingModule L (W i)] [∀ i, LieModule ℂ L (W i)]
    (r : κ ≃ ι) (f : ∀ j, V (r j) ≃ₗ⁅ℂ,L⁆ W j) :
    (⨁ i, V i) ≃ₗ⁅ℂ,L⁆ (⨁ j, W j) := by
  let e := (DirectSum.lequivCongrLeft ℂ r.symm (M := V)).trans
    (DirectSum.congrLinearEquiv fun j => (f j).toLinearEquiv)
  refine ⟨⟨e.toLinearMap, ?_⟩, e.symm, e.left_inv, e.right_inv⟩
  intro x m
  apply DFinsupp.ext
  intro j
  change e ⁅x, m⁆ j = ⁅x, e m⁆ j
  simp [e, DirectSum.coe_congrLinearEquiv]
  exact (f j).toLieModuleHom.map_lie x (m (r j))

private def tensorEquiv {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    {M N P Q : Type*} [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
    [AddCommGroup N] [Module ℂ N] [LieRingModule L N] [LieModule ℂ L N]
    [AddCommGroup P] [Module ℂ P] [LieRingModule L P] [LieModule ℂ L P]
    [AddCommGroup Q] [Module ℂ Q] [LieRingModule L Q] [LieModule ℂ L Q]
    (f : M ≃ₗ⁅ℂ,L⁆ P) (g : N ≃ₗ⁅ℂ,L⁆ Q) : (M ⊗[ℂ] N) ≃ₗ⁅ℂ,L⁆ (P ⊗[ℂ] Q) := by
  let e := TensorProduct.congr f.toLinearEquiv g.toLinearEquiv
  refine ⟨⟨e.toLinearMap, ?_⟩, e.symm, e.left_inv, e.right_inv⟩
  intro x m
  change e ⁅x, m⁆ = ⁅x, e m⁆
  induction m using TensorProduct.inductionOn with
  | tmul m n =>
    have hf : f ⁅x, m⁆ = ⁅x, f m⁆ := f.toLieModuleHom.map_lie x m
    have hg : g ⁅x, n⁆ = ⁅x, g n⁆ := g.toLieModuleHom.map_lie x n
    simp [e, hf, hg]
  | add m n hm hn => simp only [lie_add, map_add, hm, hn]

open private exists_raisingVectors from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient

section TensorDecomposition

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} {φ : Direction H}

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

private def loneSimple (A : RankOneData (H := H) (φ := φ)) : simple H φ := by
  refine ⟨2 • A.ω, (lonePositive A).property, ?_⟩
  intro b hb c hc he
  rw [A.positives, Set.mem_singleton_iff] at hb hc
  rw [hb, hc] at he
  have he' := congrArg (fun x : Module.Dual ℂ H => x A.h) he
  norm_num [two_nsmul, A.omegaValue] at he'

private theorem dominant₁ (A : RankOneData (H := H) (φ := φ)) (c : ℕ) :
    IsDominant H φ ((c : ℂ) • A.ω) := by
  intro x
  have hx := congrArg Subtype.val (eq_lonePositive A ⟨x.val, x.property.1⟩)
  change x.val = 2 • A.ω at hx
  refine ⟨c, ?_⟩
  change ((c : ℂ) • A.ω) (coroot_value H x.val) = c
  rw [hx, A.positiveCoroot, eval_smul_omega]

private theorem dominant_eq_smul (A : RankOneData (H := H) (φ := φ))
    (a : Module.Dual ℂ H) (ha : IsDominant H φ a) :
    ∃ c : ℕ, a = (c : ℂ) • A.ω := by
  obtain ⟨c, hc⟩ := ha (loneSimple A)
  change a (coroot_value H (2 • A.ω)) = (c : ℂ) at hc
  rw [A.positiveCoroot] at hc
  exact ⟨c, A.separates (hc.trans (eval_smul_omega A _).symm)⟩

private theorem weightNat_inj (A : RankOneData (H := H) (φ := φ)) :
    Function.Injective (fun c : ℕ => (c : ℂ) • A.ω) := by
  intro c d h
  have he := congrArg (fun a : Module.Dual ℂ H => a A.h) h
  simp only [eval_smul_omega] at he
  exact_mod_cast he

private theorem character_eq [H.IsCartanSubalgebra]
    (hss : SolvableRadical.IsSemisimple_value ℂ L) (hφ : Regular H φ)
    {a : Module.Dual ℂ H} {χ ψ : U (borel_value H φ) →ₐ[ℂ] ℂ}
    (hχ : IsWeightCharacter H φ a χ) (hψ : IsWeightCharacter H φ a ψ) : χ = ψ := by
  obtain ⟨η, _, hη⟩ := VermaModules.character_existsUnique hss H φ hφ a
  exact (hη χ hχ).trans (hη ψ hψ).symm

theorem rankOneTensor : rankOneTensorType.{u} := by
  intro L _ _ _ hss H _ φ hφ A a b
  let w (c : ℕ) := (c : ℂ) • A.ω
  have hc (c : ℕ) : ∃ χ, IsWeightCharacter H φ (w c) χ :=
    (VermaModules.character_existsUnique hss H φ hφ _).exists
  choose χ hχ using hc
  refine ⟨χ, hχ, fun ψ ξ hψ hξ => ?_⟩
  obtain ⟨hS, _, ⟨S, label, dec⟩, count⟩ :=
    SteinbergTensorMultiplicity.formula hss H φ hφ (w a) (w b) ψ ξ (dominant₁ A a) (dominant₁ A b) hψ hξ
  have decCopy := dec
  obtain ⟨hfin, ⟨e, _⟩, models⟩ := decCopy
  have hm (i : S) : ∃ c : ℕ, (label i).val = w c :=
    dominant_eq_smul A (label i).val (label i).property
  choose m hm using hm
  choose η hη hi using models
  have hχeq (i : S) : η i = χ (m i) := character_eq hss hφ (hm i ▸ hη i) (hχ (m i))
  have mods (i : S) : Nonempty (↥i.val ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ (χ (m i))) :=
    hχeq i ▸ hi i
  have iff_eq (i : S) (c : ℕ) :
      Nonempty (↥i.val ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ (χ c)) ↔ m i = c := by
    constructor
    · rintro ⟨f⟩
      let g := (mods i).some.symm.trans f
      exact weightNat_inj A ((HighestWeightClassification.simple_quotients_equiv_iff
        hss H φ hφ (w (m i)) (w c) (χ (m i)) (χ c) (hχ (m i)) (hχ c)).mp ⟨g⟩)
    · rintro rfl
      exact mods i
  let score (j : Fin (min a b + 1)) := a + b - 2 * j.val
  have card_eq (c : ℕ) : Nat.card {i : S // m i = c} =
      if ∃ j : Fin (min a b + 1), c = score j then 1 else 0 := by
    have hc := count S label dec ⟨w c, dominant₁ A c⟩ (χ c) (hχ c)
    have he := Nat.card_congr (Equiv.subtypeEquivRight (fun i : S => iff_eq i c))
    rw [he, signedCount A hS a b c] at hc
    by_cases hj : ∃ j : Fin (min a b + 1), c = score j <;>
      simpa [hj, score] using hc
  have uniqueFor (j : Fin (min a b + 1)) :
      ∃ i : {i : S // m i = score j}, ∀ k : {i : S // m i = score j}, k = i := by
    apply Nat.card_eq_one_iff_exists.mp
    rw [card_eq, ite_eq_left ⟨j, rfl⟩]
  choose F hF using uniqueFor
  have score_injective : Function.Injective score := by
    intro i j he
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    dsimp [score] at he
    omega
  let f (j : Fin (min a b + 1)) := (F j).val
  let r : Fin (min a b + 1) ≃ S := Equiv.ofBijective f ⟨by
    intro j k he
    apply score_injective
    exact (F j).property.symm.trans ((congrArg m he).trans (F k).property), by
    intro i
    have nonempty : Nonempty {k : S // m k = m i} := ⟨⟨i, rfl⟩⟩
    let := hfin.fintype
    have hp : 0 < Nat.card {k : S // m k = m i} := Nat.card_pos_iff.mpr ⟨nonempty, inferInstance⟩
    have hs : ∃ j, m i = score j := by
      by_contra hn
      rw [card_eq, ite_eq_right hn] at hp
      exact (lt_irrefl 0) hp
    obtain ⟨j, hj⟩ := hs
    exact ⟨j, congrArg Subtype.val (hF j ⟨i, hj⟩).symm⟩⟩
  have fm (j : Fin (min a b + 1)) : m (r j) = score j := (F j).property
  have fi (j : Fin (min a b + 1)) :
      Nonempty (↥(r j).val ≃ₗ⁅ℂ,L⁆ simpleQuotient_value H φ (χ (score j))) :=
    (iff_eq (r j) (score j)).mpr (fm j)
  exact ⟨e.symm.trans (directSumEquiv r (fun j => (fi j).some))⟩

end TensorDecomposition

private theorem rankOneRoot : root 1 0 1 = 2 • omega 1 1 := by
  apply LinearMap.ext
  intro h
  have ht : (∑ i : Fin 2, h.val.val i i) = 0 := h.val.property
  rw [Fin.sum_univ_two] at ht
  rw [root_apply, two_nsmul, LinearMap.add_apply, omega_one]
  change h.val.val 0 0 - h.val.val 1 1 = h.val.val 0 0 + h.val.val 0 0
  linear_combination -ht

private theorem rankOneRootNeg : root 1 1 0 = -(2 • omega 1 1) := by
  rw [← rankOneRoot]
  ext h
  simp [root_apply, neg_sub]

private theorem rankOneCartanSpan (h : cartan 1) : omega 1 1 h • matrixCoroot 1 0 1 = h := by
  have ht : (∑ i : Fin 2, h.val.val i i) = 0 := h.val.property
  rw [Fin.sum_univ_two] at ht
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  change omega 1 1 h * (matrixCoroot 1 0 1).val.val i j = h.val.val i j
  rw [omega_one]
  change h.val.val 0 0 * _ = _
  fin_cases i <;> fin_cases j <;> norm_num [coroot_apply, Matrix.single_apply]
  all_goals first | exact (h.property (by decide)).symm | linear_combination -ht

/-- The A₁ root and coroot coordinate data for the diagonal Cartan of `sl₂`. -/
def rankOneMatrixData : RankOneData (H := cartan 1) (φ := direction 1) where
  ω := omega 1 1
  h := matrixCoroot 1 0 1
  positives := by
    rw [← rankOneRoot, (positive_roots 1 (by decide)).2]
    ext x
    constructor
    · rintro ⟨i, j, h, hEq⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      exact hEq
    · intro hx
      exact ⟨0, 1, by decide, hx⟩
  roots := by
    rw [← rankOneRootNeg, ← rankOneRoot]
    ext x
    rw [ClassicalRootsA.root_set]
    constructor
    · rintro ⟨i, j, h, hEq⟩
      fin_cases i <;> fin_cases j <;> try contradiction
      · exact Or.inl hEq
      · exact Or.inr hEq
    · intro hx
      rcases hx with hx | hx
      · exact ⟨0, 1, by decide, hx⟩
      · exact ⟨1, 0, by decide, hx⟩
  positiveCoroot := rankOneRoot ▸ killing_coroot 1 0 1 (by decide)
  negativeCoroot := by
    rw [← rankOneRootNeg, killing_coroot 1 1 0 (by decide)]
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    change (matrixCoroot 1 1 0).val.val i j = -(matrixCoroot 1 0 1).val.val i j
    simp only [coroot_apply]
    ring
  omegaValue := fundamental_weights 1 1 (by decide) (by decide) 0
  separates := by
    intro a b hab
    apply LinearMap.ext
    intro h
    rw [← rankOneCartanSpan h, map_smul, map_smul]
    change omega 1 1 h • a (matrixCoroot 1 0 1) = omega 1 1 h • b (matrixCoroot 1 0 1)
    exact congrArg (fun z : ℂ => omega 1 1 h • z) hab

local instance {χ : U (borel_value (cartan 1) (direction 1)) →ₐ[ℂ] ℂ} :
    LieRingModule (sl 1) (induced_value (cartan 1) (direction 1) χ) :=
  inducedLieRingModule (cartan 1) (direction 1) χ

local instance {χ : U (borel_value (cartan 1) (direction 1)) →ₐ[ℂ] ℂ} :
    LieModule ℂ (sl 1) (induced_value (cartan 1) (direction 1) χ) :=
  inducedLieModule (cartan 1) (direction 1) χ

/-- Specialize the quotient decomposition to the symmetric-power matrix models. -/
theorem rankOneMatrixTensor : rankOneMatrixTensorType := by
  intro a b
  let H := cartan 1
  let φ := direction 1
  let := cartan_isCartan 1
  have hss := (ClassicalMatrixCartans.type_a 1).1
  have hreg := (positive_roots 1 (by decide)).1
  obtain ⟨χ, hχ, dec⟩ := rankOneTensor hss H φ hreg rankOneMatrixData a b
  obtain ⟨ψ, hψ, ⟨e⟩⟩ := TypeAHighestWeightModels.symmetric 1 (by decide) a
  obtain ⟨ξ, hξ, ⟨f⟩⟩ := TypeAHighestWeightModels.symmetric 1 (by decide) b
  obtain ⟨g⟩ := dec ψ ξ hψ hξ
  have he (j : Fin (min a b + 1)) :
      Nonempty (simpleQuotient_value H φ (χ (a + b - 2 * j.val)) ≃ₗ⁅ℂ,sl 1⁆
        symmetricPower 1 (a + b - 2 * j.val)) := by
    obtain ⟨η, hη, ⟨F⟩⟩ := TypeAHighestWeightModels.symmetric 1 (by decide) (a + b - 2 * j.val)
    have eq : η = χ (a + b - 2 * j.val) := character_eq hss hreg hη (hχ _)
    subst η
    exact ⟨F.symm⟩
  exact ⟨(tensorEquiv e f).trans (g.trans (directSumEquiv (Equiv.refl _) (fun j => (he j).some)))⟩

private abbrev Pos (n : ℕ) := positive (cartan n) (direction n)
private abbrev d₁ : cartan 2 := matrixCoroot 2 0 1
private abbrev d₂ : cartan 2 := matrixCoroot 2 1 2
private abbrev d₃ : cartan 2 := matrixCoroot 2 0 2

private theorem d₃_eq : d₃ = d₁ + d₂ := by
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  change (matrixCoroot 2 0 2).val.val i j =
    (matrixCoroot 2 0 1).val.val i j + (matrixCoroot 2 1 2).val.val i j
  simp only [coroot_apply]
  ring

private theorem root02 : root 2 0 2 = alpha₁ + alpha₂ := by
  ext h
  simp only [alpha₁, alpha₂, LinearMap.add_apply, root_apply]
  ring

private theorem omegaSum : omega 2 1 + omega 2 2 = alpha₁ + alpha₂ := by
  ext h
  have ht : (∑ i : Fin 3, h.val.val i i) = 0 := h.val.property
  rw [Fin.sum_univ_three] at ht
  rw [← root02]
  simp only [LinearMap.add_apply, omega_one, omega_apply, root_apply]
  change h.val.val 0 0 + (∑ i : Fin 3, if i.val < 2 then h.val.val i i else 0) = _
  norm_num [Fin.sum_univ_three]
  linear_combination ht

private def positiveRoot₂ (i : Fin 3) : Pos 2 := by
  refine ⟨![alpha₁, alpha₂, root 2 0 2] i, ?_⟩
  apply (positive_iff (by decide) _).mpr
  fin_cases i
  · exact ⟨0, 1, by decide, rfl⟩
  · exact ⟨1, 2, by decide, rfl⟩
  · exact ⟨0, 2, by decide, rfl⟩

private def positiveEquiv₂ : Fin 3 ≃ Pos 2 := Equiv.ofBijective positiveRoot₂ (by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> try rfl
    all_goals
      change root 2 _ _ = root 2 _ _ at hv
      have he := root_injective _ _ _ _ (by decide) (by decide) hv
      first | exact False.elim ((by decide : ¬ (_ = _)) he.1)
            | exact False.elim ((by decide : ¬ (_ = _)) he.2)
  · intro x
    obtain ⟨i, j, h, he⟩ := (positive_iff (by decide) x.val).mp x.property
    fin_cases i <;> fin_cases j <;> try contradiction
    · exact ⟨0, Subtype.ext he.symm⟩
    · exact ⟨2, Subtype.ext he.symm⟩
    · exact ⟨1, Subtype.ext he.symm⟩)

private theorem omega₁_d₁ : omega 2 1 d₁ = 1 := fundamental_weights 2 1 (by decide) (by decide) 0
private theorem omega₁_d₂ : omega 2 1 d₂ = 0 := fundamental_weights 2 1 (by decide) (by decide) 1
private theorem omega₂_d₁ : omega 2 2 d₁ = 0 := fundamental_weights 2 2 (by decide) (by decide) 0
private theorem omega₂_d₂ : omega 2 2 d₂ = 1 := fundamental_weights 2 2 (by decide) (by decide) 1

/-- The diagonal Cartan of `sl₃` has the A₂ data used in the dimension evaluation. -/
def rankTwoMatrixData : RankTwoData (H := cartan 2) (φ := direction 2) where
  α₁ := alpha₁
  α₂ := alpha₂
  ω₁ := omega 2 1
  ω₂ := omega 2 2
  positiveOrder := positiveEquiv₂
  firstRoot := rfl
  secondRoot := rfl
  highestRoot := root02
  simpleRoots := by
    rw [simple_roots 2 (by decide)]
    ext x
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · intro hx
      rcases hx with (rfl | hx)
      · exact ⟨0, rfl⟩
      · have h : x = alpha₂ := hx
        exact ⟨1, h⟩
  highestCoroot := by
    rw [← root02]
    unfold alpha₁ alpha₂
    rw [killing_coroot 2 0 2 (by decide), killing_coroot 2 0 1 (by decide),
      killing_coroot 2 1 2 (by decide)]
    exact d₃_eq
  highestWeight := omegaSum.symm
  firstFirst := (congrArg (omega 2 1) (killing_coroot 2 0 1 (by decide))).trans omega₁_d₁
  firstSecond := (congrArg (omega 2 1) (killing_coroot 2 1 2 (by decide))).trans omega₁_d₂
  secondFirst := (congrArg (omega 2 2) (killing_coroot 2 0 1 (by decide))).trans omega₂_d₁
  secondSecond := (congrArg (omega 2 2) (killing_coroot 2 1 2 (by decide))).trans omega₂_d₂

theorem rankTwoDimension : rankTwoDimensionType.{u} := by
  intro L _ _ _ hss H _ φ hφ A a b
  dsimp only
  let lam := (a : ℂ) • A.ω₁ + (b : ℂ) • A.ω₂
  have h₁ : lam (coroot_value H A.α₁) = (a : ℂ) := by
    simp only [lam, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      A.firstFirst, A.secondFirst, mul_one, mul_zero, add_zero]
  have h₂ : lam (coroot_value H A.α₂) = (b : ℂ) := by
    simp only [lam, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      A.firstSecond, A.secondSecond, mul_one, mul_zero, zero_add]
  have hdom : IsDominant H φ lam := by
    rintro ⟨x, hx⟩
    change ∃ (n : ℕ), lam (coroot_value H x) = (n : ℂ)
    rw [A.simpleRoots] at hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact ⟨a, hx.symm ▸ h₁⟩
    · exact ⟨b, (Set.mem_singleton_iff.mp hx).symm ▸ h₂⟩
  refine ⟨(VermaModules.character_existsUnique hss H φ hφ lam).exists, fun χ hχ => ?_⟩
  obtain ⟨fd, hS, _, _, hprod, _⟩ := WeylDimension.formula hss H φ hφ lam χ hdom hχ
  refine ⟨fd, hprod.trans ?_⟩
  let := Fintype.ofEquiv _ A.positiveOrder
  have hρ : cartanRho H φ hS = A.ω₁ + A.ω₂ := by
    rw [cartanRho, Finset.sum_subtype hS.toFinset (fun _ => hS.mem_toFinset) (fun x => x),
      ← A.positiveOrder.sum_comp (fun x : positive H φ => x.val), Fin.sum_univ_three]
    change (1 / 2 : ℂ) • ((A.positiveOrder 0).val + (A.positiveOrder 1).val +
      (A.positiveOrder 2).val) = _
    rw [A.firstRoot, A.secondRoot, A.highestRoot, ← two_smul ℂ, smul_smul, A.highestWeight]
    norm_num
  simp only [hρ]
  rw [Finset.prod_subtype hS.toFinset (fun _ => hS.mem_toFinset),
    ← A.positiveOrder.prod_comp (fun x : positive H φ =>
      (lam + (A.ω₁ + A.ω₂)) (coroot_value H x.val) /
        (A.ω₁ + A.ω₂) (coroot_value H x.val)),
    Fin.prod_univ_three]
  rw [A.firstRoot, A.secondRoot, A.highestRoot, A.highestCoroot]
  simp only [map_add, LinearMap.add_apply, h₁, h₂, A.firstFirst, A.firstSecond,
    A.secondFirst, A.secondSecond, add_zero, zero_add, div_one]
  ring

/-- Specialize the dimension theorem to the concrete matrix realization. -/
theorem rankTwoMatrixDimension : rankTwoMatrixDimensionType := by
  intro a b
  let := cartan_isCartan 2
  exact rankTwoDimension (ClassicalMatrixCartans.type_a 2).1 (cartan 2) (direction 2)
    (positive_roots 2 (by decide)).1 rankTwoMatrixData a b

section RankTwoRoots

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} {φ : Direction H}

private theorem rankTwoPositiveCases (A : RankTwoData (H := H) (φ := φ)) (x : positive H φ) :
    x.val = A.α₁ ∨ x.val = A.α₂ ∨ x.val = A.α₁ + A.α₂ := by
  obtain ⟨i, rfl⟩ := A.positiveOrder.surjective x
  fin_cases i
  · exact Or.inl A.firstRoot
  · exact Or.inr (Or.inl A.secondRoot)
  · exact Or.inr (Or.inr A.highestRoot)

private theorem rootCorootSelf (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) {α : Module.Dual ℂ H}
    (ha : α ∈ rootSet_value H) : α (coroot_value H α) = 2 := by
  rw [killingCoroot_pairing hss H hH]
  exact mul_div_cancel_right₀ _ (rootForm_self_ne_zero hss H hH α ha)

private theorem rankTwoRootEvaluations (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) (A : RankTwoData (H := H) (φ := φ)) :
    A.α₁ (coroot_value H A.α₁) = 2 ∧
    A.α₂ (coroot_value H A.α₁) = -1 ∧
    A.α₁ (coroot_value H A.α₂) = -1 ∧
    A.α₂ (coroot_value H A.α₂) = 2 := by
  have h₁ := rootCorootSelf hss hH (A.firstRoot ▸ (A.positiveOrder 0).property.1)
  have h₂ := rootCorootSelf hss hH (A.secondRoot ▸ (A.positiveOrder 1).property.1)
  have sum₁ := congrArg (fun x : Module.Dual ℂ H => x (coroot_value H A.α₁)) A.highestWeight
  have sum₂ := congrArg (fun x : Module.Dual ℂ H => x (coroot_value H A.α₂)) A.highestWeight
  simp only [LinearMap.add_apply, A.firstFirst, A.secondFirst, h₁, add_zero] at sum₁
  simp only [LinearMap.add_apply, A.firstSecond, A.secondSecond, h₂, zero_add] at sum₂
  exact ⟨h₁, by linear_combination sum₁, by linear_combination sum₂, h₂⟩

private theorem rootCoefficients₂ (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) (A : RankTwoData (H := H) (φ := φ))
    (s t p q r : ℕ) :
    p • A.α₁ + q • A.α₂ + r • (A.α₁ + A.α₂) = s • A.α₁ + t • A.α₂ ↔
    p + r = s ∧ q + r = t := by
  constructor
  · intro h
    obtain ⟨v₁₁, v₂₁, v₁₂, v₂₂⟩ := rankTwoRootEvaluations hss hH A
    have h₁ := congrArg (fun x : Module.Dual ℂ H => x (coroot_value H A.α₁)) h
    have h₂ := congrArg (fun x : Module.Dual ℂ H => x (coroot_value H A.α₂)) h
    simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, v₁₁, v₂₁, v₁₂, v₂₂]
      at h₁ h₂
    have hp : (p : ℂ) + r = s := by linear_combination (2 * h₁ + h₂) / 3
    have hq : (q : ℂ) + r = t := by linear_combination (h₁ + 2 * h₂) / 3
    exact ⟨by exact_mod_cast hp, by exact_mod_cast hq⟩
  · rintro ⟨rfl, rfl⟩
    simp only [add_nsmul, nsmul_add]
    abel

private theorem sum_decomposition₂ (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) (A : RankTwoData (H := H) (φ := φ))
    (f : positive H φ → ℕ) (s t : ℕ) :
    (∑ᶠ x, f x • x.val) = s • A.α₁ + t • A.α₂ ↔
      f (A.positiveOrder 0) + f (A.positiveOrder 2) = s ∧
      f (A.positiveOrder 1) + f (A.positiveOrder 2) = t := by
  let := Fintype.ofEquiv _ A.positiveOrder
  rw [finsum_eq_sum_of_fintype, ← A.positiveOrder.sum_comp (fun x : positive H φ => f x • x.val),
    Fin.sum_univ_three, A.firstRoot, A.secondRoot, A.highestRoot, rootCoefficients₂ hss hH A]

end RankTwoRoots

private def highestRootMultiplicityEquiv (s t : ℕ) :
    {n : Fin 3 → ℕ // n 0 + n 2 = s ∧ n 1 + n 2 = t} ≃ Fin (min s t + 1) where
  toFun n := ⟨n.val 2, by
    obtain ⟨h₁, h₂⟩ := n.property
    omega⟩
  invFun j := ⟨![s - j.val, t - j.val, j.val], by
    have hj := j.isLt
    change s - j.val + j.val = s ∧ t - j.val + j.val = t
    omega⟩
  left_inv n := by
    apply Subtype.ext
    funext i
    obtain ⟨h₁, h₂⟩ := n.property
    fin_cases i
    · change s - n.val 2 = n.val 0
      omega
    · change t - n.val 2 = n.val 1
      omega
    · rfl
  right_inv j := Fin.ext rfl

theorem rankTwoPartitionForPositiveSystem : rankTwoPartitionForPositiveSystemType.{u} := by
  intro L _ _ _ hss H _ φ A s t
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  let coords := Equiv.arrowCongr A.positiveOrder.symm (Equiv.refl ℕ)
  let e : Decomposition H φ (s • A.α₁ + t • A.α₂) ≃
      {n : Fin 3 → ℕ // n 0 + n 2 = s ∧ n 1 + n 2 = t} :=
    coords.subtypeEquiv fun f => sum_decomposition₂ hss hH A f s t
  simpa [partition] using Nat.card_congr (e.trans (highestRootMultiplicityEquiv s t))

theorem rankTwoPartition : rankTwoPartitionType := by
  intro s t
  let := cartan_isCartan 2
  exact rankTwoPartitionForPositiveSystem (ClassicalMatrixCartans.type_a 2).1 (cartan 2)
    (direction 2) rankTwoMatrixData s t

private theorem weightSpace_image {L : Type*} [LieRing L] [LieAlgebra ℂ L]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]
    [AddCommGroup W] [Module ℂ W] [LieRingModule L W] [LieModule ℂ L W]
    (e : V ≃ₗ⁅ℂ,L⁆ W) (H : LieSubalgebra ℂ L) (a : Module.Dual ℂ H) :
    (HighestWeightData.weightSpace_value V H a).map e.toLinearEquiv.toLinearMap =
      HighestWeightData.weightSpace_value W H a := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := (HighestWeight.mem_weightSpace V H a x).mp hx
    apply (HighestWeight.mem_weightSpace W H a (e x)).mpr
    intro h
    change ⁅(h : L), e.toLieModuleHom x⁆ = a h • e.toLieModuleHom x
    rw [← e.toLieModuleHom.map_lie, hx' h, map_smul]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have hy' := (HighestWeight.mem_weightSpace W H a y).mp hy
    apply (HighestWeight.mem_weightSpace V H a (e.symm y)).mpr
    intro h
    change ⁅(h : L), e.symm.toLieModuleHom y⁆ = a h • e.symm.toLieModuleHom y
    rw [← e.symm.toLieModuleHom.map_lie, hy' h, map_smul]

open private rootSet_spans rootSet_separates from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
open private rank_eq_rank_cartan_add_card_roots from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Reconstruction

section Adjoint

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} {φ : Direction H}

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieRingModule L (induced_value H φ χ) := inducedLieRingModule H φ χ

local instance {χ : U (borel_value H φ) →ₐ[ℂ] ℂ} :
    LieModule ℂ L (induced_value H φ χ) := inducedLieModule H φ χ

private theorem rootSet_neg (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) {α : Module.Dual ℂ H}
    (ha : α ∈ rootSet_value H) : -α ∈ rootSet_value H := by
  obtain ⟨_, f, _, hf, _, hf₀, _⟩ := exists_root_triple hss H hH α ha
  refine ⟨neg_ne_zero.mpr ha.1, fun h => hf₀ ?_⟩
  change rootSpace H (-α) = ⊥ at h
  rwa [h, Submodule.mem_bot] at hf

private def negativeToPositive (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) (hφ : Regular H φ)
    (a : rootSet_value H) (ha : ¬ 0 < φ a.val) : positive H φ :=
  ⟨-a.val, rootSet_neg hss hH a.property, by
    rw [map_neg]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt ha) (hφ a.val a.property))⟩

private def rootsEquivPositiveSum (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) (hφ : Regular H φ) :
    rootSet_value H ≃ (positive H φ ⊕ positive H φ) where
  toFun a := if ha : 0 < φ a.val then Sum.inl ⟨a.val, a.property, ha⟩
    else Sum.inr (negativeToPositive hss hH hφ a ha)
  invFun := Sum.elim (fun a => ⟨a.val, a.property.1⟩)
    (fun a => ⟨-a.val, rootSet_neg hss hH a.property.1⟩)
  left_inv a := by
    dsimp only
    split_ifs
    · rfl
    · exact Subtype.ext (neg_neg a.val)
  right_inv := by
    rintro (a | a)
    · exact dite_eq_left a.property.2
    · have ha : ¬ 0 < φ (-a.val) := by
        rw [map_neg]
        exact not_lt_of_ge (neg_nonpos.mpr a.property.2.le)
      dsimp only [Sum.elim_inr]
      rw [dite_eq_right ha]
      exact congrArg Sum.inr (Subtype.ext (neg_neg a.val))

private theorem rankTwoCartanFinrank (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) (hφ : Regular H φ)
    (A : RankTwoData (H := H) (φ := φ)) : Module.finrank ℂ H = 2 := by
  let eval := A.α₁.prod A.α₂
  have hinj : Function.Injective eval := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change (A.α₁ x, A.α₂ x) = (0, 0) at hx
    have hx₁ : A.α₁ x = 0 := congrArg Prod.fst hx
    have hx₂ : A.α₂ x = 0 := congrArg Prod.snd hx
    have hz (a : positive H φ) : a.val x = 0 := by
      rcases rankTwoPositiveCases A a with h | h | h <;> simp [h, hx₁, hx₂]
    apply rootSet_separates (rootSet_spans hss hH) x
    intro a ha
    by_cases hp : 0 < φ a
    · exact hz ⟨a, ha, hp⟩
    · have hn : (-a) x = 0 := hz (negativeToPositive hss hH hφ ⟨a, ha⟩ hp)
      simpa using hn
  have hsurj : Function.Surjective eval := by
    rintro ⟨c, d⟩
    obtain ⟨v₁₁, v₂₁, v₁₂, v₂₂⟩ := rankTwoRootEvaluations hss hH A
    let x := ((2 * c + d) / 3) • coroot_value H A.α₁ +
      ((c + 2 * d) / 3) • coroot_value H A.α₂
    refine ⟨x, Prod.ext ?_ ?_⟩
    · change A.α₁ x = c
      simp only [x, map_add, map_smul, smul_eq_mul, v₁₁, v₁₂]
      ring
    · change A.α₂ x = d
      simp only [x, map_add, map_smul, smul_eq_mul, v₂₁, v₂₂]
      ring
  exact (LinearEquiv.ofBijective eval ⟨hinj, hsurj⟩).finrank_eq.trans
    (by norm_num [Module.finrank_prod])

private theorem rankTwoAlgebraFinrank (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) (hφ : Regular H φ)
    (A : RankTwoData (H := H) (φ := φ)) : Module.finrank ℂ L = 8 := by
  let := Fintype.ofEquiv _ A.positiveOrder
  have hp : Nat.card (positive H φ) = 3 := by
    rw [← Nat.card_congr A.positiveOrder, Nat.card_fin]
  rw [rank_eq_rank_cartan_add_card_roots hss H hH, rankTwoCartanFinrank hss hH hφ A,
    Nat.card_congr (rootsEquivPositiveSum hss hH hφ), Nat.card_sum, hp]

theorem rankTwoAdjointForPositiveSystem : rankTwoAdjointForPositiveSystemType.{u} := by
  intro L _ _ _ hss H _ φ hφ A
  have hd := rankTwoDimension hss H φ hφ A 1 1
  simp only [Nat.cast_one, one_smul, ← A.highestWeight] at hd
  refine ⟨hd.1, fun χ hχ => ?_⟩
  obtain ⟨fd, hprod⟩ := hd.2 χ hχ
  let Q := simpleQuotient_value H φ χ
  let : FiniteDimensional ℂ Q := fd
  have hdimQ : Module.finrank ℂ Q = 8 := by
    have hn : (Module.finrank ℂ Q : ℂ) = (8 : ℂ) := hprod.trans (by norm_num)
    exact_mod_cast hn
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  have hdimL := rankTwoAlgebraFinrank hss hH hφ A
  let θ := A.α₁ + A.α₂
  have hθ : θ ∈ positive H φ := by
    change A.α₁ + A.α₂ ∈ positive H φ
    exact A.highestRoot ▸ (A.positiveOrder 2).property
  have hα₁ : A.α₁ ∈ positive H φ := A.firstRoot ▸ (A.positiveOrder 0).property
  have hα₂ : A.α₂ ∈ positive H φ := A.secondRoot ▸ (A.positiveOrder 1).property
  have hmax (a : positive H φ) : φ a.val ≤ φ θ := by
    have h₁ := hα₁.2
    have h₂ := hα₂.2
    rcases rankTwoPositiveCases A a with h | h | h <;> rw [h] <;>
      simp only [θ, map_add] <;> linarith
  obtain ⟨x, _, hx, _, hx₀, _⟩ := exists_root_triple hss H hH θ hθ.1
  obtain ⟨E, hE⟩ := exists_raisingVectors H φ
  have hraise (i : simple H φ) : ⁅E i, x⁆ = 0 := by
    let b := i.val + θ
    have hlt : φ θ < φ b := by
      have hi := i.property.1.2
      simp only [b, map_add]
      linarith
    have hb : 0 < φ b := lt_trans hθ.2 hlt
    have hn : b ≠ 0 := by
      intro h
      rw [h, map_zero] at hb
      exact (lt_irrefl 0) hb
    have hnr : b ∉ rootSet_value H := fun h => not_le_of_gt hlt (hmax ⟨b, h, hb⟩)
    have hbr := rootSpace_bracket H i.val θ (E i) x (hE i).1 hx
    exact (Submodule.mem_bot ℂ).mp (rootSpace_eq_bot_of_not_mem H b hn hnr ▸ hbr)
  let N := LieSubmodule.lieSpan ℂ L ({x} : Set L)
  let y : N := ⟨x, LieSubmodule.subset_lieSpan (Set.mem_singleton x)⟩
  have hy : SimpleHighestWeightQuotient.IsHighestWeight E θ y := by
    refine ⟨fun hy₀ => hx₀ (congrArg Subtype.val hy₀), ?_, ?_, ?_⟩
    · intro h
      exact Subtype.ext ((mem_rootSpace H θ x).mp hx h)
    · intro i
      exact Subtype.ext (hraise i)
    · let S := LieSubmodule.lieSpan ℂ L ({y} : Set N)
      have hle : N ≤ S.map N.incl := LieSubmodule.lieSpan_le.mpr
        (Set.singleton_subset_iff.mpr (LieSubmodule.mem_map_of_mem
          (N := S) (f := N.incl) (LieSubmodule.subset_lieSpan (Set.mem_singleton y))))
      apply top_unique
      intro z _
      obtain ⟨w, hw, hz⟩ := (LieSubmodule.mem_map _).mp (hle z.property)
      exact (Subtype.ext hz : w = z) ▸ hw
  -- The cyclic adjoint submodule must fill the ambient eight-dimensional module.
  obtain ⟨f, ⟨_, hf⟩, _⟩ :=
    SimpleHighestWeightQuotient.highest_weight_surjects hss H φ hφ θ χ hχ E hE N y hy
  have hNQ : Module.finrank ℂ N = Module.finrank ℂ Q := by
    apply le_antisymm ?_ (LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hf)
    rw [hdimQ, ← hdimL]
    exact Submodule.finrank_le N.toSubmodule
  have hf₁ : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hNQ (f := f.toLinearMap)).mpr hf
  have hi : Function.Surjective N.incl :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hNQ.trans (hdimQ.trans hdimL.symm)) (f := N.incl.toLinearMap)).mp N.injective_incl
  let g := LinearEquiv.ofBijective N.incl.toLinearMap ⟨N.injective_incl, hi⟩
  let F := LinearEquiv.ofBijective f.toLinearMap ⟨hf₁, hf⟩
  let i : N ≃ₗ⁅ℂ,L⁆ L := ⟨N.incl, g.symm, g.left_inv, g.right_inv⟩
  let e : L ≃ₗ⁅ℂ,L⁆ Q := i.symm.trans ⟨f, F.symm, F.left_inv, F.right_inv⟩
  have hm := weightSpace_image e H 0
  change (rootSpace H 0).map e.toLinearEquiv.toLinearMap = _ at hm
  rw [rootSpace_zero hss H hH] at hm
  refine ⟨⟨e, hm⟩, ?_, hdimQ⟩
  let e₀ := e.toLinearEquiv.ofSubmodules _ _ hm
  unfold FormalCharacters.multiplicity
  rw [← e₀.finrank_eq]
  exact_mod_cast rankTwoCartanFinrank hss hH hφ A

end Adjoint

theorem rankTwoAdjoint : rankTwoAdjointType := by
  let := cartan_isCartan 2
  have h := rankTwoAdjointForPositiveSystem (ClassicalMatrixCartans.type_a 2).1 (cartan 2)
    (direction 2) (positive_roots 2 (by decide)).1 rankTwoMatrixData
  exact ⟨h.1, fun χ hχ => (h.2 χ hχ).2⟩

section ChosenPositiveSystem

open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open Module (Basis)

open private direction_vector simple_equiv vector_regular reflection_extension from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
  {H : LieSubalgebra ℂ L} {φ : Direction H}

/-- On the chosen Cartan, the simple coroots form a complex basis and every
root belongs to any set containing the simple roots and closed under their
reflections. -/
private theorem simpleCorootBasisAndOrbit [H.IsCartanSubalgebra]
    (hss : SolvableRadical.IsSemisimple_value ℂ L) (hφ : Regular H φ)
    {ι : Type v} (b : ι ≃ simple H φ) :
    (∃ c : Basis ι ℂ H, ∀ i, c i = coroot_value H (b i).val) ∧
    (∀ S : Set (Module.Dual ℂ H), (∀ i, (b i).val ∈ S) →
      (∀ i, ∀ x ∈ S, RootStrings.rootReflection H (b i).val x ∈ S) →
      rootSet_value H ⊆ S) := by
  obtain ⟨d, hd⟩ := HighestWeight.cartan_lattice_comparison.{u, v} hss H
  let _ := d.normedAddCommGroup
  let _ := d.innerProductSpace
  let _ : Fact (Realization H) := ⟨d⟩
  obtain ⟨v, hv⟩ := direction_vector d φ
  obtain ⟨s, hs⟩ := simple_equiv d φ hv
  have hreg := vector_regular d φ hv hφ
  obtain ⟨_, c, _, _, hc, _⟩ := hd v hreg (b.trans s)
  refine ⟨⟨c, fun i => ?_⟩, ?_⟩
  · simpa only [Equiv.trans_apply, hs] using (hc i).2.2.1
  · intro S hsimple hreflect x hx
    have hx' : rootRestriction H x ∈ realRoots H := ⟨x, hx, rfl⟩
    rw [simpleRoots_orbit (realRoots H) d.root_system v hreg] at hx'
    obtain ⟨w, a, ha, hwa⟩ := hx'
    obtain ⟨l, hl⟩ := exists_weylWord d.root_system hreg w
    have hj (i : simpleRoots (realRoots H) v) :
        d.j i.val = (b ((b.trans s).symm i)).val := by
      let j := (b.trans s).symm i
      have he : s (b j) = i := (b.trans s).apply_symm_apply i
      simpa only [he] using hs (b j)
    have hw (k : List (simpleRoots (realRoots H) v)) :
        d.j (weylWordProduct k a) ∈ S := by
      induction k with
      | nil =>
        change d.j a ∈ S
        rw [hj ⟨a, ha⟩]
        exact hsimple _
      | cons i k ih =>
        rw [weylWordProduct_cons, LinearEquiv.mul_apply, reflection_extension d i.property, hj i]
        exact hreflect _ _ ih
    simpa only [hl, hwa, d.extension_root x hx] using hw l

private theorem coroot_neg (a : Module.Dual ℂ H) :
    coroot_value H (-a) = -coroot_value H a := by
  change (2 / rootForm H (-a) (-a)) • rootDualMap H (-a) =
    -((2 / rootForm H a a) • rootDualMap H a)
  simp only [map_neg, LinearMap.neg_apply, neg_neg, smul_neg]

omit [FiniteDimensional ℂ L] in
private theorem neg_not_positive {a : Module.Dual ℂ H} (ha : a ∈ positive H φ) :
    -a ∉ positive H φ := by
  intro hn
  exact (not_lt_of_ge (neg_nonpos.mpr ha.2.le)) (map_neg φ a ▸ hn.2)

theorem rankOneDataForPositiveSystem : rankOneDataForPositiveSystemType.{u} := by
  intro L _ _ _ hss H _ φ hφ b
  obtain ⟨⟨c, hc⟩, horbit⟩ := simpleCorootBasisAndOrbit hss hφ b
  let a := (b 0).val
  let h := coroot_value H a
  have hpos : a ∈ positive H φ := (b 0).property.1
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  have hself : a h = 2 := rootCorootSelf hss hH hpos.1
  have hsep : Function.Injective (fun x : Module.Dual ℂ H => x h) := by
    intro x y hxy
    apply c.ext
    intro i
    fin_cases i
    rw [hc]
    exact hxy
  have hreflect (x : Module.Dual ℂ H) : RootStrings.rootReflection H a x = -x := by
    apply hsep
    change (x - x h • a) h = (-x) h
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hself, LinearMap.neg_apply]
    ring
  have hneg : -a ∈ rootSet_value H := by
    rw [← hreflect a]
    exact RootStrings.reflection_mem_rootSet hss H hH a a hpos.1 hpos.1
  have hroots : rootSet_value H = {a, -a} := by
    apply Set.Subset.antisymm
    · apply horbit
      · intro i
        fin_cases i
        exact Set.mem_insert _ _
      · intro i x hx
        fin_cases i
        change RootStrings.rootReflection H a x ∈ ({a, -a} : Set _)
        rw [hreflect]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl <;> simp
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hpos.1
      · exact hneg
  have hpositives : positive H φ = {a} := by
    ext x
    constructor
    · intro hx
      have hx' := hx.1
      rw [hroots] at hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx'
      rcases hx' with rfl | rfl
      · exact Set.mem_singleton _
      · exact (neg_not_positive hpos hx).elim
    · rintro rfl
      exact hpos
  let ω : Module.Dual ℂ H := (1 / 2 : ℂ) • a
  have haω : 2 • ω = a := by
    change 2 • ((1 / 2 : ℂ) • a) = a
    rw [two_nsmul, ← add_smul]
    norm_num
  refine ⟨{
    ω := ω
    h := h
    positives := haω ▸ hpositives
    roots := haω ▸ hroots
    positiveCoroot := haω ▸ rfl
    negativeCoroot := haω ▸ coroot_neg a
    omegaValue := ?_
    separates := hsep }, haω⟩
  simp [ω, hself]

/-- The two mixed Cartan entries of type A₂ force the three positive
roots to have the same squared length for the Killing-induced form. -/
private theorem coroot_add_of_mixed_entries
    (hss : SolvableRadical.IsSemisimple_value ℂ L)
    (hH : MaximalTori.IsMaximalToral_value H) {a b : Module.Dual ℂ H}
    (ha : a ∈ rootSet_value H) (hb : b ∈ rootSet_value H)
    (hab : b (coroot_value H a) = -1) (hba : a (coroot_value H b) = -1) :
    coroot_value H (a + b) = coroot_value H a + coroot_value H b := by
  let B := rootForm H
  have hsym : B a b = B b a := LieModule.traceForm_comm ℂ L L (tAlpha H a : L) (tAlpha H b : L)
  have ha₀ : B a a ≠ 0 := rootForm_self_ne_zero hss H hH a ha
  have hb₀ : B b b ≠ 0 := rootForm_self_ne_zero hss H hH b hb
  have hm₁ : 2 * B b a = -B a a := by
    have he : (-1 : ℂ) = 2 * B b a / B a a :=
      hab.symm.trans (killingCoroot_pairing hss H hH a b)
    simpa only [neg_mul, one_mul] using ((eq_div_iff ha₀).mp he).symm
  have hm₂ : 2 * B b a = -B b b := by
    have he : (-1 : ℂ) = 2 * B a b / B b b :=
      hba.symm.trans (killingCoroot_pairing hss H hH b a)
    rw [hsym] at he
    simpa only [neg_mul, one_mul] using ((eq_div_iff hb₀).mp he).symm
  have hlen : B a a = B b b := by linear_combination hm₁ - hm₂
  have hsum : B (a + b) (a + b) = B a a := by
    simp only [map_add, LinearMap.add_apply, hsym]
    linear_combination hm₂
  change (2 / B (a + b) (a + b)) • rootDualMap H (a + b) =
    (2 / B a a) • rootDualMap H a + (2 / B b b) • rootDualMap H b
  rw [hsum, ← hlen, map_add, smul_add]

private theorem weightReflection_eq_rootReflection {a : Module.Dual ℂ H}
    (ha : a (coroot_value H a) = 2) (x : Module.Dual ℂ H) :
    weightReflection H a x = RootStrings.rootReflection H a x := by
  rw [weightReflection, dite_eq_left ha]
  exact Module.reflection_apply (f := corootEvaluation H a) x ha

theorem rankTwoDataForPositiveSystem : rankTwoDataForPositiveSystemType.{u} := by
  intro L _ _ _ hss H _ φ hφ b h₂₁ h₁₂
  obtain ⟨⟨c, hc⟩, horbit⟩ := simpleCorootBasisAndOrbit hss hφ b
  let a₁ := (b 0).val
  let a₂ := (b 1).val
  let θ := a₁ + a₂
  change a₂ (coroot_value H a₁) = -1 at h₂₁
  change a₁ (coroot_value H a₂) = -1 at h₁₂
  have hp₁ : a₁ ∈ positive H φ := (b 0).property.1
  have hp₂ : a₂ ∈ positive H φ := (b 1).property.1
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  have h₁₁ : a₁ (coroot_value H a₁) = 2 := rootCorootSelf hss hH hp₁.1
  have h₂₂ : a₂ (coroot_value H a₂) = 2 := rootCorootSelf hss hH hp₂.1
  let r₁ := weightReflection H a₁
  let r₂ := weightReflection H a₂
  have r₁₁ : r₁ a₁ = -a₁ := by
    change weightReflection H a₁ a₁ = -a₁
    rw [weightReflection, dite_eq_left h₁₁]
    exact Module.reflection_apply_self (f := corootEvaluation H a₁) h₁₁
  have r₂₂ : r₂ a₂ = -a₂ := by
    change weightReflection H a₂ a₂ = -a₂
    rw [weightReflection, dite_eq_left h₂₂]
    exact Module.reflection_apply_self (f := corootEvaluation H a₂) h₂₂
  have r₁₂ : r₁ a₂ = θ := by
    change weightReflection H a₁ a₂ = θ
    rw [weightReflection_eq_rootReflection h₁₁]
    change a₂ - a₂ (coroot_value H a₁) • a₁ = θ
    rw [h₂₁, neg_smul, one_smul, sub_neg_eq_add, add_comm]
  have r₂₁ : r₂ a₁ = θ := by
    change weightReflection H a₂ a₁ = θ
    rw [weightReflection_eq_rootReflection h₂₂]
    change a₁ - a₁ (coroot_value H a₂) • a₂ = θ
    rw [h₁₂, neg_smul, one_smul, sub_neg_eq_add]
  have r₁θ : r₁ θ = a₂ := by simp only [θ, map_add, r₁₁, r₁₂, neg_add_cancel_left]
  have r₂θ : r₂ θ = a₁ := by simp only [θ, map_add, r₂₂, r₂₁, add_neg_cancel_right]
  have hpθ : θ ∈ positive H φ := by
    refine ⟨?_, ?_⟩
    · rw [← r₁₂, show r₁ a₂ = RootStrings.rootReflection H a₁ a₂ from
        weightReflection_eq_rootReflection h₁₁ a₂]
      exact RootStrings.reflection_mem_rootSet hss H hH a₁ a₂ hp₁.1 hp₂.1
    · change 0 < φ (a₁ + a₂)
      rw [map_add]
      exact add_pos hp₁.2 hp₂.2
  let S : Set (Module.Dual ℂ H) := {a₁, a₂, θ, -a₁, -a₂, -θ}
  have hroots : rootSet_value H ⊆ S := by
    apply horbit
    · intro i
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · intro i x hx
      fin_cases i
      · change RootStrings.rootReflection H a₁ x ∈ S
        rw [← weightReflection_eq_rootReflection h₁₁ x]
        change r₁ x ∈ S
        simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with h | h | h | h | h | h <;> rw [h] <;>
          simp [S, map_neg, r₁₁, r₁₂, r₁θ]
      · change RootStrings.rootReflection H a₂ x ∈ S
        rw [← weightReflection_eq_rootReflection h₂₂ x]
        change r₂ x ∈ S
        simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with h | h | h | h | h | h <;> rw [h] <;>
          simp [S, map_neg, r₂₁, r₂₂, r₂θ]
  have hdiff : a₁ ≠ a₂ := by
    intro he
    exact (by decide : (0 : Fin 2) ≠ 1) (b.injective (Subtype.ext he))
  have hdiff₁ : a₁ ≠ θ := by
    intro he
    have hh := congrArg φ he
    change φ a₁ = φ (a₁ + a₂) at hh
    rw [map_add] at hh
    linarith [hp₂.2]
  have hdiff₂ : a₂ ≠ θ := by
    intro he
    have hh := congrArg φ he
    change φ a₂ = φ (a₁ + a₂) at hh
    rw [map_add] at hh
    linarith [hp₁.2]
  let p : Fin 3 → positive H φ := ![⟨a₁, hp₁⟩, ⟨a₂, hp₂⟩, ⟨θ, hpθ⟩]
  let order := Equiv.ofBijective p (by
    constructor
    · intro i j he
      have hv := congrArg Subtype.val he
      fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact (hdiff hv).elim
      | exact (hdiff hv.symm).elim
      | exact (hdiff₁ hv).elim
      | exact (hdiff₁ hv.symm).elim
      | exact (hdiff₂ hv).elim
      | exact (hdiff₂ hv.symm).elim
    · intro x
      have hx := hroots x.property.1
      simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h | h | h | h
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext h.symm⟩
      · exact ⟨2, Subtype.ext h.symm⟩
      · exact (neg_not_positive hp₁ (h ▸ x.property)).elim
      · exact (neg_not_positive hp₂ (h ▸ x.property)).elim
      · exact (neg_not_positive hpθ (h ▸ x.property)).elim)
  have hsimp : simple H φ = {a₁, a₂} := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := b.surjective ⟨x, hx⟩
      have hv := congrArg Subtype.val hi
      fin_cases i
      · exact Set.mem_insert_iff.mpr (Or.inl hv.symm)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hv.symm))
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact (b 0).property
      · exact (b 1).property
  let ω₁ := c.dualBasis 0
  let ω₂ := c.dualBasis 1
  have hf (i j : Fin 2) : c.dualBasis i (coroot_value H (b j).val) =
      (if j = i then 1 else 0 : ℂ) := by
    rw [← hc j, c.dualBasis_apply_self]
  have hf₁₁ : ω₁ (coroot_value H a₁) = 1 := (hf 0 0).trans (ite_eq_left rfl)
  have hf₁₂ : ω₁ (coroot_value H a₂) = 0 := (hf 0 1).trans (ite_eq_right (by decide))
  have hf₂₁ : ω₂ (coroot_value H a₁) = 0 := (hf 1 0).trans (ite_eq_right (by decide))
  have hf₂₂ : ω₂ (coroot_value H a₂) = 1 := (hf 1 1).trans (ite_eq_left rfl)
  refine ⟨{
    α₁ := a₁
    α₂ := a₂
    ω₁ := ω₁
    ω₂ := ω₂
    positiveOrder := order
    firstRoot := rfl
    secondRoot := rfl
    highestRoot := rfl
    simpleRoots := hsimp
    highestCoroot := coroot_add_of_mixed_entries hss hH hp₁.1 hp₂.1 h₂₁ h₁₂
    highestWeight := ?_
    firstFirst := hf₁₁
    firstSecond := hf₁₂
    secondFirst := hf₂₁
    secondSecond := hf₂₂ }, rfl, rfl, ?_⟩
  · apply c.ext
    intro i
    rw [hc]
    fin_cases i
    · change (a₁ + a₂) (coroot_value H a₁) = (ω₁ + ω₂) (coroot_value H a₁)
      norm_num only [LinearMap.add_apply, h₁₁, h₂₁, hf₁₁, hf₂₁]
    · change (a₁ + a₂) (coroot_value H a₂) = (ω₁ + ω₂) (coroot_value H a₂)
      norm_num only [LinearMap.add_apply, h₁₂, h₂₂, hf₁₂, hf₂₂]
  · intro x y hxy
    apply c.ext
    intro i
    rw [hc]
    fin_cases i
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy

end ChosenPositiveSystem

end LieAlgebrasAndRepresentations.LowRankCharacterChecks
