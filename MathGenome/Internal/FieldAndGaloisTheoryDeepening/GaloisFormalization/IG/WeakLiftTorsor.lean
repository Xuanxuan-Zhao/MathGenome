import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.LiftCoordinates
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.WeakLiftTorsor
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Abel

namespace GaloisFormalization.IG.FiniteEmbeddingProblem

abbrev weakSolutionConjugacy :=
  @_root_.Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.weakSolutionConjugacy

abbrev WeakSolutionConjugacyClasses :=
  @_root_.Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.WeakSolutionConjugacyClasses

abbrev weakSolutionClass :=
  @_root_.Specs.GaloisFormalization.IG.FiniteEmbeddingProblem.weakSolutionClass

open scoped IsMulCommutative
open private vec_one from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains

universe u v w

private theorem addTorsor_eq_of_vadd_eq {H X : Type*} [AddGroup H]
    (T U : AddTorsor H X)
    (h : ∀ (c : H) (x : X),
      T.toAddAction.toVAdd.vadd c x = U.toAddAction.toVAdd.vadd c x) : T = U := by
  have hvsub (y x : X) : T.toVSub.vsub y x = U.toVSub.vsub y x := by
    have key : T.toAddAction.toVAdd.vadd (U.toVSub.vsub y x) x = y :=
      (h _ _).trans (U.vsub_vadd' y x)
    exact (congrArg (fun z => T.toVSub.vsub z x) key).symm.trans
      (T.vadd_vsub' (U.toVSub.vsub y x) x)
  cases T with
  | @mk tAdd tSub tNonempty tDisplacement tCancellation =>
    cases U with
    | @mk uAdd uSub uNonempty uDisplacement uCancellation =>
      change ∀ (c : H) (x : X), tAdd.toVAdd.vadd c x = uAdd.toVAdd.vadd c x at h
      change ∀ (y x : X), tSub.vsub y x = uSub.vsub y x at hvsub
      have hAdd : tAdd = uAdd := by
        ext c x
        exact h c x
      have hSub : tSub = uSub := by
        cases tSub
        cases uSub
        congr 1
        exact funext fun x => funext (hvsub x)
      subst uAdd
      subst uSub
      rfl

noncomputable section

variable {Γ : Type u} {B : Type v} {Q : Type w}
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
  [Group B] [Finite B] [TopologicalSpace B] [DiscreteTopology B]
  [Group Q] [Finite Q] [TopologicalSpace Q] [DiscreteTopology Q]
  (P : FiniteEmbeddingProblem Γ B Q) [IsMulCommutative P.kernel]

local notation "A" => Additive P.kernel
local notation "C" => GH.continuousCochains Γ A 1
local notation "X" => WeakSolutionConjugacyClasses P

local instance : DistribMulAction Γ A := P.pullbackKernelAction
local instance : ContinuousSMul Γ A := P.continuousSMul_pullbackKernelAction

local notation "Z" => GH.continuousCocycles Γ A 1
local notation "H" => GH.ContinuousH Γ A 1

private theorem conjugacy_iff_coordinate_difference
    (s : NormalizedSection P)
    (e : P.WeakSolution ≃ LiftCoordinateSolutions P s)
    (he : ∀ (x : P.WeakSolution) (g : Γ),
      (e x).val.val ![g] = kernelCoordinate P s (x.lift g))
    (x y : P.WeakSolution) :
    (weakSolutionConjugacy P).r x y ↔
      ∃ t : GH.continuousCochains Γ A 0,
        GH.continuousDifferential Γ A 0 t = (e x).val - (e y).val := by
  constructor
  · rintro ⟨a, ha⟩
    let b : A := Additive.ofMul a
    have hb (g : Γ) : y.lift g = b.toMul.val * x.lift g * b.toMul.val⁻¹ := ha g
    refine ⟨GH.cochainZero b, Subtype.ext (funext fun args => ?_)⟩
    rw [← vec_one args]
    change (GH.continuousDifferential Γ A 0 (GH.cochainZero b)).val
      ![args 0] = (e x).val.val ![args 0] - (e y).val.val ![args 0]
    rw [GH.differential_cochainZero, he x, he y, hb (args 0),
      kernelCoordinate_conj P s b _ _ (x.commutes_apply _)]
    abel
  · rintro ⟨t, ht⟩
    let a : A := t.val Fin.elim0
    refine ⟨a.toMul, fun g => ?_⟩
    have hd := congrArg (fun z : C => z.val ![g]) ht
    change (GH.continuousDifferential Γ A 0 t).val ![g] =
      (e x).val.val ![g] - (e y).val.val ![g] at hd
    rw [GH.differential_zero, he x, he y] at hd
    apply (sectionCoordinates P s).symm.injective
    rw [sectionCoordinates_symm_apply, sectionCoordinates_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [kernelCoordinate_conj P s a g (x.lift g) (x.commutes_apply g)]
      change kernelCoordinate P s (y.lift g) = kernelCoordinate P s (x.lift g) +
        t.val Fin.elim0 - g • t.val Fin.elim0
      calc
        _ = kernelCoordinate P s (x.lift g) -
            (kernelCoordinate P s (x.lift g) - kernelCoordinate P s (y.lift g)) :=
          (sub_sub_cancel _ _).symm
        _ = kernelCoordinate P s (x.lift g) - (g • t.val Fin.elim0 - t.val Fin.elim0) := by rw [hd]
        _ = _ := by abel
    · have ha : P.pi (a.toMul : B) = 1 := a.toMul.property
      simp only [map_mul, map_inv, ha, one_mul, inv_one, mul_one, WeakSolution.commutes_apply]

/-- For an abelian kernel and a weak solution, continuous first cohomology acts
freely and transitively on the conjugacy classes by pointwise cocycle twisting. -/
theorem weakSolutionClasses_torsor (hWeak : Nonempty P.WeakSolution) :
    ∃! torsor : AddTorsor H X,
      letI := torsor
      (∀ (c : Z) (x : P.WeakSolution), ∃ y : P.WeakSolution,
        (∀ g : Γ, y.lift g = (c.val.val ![g]).toMul.val * x.lift g) ∧
        GH.continuousClass Γ A 1 c +ᵥ weakSolutionClass P x = weakSolutionClass P y) ∧
      ∀ x y : X, ∃! c : H, c +ᵥ x = y := by
  obtain ⟨x₀⟩ := hWeak
  let s := normalizedSection P
  obtain ⟨e, he, heInv⟩ := weakSolution_coordinateEquiv P s
  let difference (x : P.WeakSolution) : Z :=
    ⟨(e x).val - (e x₀).val, by
      change GH.continuousDifferential Γ A 1 ((e x).val - (e x₀).val) = 0
      rw [map_sub, (e x).property, (e x₀).property, sub_self]⟩
  let coordinateClass (x : P.WeakSolution) : H := GH.continuousClass Γ A 1 (difference x)
  have class_eq_iff (x y : P.WeakSolution) :
      coordinateClass x = coordinateClass y ↔ (weakSolutionConjugacy P).r x y := by
    rw [conjugacy_iff_coordinate_difference P s e he]
    change GH.continuousClass Γ A 1 (difference x) =
      GH.continuousClass Γ A 1 (difference y) ↔ _
    rw [GH.continuousClass_succ_eq_iff (n := 0)]
    have hd : (difference x).val - (difference y).val = (e x).val - (e y).val := by
      change ((e x).val - (e x₀).val) - ((e y).val - (e x₀).val) = _
      abel
    rw [hd]
  let descend : X → H :=
    Quotient.lift coordinateClass fun x y h => (class_eq_iff x y).mpr h
  have translate (c : Z) (x : P.WeakSolution) : ∃ y : P.WeakSolution,
      (∀ g : Γ, y.lift g = (c.val.val ![g]).toMul.val * x.lift g) ∧
      coordinateClass y = GH.continuousClass Γ A 1 c + coordinateClass x := by
    let z : LiftCoordinateSolutions P s :=
      ⟨(e x).val + c.val, (liftCoordinateSolutions_add_iff P s (e x) c.val).mpr c.property⟩
    refine ⟨e.symm z, fun g => ?_, ?_⟩
    · have hx := heInv (e x) g
      rw [e.symm_apply_apply] at hx
      rw [heInv, hx]
      change (((e x).val.val ![g] + c.val.val ![g]).toMul : B) * s (P.rho g) =
        (c.val.val ![g]).toMul.val * (((e x).val.val ![g]).toMul.val * s (P.rho g))
      rw [add_comm, toMul_add, Subgroup.coe_mul, mul_assoc]
    · change GH.continuousClass Γ A 1 (difference (e.symm z)) =
        GH.continuousClass Γ A 1 c + GH.continuousClass Γ A 1 (difference x)
      rw [← map_add]
      congr 1
      apply Subtype.ext
      change (e (e.symm z)).val - (e x₀).val = c.val + ((e x).val - (e x₀).val)
      rw [e.apply_symm_apply]
      change (e x).val + c.val - (e x₀).val = _
      abel
  have bijective : Function.Bijective descend := by
    constructor
    · intro x y h
      revert h
      refine Quotient.inductionOn₂ x y fun u v h => ?_
      exact Quotient.sound ((class_eq_iff u v).mp h)
    · intro h
      obtain ⟨c, hc⟩ := GH.continuousClass_surjective (G := Γ) (M := A) 1 h
      obtain ⟨y, _, hy⟩ := translate c x₀
      have hz : coordinateClass x₀ = 0 := by
        change GH.continuousClass Γ A 1 (difference x₀) = 0
        rw [← map_zero (GH.continuousClass Γ A 1)]
        congr 1
        exact Subtype.ext (sub_self _)
      refine ⟨weakSolutionClass P y, ?_⟩
      change coordinateClass y = h
      simpa only [hz, add_zero, hc] using hy
  let F : X ≃ H := Equiv.ofBijective descend bijective
  let torsor : AddTorsor H X :=
    { vadd := fun c x => F.symm (c + F x)
      vsub := fun y x => F y - F x
      nonempty := ⟨weakSolutionClass P x₀⟩
      zero_vadd := fun x => by
        change F.symm (0 + F x) = x
        rw [zero_add, F.symm_apply_apply]
      add_vadd := fun c d x => by
        change F.symm (c + d + F x) = F.symm (c + F (F.symm (d + F x)))
        rw [F.apply_symm_apply, add_assoc]
      vsub_vadd' := fun y x => by
        change F.symm (F y - F x + F x) = y
        rw [sub_add_cancel, F.symm_apply_apply]
      vadd_vsub' := fun c x => by
        change F (F.symm (c + F x)) - F x = c
        rw [F.apply_symm_apply, add_sub_cancel_right] }
  refine ⟨torsor, ⟨?_, ?_⟩, ?_⟩
  · intro c x
    obtain ⟨y, hy, hyclass⟩ := translate c x
    refine ⟨y, hy, F.injective ?_⟩
    exact (F.apply_symm_apply _).trans hyclass.symm
  · intro x y
    refine ⟨F y - F x, ?_, fun c hc => ?_⟩
    · change F.symm (F y - F x + F x) = y
      simp
    · have h := congrArg F hc
      change F (F.symm (c + F x)) = F y at h
      rw [F.apply_symm_apply] at h
      exact eq_sub_of_add_eq h
  · intro other hOther
    apply addTorsor_eq_of_vadd_eq
    intro h x
    obtain ⟨c, rfl⟩ := GH.continuousClass_surjective (G := Γ) (M := A) 1 h
    refine Quotient.inductionOn x fun x => ?_
    obtain ⟨y, hy, hyOther⟩ := hOther.1 c x
    obtain ⟨z, hz, hzClass⟩ := translate c x
    have hyz : weakSolutionClass P y = weakSolutionClass P z := by
      apply Quotient.sound
      exact ⟨1, fun g => by simpa using (hz g).trans (hy g).symm⟩
    change other.toAddAction.toVAdd.vadd (GH.continuousClass Γ A 1 c) (weakSolutionClass P x) =
      F.symm (GH.continuousClass Γ A 1 c + F (weakSolutionClass P x))
    exact hyOther.trans (hyz.trans (F.injective ((F.apply_symm_apply _).trans hzClass.symm)).symm)

end
end GaloisFormalization.IG.FiniteEmbeddingProblem
