import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitComponentDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.TensorProduct.Pi

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Set Module

universe u v

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitComponentDescent

open Specs.QuasiSplitComponentDescent
open Specs.AbsoluteDynkinTypes
open RootData (integralCartan)

noncomputable section

private theorem orthogonal_components {I : Type*} (A : Matrix I I ℤ)
    {i j : I} (h : component (A := A) i ≠ component j) :
    A i j = 0 ∧ A j i = 0 := by
  have hij : i ≠ j := fun e => h (congrArg component e)
  have hne : ¬ (A i j ≠ 0 ∨ A j i ≠ 0) := fun he =>
    h (Quotient.sound (.rel i j ⟨hij, he⟩))
  simpa only [not_or, not_not] using hne

theorem componentAction : ComponentAction.{u,v} := by
  intro Γ I _ _ A hA
  have hrel (g : Γ) {i j : I} (h : Relation.EqvGen (Adjacent A) i j) :
      Relation.EqvGen (Adjacent A) (g • i) (g • j) := by
    induction h with
    | rel i j h =>
      exact .rel _ _ ⟨(MulAction.injective g).ne h.1, by simpa only [hA] using h.2⟩
    | refl i => exact .refl _
    | symm i j _ ih => exact .symm _ _ ih
    | trans i j k _ _ hi hj => exact .trans _ _ _ hi hj
  let act (g : Γ) : Components A → Components A :=
    Quotient.map (g • ·) fun _ _ h => hrel g h
  let ρ : MulAction Γ (Components A) :=
    { smul := act
      one_smul := fun c => Quotient.inductionOn c fun i => congrArg component (one_smul Γ i)
      mul_smul := fun g h c => Quotient.inductionOn c fun i => congrArg component (mul_smul g h i) }
  exact ⟨ρ, fun _ _ => rfl, fun _ _ => orthogonal_components A⟩

theorem diagramAdjacency : DiagramAdjacency.{u} := by
  classical
  intro I X Y _ _ _ P B i j
  let A := integralCartan P B
  change Adjacent A i j ↔ (@ite _ (i = j) (Classical.propDecidable _) 0 (A i j * A j i).toNat) ≠ 0
  by_cases hij : i = j
  · simp [Specs.QuasiSplitPinnedProduct.Adjacent, hij]
  have hzero : A i j = 0 ↔ A j i = 0 := P.pairing_eq_zero_iff'
  have h₁ : A i j ≤ 0 := by
    have h := B.pairingIn_le_zero_of_ne (fun e => hij (Subtype.ext e.symm)) j.property i.property
    change P.pairing j.val i.val ≤ 0
    exact (show P.pairingIn ℤ j.val i.val = P.pairing j.val i.val from
      P.algebraMap_pairingIn ℤ j.val i.val) ▸ h
  have h₂ : A j i ≤ 0 := by
    have h := B.pairingIn_le_zero_of_ne (fun e => hij (Subtype.ext e)) i.property j.property
    change P.pairing i.val j.val ≤ 0
    exact (show P.pairingIn ℤ i.val j.val = P.pairing i.val j.val from
      P.algebraMap_pairingIn ℤ i.val j.val) ▸ h
  have hpos : 0 ≤ A i j * A j i := mul_nonneg_of_nonpos_of_nonpos h₁ h₂
  rw [ite_eq_right hij, show (A i j * A j i).toNat ≠ 0 ↔ A i j * A j i ≠ 0 by
    rw [ne_eq, Int.toNat_eq_zero]; omega]
  simp [Specs.QuasiSplitPinnedProduct.Adjacent, hij, mul_eq_zero, hzero]

theorem basedComponentAction : BasedComponentAction.{u} := by
  intro Γ _ D ω A
  let s : Aut D →* Equiv.Perm D.base.support :=
    { toFun := simplePermutation D
      map_one' := by ext i; rfl
      map_mul' := fun σ τ => by ext i; rfl }
  let := MulAction.compHom D.base.support (s.comp ω)
  have hA (σ : Γ) (i j : D.base.support) : A (σ • i) (σ • j) = A i j := by
    exact (ω σ).asIso.hom.val.toHom.pairing
  exact (componentAction A hA).imp fun _ h => h.1

theorem componentDiagramConnected : ComponentDiagramConnected.{u} := by
  intro D c B
  let A := integralCartan D.datum D.base
  let A' := integralCartan B.datum.datum B.datum.base
  let V := B.vertices
  let := B.datum.finiteRoots
  have lift {i j : D.base.support} (h : Relation.EqvGen (Adjacent A) i j)
      (hi : component (A := A) i = c) (hj : component (A := A) j = c) :
      Relation.EqvGen (fun x y => (integralDiagram A').edges x y ≠ 0)
        (V.symm ⟨i, hi⟩) (V.symm ⟨j, hj⟩) := by
    induction h with
    | rel i j h =>
      apply Relation.EqvGen.rel
      apply (diagramAdjacency B.datum.datum B.datum.base _ _).mp
      have hV (i : D.base.support) (hi : component (A := A) i = c) :
          (V (V.symm ⟨i, hi⟩)).val = i := congrArg Subtype.val (V.apply_symm_apply _)
      refine ⟨fun e => h.1 (by rw [← hV i hi, ← hV j hj, e]), ?_⟩
      rw [B.preservesCartan, B.preservesCartan, hV, hV]
      exact h.2
    | refl i => exact .refl _
    | symm i j _ ih => exact .symm _ _ (ih hj hi)
    | trans i j k h₁ _ ih₁ ih₂ =>
      have hm : component (A := A) j = c := (Quotient.sound h₁).symm.trans hi
      exact .trans _ _ _ (ih₁ hi hm) (ih₂ hm hj)
  refine ⟨?_, ?_⟩
  · obtain ⟨i, rfl⟩ := Quotient.exists_rep c
    exact ⟨V.symm ⟨i, rfl⟩⟩
  · intro i j
    obtain ⟨i, rfl⟩ := V.symm.surjective i
    obtain ⟨j, rfl⟩ := V.symm.surjective j
    exact lift (Quotient.exact (i.property.trans j.property.symm)) i.property j.property

private theorem simplePermutation_mul (D : Specs.Pinning.BasedRootDatum.{u}) (g h : Aut D)
    (i : D.base.support) :
    simplePermutation D (g * h) i = simplePermutation D g (simplePermutation D h i) := by
  apply Subtype.ext
  rfl

theorem basedComponentTransport : BasedComponentTransport.{u} := by
  intro Γ _ D ω A _ hρ B
  let perm (σ : Γ) := simplePermutation D (ω σ)
  have hp (σ : Γ) (i j : D.base.support) : A (perm σ i) (perm σ j) = A i j :=
    (ω σ).asIso.hom.val.toHom.pairing
  let relabel (σ : Γ) (c d : Components A) (h : σ • c = d) :
      (B c).datum.base.support ≃ (B d).datum.base.support :=
    (B c).vertices.trans ((perm σ).subtypeEquiv (fun i => by
      change component (A := A) i = c ↔ component (A := A) (perm σ i) = d
      rw [← hρ, ← h, (MulAction.injective σ).eq_iff])) |>.trans (B d).vertices.symm
  have relabel_apply (σ : Γ) (c d : Components A) (h : σ • c = d)
      (i : (B c).datum.base.support) :
      ((B d).vertices (relabel σ c d h i)).val = perm σ ((B c).vertices i).val := by
    change ((B d).vertices ((B d).vertices.symm _)).val = _
    rw [Equiv.apply_symm_apply]
    rfl
  have label (σ : Γ) (c d : Components A) (h : σ • c = d) :
      PreservesCartan (integralCartan (B c).datum.datum (B c).datum.base)
        (integralCartan (B d).datum.datum (B d).datum.base) (relabel σ c d h) := by
    intro i j
    rw [(B c).preservesCartan, (B d).preservesCartan,
      relabel_apply σ c d h i, relabel_apply σ c d h j]
    exact (hp σ _ _).symm
  have lifts (σ : Γ) (c d : Components A) (h : σ • c = d) :=
    (RootData.AbsoluteDynkinTypes.cartanDeterminesBasedDatum (B c).datum (B d).datum
      (B c).fullCorootLattice (B d).fullCorootLattice (relabel σ c d h)).mp (label σ c d h)
  choose e he hu using lifts
  have hmatch (σ : Γ) (c d : Components A) (h : σ • c = d)
      (i : (B c).datum.base.support) (j : (B d).datum.base.support) :
      (e σ c d h).val.indexEquiv i.val = j.val ↔
        perm σ ((B c).vertices i).val = ((B d).vertices j).val := by
    rw [he, ← relabel_apply σ c d h i]
    exact ⟨fun h' => by rw [Subtype.ext h'],
      fun h' => congrArg Subtype.val ((B d).vertices.injective (Subtype.ext h'))⟩
  have hcast (σ : Γ) (c d : Components A) (h : σ • c = d) :
      e σ c d h = e σ c (σ • c) rfl ≫ eqToHom (congrArg (fun j => (B j).datum) h) := by
    subst d
    simp
  refine ⟨fun σ c => e σ c (σ • c) rfl, fun σ c => hmatch σ c (σ • c) rfl, ?_⟩
  intro c
  let J := MulAction.stabilizer Γ c
  let f (σ : J) := e σ.val c c (MulAction.mem_stabilizer_iff.mp σ.property)
  let s : J →* Aut (B c).datum :=
    { toFun := fun σ => Aut.of (asIso (f σ))
      map_one' := by
        apply Aut.ext
        apply Iso.ext
        change f 1 = 𝟙 (B c).datum
        symm
        apply hu
        intro i
        have h : perm 1 ((B c).vertices i).val = ((B c).vertices i).val := by
          simp only [perm, map_one]
          rfl
        have hh := (hmatch 1 c c (one_smul Γ c) i i).mpr h
        exact hh.symm.trans (he 1 c c (one_smul Γ c) i)
      map_mul' := by
        intro σ τ
        apply Aut.ext
        apply Iso.ext
        change f (σ * τ) = (show (B c).datum ⟶ (B c).datum from f τ) ≫
          (show (B c).datum ⟶ (B c).datum from f σ)
        symm
        apply hu
        intro i
        let hs : σ.val • c = c := MulAction.mem_stabilizer_iff.mp σ.property
        let ht : τ.val • c = c := MulAction.mem_stabilizer_iff.mp τ.property
        let hst : (σ * τ : J).val • c = c := MulAction.mem_stabilizer_iff.mp (σ * τ).property
        let j := relabel τ.val c c ht i
        let l := relabel σ.val c c hs j
        change (f σ).val.indexEquiv ((f τ).val.indexEquiv i.val) = _
        rw [show (f τ).val.indexEquiv i.val = j.val from he τ.val c c ht i,
          show (f σ).val.indexEquiv j.val = l.val from he σ.val c c hs j]
        have h : perm (σ * τ : J).val ((B c).vertices i).val = ((B c).vertices l).val := by
          change simplePermutation D (ω (σ.val * τ.val)) _ = _
          rw [map_mul, simplePermutation_mul, relabel_apply σ.val c c hs j,
            relabel_apply τ.val c c ht i]
        exact ((hmatch _ c c hst i l).mpr h).symm.trans (he _ c c hst i) }
  exact ⟨s, fun σ => hcast σ.val c c (MulAction.mem_stabilizer_iff.mp σ.property)⟩


private theorem simple_supported {I : Type*} [DecidableEq I] (A : Matrix I I ℤ) (i : I) :
    SupportedOn {j | component j = component (A := A) i} (simpleCharacter A i, Pi.single i 1) := by
  intro j hj
  have hc : component (A := A) j ≠ component i := hj
  have hji : j ≠ i := fun e => hc (congrArg component e)
  exact ⟨(orthogonal_components A hc).1, Pi.single_eq_of_ne hji 1⟩

private theorem cartanRoot_supported {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} {p : (I → ℤ) × (I → ℤ)} (h : CartanRoots A p) :
    ∃ c : Components A, SupportedOn {j | component j = c} p := by
  induction h with
  | simple i => exact ⟨component i, simple_supported A i⟩
  | neg _ ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c, fun i hi => ?_⟩
    obtain ⟨h₁, h₂⟩ := hc i hi
    exact ⟨by simpa only [Pi.neg_apply, neg_zero] using congrArg Neg.neg h₁,
      by simpa only [Pi.neg_apply, neg_zero] using congrArg Neg.neg h₂⟩
  | reflect i _ ih =>
    obtain ⟨c, hc⟩ := ih
    let S := {j | component (A := A) j = c}
    have hcross (a : I) (ha : a ∈ S) (b : I) (hb : b ∉ S) : A a b = 0 ∧ A b a = 0 :=
      orthogonal_components A fun e => hb (e.symm.trans ha)
    have hr := (RootData.AbsoluteDynkinTypes.cartanRootBlocks A S hcross).2 _ hc i
    refine ⟨c, ?_⟩
    by_cases hi : i ∈ S
    · exact hr.2 hi
    · rwa [hr.1 hi]

theorem rootComponentCoordinates : RootComponentCoordinates.{u} := by
  classical
  intro I X Y _ _ _ P _ B h
  let A := integralCartan P B
  obtain ⟨b, x, hb, hp, hx, hr⟩ :=
    RootData.AbsoluteDynkinTypes.cartanCoordinates P B h A (Equiv.refl _) (fun _ _ => rfl)
  refine ⟨x, b.equivFun, ?_, ?_, hp, ?_⟩
  · intro i j
    exact congrFun (hx i) j
  · intro i
    rw [show P.coroot i.val = b i from (hb i).symm]
    funext j
    simp [Basis.equivFun_self, Pi.single_apply, eq_comm]
  · intro i
    have hm : (x (P.root i), b.equivFun (P.coroot i)) ∈ {p | CartanRoots A p} := by
      rw [← hr]
      exact mem_range_self i
    obtain ⟨c, hc⟩ := cartanRoot_supported hm
    refine ⟨c, hc, ?_⟩
    intro d hd
    by_contra hdc
    have hz : x (P.root i) = 0 := by
      funext j
      by_cases hj : component (A := A) j = c
      · exact (hd j (fun he => hdc (he.symm.trans hj))).1
      · exact (hc j hj).1
    exact P.ne_zero i (x.injective (hz.trans (map_zero x).symm))

open private blockDatum blockDatum_reduced blockDatum_coroot_span blockIndex
  coordinatePairing_apply splitLattice restrict_zero_outside block_sum
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

private theorem restrict_simple_independent {J : Type u} (S : Set J) [DecidablePred (· ∈ S)]
    {a : J → J → ℤ} (ha : LinearIndependent ℤ a)
    (hs : ∀ j ∈ S, ∀ k ∉ S, a j k = 0) :
    LinearIndependent ℤ (fun j : S => fun k : S => a j.val k.val) := by
  let f := (splitLattice S).symm.toLinearMap.comp (LinearMap.inl ℤ _ _)
  apply LinearIndependent.of_comp f
  have he (j : S) : f (fun k : S => a j.val k.val) = a j.val := by
    apply (splitLattice S).injective
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact (restrict_zero_outside (hs j.val j.property)).symm
  rw [show (⇑f ∘ fun j : S => fun k : S => a j.val k.val) =
      a ∘ Subtype.val from funext he]
  exact ha.comp Subtype.val Subtype.val_injective

private theorem restrict_simple_closure {J : Type u} (S : Set J) {a : J → J → ℤ}
    (hs : ∀ j ∉ S, ∀ k ∈ S, a j k = 0) {z : J → ℤ}
    (hz : z ∈ AddSubmonoid.closure (range a)) :
    (fun j : S => z j.val) ∈
      AddSubmonoid.closure (range fun j : S => fun k : S => a j.val k.val) := by
  classical
  induction hz using AddSubmonoid.closure_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    by_cases hj : j ∈ S
    · exact AddSubmonoid.subset_closure ⟨⟨j, hj⟩, rfl⟩
    · rw [show (fun k : S => a j k.val) = 0 from funext fun k => hs j hj k.val k.property]
      exact AddSubmonoid.zero_mem _
  | zero => exact AddSubmonoid.zero_mem _
  | add _ _ _ _ hy hz => exact AddSubmonoid.add_mem _ hy hz

private theorem map_simple_closure {I V W : Type u} [AddCommGroup V] [AddCommGroup W]
    (f : V →ₗ[ℤ] W) (v : I → V) (s : Finset I) {a : V}
    (h : a ∈ AddSubmonoid.closure (v '' (s : Set I))) :
    f a ∈ AddSubmonoid.closure (range fun j : s => f (v j.val)) := by
  rw [show (range fun j : s => f (v j.val)) = f '' (v '' (s : Set I)) by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨v j.val, ⟨j.val, j.property, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩]
  rw [← AddMonoidHom.map_mclosure]
  exact AddSubmonoid.mem_map.mpr ⟨a, h, rfl⟩

theorem rootComponentData : RootComponentData.{u} := by
  classical
  intro I X Y _ _ _ P _ B h
  obtain ⟨x, y, hx, hy, hpair, _⟩ := rootComponentCoordinates P B h
  refine ⟨x, y, hpair, hy, ?_⟩
  intro c S
  let : DecidablePred (· ∈ S) := Classical.decPred _
  let A := integralCartan P B
  let s : B.support → I := Subtype.val
  have hcross (i j : B.support) (hi : i ∈ S) (hj : j ∉ S) : A i j = 0 ∧ A j i = 0 :=
    orthogonal_components A (fun e => hj (e.symm.trans hi))
  have hsimple (j : B.support) (hj : j ∈ S) :
      SupportedOn S (x (P.root (s j)), y (P.coroot (s j))) := by
    intro l hl
    have hne : l ≠ j := fun e => hl (e ▸ hj)
    exact ⟨(hx j l).trans (hcross j l hj hl).2,
      by rw [show y (P.coroot (s j)) = Pi.single j 1 from hy j]
         exact Pi.single_eq_of_ne hne 1⟩
  let R := blockDatum P x y S hpair
  have hcoord (a b : S → ℤ) : R.toLinearMap a b = ∑ j : S, b j * a j :=
    coordinatePairing_apply a b
  let t (j : S) : blockIndex P x y S := ⟨s j.val, hsimple j.val j.property⟩
  have ht : Function.Injective t := by
    intro j k he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : blockIndex P x y S => a.val) he
  let simple : Finset (blockIndex P x y S) := Finset.univ.image t
  have hm (i : blockIndex P x y S) : i ∈ simple ↔ ∃ j, t j = i := by
    simp [simple]
  let equiv : S ≃ (simple : Set (blockIndex P x y S)) :=
    Equiv.ofBijective (fun j => ⟨t j, (hm _).mpr ⟨j, rfl⟩⟩)
      ⟨fun _ _ h => ht (congrArg Subtype.val h), fun i => by
        obtain ⟨j, hj⟩ := (hm i.val).mp i.property
        exact ⟨j, Subtype.ext hj⟩⟩
  have hindRoot : LinearIndepOn ℤ R.root (simple : Set _) := by
    have h₁ := B.linearIndepOn_root.linearIndependent.map' x.toLinearMap (LinearMap.ker_eq_bot.mpr x.injective)
    have h₂ := restrict_simple_independent S h₁ (fun j hj l hl => (hsimple j hj l hl).1)
    have h₃ := h₂.comp equiv.symm equiv.symm.injective
    change LinearIndependent ℤ (fun i : (simple : Set _) => R.root i.val)
    have he (i : (simple : Set _)) : t (equiv.symm i) = i.val :=
      congrArg Subtype.val (equiv.apply_symm_apply i)
    rw [show (fun i : (simple : Set _) => R.root i.val) =
      (fun j : S => R.root (t j)) ∘ equiv.symm from funext fun i => congrArg R.root (he i).symm]
    exact h₃
  have hindCoroot : LinearIndepOn ℤ R.coroot (simple : Set _) := by
    have h₁ := B.linearIndepOn_coroot.linearIndependent.map' y.toLinearMap (LinearMap.ker_eq_bot.mpr y.injective)
    have h₂ := restrict_simple_independent S h₁ (fun j hj l hl => (hsimple j hj l hl).2)
    have h₃ := h₂.comp equiv.symm equiv.symm.injective
    change LinearIndependent ℤ (fun i : (simple : Set _) => R.coroot i.val)
    have he (i : (simple : Set _)) : t (equiv.symm i) = i.val :=
      congrArg Subtype.val (equiv.apply_symm_apply i)
    rw [show (fun i : (simple : Set _) => R.coroot i.val) =
      (fun j : S => R.coroot (t j)) ∘ equiv.symm from funext fun i => congrArg R.coroot (he i).symm]
    exact h₃
  have hrangeRoot : (R.root '' (simple : Set _)) =
      range fun j : S => fun l : S => x (P.root (s j.val)) l.val := by
    ext w
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, rfl⟩ := (hm i).mp hi
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨t j, (hm _).mpr ⟨j, rfl⟩, rfl⟩
  have hrangeCoroot : (R.coroot '' (simple : Set _)) =
      range fun j : S => fun l : S => y (P.coroot (s j.val)) l.val := by
    ext w
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, rfl⟩ := (hm i).mp hi
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨t j, (hm _).mpr ⟨j, rfl⟩, rfl⟩
  have hrootZero (j : B.support) (hj : j ∉ S) (l : B.support) (hl : l ∈ S) :
      x (P.root (s j)) l = 0 := (hx j l).trans (hcross l j hl hj).1
  have hcorootZero (j : B.support) (hj : j ∉ S) (l : B.support) (hl : l ∈ S) :
      y (P.coroot (s j)) l = 0 := by
    rw [show y (P.coroot (s j)) = Pi.single j 1 from hy j]
    exact Pi.single_eq_of_ne (fun he : l = j => hj (he ▸ hl)) 1
  let B' : R.Base :=
    { support := simple
      linearIndepOn_root := hindRoot
      linearIndepOn_coroot := hindCoroot
      root_mem_or_neg_mem := fun i => by
        rw [hrangeRoot]
        rcases B.root_mem_or_neg_mem i.val with h | h
        · exact .inl (restrict_simple_closure S hrootZero (map_simple_closure x.toLinearMap P.root B.support h))
        · have hh := restrict_simple_closure S hrootZero
            (map_simple_closure x.toLinearMap P.root B.support h)
          right
          change (fun j : S => -x (P.root i.val) j.val) ∈ _
          simpa only [LinearEquiv.coe_coe, map_neg, Pi.neg_apply] using hh
      coroot_mem_or_neg_mem := fun i => by
        rw [hrangeCoroot]
        rcases B.coroot_mem_or_neg_mem i.val with h | h
        · exact .inl (restrict_simple_closure S hcorootZero (map_simple_closure y.toLinearMap P.coroot B.support h))
        · have hh := restrict_simple_closure S hcorootZero
            (map_simple_closure y.toLinearMap P.coroot B.support h)
          right
          change (fun j : S => -y (P.coroot i.val) j.val) ∈ _
          simpa only [LinearEquiv.coe_coe, map_neg, Pi.neg_apply] using hh }
  let D : Specs.Pinning.BasedRootDatum.{u} :=
    { I := blockIndex P x y S
      X := S → ℤ
      Y := S → ℤ
      finiteRoots := inferInstance
      freeX := .of_basis (Pi.basisFun ℤ S)
      freeY := .of_basis (Pi.basisFun ℤ S)
      finiteX := .of_basis (Pi.basisFun ℤ S)
      finiteY := .of_basis (Pi.basisFun ℤ S)
      datum := R
      reduced := blockDatum_reduced P x y S hpair
      base := B' }
  let d : ComponentDatum P B c :=
    { datum := D
      fullCorootLattice := blockDatum_coroot_span P x y S hpair s hy hsimple
      vertices := equiv.symm
      preservesCartan := by
        intro i j
        obtain ⟨i, rfl⟩ := equiv.surjective i
        obtain ⟨j, rfl⟩ := equiv.surjective j
        change R.toLinearMap (R.root (t j)) (R.coroot (t i)) =
          P.toLinearMap (P.root (s (equiv.symm (equiv j)).val))
            (P.coroot (s (equiv.symm (equiv i)).val))
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, hpair]
        rw [hcoord]
        exact block_sum S (fun b => y (P.coroot (s i.val)) b * x (P.root (s j.val)) b)
          (fun b hb => mul_eq_zero_of_left ((hsimple i.val i.property) b hb).2 _) }

  exact ⟨d, Equiv.refl _, LinearEquiv.refl _ _, LinearEquiv.refl _ _,
    hcoord, fun _ => rfl, fun _ => rfl,
    fun i => (congrArg Subtype.val (congrArg Subtype.val (equiv.apply_symm_apply i))).symm⟩

open Specs.Pinning (AttachedDatum)
open Specs.SimplyConnectedLattice (corootLattice)
open private coroot_span_of_equiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private of_fullCorootLattice from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

theorem pinnedComponentModels : PinnedComponentModels.{u} := by
  classical
  intro F _ A P D h B
  let := B.finiteRoots
  let := B.reduced
  obtain ⟨_, _, _, _, hdata⟩ := rootComponentData B.datum B.base h
  let block c := Classical.choose (hdata c)
  obtain ⟨d, f, hobj, _, hf, _⟩ := Classification.PinnedEquivalence.pinnedEquivalence.1 A
  let := hf
  let Q (c : Components (integralCartan B.datum B.base)) := f.objPreimage (block c).datum
  let e (c : Components (integralCartan B.datum B.base)) :=
    (f.objObjPreimageIso (block c).datum).symm ≪≫ eqToIso (hobj (Q c))
  refine ⟨block, Q, fun c => d (Q c), fun c => ?_⟩
  let E := d (Q c)
  let := E.comm
  let := (block c).datum.finiteRoots
  have hE : corootLattice E = ⊤ :=
    coroot_span_of_equiv _ _ (e c).hom.val (block c).fullCorootLattice
  have hs := of_fullCorootLattice (Q c).pair E hE
  refine ⟨hs, ?_, ⟨(e c).hom⟩⟩
  exact (Classification.SimplyConnectedLattice.latticeCriterion (Q c).pair.G hs
    (Q c).pair.T (Q c).pair.split (Q c).pair.maximal E.datum).mpr hE

open private transportHom from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

set_option backward.isDefEq.respectTransparency false in
theorem pinnedComponentTransport : PinnedComponentTransport.{u} := by
  intro F Γ _ _ A D ω C _ hρ B
  obtain ⟨t, ht, hs⟩ := basedComponentTransport D ω hρ B
  obtain ⟨T, f, hobj, hmap, hf, _⟩ := Classification.PinnedEquivalence.pinnedEquivalence.1 A
  let := hf
  let ff := f.asEquivalence.fullyFaithfulFunctor
  let Q (c : C) := f.objPreimage (B c).datum
  let j (c : C) : (B c).datum ≅ f.obj (Q c) := (f.objObjPreimageIso (B c).datum).symm
  let a (c : C) : (B c).datum ≅ (T (Q c)).toBased := j c ≪≫ eqToIso (hobj (Q c))
  let transport (σ : Γ) (c : C) : Specs.Pinning.PinnedIso (Q c) (Q (σ • c)) :=
    ff.preimage ((j c).inv ≫ t σ c ≫ (j (σ • c)).hom)
  have htrans (σ : Γ) (c : C) :
      f.map (transport σ c) = (j c).inv ≫ t σ c ≫ (j (σ • c)).hom :=
    ff.map_preimage _
  refine ⟨Q, fun c => T (Q c), fun c => (a c).hom, transport, ?_, ?_, ?_⟩
  · intro c
    let E := T (Q c)
    let := E.comm
    let := (B c).datum.finiteRoots
    have hE : corootLattice E = ⊤ :=
      coroot_span_of_equiv _ _ (a c).hom.val (B c).fullCorootLattice
    have hs := of_fullCorootLattice (Q c).pair E hE
    exact ⟨hs, (Classification.SimplyConnectedLattice.latticeCriterion (Q c).pair.G hs
      (Q c).pair.T (Q c).pair.split (Q c).pair.maximal E.datum).mpr hE⟩
  · intro σ c i l hil
    let d := σ • c
    let := (T (Q c)).comm
    let := (T (Q d)).comm
    let g : (T (Q c)).toBased ⟶ (T (Q d)).toBased :=
      (hobj (Q c)) ▸ (hobj (Q d)) ▸ f.map (transport σ c)
    have hg : g = (a c).inv ≫ t σ c ≫ (a d).hom := by
      have hh := transportHom (hobj (Q c)) (hobj (Q d)) (f.map (transport σ c))
      change g = _ at hh
      rw [hh, htrans]
      simp only [a, Iso.trans_inv, Iso.trans_hom, eqToIso.hom, eqToIso.inv, Category.assoc]
      rfl
    have hcom : (a c).hom ≫ g = t σ c ≫ (a d).hom := by rw [hg, Iso.hom_inv_id_assoc]
    have hi := congrArg (fun (p : (B c).datum ⟶ (T (Q d)).toBased) =>
      p.val.indexEquiv i.val) hcom
    change g.val.indexEquiv ((a c).hom.val.indexEquiv i.val) =
      (a d).hom.val.indexEquiv ((t σ c).val.indexEquiv i.val) at hi
    rw [(ht σ c i l).mpr hil] at hi
    let χ : Specs.CharacterDescent.Character (Q c).pair.T.group :=
      ((a c).hom.val.indexEquiv i.val).val
    have hw := (hmap (Q c) (Q d) (transport σ c)).1 χ
    change g.val.weightEquiv (Additive.ofMul χ) = _ at hw
    have hr := g.val.toHom.root_weightMap_apply (T (Q c)).toBased.datum
      (T (Q d)).toBased.datum ((a c).hom.val.indexEquiv i.val)
    change g.val.weightEquiv ((T (Q c)).datum.rootDatum.root _) =
      (T (Q d)).datum.rootDatum.root _ at hr
    rw [(T (Q c)).datum.root_eq, (T (Q d)).datum.root_eq, hi] at hr
    exact congrArg Additive.toMul (hw.symm.trans hr)
  · intro c
    obtain ⟨s, hs⟩ := hs c
    have hj (d : C) (hd : d = c) :
        eqToHom (congrArg (fun x => (B x).datum) hd) ≫ (j c).hom =
          (j d).hom ≫ f.map (eqToHom (congrArg Q hd)) := by
      subst d
      simp
    let b := Aut.autMulEquivOfIso (j c)
    let e := ff.autMulEquivOfFullyFaithful (Q c)
    refine ⟨e.symm.toMonoidHom.comp (b.toMonoidHom.comp s), ?_⟩
    intro σ
    have h := congrArg (fun p => p.asIso.hom) (e.apply_symm_apply (b (s σ)))
    change f.map (e.symm (b (s σ))).asIso.hom =
      (j c).inv ≫ (s σ).asIso.hom ≫ (j c).hom at h
    apply ff.map_injective
    change f.map (e.symm (b (s σ))).asIso.hom =
      f.map (transport σ.val c ≫ eqToHom (congrArg Q (MulAction.mem_stabilizer_iff.mp σ.property)))
    rw [h, hs, f.map_comp, htrans]
    simpa only [Category.assoc] using congrArg
      (fun l : (B (σ.val • c)).datum ⟶ f.obj (Q c) => (j c).inv ≫ t σ.val c ≫ l)
      (hj (σ.val • c) (MulAction.mem_stabilizer_iff.mp σ.property))

theorem emptyMarkedSplitProduct : EmptyMarkedSplitProduct.{u} := by
  classical
  intro F _ P D M hD hS I _ H N
  have hz : IsZero P.G.val := by
    by_contra h
    obtain ⟨s⟩ := RootData.AbsoluteDynkinTypes.nonemptySimpleRoots P D hD h
    exact hS.false s
  have hsub (m : Marking) : IsZero (M.subgroup m).group := by
    let S := M.subgroup m
    let := S.isClosedImmersion
    let : Mono S.inclusion := (Grp.forget (SchemeOver F) ⋙ Over.forget _).mono_of_mono_map
      (show Mono S.inclusion.hom.hom.left from inferInstance)
    exact IsZero.of_mono_eq_zero S.inclusion (hz.eq_zero_of_tgt _)
  refine ⟨{
    projection := fun i => isEmptyElim i
    subgroupProjection := fun _ i => isEmptyElim i
    commutes := fun _ i => isEmptyElim i
    product := (isLimitEquivIsTerminalOfIsEmpty _ _).symm hz.isTerminal
    subgroupProduct := fun m => (isLimitEquivIsTerminalOfIsEmpty _ _).symm (hsub m).isTerminal }⟩


theorem weilFieldPointsRespectInclusions : WeilFieldPointsRespectInclusions.{u} := by
  intro F E _ _ _ V H U G i j a b hab
  have h := NatTrans.congr_app hab (CommAlgCat.of F F)
  change ((groupPointsFunctor F).map i).app _ ≫ b.hom.app _ =
    a.hom.app _ ≫ ((groupPointsFunctor E).map j).app _ at h
  let e := (scalarExtensionOfGroundField F E).hom
  change ((groupPointsFunctor F).map i).app _ ≫ b.hom.app _ ≫
      ((groupPointsFunctor E).obj G).map e =
    (a.hom.app _ ≫ ((groupPointsFunctor E).obj U).map e) ≫
      ((groupPointsFunctor E).map j).app _
  rw [← Category.assoc, h, Category.assoc, Category.assoc,
    ((groupPointsFunctor E).map j).naturality e]

private def productPointsEquiv {F I : Type u} [Field F] {G : I → Specs.GroupScheme F}
    [Finite I] (P : Fan G) (hP : IsLimit P) (R : TestAlgebra F) :
    ((groupPointsFunctor F).obj P.pt).obj R ≃*
      (∀ i, ((groupPointsFunctor F).obj (G i)).obj R) :=
  let Fg := Grp.forget (SchemeOver F)
  let h := (Fan.isLimitMapConeEquiv Fg G P) (isLimitOfPreserves Fg hP)
  { toFun := fun x i => ((groupPointsFunctor F).map (P.proj i)).app R x
    invFun := fun x => Fan.IsLimit.lift h x
    left_inv := fun _x => Fan.IsLimit.hom_ext h _ _ (fun i => Fan.IsLimit.fac h _ i)
    right_inv := fun _x => funext (fun i => Fan.IsLimit.fac h _ i)
    map_mul' := fun x y => funext fun i =>
      map_mul (((groupPointsFunctor F).map (P.proj i)).app R).hom x y }

theorem markedProductFieldPoints : MarkedProductFieldPoints.{u} := by
  intro F I _ _ E _ _ G H M N J W prod weil
  let R := CommAlgCat.of F F
  let e₀ := productPointsEquiv _ prod.product R
  let e₁ := MulEquiv.piCongrRight fun i => (weilFieldPointIso F (E i) (weil i).groupIso).groupIsoToMulEquiv
  let e := e₀.trans e₁
  refine ⟨e, fun _ _ => rfl, ?_⟩
  intro m x
  let f := ((groupPointsFunctor F).map (M.subgroup m).inclusion).app R
  let fᵢ (i : I) := ((groupPointsFunctor (E i)).map ((W i).subgroup m).inclusion).app (CommAlgCat.of (E i) (E i))
  let d₀ := productPointsEquiv _ (prod.subgroupProduct m) R
  let d₁ := MulEquiv.piCongrRight fun i =>
    (weilFieldPointIso F (E i) ((weil i).subgroupIso m)).groupIsoToMulEquiv
  let d := d₀.trans d₁
  have hcomm (y : ((groupPointsFunctor F).obj (M.subgroup m).group).obj R) (i : I) :
      e (f y) i = fᵢ i (d y i) := by
    have h₁ := NatTrans.congr_app
      (congrArg ((groupPointsFunctor F).map) (prod.commutes m i)) R
    simp only [Functor.map_comp, NatTrans.comp_app] at h₁
    change (weilFieldPointIso F (E i) (weil i).groupIso).hom
        (((groupPointsFunctor F).map (prod.projection i)).app R (f y)) = _
    rw [show (((groupPointsFunctor F).map (prod.projection i)).app R (f y)) =
        (((groupPointsFunctor F).map ((N i).subgroup m).inclusion).app R)
          (((groupPointsFunctor F).map (prod.subgroupProjection m i)).app R y) from
      ConcreteCategory.congr_hom h₁ y]
    exact ConcreteCategory.congr_hom
      (weilFieldPointsRespectInclusions F (E i) ((N i).subgroup m).inclusion
        ((W i).subgroup m).inclusion ((weil i).subgroupIso m) (weil i).groupIso ((weil i).commutes m))
      (((groupPointsFunctor F).map (prod.subgroupProjection m i)).app R y)
  change x ∈ f.hom.range ↔ ∀ i, e x i ∈ (fᵢ i).hom.range
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨d y i, (hcomm y i).symm⟩
  · intro h
    choose y hy using h
    refine ⟨d.symm y, e.injective (funext fun i => ?_)⟩
    rw [hcomm]
    exact (congrArg (fᵢ i) (congrFun (d.apply_symm_apply y) i)).trans (hy i)

open scoped TensorProduct

theorem orbitFieldEmbeddings : OrbitFieldEmbeddings.{u} := by
  classical
  intro F K I _ _ _ _ _ _ i horbit
  let J := MulAction.stabilizer Gal(K/F) i
  let L := IntermediateField.fixedField J
  choose g hg using horbit
  let φ (s : Gal(K/F)) : L →ₐ[F] K := s.toAlgHom.comp L.val
  have hφ (s t : Gal(K/F)) : φ s = φ t ↔ s • i = t • i := by
    have hJ : L.fixingSubgroup = J := IntermediateField.fixingSubgroup_fixedField J
    rw [← show t⁻¹ * s ∈ J ↔ s • i = t • i from by
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]]
    rw [← hJ, IntermediateField.mem_fixingSubgroup_iff]
    refine ⟨fun h x hx => ?_, fun h => AlgHom.ext fun x => ?_⟩
    · have he : s x = t x := DFunLike.congr_fun h ⟨x, hx⟩
      change t.symm (s x) = x
      rw [he, AlgEquiv.symm_apply_apply]
    · have he := h x.val x.property
      change t.symm (s x.val) = x.val at he
      exact (t.apply_symm_apply _).symm.trans (congrArg t he)
  let f (j : I) := φ (g j)
  have hf : Function.Bijective f := by
    constructor
    · intro j k h
      simpa only [hg] using (hφ (g j) (g k)).mp h
    · intro a
      obtain ⟨s₀, hs₀⟩ := IntermediateField.exists_algHom_of_splits
        (fun x : K => ⟨IsGalois.integral F x, IsGalois.splits F x⟩) a
      let s : Gal(K/F) := (algEquivEquivAlgHom F K).symm s₀
      have hs : φ s = a := (congrArg (fun b : K →ₐ[F] K => b.comp L.val)
        ((algEquivEquivAlgHom F K).apply_symm_apply s₀)).trans hs₀
      exact ⟨s • i, ((hφ (g (s • i)) s).2 (hg (s • i))).trans hs⟩
  refine ⟨Equiv.ofBijective f hf, ?_, ?_⟩
  · change φ (g i) = L.val
    exact ((hφ (g i) 1).2 ((hg i).trans (one_smul _ _).symm)).trans rfl
  · intro σ j
    change φ (g (σ • j)) = σ.toAlgHom.comp (φ (g j))
    exact ((hφ _ (σ * g j)).2 (by rw [hg, mul_smul, hg])).trans rfl

theorem orbitFieldTensorSplitting : OrbitFieldTensorSplitting.{u} := by
  classical
  intro F K _ _ _ _ _ L
  let f : K ⊗[F] L →ₐ[K] (L →ₐ[F] K) → K :=
    AlgHom.pi fun a => Algebra.TensorProduct.lift (AlgHom.id K K) a (fun _ _ => Commute.all _ _)
  have hf (r : K) (l : L) (a : L →ₐ[F] K) : f (r ⊗ₜ[F] l) a = r * a l := rfl
  have hsep (a b : L →ₐ[F] K) (h : a ≠ b) :
      ∃ z : K ⊗[F] L, f z a = 1 ∧ f z b = 0 := by
    obtain ⟨l, hl⟩ : ∃ l : L, a l ≠ b l := by
      by_contra! h'
      exact h (AlgHom.ext h')
    let c := (a l - b l)⁻¹
    refine ⟨c ⊗ₜ[F] l - (c * b l) ⊗ₜ[F] 1, ?_, ?_⟩
    · simp only [map_sub, Pi.sub_apply, hf, map_one, mul_one]
      rw [← mul_sub, inv_mul_cancel₀ (sub_ne_zero.mpr hl)]
    · simp only [map_sub, Pi.sub_apply, hf, map_one, mul_one, sub_self]
  have hsingle (a : L →ₐ[F] K) : ∃ z : K ⊗[F] L, f z = Pi.single a 1 := by
    let s := Finset.univ.erase a
    have hne (b : s) : a ≠ b.val := (Finset.mem_erase.mp b.property).1.symm
    choose z haz hbz using fun b : s => hsep a b.val (hne b)
    refine ⟨∏ b, z b, ?_⟩
    funext b
    let ev := (Pi.evalAlgHom K (fun _ : L →ₐ[F] K => K) b).comp f
    change ev (∏ b, z b) = _
    rw [show ev (∏ b, z b) = ∏ i : s, ev (z i) from map_prod ev.toMonoidHom z Finset.univ]
    by_cases h : b = a
    · subst b
      simp only [ev, AlgHom.comp_apply, Pi.evalAlgHom_apply, haz, Finset.prod_const_one,
        Pi.single_eq_same]
    · have hb : b ∈ s := Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩
      rw [Finset.prod_eq_zero (Finset.mem_univ (⟨b, hb⟩ : s)) (hbz ⟨b, hb⟩)]
      simp [Ne.symm h]
  choose z hz using hsingle
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨∑ a, ((y a) ⊗ₜ[F] (1 : L)) * z a, ?_⟩
    funext b
    simp only [map_sum, map_mul, Finset.sum_apply, Pi.mul_apply, hf, map_one, mul_one, hz]
    simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero] using Fintype.sum_ite_eq b y
  have hdim : finrank K (K ⊗[F] L) = finrank K ((L →ₐ[F] K) → K) := by
    rw [Module.finrank_baseChange, Module.finrank_pi, AlgHom.card_of_splits F L K]
    intro l
    rw [← minpoly.algHom_eq L.val L.val.injective l]
    exact Normal.splits' (l : K)
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f.toLinearMap)).2 hsurj
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

theorem orbitTensorSplittingOnTestAlgebras : OrbitTensorSplittingOnTestAlgebras.{u} := by
  classical
  intro F K _ _ _ _ _ L U
  obtain ⟨s, hs⟩ := orbitFieldTensorSplitting L
  let e (R : TestAlgebra K) : (U.obj R) ⊗[F] L ≃ₐ[R] ((L →ₐ[F] K) → R) := by
    letI : Algebra F R := (U.obj R).algebra
    letI : IsScalarTower F K R := IsScalarTower.of_algebraMap_eq' rfl
    exact (Algebra.TensorProduct.cancelBaseChange F K R R L).symm.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) s).trans
        (Algebra.TensorProduct.piScalarRight K R R _))
  have he (R : TestAlgebra K) (r : R) (l : L) (a : L →ₐ[F] K) :
      e R (r ⊗ₜ[F] l) a = r * algebraMap K R (a l) := by
    dsimp only [e, AlgEquiv.trans_apply]
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    change Algebra.TensorProduct.piScalarRight K R R _ (r ⊗ₜ[K] s (1 ⊗ₜ[F] l)) a = _
    rw [Algebra.TensorProduct.piScalarRight_tmul_apply, hs, one_mul, Algebra.smul_def, mul_comm]
  refine ⟨e, he, ?_⟩
  intro R S f x a
  induction x using TensorProduct.inductionOn with
  | tmul r l =>
    rw [Algebra.TensorProduct.map_tmul]
    change e S (f.hom r ⊗ₜ[F] l) a = f.hom (e R (r ⊗ₜ[F] l) a)
    rw [he, he, map_mul, f.hom.commutes]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

set_option backward.isDefEq.respectTransparency false in
theorem orbitTestAlgebraProduct : OrbitTestAlgebraProduct.{u} := by
  intro F K _ _ _ _ _ L R
  obtain ⟨split, pure, _⟩ := orbitTensorSplittingOnTestAlgebras L
  let A := (restrictTestAlgebra F K).obj R
  let T := (WeilRestriction.extendScalars F L).obj A
  let V (a : L →ₐ[F] K) := orbitTestAlgebra L a R
  let p (a : L →ₐ[F] K) := orbitTestProjection L a R
  let e := split R
  have hp (a : L →ₐ[F] K) (x : T) : (p a).hom x = e x a := by
    change _ = e x a
    induction x using TensorProduct.inductionOn with
    | tmul r l =>
      change r * algebraMap K R (a l) = e (r ⊗ₜ[F] l) a
      exact (pure R r l a).symm
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  let lift (s : Fan V) : s.pt ⟶ T := by
    let f : s.pt →+* ((L →ₐ[F] K) → R) := RingHom.pi fun a => (s.proj a).hom.toRingHom
    letI : Algebra L s.pt := s.pt.algebra
    letI : Algebra L T := T.algebra
    refine ConcreteCategory.ofHom (C := CommAlgCat L)
      ({ e.symm.toRingHom.comp f with commutes' := fun l => ?_ } : s.pt →ₐ[L] T)
    apply e.injective
    funext a
    change e (e.symm (f (algebraMap L s.pt l))) a = e (1 ⊗ₜ[F] l) a
    rw [AlgEquiv.apply_symm_apply, pure, one_mul]
    exact (s.proj a).hom.commutes l
  have hlift (s : Fan V) (x : s.pt) : e ((lift s).hom x) = fun a => (s.proj a).hom x :=
    e.apply_symm_apply _
  refine ⟨Fan.IsLimit.mk (Fan.mk T p) lift ?_ ?_⟩
  · intro s a
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change (p a).hom ((lift s).hom x) = (s.proj a).hom x
    rw [hp]
    exact congrFun (hlift s x) a
  · intro s m hm
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply e.injective
    funext a
    exact (hp a (m.hom x)).symm.trans
      ((ConcreteCategory.congr_hom (hm a) x).trans (congrFun (hlift s x) a).symm)

section WeilProduct

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open WeilRestriction (extendScalars spectrumPoints)
open private productOptionIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private affine_tensor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure

private def groupBaseChangePointIso (F K : Type u) [Field F] [Field K] [Algebra F K]
    (G : Specs.GroupScheme F) :
    (groupPointsFunctor K).obj ((groupBaseChange F K).obj G) ≅
      restrictTestAlgebra F K ⋙ (groupPointsFunctor F).obj G :=
  NatIso.ofComponents (fun R =>
    ({ toEquiv := Equiv.ofBijective (baseChangePoint F K G.X R) (baseChangePoints F K G.X R)
       map_mul' := baseChangePointsGroupLaw F K G R } :
      ((groupPointsFunctor K).obj ((groupBaseChange F K).obj G)).obj R ≃*
        ((groupPointsFunctor F).obj G).obj ((restrictTestAlgebra F K).obj R)).toGrpIso)
    (fun f => GrpCat.ext fun p => baseChangePointsNaturality F K G.X f p)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
private theorem pointsOnTestProduct {F I : Type u} [Field F] (X : SchemeOver F)
    (hX : IsAffine X.left)
    {T : I → TestAlgebra F} (P : Fan T) (hP : IsLimit P) :
    Function.Bijective (fun (x : Points X P.pt) i => mapPoints (P.proj i) x) := by
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  let C := A.unop
  let E := spectrumPoints C X e
  let t (R : TestAlgebra F) : (C ⟶ R) ≃ Points X R := (E.app R).toEquiv
  have ht {R S : TestAlgebra F} (f : R ⟶ S) (g : C ⟶ R) :
      t S (g ≫ f) = mapPoints f (t R g) := by
    have h := congrArg (fun (p : (C ⟶ R) ⟶ Points X S) => p.hom' g)
      (E.hom.naturality f)
    exact h
  constructor
  · intro x y h
    apply (t P.pt).symm.injective
    apply Fan.IsLimit.hom_ext hP
    intro i
    apply (t (T i)).injective
    rw [ht, ht, (t P.pt).apply_symm_apply, (t P.pt).apply_symm_apply]
    exact congrFun h i
  · intro x
    let y := Fan.IsLimit.lift hP (fun i => (t (T i)).symm (x i))
    refine ⟨t P.pt y, funext fun i => ?_⟩
    change mapPoints (P.proj i) (t P.pt y) = x i
    rw [← ht, show y ≫ P.proj i = (t (T i)).symm (x i) from Fan.IsLimit.fac hP _ i,
      Equiv.apply_symm_apply]

private theorem affineOfOverIso {F : Type u} [Field F] {X Y : SchemeOver F}
    (e : X ≅ Y) (h : IsAffine Y.left) :
    IsAffine X.left := by
  let := h
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  exact isAffine_of_isAffineHom e.hom.left

private theorem affineFiniteProduct {F I : Type u} [Field F] [Finite I]
    (X : I → SchemeOver F) (hX : ∀ i, IsAffine (X i).left) :
    IsAffine (∏ᶜ X).left := by
  classical
  cases nonempty_fintype I
  revert X
  refine Fintype.induction_empty_option
    (P := fun I [Fintype I] => ∀ (X : I → SchemeOver F),
      (∀ i, IsAffine (X i).left) → IsAffine (∏ᶜ X).left) ?_ ?_ ?_ I
  · intro α β _ e ih X hX
    have : Finite α := Finite.of_equiv β e.symm
    exact affineOfOverIso (Pi.reindex e X).symm (ih (X ∘ e) fun i => hX (e i))
  · intro X _
    let e : (∏ᶜ X) ≅ 𝟙_ (SchemeOver F) :=
      ⟨toUnit _, Pi.lift (fun i => PEmpty.elim i),
        Pi.hom_ext _ _ (fun i => PEmpty.elim i), toUnit_unique _ _⟩
    exact affineOfOverIso e (inferInstanceAs (IsAffine (Spec (CommRingCat.of F))))
  · intro α _ ih X hX
    let := hX none
    let := ih (fun i => X (some i)) fun i => hX (some i)
    exact affineOfOverIso (productOptionIso X) affine_tensor

private theorem affineGroupFiniteProduct {F I : Type u} [Field F] [Finite I]
    (X : I → Specs.GroupScheme F) (h : ∀ i, IsAffine (X i).X.left) :
    IsAffine (∏ᶜ X).X.left := by
  let U := Grp.forget (SchemeOver F)
  let p : Fan (fun i => (X i).X) := Fan.mk (∏ᶜ X).X (fun i => U.map (Pi.π X i))
  let hp : IsLimit p := (Fan.isLimitMapConeEquiv U X (Fan.mk _ (Pi.π X)))
    (isLimitOfPreserves U (limit.isLimit _))
  exact affineOfOverIso (hp.conePointUniqueUpToIso (limit.isLimit _)) (affineFiniteProduct _ h)

set_option backward.isDefEq.respectTransparency false in
private def orbitScalarProjection {F K : Type u} [Field F] [Field K] [Algebra F K]
    (L : IntermediateField F K) (a : L →ₐ[F] K) :
    letI : Algebra L K := a.toRingHom.toAlgebra
    restrictTestAlgebra F K ⋙ extendScalars F L ⟶ restrictTestAlgebra L K := by
  letI : Algebra L K := a.toRingHom.toAlgebra
  refine { app := orbitTestProjection L a, naturality := ?_ }
  intro R S f
  apply CommAlgCat.hom_ext
  apply DFunLike.ext
  intro x
  change (orbitTestProjection L a S).hom
    (Algebra.TensorProduct.map ((restrictTestAlgebra F K).map f).hom (AlgHom.id F L) x) =
      f.hom ((orbitTestProjection L a R).hom x)
  induction x using TensorProduct.inductionOn with
  | tmul r l =>
    rw [Algebra.TensorProduct.map_tmul]
    change f.hom r * algebraMap K S (a l) = f.hom (r * algebraMap K R (a l))
    rw [map_mul, f.hom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

private def orbitRestrictionProjection {F K : Type u} [Field F] [Field K] [Algebra F K]
    (L : IntermediateField F K) (a : L →ₐ[F] K)
    (W : Specs.GroupScheme F) (H : Specs.GroupScheme L)
    (e : (groupPointsFunctor F).obj W ≅ extendScalars F L ⋙ (groupPointsFunctor L).obj H) :
    (groupPointsFunctor K).obj ((groupBaseChange F K).obj W) ⟶
      (groupPointsFunctor K).obj (orbitBaseChangedGroup L a H) :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  let U := restrictTestAlgebra F K
  let V := (groupPointsFunctor L).obj H
  (groupBaseChangePointIso F K W).hom ≫ Functor.whiskerLeft U e.hom ≫
    (Functor.associator U (extendScalars F L) V).inv ≫
    Functor.whiskerRight (orbitScalarProjection L a) V ≫ (groupBaseChangePointIso L K H).inv

private theorem affineOrbitBaseChange {F K : Type u} [Field F] [Field K] [Algebra F K]
    (L : IntermediateField F K) (a : L →ₐ[F] K) (H : AffineAlgebraicGroup L) :
    IsAffine (orbitBaseChangedGroup L a H.val).X.left :=
  letI : Algebra L K := a.toRingHom.toAlgebra
  (Specs.Unipotent.baseChangedAlgebraicGroup K H).property.1

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 950000 in
theorem weilRestrictionBaseChangeProduct : WeilRestrictionBaseChangeProduct.{u} := by
  classical
  intro F K _ _ _ _ _ L W H e
  let I := L →ₐ[F] K
  let T (a : I) := orbitBaseChangedGroup L a H.val
  let G := (groupBaseChange F K).obj W.val
  let V := groupPointsFunctor K
  let n (a : I) := orbitRestrictionProjection L a W.val H.val e
  have hG : IsAffine G.X.left := (Specs.Unipotent.baseChangedAlgebraicGroup K W).property.1
  choose p hp using fun a : I => (groupHomComparison K G (T a) hG).surjective (n a)
  have hn (R : TestAlgebra K) :
      Function.Bijective (fun (x : (V.obj G).obj R) a => (n a).app R x) := by
    obtain ⟨hR⟩ := orbitTestAlgebraProduct L R
    let q := (groupBaseChangePointIso F K W.val).app R ≪≫ e.app ((restrictTestAlgebra F K).obj R)
    let z (a : I) : ((groupPointsFunctor L).obj H.val).obj (orbitTestAlgebra L a R) ≃*
        (V.obj (T a)).obj R :=
      letI : Algebra L K := a.toRingHom.toAlgebra
      ((groupBaseChangePointIso L K H.val).app R).symm.groupIsoToMulEquiv
    have h := (MulEquiv.piCongrRight z).bijective.comp
      ((pointsOnTestProduct H.val.X H.property.1 _ hR).comp q.groupIsoToMulEquiv.bijective)
    exact h
  let Y := ∏ᶜ T
  let f : G ⟶ Y := Pi.lift p
  have hY : IsAffine Y.X.left := affineGroupFiniteProduct T (fun a => affineOrbitBaseChange L a H)
  have hf (R : TestAlgebra K) : Function.Bijective ((V.map f).app R) := by
    let j := productPointsEquiv (Fan.mk Y (Pi.π T)) (limit.isLimit _) R
    have he : (fun (x : (V.obj G).obj R) a => (n a).app R x) = j ∘ ((V.map f).app R) := by
      funext x a
      change (n a).app R x = (V.map (Pi.π T a)).app R ((V.map f).app R x)
      rw [← hp a]
      have h := NatTrans.congr_app (congrArg V.map (Pi.lift_comp_π p a)) R
      rw [Functor.map_comp, NatTrans.comp_app] at h
      exact (ConcreteCategory.congr_hom h x).symm
    exact (Equiv.comp_bijective _ j.toEquiv).mp (he ▸ hn R)
  let (R : TestAlgebra K) : IsIso ((V.map f).app R) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hf R)
  let : IsIso (V.map f) := NatIso.isIso_of_isIso_app _
  obtain ⟨g, hg⟩ := (groupHomComparison K Y G hY).surjective (inv (V.map f))
  change V.map g = inv (V.map f) at hg
  have hfg : f ≫ g = 𝟙 G := (groupHomComparison K G G hG).injective (by
    change V.map (f ≫ g) = V.map (𝟙 G)
    rw [Functor.map_comp, hg, IsIso.hom_inv_id]
    exact (V.map_id G).symm)
  have hgf : g ≫ f = 𝟙 Y := (groupHomComparison K Y Y hY).injective (by
    change V.map (g ≫ f) = V.map (𝟙 Y)
    rw [Functor.map_comp, hg, IsIso.inv_hom_id]
    exact (V.map_id Y).symm)
  let j : G ≅ Y := ⟨f, g, hfg, hgf⟩
  let : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
  refine ⟨p, ⟨Fan.IsLimit.mk (Fan.mk G p) (fun s => Pi.lift s.proj ≫ j.inv) ?_ ?_⟩, ?_⟩
  · intro s a
    change (Pi.lift s.proj ≫ j.inv) ≫ p a = s.proj a
    rw [← Pi.lift_comp_π p a]
    change (Pi.lift s.proj ≫ j.inv) ≫ j.hom ≫ Pi.π T a = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Pi.lift_comp_π]
  · intro s m hm
    apply (cancel_mono j.hom).mp
    apply Pi.hom_ext
    intro a
    change m ≫ f ≫ Pi.π T a = (Pi.lift s.proj ≫ j.inv) ≫ j.hom ≫ Pi.π T a
    calc
      _ = s.proj a := by
        rw [show f ≫ Pi.π T a = p a from Pi.lift_comp_π p a]
        exact hm a
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc, Pi.lift_comp_π]
  · intro a R x
    let : Algebra L K := a.toRingHom.toAlgebra
    let j := (groupBaseChangePointIso L K H.val).app R
    let x₀ : (V.obj G).obj R := x
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (hp a) R) x₀
    change j.hom (((V.map (p a)).app R) x₀) = _
    rw [h]
    change j.hom (j.inv _) = _
    exact ConcreteCategory.congr_hom j.inv_hom_id _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
theorem weilRestrictionProjectionNaturality : WeilRestrictionProjectionNaturality.{u} := by
  intro F K _ _ _ L a V W S H f g e d p q hp hq h
  let : Algebra L K := a.toRingHom.toAlgebra
  let V' := (groupBaseChange F K).obj V.val
  let H' := orbitBaseChangedGroup L a H.val
  let f' := (groupBaseChange F K).map f
  let g' := (groupBaseChange L K).map g
  have hV : IsAffine V'.X.left := (Specs.Unipotent.baseChangedAlgebraicGroup K V).property.1
  apply (groupHomComparison K V' H' hV).injective
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  change (x ≫ (f' ≫ p).hom.hom) = (x ≫ (q ≫ g').hom.hom)
  apply (baseChangePoints L K H.val.X R).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  have hright := baseChangePointsSchemeNaturality L K g.hom.hom R (x ≫ q.hom.hom)
  change orbitBaseChangePoint L a H.val R ((x ≫ f'.hom.hom) ≫ p.hom.hom) =
    orbitBaseChangePoint L a H.val R ((x ≫ q.hom.hom) ≫ g'.hom.hom)
  rw [hp, show orbitBaseChangePoint L a H.val R ((x ≫ q.hom.hom) ≫ g'.hom.hom) =
    (orbitBaseChangePoint L a S.val R (x ≫ q.hom.hom)) ≫ g.hom.hom from hright, hq]
  rw [show baseChangePoint F K W.val.X R (x ≫ f'.hom.hom) =
    baseChangePoint F K V.val.X R x ≫ f.hom.hom from baseChangePointsSchemeNaturality F K f.hom.hom R x]
  let A := (restrictTestAlgebra F K).obj R
  let x₀ : ((groupPointsFunctor F).obj V.val).obj A := baseChangePoint F K V.val.X R x
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app h A) x₀
  let b := orbitTestProjection L a R
  let Y := (groupPointsFunctor L).obj H.val
  let Z := (groupPointsFunctor L).obj S.val
  let v := (groupPointsFunctor L).map g
  change e.hom.app A (x₀ ≫ f.hom.hom) = v.app _ (d.hom.app A x₀) at he
  change Y.map b (e.hom.app A (x₀ ≫ f.hom.hom)) =
    v.app _ (Z.map b (d.hom.app A x₀))
  rw [he]
  exact (ConcreteCategory.congr_hom (v.naturality b) (d.hom.app A x₀)).symm

end WeilProduct

open _root_.LinearAlgebraicGroups.Descent (SemilinearAction)
open WithConv
open private extendCoordinatePoint extendCoordinatePoint_injective extendCoordinatePoint_mul
  extendCoordinatePoint_equivariant exists_extendCoordinatePoint
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology

theorem descendedCoordinatePoints : DescendedCoordinatePoints.{u} := by
  intro F K _ _ _ _ A D H h R
  let := H.operations.toHopfAlgebra
  let s := SemilinearAction.scalarExtension (k := F) (K := K) D.fixed
  let t := SemilinearAction.scalarExtension (k := F) (K := K) R
  let i := H.comparison
  have hi (σ : Gal(K/F)) (x : K ⊗[F] D.fixed) :
      i (s.act σ x) = D.action.act σ (i x) := h σ x
  have hinv (σ : Gal(K/F)) (x : A) :
      i.symm (D.action.act σ x) = s.act σ (i.symm x) := by
    apply i.injective
    change i (i.symm (D.action.act σ x)) = i (s.act σ (i.symm x))
    rw [hi, i.apply_symm_apply, i.apply_symm_apply]
  let e (f : H.algebra →ₐ[F] R) :
      {g : A →ₐ[K] K ⊗[F] R // ∀ (σ : Gal(K/F)) x,
        g (D.action.act σ x) = t.act σ (g x)} :=
    ⟨(extendCoordinatePoint R f).comp i.symm.toAlgEquiv.toAlgHom, fun σ x => by
      change extendCoordinatePoint R f (i.symm (D.action.act σ x)) =
        t.act σ (extendCoordinatePoint R f (i.symm x))
      rw [hinv]
      exact extendCoordinatePoint_equivariant R f σ (i.symm x)⟩
  have he : Function.Bijective e := by
    constructor
    · intro f g hfg
      apply extendCoordinatePoint_injective (K := K) (A := H.algebra) R
      apply AlgHom.ext
      intro x
      have hfg' := DFunLike.congr_fun (congrArg Subtype.val hfg) (i x)
      change extendCoordinatePoint R f (i.symm (i x)) =
        extendCoordinatePoint R g (i.symm (i x)) at hfg'
      simpa only [i.symm_apply_apply] using hfg'
    · intro g
      let g₀ := g.val.comp i.toAlgEquiv.toAlgHom
      obtain ⟨f, hf⟩ := exists_extendCoordinatePoint (A := H.algebra) R g₀ fun σ x => by
        change g.val (i (s.act σ x)) = t.act σ (g.val (i x))
        rw [hi, g.property]
      refine ⟨f, Subtype.ext (AlgHom.ext fun x => ?_)⟩
      change extendCoordinatePoint R f (i.symm x) = g.val x
      rw [hf]
      exact congrArg g.val (i.apply_symm_apply x)
  refine ⟨Equiv.ofBijective e he, ?_, ?_⟩
  · intro f x
    change extendCoordinatePoint R f (i.symm (i (1 ⊗ₜ[F] x))) = _
    rw [i.symm_apply_apply]
    rfl
  · intro f g
    apply ofConv_injective
    change (extendCoordinatePoint R (f * g).ofConv).comp i.symm.toAlgEquiv.toAlgHom = _
    rw [extendCoordinatePoint_mul]
    exact AlgHom.convMul_comp_bialgHom_distrib _ _ i.symm.toBialgHom

section StabilizerDescent

open Specs.AdjointCocharacters (coordinateHopfMap)
open Specs.AdjointCocharacters renaming coordinateHopf -> affineCoordinateHopf
open _root_.LinearAlgebraicGroups.Descent (HopfDescentDatum HopfDescent descendHopf
  affineGroupDescentProperties)
open _root_.LinearAlgebraicGroups.Descent.Forms (scalarTowerIso)
open private standard standardAct transport twist aut_ext coefficientAction coefficientAction_apply
  baseHom_equivariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private inversePullback coordinateComparison coordinateComparison_equivariant
  coordinateComparison_natural extendedCoordinate_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
open private extendedCoordinateIso coordinateHopfMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private extendedHom_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private restrictHopfHom restrictHopfHom_base descendedMap_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private def standardOverIntermediate (L : IntermediateField F K) (P : HopfAlgebraCategory F) :
    HopfDescentDatum L (extendedHopf K P) :=
  transport (standard K (extendedHopf L P)) (scalarTowerIso P).symm

private theorem standardOverIntermediate_apply (L : IntermediateField F K) (P : HopfAlgebraCategory F)
    (σ : Gal(K/L)) (x : extendedHopf K P) :
    (standardOverIntermediate L P).action.act σ x = (standardAct K P).act (σ.restrictScalars F) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    let e := Algebra.TensorProduct.cancelBaseChange F L K K P
    change e ((standardAct K (extendedHopf L P)).act σ (e.symm (r ⊗ₜ[F] x))) =
      σ r ⊗ₜ[F] x
    rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    change e (σ r ⊗ₜ[L] ((1 : L) ⊗ₜ[F] x)) = _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [FiniteDimensional F K]

private def galoisToSubgroup (J : Subgroup Gal(K/F)) :
    Gal(K/(IntermediateField.fixedField J)) →* J :=
  let L := IntermediateField.fixedField J
  ((MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField J)).toMonoidHom).comp
    L.fixingSubgroupEquiv.symm.toMonoidHom

private def stabilizerDatum (J : Subgroup Gal(K/F)) {P : AffineAlgebraicGroup F} (a : J →* Aut P.val) :
    HopfDescentDatum (IntermediateField.fixedField J) (extendedHopf K (affineCoordinateHopf P)) := by
  let L := IntermediateField.fixedField J
  let R := standardOverIntermediate L (affineCoordinateHopf P)
  letI : TopologicalSpace (Aut (extendedHopf K (affineCoordinateHopf P))) := ⊥
  let b := (inversePullback (K := K)).comp (a.comp (galoisToSubgroup J))
  let c : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Cocycle (coefficientAction R) :=
    ⟨b, continuous_of_discreteTopology, by
      intro σ τ
      rw [map_mul]
      congr 1
      apply aut_ext
      intro x
      obtain ⟨y, rfl⟩ := (R.action.act σ).surjective x
      rw [coefficientAction_apply]
      change (b τ).asIso.hom.hom (R.action.act σ y) =
        R.action.act σ ((b τ).asIso.hom.hom y)
      rw [standardOverIntermediate_apply, standardOverIntermediate_apply]
      exact baseHom_equivariant (K := K)
        (coordinateHopfMap (G := P) (H := P) (a (galoisToSubgroup J τ)).asIso.inv)
        (σ.restrictScalars F) y⟩
  exact twist R c

private theorem stabilizerDatum_apply (J : Subgroup Gal(K/F)) {P : AffineAlgebraicGroup F}
    (a : J →* Aut P.val) (σ : Gal(K/(IntermediateField.fixedField J)))
    (x : extendedHopf K (affineCoordinateHopf P)) :
    (stabilizerDatum J a).action.act σ x =
      (extendedHopfMap K (coordinateHopfMap (G := P) (H := P)
        (a (galoisToSubgroup J σ)).asIso.inv)).hom ((standardAct K (affineCoordinateHopf P)).act
          (σ.restrictScalars F) x) := by
  exact congrArg _ (standardOverIntermediate_apply (IntermediateField.fixedField J) (affineCoordinateHopf P) σ x)

omit [FiniteDimensional F K] in
private theorem locallyOfFiniteType_extendedCoordinate (P : AffineAlgebraicGroup F) :
    LocallyOfFiniteType (specGroup (extendedHopf K (affineCoordinateHopf P))).X.hom := by
  let U := Grp.forget (SchemeOver K)
  let e := U.mapIso (extendedCoordinateIso (K := K) P)
  change LocallyOfFiniteType (U.obj (specGroup (extendedHopf K (affineCoordinateHopf P)))).hom
  rw [← Over.w e.hom]
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  let : IsOpenImmersion e.hom.left := inferInstance
  have hbase : LocallyOfFiniteType ((groupBaseChange F K).obj P.val).X.hom :=
    (Specs.Unipotent.baseChangedAlgebraicGroup K P).property.2.1
  change LocallyOfFiniteType (e.hom.left ≫ ((groupBaseChange F K).obj P.val).X.hom)
  exact @locallyOfFiniteType_comp _ _ _ e.hom.left _
    (locallyOfFiniteType_of_isOpenImmersion _) hbase

private def affineGroupOfStabilizerDescent {J : Subgroup Gal(K/F)} {P : AffineAlgebraicGroup F}
    {a : J →* Aut P.val} (H : HopfDescent (stabilizerDatum J a)) :
    AffineAlgebraicGroup (IntermediateField.fixedField J) :=
  ⟨specGroup H.algebra, by change IsAffine (Spec (CommRingCat.of H.algebra)); infer_instance,
    (affineGroupDescentProperties H).1 (locallyOfFiniteType_extendedCoordinate P)⟩

private theorem stabilizerDatum_equivariant (J : Subgroup Gal(K/F)) {P Q : AffineAlgebraicGroup F}
    (a : J →* Aut P.val) (b : J →* Aut Q.val) (j : Q.val ⟶ P.val)
    (h : ∀ σ : J, j ≫ (a σ).asIso.inv = (b σ).asIso.inv ≫ j) :
    (stabilizerDatum J a).Equivariant (stabilizerDatum J b)
      (extendedHopfMap K (coordinateHopfMap (G := Q) (H := P) j)) := by
  intro σ x
  let s := galoisToSubgroup J σ
  let j' := extendedHopfMap K (coordinateHopfMap (G := Q) (H := P) j)
  let α := extendedHopfMap K (coordinateHopfMap (G := P) (H := P) (a s).asIso.inv)
  let β := extendedHopfMap K (coordinateHopfMap (G := Q) (H := Q) (b s).asIso.inv)
  have hcomm : α ≫ j' = j' ≫ β := by
    dsimp only [α, β, j']
    rw [← extendedHom_comp, ← extendedHom_comp, ← coordinateHopfMap_comp,
      ← coordinateHopfMap_comp, h s]
  change j'.hom ((stabilizerDatum J a).action.act σ x) =
    (stabilizerDatum J b).action.act σ (j'.hom x)
  rw [stabilizerDatum_apply, stabilizerDatum_apply]
  change j'.hom (α.hom ((standardAct K (affineCoordinateHopf P)).act (σ.restrictScalars F) x)) =
    β.hom ((standardAct K (affineCoordinateHopf Q)).act (σ.restrictScalars F) (j'.hom x))
  have he := baseHom_equivariant (K := K)
    (coordinateHopfMap (G := Q) (H := P) j) (σ.restrictScalars F) x
  change j'.hom ((standardAct K (affineCoordinateHopf P)).act (σ.restrictScalars F) x) =
    (standardAct K (affineCoordinateHopf Q)).act (σ.restrictScalars F) (j'.hom x) at he
  rw [← he]
  exact ConcreteCategory.congr_hom hcomm _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem stabilizerSubgroupsDescent : StabilizerSubgroupsDescent.{u} := by
  intro F K _ _ _ _ _ J P a
  let L := IntermediateField.fixedField J
  have : IsGalois L K := IsGalois.tower_top_intermediateField L
  let D := stabilizerDatum (K := K) J a
  let H := descendHopf D
  let G := affineGroupOfStabilizerDescent H
  let e : specGroup H.algebra ≅ G.val := Iso.refl _
  let i := coordinateComparison H e
  refine ⟨G, i, ?_, ?_⟩
  · intro σ x
    exact (coordinateComparison_equivariant H e σ x).trans
      (congrArg i.hom.hom (stabilizerDatum_apply J a σ x))
  · intro S b h
    let Q := closedSubgroupAlgebraicGroup S
    let E := stabilizerDatum (P := Q) J b
    let M := descendHopf E
    let f := extendedHopfMap K (coordinateHopfMap (G := Q) (H := P) S.inclusion)
    let hf := stabilizerDatum_equivariant J (P := P) (Q := Q) a b S.inclusion h
    let g := restrictHopfHom H M f hf
    have hg : Function.Surjective g.hom :=
      descendedMap_surjective H M f hf (extendedCoordinate_surjective (K := K)
        (G := Q) (H := P) S.inclusion S.isClosedImmersion)
    let V : Specs.ClosedSubgroup G.val :=
      ⟨specGroup M.algebra, specGroupMap g, (hopfMapClosedImmersion L g).mpr hg⟩
    let d : specGroup M.algebra ≅ (closedSubgroupAlgebraicGroup V).val := Iso.refl _
    let j := coordinateComparison M d
    refine ⟨V, j, ?_, ?_⟩
    · intro σ x
      exact (coordinateComparison_equivariant M d σ x).trans
        (congrArg j.hom.hom (stabilizerDatum_apply J (P := Q) b σ x))
    · exact coordinateComparison_natural H M e d V.inclusion g (by
        change specGroupMap g ≫ 𝟙 _ = 𝟙 _ ≫ specGroupMap g
        simp) f (restrictHopfHom_base H M f hf)

theorem stabilizerGroupDescent : StabilizerGroupDescent.{u} := by
  intro F K _ _ _ _ _ J P a
  obtain ⟨H, i, hi, _⟩ := stabilizerSubgroupsDescent J P a
  exact ⟨H, i, hi⟩

end StabilizerDescent

section MarkedComparison

open Specs.AdjointCocharacters (coordinateHopfIso coordinateHopfMap)
open Specs.AdjointCocharacters renaming coordinateHopf -> affineCoordinateHopf
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Descent.Forms (spectrumIso)
open private extendedCoordinateIso extendedCoordinateIso_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private extendedGroupIso extendedSpecIso_hom_fst specGroupMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem inverseIsoSquare {C : Type*} [Category C] {X Y Z W : C}
    (a : X ≅ Y) (b : Z ≅ W) (f : X ⟶ Z) (g : Y ⟶ W)
    (h : f ≫ b.hom = a.hom ≫ g) :
    g ≫ b.inv = a.inv ≫ f := by
  calc
    g ≫ b.inv = a.inv ≫ (a.hom ≫ g) ≫ b.inv := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = a.inv ≫ f := by rw [← h, Category.assoc f, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
theorem markedComparisonOfHopf : MarkedComparisonOfHopf.{u} := by
  intro F E K _ _ _ _ _ G H M N i d hd
  let comparison (X : AffineAlgebraicGroup F) (Y : AffineAlgebraicGroup E)
      (e : extendedHopf K (affineCoordinateHopf X) ≅ extendedHopf K (affineCoordinateHopf Y)) :
      (groupBaseChange F K).obj X.val ≅ (groupBaseChange E K).obj Y.val :=
    (extendedCoordinateIso (K := K) X).symm ≪≫ spectrumIso e ≪≫
      extendedCoordinateIso (K := K) Y
  have hcomm (m : Marking) :
      (groupBaseChange F K).map (M.subgroup m).inclusion ≫ (comparison G H i).hom =
        (comparison (closedSubgroupAlgebraicGroup (M.subgroup m))
          (closedSubgroupAlgebraicGroup (N.subgroup m)) (d m)).hom ≫
          (groupBaseChange E K).map (N.subgroup m).inclusion := by
    let X := closedSubgroupAlgebraicGroup (M.subgroup m)
    let Y := closedSubgroupAlgebraicGroup (N.subgroup m)
    let f := (M.subgroup m).inclusion
    let g := (N.subgroup m).inclusion
    let p := extendedHopfMap K (coordinateHopfMap (G := X) (H := G) f)
    let q := extendedHopfMap K (coordinateHopfMap (G := Y) (H := H) g)
    let a := extendedCoordinateIso (K := K) X
    let b := extendedCoordinateIso (K := K) G
    let c := extendedCoordinateIso (K := K) Y
    let e := extendedCoordinateIso (K := K) H
    have h₀ : i.hom ≫ q = p ≫ (d m).hom := hd m
    have h₁ : i.inv ≫ p = q ≫ (d m).inv := by
      apply (cancel_epi i.hom).mp
      rw [Iso.hom_inv_id_assoc, ← Category.assoc, h₀, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    have h₂ : specGroupMap p ≫ (spectrumIso i).hom =
        (spectrumIso (d m)).hom ≫ specGroupMap q := by
      change specGroupMap p ≫ specGroupMap i.inv =
        specGroupMap (d m).inv ≫ specGroupMap q
      rw [← specGroupMap_comp, ← specGroupMap_comp, h₁]
    have ha : (groupBaseChange F K).map f ≫ b.inv = a.inv ≫ specGroupMap p :=
      inverseIsoSquare a b (specGroupMap p) ((groupBaseChange F K).map f)
        (extendedCoordinateIso_natural (G := X) (H := G) (K := K) f)
    have hb : c.hom ≫ (groupBaseChange E K).map g = specGroupMap q ≫ e.hom :=
      (extendedCoordinateIso_natural (G := Y) (H := H) (K := K) g).symm
    change (groupBaseChange F K).map f ≫ b.inv ≫ (spectrumIso i).hom ≫ e.hom =
      (a.inv ≫ (spectrumIso (d m)).hom ≫ c.hom) ≫ (groupBaseChange E K).map g
    calc
      _ = a.inv ≫ (specGroupMap p ≫ (spectrumIso i).hom) ≫ e.hom := by
        rw [← Category.assoc ((groupBaseChange F K).map f), ha]
        simp only [Category.assoc]
      _ = _ := by rw [h₂]; simp only [Category.assoc, hb]
  let j : MarkedComparison (K := K) M N :=
    ⟨comparison G H i, fun m => comparison (closedSubgroupAlgebraicGroup (M.subgroup m))
      (closedSubgroupAlgebraicGroup (N.subgroup m)) (d m), hcomm⟩
  exact ⟨j, extendedGroupIso K, extendedGroupIso K,
    extendedSpecIso_hom_fst (k := F) K, extendedSpecIso_hom_fst (k := E) K, by
      change (extendedCoordinateIso (K := K) G).symm ≪≫ spectrumIso i ≪≫
          extendedCoordinateIso (K := K) H = _
      simp only [extendedCoordinateIso, Iso.trans_symm, Iso.trans_assoc]⟩

end MarkedComparison


theorem transitiveComponentPoints : TransitiveComponentPoints.{u,v} := by
  classical
  intro Γ I A _ _ _ transport i horbit hcomp
  let eval : equivariantFamilies transport →* componentFixedPoints transport i :=
    { toFun := fun x => ⟨x.val i, fun g hg => by
        have h := x.property g i
        rwa [hg] at h⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  choose r hr using horbit
  have hequal (a : componentFixedPoints transport i) (g h : Γ) (he : g • i = h • i) :
      transport g i a.val = transport h i a.val := by
    have hstab : (h⁻¹ * g) • i = i := by
      rw [mul_smul, he, inv_smul_smul]
    have hc := congrArg (fun f : MulAut A => f a.val) (hcomp h (h⁻¹ * g) i)
    simpa [mul_assoc, hstab, MulAut.mul_apply, a.property _ hstab] using hc
  have hinj : Function.Injective eval := by
    intro x y hxy
    have hv : x.val i = y.val i := congrArg Subtype.val hxy
    apply Subtype.ext
    funext j
    rw [← hr j, ← x.property, ← y.property, hv]
  have hsurj : Function.Surjective eval := by
    intro a
    let x : I → A := fun j => transport (r j) i a.val
    have hx : x ∈ equivariantFamilies transport := by
      intro g j
      change transport g j (transport (r j) i a.val) = transport (r (g • j)) i a.val
      have hc := congrArg (fun f : MulAut A => f a.val) (hcomp g (r j) i)
      rw [MulAut.mul_apply, hr j] at hc
      rw [← hc]
      apply hequal
      simp only [mul_smul, hr]
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    change transport (r i) i a.val = a.val
    exact a.property _ (hr i)
  let e := MulEquiv.ofBijective eval ⟨hinj, hsurj⟩
  refine ⟨e, fun _ => rfl, ?_⟩
  intro U hU x
  change (∀ j, x.val j ∈ U j) ↔ x.val i ∈ U i
  refine ⟨fun hx => hx i, fun hx j => ?_⟩
  have hm := hU (r j) i (show transport (r j) i (x.val i) ∈
    Subgroup.map (transport (r j) i).toMonoidHom (U i) from ⟨_, hx, rfl⟩)
  rwa [show transport (r j) i (x.val i) = x.val j from
    (x.property (r j) i).trans (congrArg x.val (hr j)), hr j] at hm

section SplitComponents

open Specs.Unipotent (closedSubgroupAlgebraicGroup)

open Specs.Pinning (PinnedGroup PinnedIso)
open Specs.RootGroups (AdditiveLine)
open Specs.GeometricRadicals (IsReductive IsSplitTorus IsSemisimple IsUnipotentRadical)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.BorelsAndChambers (subgroupRoots)
open Specs.CharacterPairing (absoluteRoots)
open Specs.OpenCell (AreOpposite)

open private no_common_root opposite_positive_system
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOppositeBorelUniqueness
open private commonTorus_le_borel compareUnipotentRadicals
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
open private markedPinnedProductForFactors positiveBorelProjections
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct
open private inclusion_mono from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts

variable {F : Type u} [Field F]

/-- For the specified split torus, the scheme intersection condition
gives complementary positive systems. -/
private theorem rootsOfOppositeBorels {G : AffineAlgebraicGroup F}
    (hG : IsReductive G) (M : BorelPair G) (hT : IsSplitTorus M.torus.group) :
    AreOpposite M.torus M.positive M.negative := by
  obtain ⟨_, _, _, corr, _, _⟩ :=
    RootData.BorelPositivity.borelPositivity G hG M.torus hT M.maximal
  have hB := commonTorus_le_borel M (show M.positive ∈ {M.positive, M.negative} by simp)
  have hC := commonTorus_le_borel M (show M.negative ∈ {M.positive, M.negative} by simp)
  have posB := corr.1 M.positive M.positiveBorel hB
  have posC := corr.1 M.negative M.negativeBorel hC
  apply Set.ext
  intro α
  change α ∈ subgroupRoots M.torus M.negative ↔ α ∉ subgroupRoots M.torus M.positive
  have hroot := (RootData.RootGroups.rootSubgroups G hG M.torus hT M.maximal).2 α.val α.property
  let β : ↥(absoluteRoots M.torus) := ⟨α.val⁻¹, ((hroot.2.1 _).mpr (Or.inr rfl)).1⟩
  constructor
  · intro hn hp
    exact no_common_root G hG M.torus M.positive M.negative hT M.maximal M.intersection α hp hn
  · intro hp
    by_contra hn
    exact no_common_root G hG M.torus M.positive M.negative hT M.maximal M.intersection β
      ((opposite_positive_system posB (β := β) rfl).mpr hp)
      ((opposite_positive_system posC (β := β) rfl).mpr hn)

private def splitProductPair {G : AffineAlgebraicGroup F} (M : BorelPair G)
    (hG : IsReductive G) (hT : IsSplitTorus M.torus.group) :
    Specs.QuasiSplitPinnedProduct.BorelPair G where
  positive := M.positive
  negative := M.negative
  torus := M.torus
  positiveRadical := M.positiveRadical
  negativeRadical := M.negativeRadical
  positiveBorel := M.positiveBorel
  negativeBorel := M.negativeBorel
  isTorus := M.isTorus
  maximal := M.maximal
  torusInPositive := commonTorus_le_borel M (by simp)
  torusInNegative := commonTorus_le_borel M (by simp)
  opposite := rootsOfOppositeBorels hG M hT
  positiveUnipotentRadical := M.positiveUnipotentRadical
  negativeUnipotentRadical := M.negativeUnipotentRadical

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
private theorem pinnedMarkedTransport {A : AdditiveLine F} {P Q : PinnedGroup A}
    (e : PinnedIso P Q) (S : BorelPair P.pair.G) (N : BorelPair Q.pair.G)
    (hSB : S.positive = P.pair.B) (hST : S.torus = P.pair.T)
    (hNB : N.positive = Q.pair.B) (hNT : N.torus = Q.pair.T) :
    ∃ f : ∀ m, (S.subgroup m).group ≅ (N.subgroup m).group,
      ∀ m, (S.subgroup m).inclusion ≫ e.group.hom = (f m).hom ≫ (N.subgroup m).inclusion := by
  have hB : ∃ b : S.positive.group ≅ N.positive.group,
      S.positive.inclusion ≫ e.group.hom = b.hom ≫ N.positive.inclusion := by
    rw [hSB, hNB]
    exact ⟨e.borel, e.borel_comm⟩
  have hT : ∃ t : S.torus.group ≅ N.torus.group,
      S.torus.inclusion ≫ e.group.hom = t.hom ≫ N.torus.inclusion := by
    rw [hST, hNT]
    exact ⟨e.torus, e.torus_comm⟩
  obtain ⟨b, hb⟩ := hB
  obtain ⟨t, ht⟩ := hT
  have hs : IsSplitTorus S.torus.group := hST.symm ▸ P.pair.split
  have hn : IsSplitTorus N.torus.group := hNT.symm ▸ Q.pair.split
  obtain ⟨c, hc, _⟩ := QuasiSplitOppositeBorelUniqueness.oppositeUniqueness
    P.pair.reductive Q.pair.reductive S.torus S.positive S.negative N.torus N.positive N.negative
    hs hn S.maximal N.maximal S.positiveBorel S.negativeBorel N.positiveBorel N.negativeBorel
    S.intersection N.intersection e.group t b ht hb
  obtain ⟨u, hu⟩ := compareUnipotentRadicals
    (G := closedSubgroupAlgebraicGroup S.positive) (H := closedSubgroupAlgebraicGroup N.positive)
    b S.positiveUnipotentRadical N.positiveUnipotentRadical
  obtain ⟨v, hv⟩ := compareUnipotentRadicals
    (G := closedSubgroupAlgebraicGroup S.negative) (H := closedSubgroupAlgebraicGroup N.negative)
    c S.negativeUnipotentRadical N.negativeUnipotentRadical
  let j : ∀ m, (S.subgroup m).group ≅ (N.subgroup m).group
    | .positive => b
    | .negative => c
    | .torus => t
    | .positiveRadical => u
    | .negativeRadical => v
  refine ⟨j, fun m => ?_⟩
  cases m
  · exact hb
  · exact hc
  · exact ht
  · change (S.positiveRadical.inclusion ≫ S.positive.inclusion) ≫ e.group.hom =
      u.hom ≫ N.positiveRadical.inclusion ≫ N.positive.inclusion
    rw [Category.assoc, hb, ← Category.assoc, hu, Category.assoc]
  · change (S.negativeRadical.inclusion ≫ S.negative.inclusion) ≫ e.group.hom =
      v.hom ≫ N.negativeRadical.inclusion ≫ N.negative.inclusion
    rw [Category.assoc, hc, ← Category.assoc, hv, Category.assoc]


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1750000 in
private theorem splitComponentsExist {A : AdditiveLine F} (P : PinnedGroup A)
    (D : AttachedDatum P.pair) (S : BorelPair P.pair.G)
    (hB : S.positive = P.pair.B) (hT : S.torus = P.pair.T) (hD : corootLattice D = ⊤) :
    Nonempty (SplitComponents D S) := by
  classical
  let C := Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased
  letI : Finite C := Quotient.finite _
  obtain ⟨W⟩ := QuasiSplitPinnedProduct.pinnedFactorsExist D hD
  choose N hN using fun c : C => QuasiSplitPinnedPairModel.splitOppositePair (W.factor c)
  let M := splitProductPair S P.pair.reductive (hT.symm ▸ P.pair.split)
  let J (c : C) := splitProductPair (N c) (W.factor c).pair.reductive
    ((hN c).2.symm ▸ (W.factor c).pair.split)
  have hJ (c : C) : (J c).positive = (W.factor c).pair.B := (hN c).1
  have hJT (c : C) : (J c).torus = (W.factor c).pair.T := (hN c).2
  have hsimp := QuasiSplitPinnedProduct.pinnedFactorsAbsolutelyAlmostSimple W
  cases isEmpty_or_nonempty C with
  | inl hn =>
    obtain ⟨d⟩ := emptyMarkedSplitProduct P.pair D S hD
      ⟨fun i => isEmptyElim (component (A := integralCartan D.toBased.datum D.toBased.base) i)⟩ N
    exact ⟨⟨W, N, fun c => (hN c).1, fun c => (hN c).2, hsimp, d,
      isEmptyElim, fun c => isEmptyElim c, fun c => isEmptyElim c,
      fun _ c => isEmptyElim c, fun _ c => isEmptyElim c,
      fun _ _ _ => ⟨Equiv.refl _, isEmptyElim,
        fun i => isEmptyElim (component (A := integralCartan D.toBased.datum D.toBased.base) i),
        fun c => isEmptyElim c⟩⟩⟩
  | inr hn =>
    obtain ⟨B, t, hs, ht, hpin, hoff⟩ :=
      markedPinnedProductForFactors W M J hB hT hJ hJT hn hD
    obtain ⟨b, hb, ⟨lb⟩⟩ := positiveBorelProjections W B hB hJ
    let d : MarkedProduct S N :=
      { projection := B.projection
        subgroupProjection := fun m i => by
          cases m with
          | positive => exact B.subgroupProjection .positive i
          | negative => exact B.subgroupProjection .negative i
          | torus => exact B.subgroupProjection .torus i
          | positiveRadical => exact B.subgroupProjection .positiveRadical i
          | negativeRadical => exact B.subgroupProjection .negativeRadical i
        commutes := fun m i => by
          cases m with
          | positive => exact B.commutes .positive i
          | negative => exact B.commutes .negative i
          | torus => exact B.commutes .torus i
          | positiveRadical => exact B.commutes .positiveRadical i
          | negativeRadical => exact B.commutes .negativeRadical i
        product := B.product
        subgroupProduct := fun m => by
          cases m with
          | positive => exact B.subgroupProduct .positive
          | negative => exact B.subgroupProduct .negative
          | torus => exact B.subgroupProduct .torus
          | positiveRadical => exact B.subgroupProduct .positiveRadical
          | negativeRadical => exact B.subgroupProduct .negativeRadical }
    refine ⟨⟨W, N, fun c => (hN c).1, fun c => (hN c).2, hsimp, d,
      t, hs, ht, hpin, hoff, ?_⟩⟩
    intro a f hf
    obtain ⟨g, e, hg, he, _⟩ := QuasiSplitPinnedProduct.productProjectionEquivariance
      W B.projection b t B.product lb hb hs ht hpin hoff a f hf
    exact ⟨g, e, hg, he⟩

set_option backward.isDefEq.respectTransparency false in
private theorem splitComponentsTransport {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {S : BorelPair P.pair.G} (W : SplitComponents D S)
    {Γ : Type u} [Group Γ] (ω : Γ →* Aut D.toBased) (lift : Aut D.toBased ≃* Aut P)
    (hl : ∀ a, Specs.QuasiSplitPinnedProduct.LiftsBasedAutomorphism D a (lift a).asIso.hom)
    [MulAction Γ (Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased)]
    (hρ : ∀ (σ : Γ) (i : D.toBased.base.support),
      σ • component (A := integralCartan D.toBased.datum D.toBased.base) i =
        component (A := integralCartan D.toBased.datum D.toBased.base)
          (simplePermutation D.toBased (ω σ) i)) :
    ∃ e : ∀ σ c, PinnedIso (W.factors.factor c) (W.factors.factor (σ • c)),
      ∀ σ c, (lift (ω σ)).asIso.hom.group.hom ≫ W.product.projection (σ • c) =
        W.product.projection c ≫ (e σ c).group.hom := by
  choose a e ha he using fun σ : Γ =>
    W.equivariance (ω σ) (lift (ω σ)).asIso.hom (hl (ω σ))
  have h (σ : Γ) (c : Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased) :
      a σ c = σ • c := by
    induction c using Quotient.inductionOn with
    | h i => exact (ha σ i).trans (hρ σ i).symm
  have transport (σ : Γ) c (j) (hj : a σ c = j) :
      ∃ t : PinnedIso (W.factors.factor c) (W.factors.factor j),
        (lift (ω σ)).asIso.hom.group.hom ≫ W.product.projection j =
          W.product.projection c ≫ t.group.hom := by
    subst j
    exact ⟨e σ c, he σ c⟩
  choose t ht using fun σ c => transport σ c _ (h σ c)
  exact ⟨t, ht⟩

end SplitComponents

section CoordinateProducts

open Specs.QuasiSplitInducedWeilProduct
  (IsCoordinateProduct ProductInclusion)
open Specs.AdjointCocharacters (coordinateHopfMap coordinateHopfIso)
open Specs.AdjointCocharacters renaming coordinateHopf -> affineCoordinateHopf
open Opposite
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open WeilRestriction (spectrumPoints)
open _root_.LinearAlgebraicGroups.Descent (HopfDescentDatum SemilinearAction)
open private spectrumPoints_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
open private extendedCoordinateIso extendedCoordinateIso_natural coordinateHopfMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private coordinatePresentationMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
open private specGroupMap_comp specGroupMap_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private standard standardAct transport inv_apply extendedIso extendedHom_comp baseHom_equivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private extendedCoordinate_surjective coordinateMap_id from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]

private abbrev extendedCoordinate (G : AffineAlgebraicGroup F) :=
  extendedHopf K (affineCoordinateHopf G)

private abbrev extendedPullback {G H : AffineAlgebraicGroup F} (f : G.val ⟶ H.val) :
    extendedCoordinate (K := K) H ⟶ extendedCoordinate (K := K) G :=
  extendedHopfMap K (coordinateHopfMap f)

private def affineSpec {k : Type u} [Field k] (A : HopfAlgebraCategory k)
    (hA : Algebra.FiniteType k A) : AffineAlgebraicGroup k :=
  _root_.LinearAlgebraicGroups.Descent.Forms.schemeModel A hA

private def hopfPointEquiv {k : Type u} [Field k] (A : HopfAlgebraCategory k) (R : TestAlgebra k) :
    (A →ₐ[k] R) ≃ Points (specGroup A).X R :=
  ({ toFun := fun f => ConcreteCategory.ofHom (C := CommAlgCat k) f
     invFun := fun f => f.hom
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } : (A →ₐ[k] R) ≃ (CommAlgCat.of k A ⟶ R)).trans
    ((spectrumPoints (CommAlgCat.of k A) (specGroup A).X (Iso.refl _)).app R).toEquiv

private theorem hopfPointEquiv_natural {k : Type u} [Field k]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B) (R : TestAlgebra k) (x : B →ₐ[k] R) :
    hopfPointEquiv A R (x.comp f.hom.toAlgHom) =
      hopfPointEquiv B R x ≫ (specGroupMap f).hom.hom := by
  apply Over.OverMorphism.ext
  let a : CommAlgCat.of k A ⟶ R := ConcreteCategory.ofHom (x.comp f.hom.toAlgHom)
  let b : CommAlgCat.of k B ⟶ R := ConcreteCategory.ofHom x
  exact (spectrumPoints_apply (CommAlgCat.of k A) R a).trans
    ((Spec.map_comp (CommRingCat.ofHom f.hom.toAlgHom.toRingHom) (CommRingCat.ofHom x.toRingHom)).trans
      (congrArg (fun w => w ≫ (specGroupMap f).hom.hom.left)
        (spectrumPoints_apply (CommAlgCat.of k B) R b).symm))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
private theorem coordinateProductOfFan [Finite I] {G : AffineAlgebraicGroup F}
    {H : I → AffineAlgebraicGroup F} (p : ∀ i, G.val ⟶ (H i).val)
    (hp : IsLimit (Fan.mk G.val p)) :
    IsCoordinateProduct (fun i => extendedPullback (K := K) (G := G) (H := H i) (p i)) := by
  intro R
  let U := (restrictTestAlgebra F K).obj R
  let E (G : AffineAlgebraicGroup F) : (extendedCoordinate (K := K) G →ₐ[K] R) ≃
      Points G.val.X U :=
    (hopfPointEquiv (extendedCoordinate G) R).trans
      (((groupPointsFunctor K).mapIso (extendedCoordinateIso (K := K) G)).app R).groupIsoToMulEquiv.toEquiv |>.trans
      (Equiv.ofBijective (baseChangePoint F K G.val.X R) (baseChangePoints F K G.val.X R))
  let e := productPointsEquiv (Fan.mk G.val p) hp U
  let q (x : extendedCoordinate (K := K) G →ₐ[K] R) i :=
    x.comp (extendedPullback (G := G) (H := H i) (p i)).hom.toAlgHom
  have hq (x : extendedCoordinate (K := K) G →ₐ[K] R) (i : I) :
      E (H i) (q x i) = e (E G x) i := by
    let f := extendedPullback (K := K) (G := G) (H := H i) (p i)
    let z := hopfPointEquiv (extendedCoordinate (K := K) G) R x
    let F₁ := groupBaseChange F K
    let eG := extendedCoordinateIso (K := K) G
    let eH := extendedCoordinateIso (K := K) (H i)
    change baseChangePoint F K (H i).val.X R
      (hopfPointEquiv (extendedCoordinate (K := K) (H i)) R (x.comp f.hom.toAlgHom) ≫ eH.hom.hom.hom) =
      baseChangePoint F K G.val.X R (z ≫ eG.hom.hom.hom) ≫ (p i).hom.hom
    rw [hopfPointEquiv_natural]
    have h := congrArg (fun m : specGroup (extendedCoordinate (K := K) G) ⟶
        (F₁.obj (H i).val) => m.hom.hom)
      (extendedCoordinateIso_natural (K := K) (G := G) (H := H i) (p i))
    change (specGroupMap f).hom.hom ≫ eH.hom.hom.hom =
      eG.hom.hom.hom ≫ (F₁.map (p i)).hom.hom at h
    rw [Category.assoc, h, ← Category.assoc]
    exact baseChangePointsSchemeNaturality F K (p i).hom.hom R _
  let t := Equiv.piCongrRight (fun i => E (H i))
  have h : t ∘ q = e.toEquiv ∘ E G := funext fun x => funext (hq x)
  exact (Equiv.comp_bijective _ t).mp (h ▸ e.toEquiv.bijective.comp (E G).bijective)

private theorem extendedCoordinate_finiteType (G : AffineAlgebraicGroup F) :
    Algebra.FiniteType K (extendedCoordinate (K := K) G) :=
  (hopfSpec_locallyOfFiniteType_iff K _).mp (locallyOfFiniteType_extendedCoordinate (K := K) G)

private theorem pullback_comp {G H J : AffineAlgebraicGroup F}
    (f : G.val ⟶ H.val) (g : H.val ⟶ J.val) :
    extendedPullback (K := K) (G := G) (H := J) (f ≫ g) =
      extendedPullback (K := K) (G := H) (H := J) g ≫ extendedPullback (K := K) (G := G) (H := H) f := by
  change extendedHopfMap K (coordinateHopfMap _) = _
  rw [coordinateHopfMap_comp, extendedHom_comp]

private def semilinearFactorTransport {G H : AffineAlgebraicGroup F}
    (σ : Gal(K/F)) (e : G.val ≅ H.val) :
    extendedCoordinate (K := K) G ≃+* extendedCoordinate (K := K) H :=
  let i : affineCoordinateHopf G ≅ affineCoordinateHopf H :=
    { hom := coordinateHopfMap e.inv
      inv := coordinateHopfMap e.hom
      hom_inv_id := by
        rw [← coordinateHopfMap_comp, e.hom_inv_id, coordinateMap_id]
      inv_hom_id := by
        rw [← coordinateHopfMap_comp, e.inv_hom_id, coordinateMap_id] }
  let A := standard K (affineCoordinateHopf G)
  let a : extendedCoordinate (K := K) G ≃+* extendedCoordinate (K := K) G :=
    { A.action.act σ with
      map_mul' := A.map_mul σ }
  a.trans (CommHopfAlgCat.ofIso (extendedIso K i)).toAlgEquiv.toRingEquiv

private theorem semilinearFactorTransport_apply {G H : AffineAlgebraicGroup F}
    (σ : Gal(K/F)) (e : G.val ≅ H.val) (x : extendedCoordinate (K := K) G) :
    semilinearFactorTransport σ e x = (extendedPullback (G := H) (H := G) e.inv).hom
      ((standardAct K (affineCoordinateHopf G)).act σ x) := rfl

private theorem semilinearFactorTransport_scalar {G H : AffineAlgebraicGroup F}
    (σ : Gal(K/F)) (e : G.val ≅ H.val) (r : K) :
    semilinearFactorTransport σ e (algebraMap K (extendedCoordinate (K := K) G) r) =
      algebraMap K (extendedCoordinate (K := K) H) (σ r) := by
  rw [semilinearFactorTransport_apply, Algebra.TensorProduct.algebraMap_apply]
  change (extendedPullback (K := K) (G := H) (H := G) e.inv).hom
    (σ r ⊗ₜ[F] (1 : affineCoordinateHopf G)) = _
  exact (extendedPullback (K := K) (G := H) (H := G) e.inv).hom.toAlgHom.commutes (σ r)

private theorem comparisonAction {G H : AffineAlgebraicGroup F}
    (i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H)
    (σ : Gal(K/F)) (x : extendedCoordinate (K := K) G) :
    i.hom.hom ((transport (standard K (affineCoordinateHopf H)) i).action.act σ x) =
      (standardAct K (affineCoordinateHopf H)).act σ (i.hom.hom x) := inv_apply i _


open _root_.LinearAlgebraicGroups.Descent.Forms (spectrumIso IsScalarExtensionComparison)
open private extendedGroupIso extendedSpecIso_hom_fst
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private abbrev comparisonIso {E : Type u} [Field E] [Algebra E K]
    (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup E)
    (i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H) :
    (groupBaseChange F K).obj G.val ≅ (groupBaseChange E K).obj H.val :=
  (extendedCoordinateIso (K := K) G).symm ≪≫ spectrumIso i ≪≫ extendedCoordinateIso (K := K) H

set_option backward.isDefEq.respectTransparency false in
private theorem scalarComparisonUnique
    (t : ∀ B : HopfAlgebraCategory F, specGroup (extendedHopf K B) ≅
      (groupBaseChange F K).obj (specGroup B)) (h : IsScalarExtensionComparison t)
    (B : HopfAlgebraCategory F) : t B = extendedGroupIso K B := by
  apply Iso.ext
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (h B).trans (extendedSpecIso_hom_fst K B).symm
  · exact (Over.w (t B).hom.hom.hom).trans (Over.w (extendedGroupIso K B).hom.hom.hom).symm

set_option backward.isDefEq.respectTransparency false in
private theorem groupComparisonCanonical {G H : AffineAlgebraicGroup F}
    {S : BorelPair G} {M : BorelPair H}
    (cmp : Specs.QuasiSplitPinnedPairModel.MarkedComparison (K := K) S M)
    (i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H)
    (h : Specs.QuasiSplitPinnedPairModel.MatchesCoordinateComparison cmp i) :
    cmp.groupIso = comparisonIso G H i := by
  obtain ⟨t, ht, hc⟩ := h
  rw [hc, scalarComparisonUnique t ht, scalarComparisonUnique t ht]
  simp only [comparisonIso, extendedCoordinateIso, Iso.trans_symm, Iso.trans_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateIsoOfComparison {G H : AffineAlgebraicGroup F}
    (e : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val) :
    ∃ i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H,
      comparisonIso G H i = e := by
  let S := hopfSpec (CommRingCat.of K)
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of K)
  let a := extendedCoordinateIso (K := K) G
  let b := extendedCoordinateIso (K := K) H
  let g := b ≪≫ e.symm ≪≫ a.symm
  let q := ff.preimageIso g
  refine ⟨q.unop, ?_⟩
  have he : spectrumIso q.unop = g.symm := by
    apply Iso.ext
    change S.map q.inv = g.inv
    exact ff.map_preimage _
  change a.symm ≪≫ spectrumIso q.unop ≪≫ b = e
  rw [he]
  simp [g, Iso.trans_assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateComparisonSquare {G H V W : AffineAlgebraicGroup F}
    (f : V.val ⟶ G.val) (g : W.val ⟶ H.val)
    (i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H)
    (j : extendedCoordinate (K := K) V ≅ extendedCoordinate (K := K) W)
    (h : (groupBaseChange F K).map f ≫ (comparisonIso G H i).hom =
      (comparisonIso V W j).hom ≫ (groupBaseChange F K).map g) :
    i.hom ≫ extendedPullback (G := W) (H := H) g =
      extendedPullback (G := V) (H := G) f ≫ j.hom := by
  have h' := (inverseIsoSquare (comparisonIso V W j) (comparisonIso G H i)
    ((groupBaseChange F K).map f) ((groupBaseChange F K).map g) h).symm
  apply specGroupMap_injective
  rw [specGroupMap_comp, specGroupMap_comp]
  let a := extendedCoordinateIso (K := K) V
  let b := extendedCoordinateIso (K := K) G
  let c := extendedCoordinateIso (K := K) W
  let d := extendedCoordinateIso (K := K) H
  let p := extendedPullback (K := K) (G := V) (H := G) f
  let q := extendedPullback (K := K) (G := W) (H := H) g
  change specGroupMap q ≫ specGroupMap i.hom = specGroupMap j.hom ≫ specGroupMap p
  apply (cancel_mono b.hom).mp
  apply (cancel_epi c.inv).mp
  have hf := extendedCoordinateIso_natural (K := K) (G := V) (H := G) f
  have hg := extendedCoordinateIso_natural (K := K) (G := W) (H := H) g
  have hq : c.inv ≫ specGroupMap q = (groupBaseChange F K).map g ≫ d.inv :=
    (inverseIsoSquare c d _ _ hg).symm
  change (c.inv ≫ specGroupMap j.hom ≫ a.hom) ≫ (groupBaseChange F K).map f =
    (groupBaseChange F K).map g ≫ d.inv ≫ specGroupMap i.hom ≫ b.hom at h'
  have hf' : specGroupMap p ≫ b.hom = a.hom ≫ (groupBaseChange F K).map f := hf
  simp only [Category.assoc] at h' ⊢
  rw [← Category.assoc c.inv, hq, Category.assoc, ← h', ← hf']

variable [MulAction Gal(K/F) I]

set_option maxHeartbeats 1250000 in
set_option backward.isDefEq.respectTransparency false in
private def splitProductOfProjections [Finite I] {G H : AffineAlgebraicGroup F}
    {Q : I → AffineAlgebraicGroup F} (p : ∀ c, G.val ⟶ (Q c).val)
    (hp : IsLimit (Fan.mk G.val p))
    (i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H)
    (e : ∀ (σ : Gal(K/F)) (c : I), (Q c).val ≅ (Q (σ • c)).val)
    (he : ∀ (σ : Gal(K/F)) c j (h : σ • c = j) (x : extendedCoordinate (K := K) (Q c)),
      let f : (Q c).val ≅ (Q j).val := h ▸ e σ c
      (extendedPullback (G := G) (H := Q j) (p j)).hom
          (semilinearFactorTransport (G := Q c) (H := Q j) σ f x) =
        (transport (standard K (affineCoordinateHopf H)) i).action.act σ
          ((extendedPullback (G := G) (H := Q c) (p c)).hom x)) :
    ProjectedDescent p i where
  finiteType c := extendedCoordinate_finiteType (Q c)
  product := coordinateProductOfFan p hp
  datum := transport (standard K (affineCoordinateHopf H)) i
  transport σ c j h := semilinearFactorTransport (G := Q c) (H := Q j) σ (h ▸ e σ c)
  transportScalar σ c j h r := by
    let f : (Q c).val ≅ (Q j).val := h ▸ e σ c
    change semilinearFactorTransport (G := Q c) (H := Q j) σ f
      (algebraMap K (extendedCoordinate (K := K) (Q c)) r) =
      algebraMap K (extendedCoordinate (K := K) (Q j)) (σ r)
    exact semilinearFactorTransport_scalar (G := Q c) (H := Q j) σ f r
  transportProjection := he
  equivariant σ x := by
    change i.inv.hom ((standardAct K (affineCoordinateHopf H)).act σ x) =
      i.inv.hom ((standardAct K (affineCoordinateHopf H)).act σ (i.hom.hom (i.inv.hom x)))
    rw [inv_apply i]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem splitTransportOfPinnedMaps {G H : AffineAlgebraicGroup F}
    {Q : I → AffineAlgebraicGroup F} (p : ∀ c, G.val ⟶ (Q c).val)
    (i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H)
    (a : Gal(K/F) → (G.val ≅ G.val))
    (hact : ∀ σ x, (transport (standard K (affineCoordinateHopf H)) i).action.act σ x =
      (extendedPullback (G := G) (H := G) (a σ).inv).hom
        ((standardAct K (affineCoordinateHopf G)).act σ x))
    (e : ∀ (σ : Gal(K/F)) (c : I), (Q c).val ≅ (Q (σ • c)).val)
    (he : ∀ σ c, (a σ).hom ≫ p (σ • c) = p c ≫ (e σ c).hom)
    (σ : Gal(K/F)) (c j : I) (h : σ • c = j) (x : extendedCoordinate (K := K) (Q c)) :
    let f : (Q c).val ≅ (Q j).val := h ▸ e σ c
    (extendedPullback (G := G) (H := Q j) (p j)).hom (semilinearFactorTransport σ f x) =
      (transport (standard K (affineCoordinateHopf H)) i).action.act σ
        ((extendedPullback (G := G) (H := Q c) (p c)).hom x) := by
  subst j
  dsimp only [eq_rec_constant]
  rw [hact, semilinearFactorTransport_apply]
  have hb := baseHom_equivariant (K := K)
    (coordinateHopfMap (G := G) (H := Q c) (p c)) σ x
  change (extendedPullback (G := G) (H := Q c) (p c)).hom
      ((standardAct K (affineCoordinateHopf (Q c))).act σ x) =
    (standardAct K (affineCoordinateHopf G)).act σ ((extendedPullback (G := G) (H := Q c) (p c)).hom x) at hb
  rw [← hb]
  have hinv := inverseIsoSquare (a σ) (e σ c) (p c) (p (σ • c)) (he σ c).symm
  have hh := congrArg (extendedPullback (K := K) (G := G) (H := Q c)) hinv
  rw [pullback_comp, pullback_comp] at hh
  exact ConcreteCategory.congr_hom hh _


private theorem pullbackSquare {G H V W : AffineAlgebraicGroup F}
    (p : G.val ⟶ H.val) (q : V.val ⟶ W.val) (f : V.val ⟶ G.val) (g : W.val ⟶ H.val)
    (h : f ≫ p = q ≫ g) :
    extendedPullback (K := K) (G := G) (H := H) p ≫ extendedPullback (G := V) (H := G) f =
      extendedPullback (G := W) (H := H) g ≫ extendedPullback (G := V) (H := W) q := by
  rw [← pullback_comp, ← pullback_comp, h]

private theorem semilinear_inclusion {X Y U V : AffineAlgebraicGroup F}
    (f : U.val ⟶ X.val) (g : V.val ⟶ Y.val) (e : X.val ≅ Y.val) (d : U.val ≅ V.val)
    (h : f ≫ e.hom = d.hom ≫ g) (σ : Gal(K/F)) (x : extendedCoordinate (K := K) X) :
    (extendedPullback (G := V) (H := Y) g).hom (semilinearFactorTransport σ e x) =
      semilinearFactorTransport σ d ((extendedPullback (G := U) (H := X) f).hom x) := by
  rw [semilinearFactorTransport_apply, semilinearFactorTransport_apply]
  have h₁ := baseHom_equivariant (K := K)
    (coordinateHopfMap (G := U) (H := X) f) σ x
  change (extendedPullback (G := U) (H := X) f).hom
      ((standardAct K (affineCoordinateHopf X)).act σ x) =
    (standardAct K (affineCoordinateHopf U)).act σ ((extendedPullback (G := U) (H := X) f).hom x) at h₁
  rw [← h₁]
  have h₂ := inverseIsoSquare d e f g h
  have hh := congrArg (extendedPullback (K := K) (G := V) (H := X)) h₂
  rw [pullback_comp, pullback_comp] at hh
  exact ConcreteCategory.congr_hom hh _

set_option backward.isDefEq.respectTransparency false in
private theorem inclusion_act {G H V W : AffineAlgebraicGroup F}
    (f : V.val ⟶ G.val) (g : W.val ⟶ H.val)
    (i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H)
    (j : extendedCoordinate (K := K) V ≅ extendedCoordinate (K := K) W)
    (h : i.hom ≫ extendedPullback (G := W) (H := H) g =
      extendedPullback (G := V) (H := G) f ≫ j.hom)
    (σ : Gal(K/F)) (x : extendedCoordinate (K := K) G) :
    (extendedPullback (G := V) (H := G) f).hom
        ((transport (standard K (affineCoordinateHopf H)) i).action.act σ x) =
      (transport (standard K (affineCoordinateHopf W)) j).action.act σ
        ((extendedPullback (G := V) (H := G) f).hom x) := by
  let p := extendedPullback (K := K) (G := V) (H := G) f
  let q := extendedPullback (K := K) (G := W) (H := H) g
  have hh (x : extendedCoordinate (K := K) G) : j.hom.hom (p.hom x) = q.hom (i.hom.hom x) :=
    (ConcreteCategory.congr_hom h x).symm
  apply (CommHopfAlgCat.ofIso j).toAlgEquiv.injective
  change j.hom.hom (p.hom _) = j.hom.hom _
  rw [hh, comparisonAction i, comparisonAction j, hh]
  exact baseHom_equivariant (K := K) (coordinateHopfMap (G := W) (H := H) g) σ (i.hom.hom x)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
private theorem markedTransportOfProjections {G H V W : AffineAlgebraicGroup F}
    {Q U : I → AffineAlgebraicGroup F}
    (p : ∀ c, G.val ⟶ (Q c).val) (q : ∀ c, V.val ⟶ (U c).val)
    (f : V.val ⟶ G.val) (g : W.val ⟶ H.val) (b : ∀ c, (U c).val ⟶ (Q c).val)
    (hclosed : ∀ c, IsClosedImmersion (b c).hom.hom.left)
    (h₀ : ∀ c, f ≫ p c = q c ≫ b c)
    (i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H)
    (j : extendedCoordinate (K := K) V ≅ extendedCoordinate (K := K) W)
    (hcomp : i.hom ≫ extendedPullback (G := W) (H := H) g =
      extendedPullback (G := V) (H := G) f ≫ j.hom)
    (e : ∀ (σ : Gal(K/F)) (c : I), (Q c).val ≅ (Q (σ • c)).val)
    (d : ∀ (σ : Gal(K/F)) (c : I), (U c).val ≅ (U (σ • c)).val)
    (hed : ∀ σ c, b c ≫ (e σ c).hom = (d σ c).hom ≫ b (σ • c))
    (hact : ∀ (σ : Gal(K/F)) c (x : extendedCoordinate (K := K) (Q c)),
      (extendedPullback (G := G) (H := Q (σ • c)) (p (σ • c))).hom
          (semilinearFactorTransport σ (e σ c) x) =
        (transport (standard K (affineCoordinateHopf H)) i).action.act σ
          ((extendedPullback (G := G) (H := Q c) (p c)).hom x))
    (σ : Gal(K/F)) (c l : I) (h : σ • c = l) (x : extendedCoordinate (K := K) (U c)) :
    let t : (U c).val ≅ (U l).val := h ▸ d σ c
    (extendedPullback (G := V) (H := U l) (q l)).hom (semilinearFactorTransport σ t x) =
      (transport (standard K (affineCoordinateHopf W)) j).action.act σ
        ((extendedPullback (G := V) (H := U c) (q c)).hom x) := by
  subst l
  let z := σ • c
  obtain ⟨y, rfl⟩ := extendedCoordinate_surjective (K := K)
    (G := U c) (H := Q c) (b c) (hclosed c) x
  change (extendedPullback (G := V) (H := U z) (q z)).hom
      (semilinearFactorTransport σ (d σ c) ((extendedPullback (G := U c) (H := Q c) (b c)).hom y)) = _
  rw [← semilinear_inclusion (b c) (b z) (e σ c) (d σ c) (hed σ c)]
  have hs (v : I) (u : extendedCoordinate (K := K) (Q v)) :
      (extendedPullback (G := V) (H := U v) (q v)).hom
          ((extendedPullback (G := U v) (H := Q v) (b v)).hom u) =
        (extendedPullback (G := V) (H := G) f).hom
          ((extendedPullback (G := G) (H := Q v) (p v)).hom u) :=
    (ConcreteCategory.congr_hom (pullbackSquare (K := K) (p v) (q v) f (b v) (h₀ v)) u).symm
  rw [hs, hs, hact]
  exact inclusion_act f g i j hcomp σ _

private theorem pinnedTwist_action {G : AffineAlgebraicGroup F}
    {A : Specs.RootGroups.AdditiveLine F} {P : Specs.Pinning.PinnedGroup A}
    {D : AttachedDatum P.pair} {lift : Aut D.toBased ≃* Aut P}
    {B T : ClosedSubgroup G.val} (w : Specs.AdjointBorelCohomology.PinnedTwist K D lift B T)
    (σ : Gal(K/F)) (x : extendedCoordinate (K := K) P.pair.G) :
    (transport (standard K (affineCoordinateHopf G)) w.groupIso).action.act σ x =
      (extendedPullback (G := P.pair.G) (H := P.pair.G) (lift (w.outer σ)).asIso.hom.group.inv).hom
        ((standardAct K (affineCoordinateHopf P.pair.G)).act σ x) := by
  let a := lift (w.outer σ)
  let b := Functor.mapAut P (Specs.AutomorphismSequence.forgetPinning (A := A)) a
  have hab : b.asIso = a.asIso.hom.group := Iso.ext rfl
  apply (CommHopfAlgCat.ofIso w.groupIso).toAlgEquiv.injective
  change w.groupIso.hom.hom _ = w.groupIso.hom.hom _
  rw [comparisonAction]
  rw [show (lift (w.outer σ)).asIso.hom.group.inv = b.asIso.inv from (congrArg Iso.inv hab).symm]
  exact w.twistedAction σ x

set_option backward.isDefEq.respectTransparency false in
private def projectedInclusion {G H V W : AffineAlgebraicGroup F}
    {Q U : I → AffineAlgebraicGroup F} {p : ∀ c, G.val ⟶ (Q c).val}
    {q : ∀ c, V.val ⟶ (U c).val}
    {i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H}
    {j : extendedCoordinate (K := K) V ≅ extendedCoordinate (K := K) W}
    (a : ProjectedDescent p i) (s : ProjectedDescent q j)
    (f : V.val ⟶ G.val) (g : W.val ⟶ H.val) (b : ∀ c, (U c).val ⟶ (Q c).val)
    (hclosed : ∀ c, IsClosedImmersion (b c).hom.hom.left)
    (hproj : ∀ c, f ≫ p c = q c ≫ b c)
    (hcomp : i.hom ≫ extendedPullback (G := W) (H := H) g =
      extendedPullback (G := V) (H := G) f ≫ j.hom) :
    ProductInclusion a.productDescent s.productDescent where
  extended := extendedPullback (G := V) (H := G) f
  ground := coordinateHopfMap (G := W) (H := H) g
  factor c := extendedPullback (G := U c) (H := Q c) (b c)
  closed c := extendedCoordinate_surjective (K := K) (G := U c) (H := Q c) (b c) (hclosed c)
  projected c := pullbackSquare (K := K) (p c) (q c) f (b c) (hproj c)
  compared := (inverseIsoSquare i j (extendedPullback (G := V) (H := G) f)
    (extendedPullback (G := W) (H := H) g) hcomp.symm).symm

open Specs.Pinning (PinnedGroup PinnedIso)
open Specs.RootGroups (AdditiveLine)
open Specs.AdjointBorelCohomology (PinnedTwist)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2100000 in
private theorem markedProjectionDescent {G : AffineAlgebraicGroup F}
    {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {M : BorelPair G} {S : BorelPair P.pair.G}
    (W : SplitComponents D S) (w : PinnedTwist K D l M.positive M.torus)
    (cmp : Specs.QuasiSplitPinnedPairModel.MarkedComparison (K := K) S M)
    (hcmp : Specs.QuasiSplitPinnedPairModel.MatchesCoordinateComparison cmp w.groupIso)
    [MulAction Gal(K/F) (Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased)]
    (t : ∀ (σ : Gal(K/F)) c, PinnedIso (W.factors.factor c) (W.factors.factor (σ • c)))
    (ht : ∀ σ c, (l (w.outer σ)).asIso.hom.group.hom ≫ W.product.projection (σ • c) =
      W.product.projection c ≫ (t σ c).group.hom) :
    ∃ (j : ∀ m, extendedCoordinate (K := K) (closedSubgroupAlgebraicGroup (S.subgroup m)) ≅
        extendedCoordinate (K := K) (closedSubgroupAlgebraicGroup (M.subgroup m)))
      (_s : ∀ m, ProjectedDescent
        (Q := fun c => closedSubgroupAlgebraicGroup ((W.pairs c).subgroup m))
        (W.product.subgroupProjection m) (j m)),
      ∀ m, w.groupIso.hom ≫
        extendedPullback (G := closedSubgroupAlgebraicGroup (M.subgroup m)) (H := G)
          (M.subgroup m).inclusion =
        extendedPullback (G := closedSubgroupAlgebraicGroup (S.subgroup m)) (H := P.pair.G)
          (S.subgroup m).inclusion ≫ (j m).hom := by
  let C := Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased
  letI : Finite C := Quotient.finite _
  let Q (c : C) := (W.factors.factor c).pair.G
  let V (m : Marking) := closedSubgroupAlgebraicGroup (S.subgroup m)
  let X (m : Marking) := closedSubgroupAlgebraicGroup (M.subgroup m)
  let U (m : Marking) (c : C) := closedSubgroupAlgebraicGroup ((W.pairs c).subgroup m)
  have hG := groupComparisonCanonical (G := P.pair.G) (H := G) cmp w.groupIso hcmp
  choose j hj using fun m => coordinateIsoOfComparison (K := K) (G := V m) (H := X m) (cmp.subgroupIso m)
  have hs (m : Marking) : w.groupIso.hom ≫
      extendedPullback (G := X m) (H := G) (M.subgroup m).inclusion =
      extendedPullback (G := V m) (H := P.pair.G) (S.subgroup m).inclusion ≫ (j m).hom :=
    coordinateComparisonSquare (G := P.pair.G) (H := G) (V := V m) (W := X m)
      (S.subgroup m).inclusion (M.subgroup m).inclusion w.groupIso (j m) (by
        rw [← hG, hj m]
        exact cmp.commutes m)
  choose e he using fun (σ : Gal(K/F)) (c : C) => pinnedMarkedTransport (t σ c) (W.pairs c) (W.pairs (σ • c))
    (W.positive_eq c) (W.torus_eq c) (W.positive_eq (σ • c)) (W.torus_eq (σ • c))
  have hact (σ : Gal(K/F)) (c : C) (x : extendedCoordinate (K := K) (Q c)) :
      (extendedPullback (G := P.pair.G) (H := Q (σ • c)) (W.product.projection (σ • c))).hom
        (semilinearFactorTransport (G := Q c) (H := Q (σ • c)) σ (t σ c).group x) =
      (transport (standard K (affineCoordinateHopf G)) w.groupIso).action.act σ
        ((extendedPullback (G := P.pair.G) (H := Q c) (W.product.projection c)).hom x) :=
    splitTransportOfPinnedMaps (G := P.pair.G) (H := G) (Q := Q) W.product.projection w.groupIso
      (fun σ => (l (w.outer σ)).asIso.hom.group) (pinnedTwist_action w) (fun σ c => (t σ c).group)
      ht σ c (σ • c) rfl x
  refine ⟨j, fun m => splitProductOfProjections (G := V m) (H := X m) (Q := U m) (W.product.subgroupProjection m)
    (W.product.subgroupProduct m) (j m) (fun σ c => e σ c m) ?_, hs⟩
  exact markedTransportOfProjections (G := P.pair.G) (H := G) (V := V m) (W := X m)
    (Q := Q) (U := U m) W.product.projection
    (W.product.subgroupProjection m) (S.subgroup m).inclusion (M.subgroup m).inclusion
    (fun c => ((W.pairs c).subgroup m).inclusion) (fun c => ((W.pairs c).subgroup m).isClosedImmersion)
    (W.product.commutes m) w.groupIso (j m) (hs m) (fun σ c => (t σ c).group)
    (fun σ c => e σ c m) (fun σ c => he σ c m) hact

end CoordinateProducts



section GeometryOfOrbitFactors

open Specs.GeometricRadicals
  (IsReductive IsSplitTorus IsTorus IsSemisimple IsUnipotentRadical IsTrivialSubgroup
    IsSmoothConnectedNormal GeometricGroup)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup IsUnipotent)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.Pinning (SplitBorelPair PinnedGroup PinnedIso)
open Specs.RootGroups (AdditiveLine)
open private groupBaseChangeTower extendSubgroup subgroup_baseChange_iff
  smooth_baseChange_iff connected_baseChange_iff radical_of_extended_radical
  unipotent_of_iso unipotent_subgroup_baseChange_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private isIso_of_schemeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private smooth_of_iso connected_of_iso borel_of_square
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
open private geometricallyConnected_of_connected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private inclusion_mono pushSubgroup normal_postcompose_iso radical_transport
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private subgroupSections_mono borelRadicalAfterSplitting semisimple_of_iso commonTorus_le_borel
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
open private intersection_baseChange maximal_of_selfCentralizing
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitBorelPairBaseChange
open private transport_intersection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOppositeBorelUniqueness
open private schemeIntersection_exists subgroup_of_intersection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private maximal_of_square from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private extendedBorel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.BorelInnerAlignment
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag

variable {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F K] [Algebra E K]

private abbrev extendComparison {R : Type u} [Field R] [Algebra F R] [Algebra E R]
    [Algebra K R] [IsScalarTower F K R] [IsScalarTower E K R]
    {G : GroupScheme F} {H : GroupScheme E}
    (e : (groupBaseChange F K).obj G ≅ (groupBaseChange E K).obj H) :
    (groupBaseChange F R).obj G ≅ (groupBaseChange E R).obj H :=
  (groupBaseChangeTower (k := F) (K := K) R).app G ≪≫
    (groupBaseChange K R).mapIso e ≪≫ (groupBaseChangeTower (k := E) (K := K) R).symm.app H

set_option backward.isDefEq.respectTransparency false in
private theorem extendComparison_square {R : Type u} [Field R] [Algebra F R] [Algebra E R]
    [Algebra K R] [IsScalarTower F K R] [IsScalarTower E K R]
    {G X : GroupScheme F} {H Y : GroupScheme E}
    (e : (groupBaseChange F K).obj G ≅ (groupBaseChange E K).obj H)
    (d : (groupBaseChange F K).obj X ≅ (groupBaseChange E K).obj Y)
    (f : X ⟶ G) (g : Y ⟶ H)
    (h : (groupBaseChange F K).map f ≫ e.hom = d.hom ≫ (groupBaseChange E K).map g) :
    (groupBaseChange F R).map f ≫ (extendComparison (R := R) e).hom =
      (extendComparison (R := R) d).hom ≫ (groupBaseChange E R).map g := by
  let a := groupBaseChangeTower (k := F) (K := K) R
  let b := groupBaseChangeTower (k := E) (K := K) R
  let L := groupBaseChange K R
  change (groupBaseChange F R).map f ≫ a.hom.app G ≫ L.map e.hom ≫ b.inv.app H =
    (a.hom.app X ≫ L.map d.hom ≫ b.inv.app Y) ≫ (groupBaseChange E R).map g
  have hw := congrArg L.map h
  simp only [L.map_comp] at hw
  simp only [Category.assoc, ← b.inv.naturality g, a.hom.naturality_assoc f, Functor.comp_map]
  rw [← Category.assoc (L.map d.hom), ← hw, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem semisimple_of_commonExtension {G : AffineAlgebraicGroup F}
    {H : AffineAlgebraicGroup E} (hG : IsSemisimple G)
    (e : (groupBaseChange F K).obj G.val ≅ (groupBaseChange E K).obj H.val) :
    IsSemisimple H := by
  have hGK := (Reductive.RadicalBaseChange.semisimpleFieldExtension
    (K := K) G hG.1 hG.2.1).mpr hG
  have hs := smooth_of_iso e hGK.1
  have hconn : ConnectedSpace (baseChangedAlgebraicGroup K G).val.X.left := by
    letI := hGK.2.1
    exact GeometricallyConnected.connectedSpace_of_subsingleton
      (baseChangedAlgebraicGroup K G).val.X.hom
  have hc := connected_of_iso e hconn
  have hs' := (smooth_baseChange_iff (K := K) H.val.X).mp hs
  have hc' := @geometricallyConnected_of_connected E _ H
    ((connected_baseChange_iff (K := K) H).mp hc)
  have hcK := @geometricallyConnected_of_connected K _ (baseChangedAlgebraicGroup K H) hc
  exact (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) H hs' hc').mp
    (semisimple_of_iso e hGK hs hcK)

open private fibreTowerIso noCentralCovers_of_span realization_corootSpan of_fullCorootLattice
  centralIsogeny_postIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private connectedDiagram_of_basedIso connectedSplitNormalSubgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct
open private coroot_span_of_equiv nontrivial_of_root
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
private theorem simpleFormOfConnectedDiagram {P : SplitBorelPair F} (D : AttachedDatum P)
    {H : AffineAlgebraicGroup E} [Algebra.IsAlgebraic E K]
    (hD : corootLattice D = ⊤)
    (hc : (integralDiagram (integralCartan D.toBased.datum D.toBased.base)).IsConnected)
    (e : (groupBaseChange F K).obj P.G.val ≅ (groupBaseChange E K).obj H.val) :
    IsAbsolutelyAlmostSimple H ∧ GeometricallySimplyConnected H := by
  letI := D.comm
  letI := D.toBased.finiteRoots
  let L := AlgebraicClosure E
  let a : K →ₐ[E] L := IsAlgClosed.lift
  letI : Algebra K L := a.toRingHom.toAlgebra
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq fun x => (a.commutes x).symm
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨A, X, f, _⟩ := M.fieldFibre F
  obtain ⟨A', Y, g, _⟩ := M.fieldFibre L
  obtain ⟨d⟩ := ((Classification.PinnedEquivalence.pinnedEquivalence.2 F).2.1
    P X.pinned.pair D X.attached).mpr ⟨X.datumIso.val⟩
  let q : (GeometricGroup H).val ≅ Y.pinned.pair.G.val :=
    (extendComparison (R := L) e).symm ≪≫ (groupBaseChange F L).mapIso (d ≪≫ f.symm) ≪≫
      ((fibreTowerIso F L).app M.group).symm ≪≫ g
  obtain ⟨_, _, B, ⟨W⟩⟩ := RootData.AbsoluteDynkinTypes.splitPinnedComparison A' Y.pinned.pair
  letI := B.comm
  let j : D.toBased ⟶ B.toBased :=
    Y.datumIso ≫ Classification.Pinning.inducedBasedIso (PinnedIso.refl Y.pinned) Y.attached B
  have hB : corootLattice B = ⊤ := coroot_span_of_equiv _ _ j.val hD
  have hBC := connectedDiagram_of_basedIso j hc
  have hYG := of_fullCorootLattice Y.pinned.pair B hB
  obtain ⟨v⟩ := hBC.1
  refine ⟨⟨semisimple_of_commonExtension (of_fullCorootLattice P D hD) e,
    fun z => nontrivial_of_root Y.pinned.pair v.val (z.of_iso q.symm), ?_⟩, ?_⟩
  · intro N hN
    let U := pushSubgroup q N
    have hU : IsSmoothConnectedNormal (G := Y.pinned.pair.G) U :=
      ⟨hN.1, hN.2.1, normal_postcompose_iso N.inclusion q hN.2.2⟩
    rcases connectedSplitNormalSubgroup B hYG hB hBC W U hU with h | h
    · exact Or.inl h
    · right
      letI : IsIso (N.inclusion ≫ q.hom) := h
      exact IsIso.of_isIso_comp_right N.inclusion q.hom
  · intro J hJ p hp
    letI := noCentralCovers_of_span Y.pinned.pair B hB J hJ (p ≫ q.hom)
      (centralIsogeny_postIso q hp)
    exact IsIso.of_isIso_comp_right p q.hom

set_option backward.isDefEq.respectTransparency false in
private theorem intersection_of_scalarExtension {H : AffineAlgebraicGroup E}
    (B C T : ClosedSubgroup H.val)
    (h : IsSchemeIntersection {extendSubgroup K B, extendSubgroup K C} (extendSubgroup K T)) :
    IsSchemeIntersection {B, C} T := by
  obtain ⟨J, hJ⟩ := schemeIntersection_exists H {B, C}
  have hJ' := intersection_baseChange (K := K) B C J hJ
  have hle (U V : ClosedSubgroup H.val)
      (hU : IsSchemeIntersection {extendSubgroup K B, extendSubgroup K C} (extendSubgroup K U))
      (hV : IsSchemeIntersection {extendSubgroup K B, extendSubgroup K C} (extendSubgroup K V)) :
      IsSubgroupOf U V := by
    apply (subgroup_baseChange_iff (K := K) U V).mp
    exact (subgroup_of_intersection hV).mpr
      ((subgroup_of_intersection hU).mp ⟨𝟙 _, Category.id_comp _⟩)
  intro Y y
  exact (show y ∈ Specs.SubgroupSections T Y ↔ y ∈ Specs.SubgroupSections J Y from
    ⟨fun hy => subgroupSections_mono (hle T J h hJ') Y hy,
      fun hy => subgroupSections_mono (hle J T hJ' h) Y hy⟩).trans (hJ Y y)

set_option backward.isDefEq.respectTransparency false in
private theorem borelRadicalOfComparison {G : AffineAlgebraicGroup F}
    {H : AffineAlgebraicGroup E} (hG : IsReductive G) (M : BorelPair G)
    (hs : IsSplitTorus ((groupBaseChange F K).obj M.torus.group))
    {B : ClosedSubgroup G.val} (hB : IsKBorel B) (hTB : IsSubgroupOf M.torus B)
    (U : ClosedSubgroup B.group) (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U)
    (D V : ClosedSubgroup H.val)
    (e : (groupBaseChange F K).obj G.val ≅ (groupBaseChange E K).obj H.val)
    (b : (groupBaseChange F K).obj B.group ≅ (groupBaseChange E K).obj D.group)
    (u : (groupBaseChange F K).obj U.group ≅ (groupBaseChange E K).obj V.group)
    (hb : (groupBaseChange F K).map B.inclusion ≫ e.hom =
      b.hom ≫ (groupBaseChange E K).map D.inclusion)
    (hu : (groupBaseChange F K).map (U.inclusion ≫ B.inclusion) ≫ e.hom =
      u.hom ≫ (groupBaseChange E K).map V.inclusion) :
    ∃ V' : ClosedSubgroup D.group, V'.group = V.group ∧ subgroupOfSubgroup D V' = V ∧
      IsUnipotentRadical (closedSubgroupAlgebraicGroup D) V' := by
  let F₁ := groupBaseChange F K
  let E₁ := groupBaseChange E K
  have hV : IsSubgroupOf V D := by
    apply (subgroup_baseChange_iff (K := K) V D).mp
    refine ⟨u.inv ≫ F₁.map U.inclusion ≫ b.hom, ?_⟩
    change (u.inv ≫ F₁.map U.inclusion ≫ b.hom) ≫ E₁.map D.inclusion = E₁.map V.inclusion
    rw [Category.assoc, Category.assoc, ← hb, ← Category.assoc (F₁.map U.inclusion),
      ← F₁.map_comp, hu, u.inv_hom_id_assoc]
  obtain ⟨r, hr⟩ := hV
  have hclosed : IsClosedImmersion r.hom.hom.left := by
    letI := D.isClosedImmersion
    haveI : IsClosedImmersion (r.hom.hom.left ≫ D.inclusion.hom.hom.left) := by
      rw [show r.hom.hom.left ≫ D.inclusion.hom.hom.left = V.inclusion.hom.hom.left
        from congrArg (fun f : V.group ⟶ H.val => f.hom.hom.left) hr]
      exact V.isClosedImmersion
    exact IsClosedImmersion.of_comp_isClosedImmersion _ D.inclusion.hom.hom.left
  let V' : ClosedSubgroup D.group := ⟨V.group, r, hclosed⟩
  have hVR : subgroupOfSubgroup D V' = V := by
    rcases V with ⟨X, i, c⟩
    change r ≫ D.inclusion = i at hr
    change (⟨X, r ≫ D.inclusion, _⟩ : ClosedSubgroup H.val) = ⟨X, i, c⟩
    congr 1
  have hr' : F₁.map U.inclusion ≫ b.hom = u.hom ≫ E₁.map r := by
    letI : Mono (E₁.map D.inclusion) := inclusion_mono (extendSubgroup K D)
    apply (cancel_mono (E₁.map D.inclusion)).mp
    rw [Category.assoc, ← hb, ← Category.assoc, ← F₁.map_comp, hu,
      Category.assoc, ← E₁.map_comp, hr]
  have hUK := borelRadicalAfterSplitting (K := K) hG hB M.maximal hTB hs hU
  let W := pushSubgroup b (extendSubgroup K U)
  have hW : IsUnipotentRadical (baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup D)) W :=
    radical_transport
      (A := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup B))
      (B := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup D)) b (extendSubgroup K U) hUK
  refine ⟨V', rfl, hVR, ?_⟩
  apply radical_of_extended_radical (G := closedSubgroupAlgebraicGroup D) (K := K)
    (P := IsUnipotent) (Q := IsUnipotent) (M := V')
    (fun S _ => unipotent_subgroup_baseChange_iff S)
    (fun j _ _ => unipotent_of_iso j) hW u.symm
  change u.inv ≫ (F₁.map U.inclusion ≫ b.hom) = E₁.map r
  rw [hr', u.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
private theorem borelPairOfComparison {G : AffineAlgebraicGroup F}
    {H : AffineAlgebraicGroup E} [Algebra.IsSeparable E K]
    (hG : IsReductive G) (M : BorelPair G) (hs : IsSplitTorus M.torus.group)
    (N : Marking → ClosedSubgroup H.val)
    (e : (groupBaseChange F K).obj G.val ≅ (groupBaseChange E K).obj H.val)
    (d : ∀ m, (groupBaseChange F K).obj (M.subgroup m).group ≅
      (groupBaseChange E K).obj (N m).group)
    (hd : ∀ m, (groupBaseChange F K).map (M.subgroup m).inclusion ≫ e.hom =
      (d m).hom ≫ (groupBaseChange E K).map (N m).inclusion) :
    ∃ P : BorelPair H, ∀ m, P.subgroup m = N m := by
  have hsK := splitTorus_baseChange (K := K) hs
  have ht : IsTorus (N .torus).group := by
    obtain ⟨n, ⟨a⟩⟩ := hsK
    exact ⟨K, inferInstance, inferInstance, inferInstance, n, ⟨(d .torus).symm ≪≫ a⟩⟩
  have hTi := intersection_baseChange (K := K) M.positive M.negative M.torus M.intersection
  have hT := intersection_of_scalarExtension (K := K) (N .positive) (N .negative) (N .torus)
    (transport_intersection e (d .torus) (d .positive) (d .negative)
      (hd .torus) (hd .positive) (hd .negative) hTi)
  obtain ⟨U, _, hU, hu⟩ := borelRadicalOfComparison hG M hsK M.positiveBorel
    (commonTorus_le_borel M (by simp)) M.positiveRadical M.positiveUnipotentRadical
    (N .positive) (N .positiveRadical) e (d .positive) (d .positiveRadical)
    (hd .positive) (hd .positiveRadical)
  obtain ⟨V, _, hV, hv⟩ := borelRadicalOfComparison hG M hsK M.negativeBorel
    (commonTorus_le_borel M (by simp)) M.negativeRadical M.negativeUnipotentRadical
    (N .negative) (N .negativeRadical) e (d .negative) (d .negativeRadical)
    (hd .negative) (hd .negativeRadical)
  have geom : IsKBorel (N .positive) ∧ IsKBorel (N .negative) ∧ IsGeometricallyMaximal (N .torus) := by
    let L := AlgebraicClosure E
    let a : K →ₐ[E] L := IsAlgClosed.lift
    letI : Algebra K L := a.toRingHom.toAlgebra
    letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
    letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq fun x => (a.commutes x).symm
    let f := extendComparison (R := L) e
    let W := baseChangedAlgebraicGroup L G
    let Y := GeometricGroup H
    have borel (m : Marking) (hm : IsKBorel (M.subgroup m)) : IsKBorel (N m) := by
      refine ⟨(extendSubgroup L (N m)).isClosedImmersion, ?_⟩
      exact borel_of_square (X := W) (Y := Y) f (extendSubgroup L (M.subgroup m))
        (extendSubgroup L (N m)) (extendComparison (R := L) (d m))
        (extendComparison_square (R := L) e (d m) _ _ (hd m)).symm
        (extendedBorel G hG _ hm L)
    refine ⟨borel .positive M.positiveBorel, borel .negative M.negativeBorel,
      (extendSubgroup L (N .torus)).isClosedImmersion, ?_⟩
    let T := extendSubgroup L M.torus
    have hC := Reductive.TorusCentralizer.maximalTorusCentralizer G hG M.torus M.isTorus M.maximal
    obtain ⟨_, hCL⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange
      F L M.torus.inclusion M.torus hC
    have htL : IsTorus T.group := lattice_torus_of_split (splitTorus_baseChange hs)
    have hmax := maximal_of_selfCentralizing (G := W) T htL hCL
    exact maximal_of_square f T (extendSubgroup L (N .torus))
      (extendComparison (R := L) (d .torus))
      (extendComparison_square (R := L) e (d .torus) _ _ (hd .torus)).symm hmax
  let P : BorelPair H := ⟨N .positive, N .negative, N .torus, U, V, geom.1, geom.2.1,
    ht, geom.2.2, hT, hu, hv⟩
  refine ⟨P, fun m => ?_⟩
  cases m
  · rfl
  · rfl
  · rfl
  · exact hU
  · exact hV

end GeometryOfOrbitFactors

section OrbitMarkings

open Specs.AdjointCocharacters (coordinateHopfMap coordinateHopfIso)
open Specs.AdjointCocharacters renaming coordinateHopf -> affineCoordinateHopf
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open private presentationIso presentationIso_natural presentationIso_spec
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
open private extendedIso extendedHom_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private extendedCoordinateIso extendedCoordinateIso_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private extendedGroupIso extendedSpecIso_hom_fst specGroupMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open _root_.LinearAlgebraicGroups.Descent.Forms (spectrumIso)

variable {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F K] [Algebra E K]

private def coordinateIsoWithPresentation {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup E}
    {C : HopfAlgebraCategory E} (s : specGroup C ≅ H.val)
    (e : extendedCoordinate (K := K) G ≅ extendedHopf K C) :
    extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H :=
  e ≪≫ extendedIso K (presentationIso H C s).symm

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateIsoWithPresentation_square {G X : AffineAlgebraicGroup F}
    {H Y : AffineAlgebraicGroup E} {B C : HopfAlgebraCategory E} (t : B ⟶ C)
    (s : specGroup B ≅ H.val) (r : specGroup C ≅ Y.val) (f : X.val ⟶ G.val) (g : Y.val ⟶ H.val)
    (hg : specGroupMap t ≫ s.hom = r.hom ≫ g)
    (i : extendedCoordinate (K := K) G ≅ extendedHopf K B)
    (j : extendedCoordinate (K := K) X ≅ extendedHopf K C)
    (h : i.hom ≫ extendedHopfMap K t = extendedPullback (G := X) (H := G) f ≫ j.hom) :
    (coordinateIsoWithPresentation s i).hom ≫ extendedPullback (K := K) (G := Y) (H := H) g =
      extendedPullback (G := X) (H := G) f ≫ (coordinateIsoWithPresentation r j).hom := by
  let a := extendedIso K (presentationIso H B s)
  let b := extendedIso K (presentationIso Y C r)
  let q := extendedPullback (K := K) (G := Y) (H := H) g
  let p := extendedPullback (K := K) (G := X) (H := G) f
  have hn : a.hom ≫ extendedHopfMap K t = q ≫ b.hom := by
    change extendedHopfMap K _ ≫ extendedHopfMap K _ = extendedHopfMap K _ ≫ extendedHopfMap K _
    rw [← extendedHom_comp, ← extendedHom_comp, presentationIso_natural s r g t hg]
  change (i.hom ≫ a.inv) ≫ q = p ≫ j.hom ≫ b.inv
  apply (cancel_mono b.hom).mp
  simp only [Category.assoc]
  rw [← hn, a.inv_hom_id_assoc, b.inv_hom_id]
  simpa only [Category.comp_id] using h

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonIso_square {G X : AffineAlgebraicGroup F}
    {H Y : AffineAlgebraicGroup E} (f : X.val ⟶ G.val) (g : Y.val ⟶ H.val)
    (i : extendedCoordinate (K := K) G ≅ extendedCoordinate (K := K) H)
    (j : extendedCoordinate (K := K) X ≅ extendedCoordinate (K := K) Y)
    (h : i.hom ≫ extendedPullback (G := Y) (H := H) g =
      extendedPullback (G := X) (H := G) f ≫ j.hom) :
    (groupBaseChange F K).map f ≫ (comparisonIso G H i).hom =
      (comparisonIso X Y j).hom ≫ (groupBaseChange E K).map g := by
  let p := extendedPullback (K := K) (G := X) (H := G) f
  let q := extendedPullback (K := K) (G := Y) (H := H) g
  let a := extendedCoordinateIso (K := K) X
  let b := extendedCoordinateIso (K := K) G
  let c := extendedCoordinateIso (K := K) Y
  let d := extendedCoordinateIso (K := K) H
  have h' : i.inv ≫ p = q ≫ j.inv :=
    (inverseIsoSquare i j p q h.symm).symm
  have h'' : specGroupMap p ≫ (spectrumIso i).hom = (spectrumIso j).hom ≫ specGroupMap q := by
    change specGroupMap p ≫ specGroupMap i.inv = specGroupMap j.inv ≫ specGroupMap q
    rw [← specGroupMap_comp, ← specGroupMap_comp, h']
  have ha : (groupBaseChange F K).map f ≫ b.inv = a.inv ≫ specGroupMap p :=
    inverseIsoSquare a b (specGroupMap p) ((groupBaseChange F K).map f)
      (extendedCoordinateIso_natural (K := K) (G := X) (H := G) f)
  have hc : c.hom ≫ (groupBaseChange E K).map g = specGroupMap q ≫ d.hom :=
    (extendedCoordinateIso_natural (K := K) (G := Y) (H := H) g).symm
  change (groupBaseChange F K).map f ≫ b.inv ≫ (spectrumIso i).hom ≫ d.hom =
    (a.inv ≫ (spectrumIso j).hom ≫ c.hom) ≫ (groupBaseChange E K).map g
  calc
    _ = a.inv ≫ (specGroupMap p ≫ (spectrumIso i).hom) ≫ d.hom := by
      rw [← Category.assoc ((groupBaseChange F K).map f), ha]
      simp only [Category.assoc]
    _ = _ := by
      rw [h'']
      simp only [Category.assoc, hc]

private def closedFromHopf {B C : HopfAlgebraCategory E}
    (g : B ⟶ C) (hg : Function.Surjective g.hom) : ClosedSubgroup (specGroup B) :=
  ⟨specGroup C, specGroupMap g, (hopfMapClosedImmersion E g).mpr hg⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
private theorem markedOrbitGeometry {G : AffineAlgebraicGroup F}
    [Algebra.IsSeparable E K] (hG : IsReductive G)
    (M : BorelPair G) (hT : IsSplitTorus M.torus.group)
    (B : HopfAlgebraCategory E) (hB : Algebra.FiniteType E B)
    (C : Marking → HopfAlgebraCategory E)
    (g : ∀ m, B ⟶ C m) (hg : ∀ m, Function.Surjective (g m).hom)
    (i : extendedCoordinate (K := K) G ≅ extendedHopf K B)
    (j : ∀ m, extendedCoordinate (K := K) (closedSubgroupAlgebraicGroup (M.subgroup m)) ≅
      extendedHopf K (C m))
    (hj : ∀ m, i.hom ≫ extendedHopfMap K (g m) =
      extendedPullback (G := closedSubgroupAlgebraicGroup (M.subgroup m)) (H := G)
        (M.subgroup m).inclusion ≫ (j m).hom) :
    let H := affineSpec B hB
    let i' := coordinateIsoWithPresentation (H := H) (Iso.refl _) i
    ∃ (P : BorelPair H) (c : MarkedComparison (K := K) M P),
      (∀ m, P.subgroup m = closedFromHopf (g m) (hg m)) ∧
      c.groupIso = comparisonIso G H i' ∧ MatchesCoordinateComparison c i' := by
  dsimp only
  let H := affineSpec B hB
  let N (m : Marking) : ClosedSubgroup H.val := closedFromHopf (g m) (hg m)
  let i' := coordinateIsoWithPresentation (G := G) (H := H) (Iso.refl (specGroup B)) i
  let j' (m : Marking) := coordinateIsoWithPresentation
    (G := closedSubgroupAlgebraicGroup (M.subgroup m)) (H := closedSubgroupAlgebraicGroup (N m))
    (Iso.refl (specGroup (C m))) (j m)
  let e := comparisonIso G H i'
  let d (m : Marking) := comparisonIso (closedSubgroupAlgebraicGroup (M.subgroup m))
    (closedSubgroupAlgebraicGroup (N m)) (j' m)
  have hd (m : Marking) :
      (groupBaseChange F K).map (M.subgroup m).inclusion ≫ e.hom =
        (d m).hom ≫ (groupBaseChange E K).map (N m).inclusion := by
    let X := closedSubgroupAlgebraicGroup (M.subgroup m)
    let Y := closedSubgroupAlgebraicGroup (N m)
    have h := coordinateIsoWithPresentation_square (G := G) (X := X) (H := H) (Y := Y)
      (g m) (Iso.refl (specGroup B)) (Iso.refl (specGroup (C m)))
      (M.subgroup m).inclusion (N m).inclusion
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl) i (j m) (hj m)
    exact comparisonIso_square (G := G) (X := X) (H := H) (Y := Y)
      (M.subgroup m).inclusion (N m).inclusion i' (j' m) h
  obtain ⟨P, hP⟩ := borelPairOfComparison (G := G) (H := H) hG M hT N e d hd
  have compare (m : Marking) (U : ClosedSubgroup H.val) (hU : U = N m) :
      ∃ d' : (groupBaseChange F K).obj (M.subgroup m).group ≅ (groupBaseChange E K).obj U.group,
        (groupBaseChange F K).map (M.subgroup m).inclusion ≫ e.hom =
          d'.hom ≫ (groupBaseChange E K).map U.inclusion := by
    subst U
    exact ⟨d m, hd m⟩
  choose d' hd' using fun m => compare m (P.subgroup m) (hP m)
  let c : MarkedComparison (K := K) M P := ⟨e, d', hd'⟩
  refine ⟨P, c, hP, rfl, extendedGroupIso K, extendedGroupIso K,
    extendedSpecIso_hom_fst (k := F) K, extendedSpecIso_hom_fst (k := E) K, ?_⟩
  simp only [c, e, comparisonIso, extendedCoordinateIso, Iso.trans_symm, Iso.trans_assoc]
  rfl

end OrbitMarkings

section AssembleOrbitFactors

open Specs.Pinning (PinnedGroup)
open Specs.RootGroups (AdditiveLine)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.QuasiSplitInducedWeilProduct (ProductDescent OrbitWeilRestriction)
open Specs.AdjointCocharacters (coordinateHopfIso)
open private presentationIso presentationIso_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
open private extendedIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

variable {F K I : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  [IsGalois F K] [MulAction Gal(K/F) I]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
private def orbitFactorOfWeil {a : ProductDescent (F := F) (K := K) (I := I)} {c : I}
    {A : AdditiveLine F} {P : PinnedGroup A} (D : AttachedDatum P.pair)
    (hD : corootLattice D = ⊤)
    (hc : (integralDiagram (integralCartan D.toBased.datum D.toBased.base)).IsConnected)
    (S : BorelPair P.pair.G) (hs : IsSplitTorus S.torus.group)
    (z : OrbitWeilRestriction a c)
    {s : Marking → ProductDescent (F := F) (K := K) (I := I)}
    (v : ∀ m, OrbitWeilRestriction (s m) c)
    (g : ∀ m, z.descended.coordinate ⟶ (v m).descended.coordinate)
    (hg : ∀ m, Function.Surjective (g m).hom)
    (f : ∀ m, (v m).restriction.val ⟶ z.restriction.val)
    (hf : ∀ m, IsClosedImmersion (f m).hom.hom.left)
    (hn : ∀ m, (groupPointsFunctor F).map (f m) ≫ z.weil.hom =
      (v m).weil.hom ≫ Functor.whiskerLeft
        (WeilRestriction.extendScalars F (orbitField (F := F) (K := K) c))
        ((groupPointsFunctor _).map (specGroupMap (g m))))
    (hP : extensionCoordinates (K := K) P.pair.G = a.factor c)
    (i : extendedCoordinate (K := K) P.pair.G ≅ extendedHopf K z.descended.coordinate)
    (hi : i.hom = eqToHom hP ≫ z.descended.comparison.inv)
    (j : ∀ m, extendedCoordinate (K := K) (closedSubgroupAlgebraicGroup (S.subgroup m)) ≅
      extendedHopf K (v m).descended.coordinate)
    (hj : ∀ m, i.hom ≫ extendedHopfMap K (g m) =
      extendedPullback (G := closedSubgroupAlgebraicGroup (S.subgroup m)) (H := P.pair.G)
        (S.subgroup m).inclusion ≫ (j m).hom) : OrbitFactor a c S := by
  let L := orbitField (F := F) (K := K) c
  let H := descendedGroup z
  let B := z.descended.coordinate
  let C (m : Marking) := (v m).descended.coordinate
  let e := coordinateIsoWithPresentation (G := P.pair.G) (H := H) (Iso.refl (specGroup B)) i
  choose N cmp hN hcmp hm using markedOrbitGeometry (E := L) (G := P.pair.G)
    P.pair.reductive S hs B z.descended.finiteType C g hg i j hj
  have hgeom : IsAbsolutelyAlmostSimple H ∧ GeometricallySimplyConnected H :=
    simpleFormOfConnectedDiagram D hD hc cmp.groupIso
  let U (m : Marking) : ClosedSubgroup z.restriction.val := ⟨(v m).restriction.val, f m, hf m⟩
  have represent (m : Marking) (V : ClosedSubgroup H.val)
      (hV : V = closedFromHopf (g m) (hg m)) :
      ∃ η : (groupPointsFunctor F).obj (U m).group ≅
          WeilRestriction.extendScalars F L ⋙ (groupPointsFunctor L).obj V.group,
        (groupPointsFunctor F).map (U m).inclusion ≫ z.weil.hom =
          η.hom ≫ Functor.whiskerLeft (WeilRestriction.extendScalars F L)
            ((groupPointsFunctor L).map V.inclusion) := by
    subst V
    exact ⟨(v m).weil, hn m⟩
  choose η hη using fun m => represent m (N.subgroup m) (hN m)
  refine { orbit := z
           pair := N
           quasiSplit := ⟨reductive_of_semisimple H hgeom.1.1, N.positive, N.positiveBorel⟩
           absolutelyAlmostSimple := hgeom.1
           simplyConnected := hgeom.2
           comparison := cmp
           comparisonCoordinate := e
           comparisonMatches := hm
           factorPresentation := hP
           comparisonPresents := ?_
           restrictedSubgroup := U
           weilSubgroup := η
           weilCommutes := hη }
  let p := presentationIso H B (Iso.refl (specGroup B))
  refine ⟨p, ?_, ?_⟩
  · simpa only [Iso.refl_hom, Category.id_comp] using presentationIso_spec H B (Iso.refl (specGroup B))
  · let q := extendedIso K p
    change (i.hom ≫ q.inv) ≫ q.hom = _
    rw [Category.assoc, q.inv_hom_id, Category.comp_id, hi]

end AssembleOrbitFactors

section OrbitAssembly

open Specs.Pinning (PinnedGroup PinnedIso)
open Specs.RootGroups (AdditiveLine)
open Specs.AdjointBorelCohomology (PinnedTwist)
open Specs.AdjointCocharacters (coordinateHopfIso)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.QuasiSplitInducedWeilProduct (ProductDescent ProductInclusion OrbitWeilRestriction)
open private coordinatePresentationMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
open private coroot_span_of_equiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private connectedDiagram_of_basedIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct
open private range_under_product_equiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]

private def productThroughIso {C J : Type*} [Category C] {X Y : C} {Z : J → C}
    (p : ∀ j, X ⟶ Z j) (h : IsLimit (Fan.mk X p)) (e : Y ≅ X) :
    IsLimit (Fan.mk Y (fun j => e.hom ≫ p j)) :=
  IsLimit.ofIsoLimit h <| Fan.ext e.symm fun j => (e.inv_hom_id_assoc (p j)).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2300000 in
private theorem orbitProductOfMarkedProjections {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup F}
    {M : BorelPair G} {S : BorelPair P.pair.G} (W : SplitComponents D S)
    (w : PinnedTwist K D l M.positive M.torus)
    (cmp : Specs.QuasiSplitPinnedPairModel.MarkedComparison (K := K) S M)
    (hcmp : Specs.QuasiSplitPinnedPairModel.MatchesCoordinateComparison cmp w.groupIso)
    [MulAction Gal(K/F) (Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased)]
    (t : ∀ (σ : Gal(K/F)) c, PinnedIso (W.factors.factor c) (W.factors.factor (σ • c)))
    (ht : ∀ σ c, (l (w.outer σ)).asIso.hom.group.hom ≫ W.product.projection (σ • c) =
      W.product.projection c ≫ (t σ c).group.hom)
    (d : ProjectedDescent (Q := fun c => (W.factors.factor c).pair.G) W.product.projection w.groupIso) :
    let O := MulAction.orbitRel.Quotient Gal(K/F) (Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased)
    ∃ (pieces : ∀ o : O, OrbitFactor d.productDescent o.out (W.pairs o.out))
      (p : OrbitProduct M pieces),
      ∀ o, p.project o = (coordinateHopfIso G).inv ≫ (pieces o).orbit.projection := by
  classical
  let C := Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased
  intro O
  letI : Finite C := Quotient.finite _
  let Q (c : C) := (W.factors.factor c).pair.G
  let U (m : Marking) (c : C) := closedSubgroupAlgebraicGroup ((W.pairs c).subgroup m)
  let V (m : Marking) := closedSubgroupAlgebraicGroup (S.subgroup m)
  let X (m : Marking) := closedSubgroupAlgebraicGroup (M.subgroup m)
  obtain ⟨j, s, hs⟩ := markedProjectionDescent W w cmp hcmp t ht
  let a := d.productDescent
  let b (m : Marking) := (s m).productDescent
  let J (m : Marking) : ProductInclusion a (b m) :=
    projectedInclusion (G := P.pair.G) (H := G) (V := V m) (W := X m)
      (Q := Q) (U := U m) d (s m) (S.subgroup m).inclusion (M.subgroup m).inclusion
      (fun c => ((W.pairs c).subgroup m).inclusion)
      (fun c => ((W.pairs c).subgroup m).isClosedImmersion) (W.product.commutes m) (hs m)
  obtain ⟨z, ⟨hz⟩, _⟩ := QuasiSplitInducedWeilProduct.inducedWeilProduct a
  choose v hv using fun m => QuasiSplitInducedWeilProduct.inducedWeilProduct (b m)
  choose g f h using fun m => QuasiSplitInducedWeilProduct.inducedWeilProductInclusions (J m) z (v m)
  have hfull (c : C) : corootLattice (W.factors.attached c) = ⊤ := by
    let B := (W.factors.coordinates.blocks c).block.datum
    let E := (W.factors.attached c).toBased
    let := B.finiteRoots
    let := E.finiteRoots
    exact coroot_span_of_equiv B.datum E.datum (W.factors.based c).val
      (W.factors.coordinates.blocks c).block.fullCorootLattice
  have hconnected (c : C) := connectedDiagram_of_basedIso (W.factors.based c)
    (componentDiagramConnected D.toBased (W.factors.coordinates.blocks c).block)
  have hsplit (c : C) : Specs.GeometricRadicals.IsSplitTorus (W.pairs c).torus.group :=
    (W.torus_eq c).symm ▸ (W.factors.factor c).pair.split
  have hfactor (o : O) (m : Marking) :
      (z o).descended.comparison.inv ≫ extendedHopfMap K (g m o) =
        extendedPullback (G := U m o.out) (H := Q o.out) ((W.pairs o.out).subgroup m).inclusion ≫
          (v m o).descended.comparison.inv :=
    (inverseIsoSquare (z o).descended.comparison (v m o).descended.comparison
      (extendedHopfMap K (g m o)) ((J m).factor o.out) ((h m).1 o).2.2.1.symm).symm
  let pieces (o : O) : OrbitFactor a o.out (W.pairs o.out) :=
    orbitFactorOfWeil (W.factors.attached o.out) (hfull o.out) (hconnected o.out)
      (W.pairs o.out) (hsplit o.out) (z o) (s := b) (fun m => v m o)
      (fun m => g m o) (fun m => ((h m).1 o).1)
      (fun m => f m o) (fun m => ((h m).1 o).2.1) (fun m => ((h m).1 o).2.2.2.2)
      rfl (z o).descended.comparison.symm (Category.id_comp _).symm
      (fun m => (v m o).descended.comparison.symm) (hfactor o)
  let p (o : O) : G.val ⟶ (z o).restriction.val := (coordinateHopfIso G).inv ≫ (z o).projection
  let q (m : Marking) (o : O) : (X m).val ⟶ (v m o).restriction.val :=
    (coordinateHopfIso (X m)).inv ≫ (v m o).projection
  have hq (m : Marking) (o : O) : (M.subgroup m).inclusion ≫ p o = q m o ≫ f m o := by
    let e := coordinateHopfIso G
    let e' := coordinateHopfIso (X m)
    have he : specGroupMap (J m).ground = e'.hom ≫ (M.subgroup m).inclusion ≫ e.inv :=
      coordinatePresentationMap (G := X m) (H := G) (M.subgroup m).inclusion
    have hh := ((h m).1 o).2.2.2.1
    change (M.subgroup m).inclusion ≫ e.inv ≫ (z o).projection =
      (e'.inv ≫ (v m o).projection) ≫ f m o
    rw [Category.assoc, ← hh, he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ⟨pieces, {
    project := p
    markedProject := q
    projectCommutes := hq
    product := productThroughIso (fun o => (z o).projection) hz (coordinateHopfIso G).symm
    markedProduct := fun m => productThroughIso (fun o => (v m o).projection)
      (Classical.choice (hv m).1) (coordinateHopfIso (X m)).symm }, fun _ => rfl⟩

omit [IsGalois F K] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1700000 in
private theorem orbitProductFieldPoints {I : Type u} [Finite I] [MulAction Gal(K/F) I]
    {G : AffineAlgebraicGroup F} {M : BorelPair G} {Q : I → AffineAlgebraicGroup F}
    {S : ∀ c, BorelPair (Q c)} {a : ProductDescent (F := F) (K := K) (I := I)}
    (pieces : ∀ o : MulAction.orbitRel.Quotient Gal(K/F) I, OrbitFactor a o.out (S o.out))
    (p : OrbitProduct M pieces) :
    let O := MulAction.orbitRel.Quotient Gal(K/F) I
    ∃ points : ((groupPointsFunctor F).obj G.val).obj (CommAlgCat.of F F) ≃*
        (∀ o : O, ((groupPointsFunctor _).obj (descendedGroup (pieces o).orbit).val).obj
          (CommAlgCat.of _ _)),
      (∀ x o, points x o = (weilFieldPointIso F _ (pieces o).orbit.weil).hom
        (((groupPointsFunctor F).map (p.project o)).app _ x)) ∧
      ∀ m x,
        x ∈ (((groupPointsFunctor F).map (M.subgroup m).inclusion).app
          (CommAlgCat.of F F)).hom.range ↔
        ∀ o : O, points x o ∈ (((groupPointsFunctor _).map ((pieces o).pair.subgroup m).inclusion).app
          (CommAlgCat.of _ _)).hom.range := by
  intro O
  letI : Finite O := Quotient.finite _
  let R := CommAlgCat.of F F
  let L (o : O) := orbitField (F := F) (K := K) o.out
  let e := (productPointsEquiv _ p.product R).trans
    (MulEquiv.piCongrRight (fun o => (weilFieldPointIso F (L o) (pieces o).orbit.weil).groupIsoToMulEquiv))
  refine ⟨e, fun _ _ => rfl, ?_⟩
  intro m x
  let d := (productPointsEquiv _ (p.markedProduct m) R).trans
    (MulEquiv.piCongrRight (fun o => (weilFieldPointIso F (L o) ((pieces o).weilSubgroup m)).groupIsoToMulEquiv))
  let f := ((groupPointsFunctor F).map (M.subgroup m).inclusion).app R
  let g (o : O) := ((groupPointsFunctor (L o)).map ((pieces o).pair.subgroup m).inclusion).app
    (CommAlgCat.of (L o) (L o))
  refine range_under_product_equiv d.toEquiv e.toEquiv f (fun o y => g o y) ?_ x
  intro y o
  let a := ((groupPointsFunctor F).map (p.project o)).app R
  let b := ((groupPointsFunctor F).map (p.markedProject m o)).app R
  let c := ((groupPointsFunctor F).map ((pieces o).restrictedSubgroup m).inclusion).app R
  let w := weilFieldPointIso F (L o) (pieces o).orbit.weil
  let v := weilFieldPointIso F (L o) ((pieces o).weilSubgroup m)
  have h := NatTrans.congr_app (congrArg (groupPointsFunctor F).map (p.projectCommutes m o)) R
  simp only [Functor.map_comp, NatTrans.comp_app] at h
  have h' : f ≫ a = b ≫ c := h
  have hn : c ≫ w.hom = v.hom ≫ g o :=
    weilFieldPointsRespectInclusions F (L o) ((pieces o).restrictedSubgroup m).inclusion
      ((pieces o).pair.subgroup m).inclusion ((pieces o).weilSubgroup m) (pieces o).orbit.weil
      ((pieces o).weilCommutes m)
  change w.hom (a (f y)) = g o (v.hom (b y))
  rw [show a (f y) = c (b y) from ConcreteCategory.congr_hom h' y]
  exact ConcreteCategory.congr_hom hn (b y)

open private standard transport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open Specs.AdjointCocharacters renaming coordinateHopf -> affineCoordinateHopf

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1700000 in
private theorem descendSplitComponents {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup F}
    {M : BorelPair G} {S : BorelPair P.pair.G} (W : SplitComponents D S)
    (w : PinnedTwist K D l M.positive M.torus)
    (hl : Specs.QuasiSplitPinnedPairModel.IsBasedLift D l)
    (cmp : Specs.QuasiSplitPinnedPairModel.MarkedComparison (K := K) S M)
    (hcmp : Specs.QuasiSplitPinnedPairModel.MatchesCoordinateComparison cmp w.groupIso)
    [MulAction Gal(K/F) (Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased)]
    (hρ : ∀ (σ : Gal(K/F)) (i : D.toBased.base.support),
      σ • component (A := integralCartan D.toBased.datum D.toBased.base) i =
        component (A := integralCartan D.toBased.datum D.toBased.base)
          (simplePermutation D.toBased (w.outer σ) i)) : DescentOfSplitComponents w W := by
  let C := Specs.QuasiSplitPinnedProduct.DatumComponents D.toBased
  letI : Finite C := Quotient.finite _
  let Q (c : C) := (W.factors.factor c).pair.G
  obtain ⟨t, ht⟩ := splitComponentsTransport W w.outer l (fun a => (hl a).1) hρ
  let d : ProjectedDescent (Q := Q) W.product.projection w.groupIso :=
    splitProductOfProjections (Q := Q) W.product.projection W.product.product w.groupIso
      (fun σ c => (t σ c).group)
      (splitTransportOfPinnedMaps (Q := Q) W.product.projection w.groupIso
        (fun σ => (l (w.outer σ)).asIso.hom.group) (pinnedTwist_action w) (fun σ c => (t σ c).group) ht)
  obtain ⟨pieces, p, hp⟩ := orbitProductOfMarkedProjections W w cmp hcmp t ht d
  refine ⟨t, d, pieces, p, ht, ?_, hp, orbitProductFieldPoints pieces p⟩
  intro σ c j h x
  let e : (Q c).val ≅ (Q j).val := h ▸ (t σ c).group
  exact semilinearFactorTransport_apply (G := Q c) (H := Q j) σ e x

end OrbitAssembly

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Component descent for the prescribed opposite Borels and their radicals over any field. -/
theorem componentDescent : Statement.{u} := by
  intro F _ G hG hsc M
  obtain ⟨K, hK, hFK, hfd, hGal, A, P, D, lift, w, S, hB, hT, _, hD, hl, _, ha, cmp, hc⟩ :=
    QuasiSplitPinnedPairModel.initialPinnedComparison G hG hsc M
  letI := hK
  letI := hFK
  letI := hfd
  letI := hGal
  obtain ⟨W⟩ := splitComponentsExist P D S hB hT hD
  obtain ⟨ρ, hρ⟩ := basedComponentAction D.toBased w.outer
  letI := ρ
  exact ⟨K, hK, hFK, hfd, hGal, A, P, D, lift, w, S, hB, hT, hD, hl, ha,
    ⟨cmp, hc⟩, W, ρ, hρ, descendSplitComponents W w hl cmp hc hρ⟩

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitComponentDescent
