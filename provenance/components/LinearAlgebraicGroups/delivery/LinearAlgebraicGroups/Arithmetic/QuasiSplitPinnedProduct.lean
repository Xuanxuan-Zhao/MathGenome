import Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct
import LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Set Module

universe u v

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct

open Specs.QuasiSplitPinnedProduct
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
  · simp [Adjacent, hij]
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
  simp [Adjacent, hij, mul_eq_zero, hzero]

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
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

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
  obtain ⟨x, y, hx, hy, hpair, hsupp⟩ := rootComponentCoordinates P B h
  refine ⟨x, y, hpair, hy, hsupp, ?_⟩
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

open Specs.Pinning (AttachedDatum PinnedGroup PinnedIso transportCharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.SimplyConnectedLattice (corootLattice)
open private coroot_span_of_equiv from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private of_fullCorootLattice from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

theorem pinnedComponentModels : PinnedComponentModels.{u} := by
  classical
  intro F _ A P D h B
  let := B.finiteRoots
  let := B.reduced
  obtain ⟨_, _, _, _, _, hdata⟩ := rootComponentData B.datum B.base h
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


set_option backward.isDefEq.respectTransparency false in
theorem pinnedFactorsExist : PinnedFactorsExist.{u} := by
  classical
  intro F _ A P D hD
  let B := D.toBased
  letI := B.finiteRoots
  letI := B.reduced
  obtain ⟨x, y, hxy, hy, hsupp, hblocks⟩ := rootComponentData B.datum B.base hD
  have hex (c : DatumComponents B) : Nonempty (BlockCoordinates B x y c) := by
    obtain ⟨b, a, v, w, hp, hr, hc, hb⟩ := hblocks c
    exact ⟨⟨b, a, v, w, hp, hr, hc, hb⟩⟩
  let coords : ComponentCoordinates B := ⟨x, y, hxy, hy, hsupp, fun c => (hex c).some⟩
  obtain ⟨d, f, hobj, _, hf, _⟩ := Classification.PinnedEquivalence.pinnedEquivalence.1 A
  letI := hf
  let Q (c : DatumComponents B) := f.objPreimage (coords.blocks c).block.datum
  let e (c : DatumComponents B) :=
    (f.objObjPreimageIso (coords.blocks c).block.datum).symm ≪≫ eqToIso (hobj (Q c))
  have hE (c : DatumComponents B) : corootLattice (d (Q c)) = ⊤ := by
    letI := (d (Q c)).comm
    letI := (coords.blocks c).block.datum.finiteRoots
    exact coroot_span_of_equiv _ _ (e c).hom.val (coords.blocks c).block.fullCorootLattice
  let hs (c : DatumComponents B) := of_fullCorootLattice (Q c).pair (d (Q c)) (hE c)
  refine ⟨⟨coords, Q, (fun c => d (Q c)), (fun c => (e c).hom), hs, fun c => ?_⟩⟩
  let E := d (Q c)
  letI := E.comm
  exact (Classification.SimplyConnectedLattice.latticeCriterion (Q c).pair.G (hs c)
    (Q c).pair.T (Q c).pair.split (Q c).pair.maximal E.datum).mpr (hE c)

open Specs.BorelsAndChambers (subgroupRoots IsPositiveSystem)
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag

theorem splitMarkingsExist : SplitMarkingsExist.{u} := by
  intro F _ P
  obtain ⟨_, _, _, hcor, _, _, hdec⟩ :=
    RootData.BorelPositivity.borelPositivity P.G P.reductive P.T P.split P.maximal
  obtain ⟨l, hreg, hpos⟩ := hcor.1 P.B P.borel P.containsTorus
  have hneg : IsPositiveSystem P.T (subgroupRoots P.T P.B)ᶜ := by
    refine ⟨-l, fun α => neg_ne_zero.mpr (hreg α), ?_⟩
    rw [hpos]
    ext α
    change ¬ 0 < l (Additive.ofMul α.val) ↔ 0 < -(l (Additive.ofMul α.val))
    exact ⟨fun h => neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) (hreg α)),
      fun h => not_lt_of_ge (neg_pos.mp h).le⟩
  obtain ⟨C, hC, hTC, hCroots⟩ := hcor.2.1 _ hneg
  obtain ⟨U, _, _, hU, _⟩ := hdec P.B P.borel P.containsTorus
  obtain ⟨V, _, _, hV, _⟩ := hdec C hC hTC
  exact ⟨⟨P.B, C, P.T, U, V, P.borel, hC, lattice_torus_of_split P.split,
    P.maximal, P.containsTorus, hTC, hCroots, hU, hV⟩, rfl, rfl⟩

section Tori

open Specs.CharacterDescent (Character)
open Specs.CellHomomorphism (pullbackCharacters)
open scoped CategoryTheory.MonObj
open private torusMapOfCharacters from LinearAlgebraicGroups.Classification.OrdinaryCentralLifting
open private split_character_hom_ext from LinearAlgebraicGroups.Classification.NormalizerComparison
open private postcompose from LinearAlgebraicGroups.Reductive.CentralDerived

variable {F : Type u} [Field F] {A : AdditiveLine F} {P : PinnedGroup A}
variable {D : AttachedDatum P.pair} (W : PinnedFactors D)

private def factorWeightCoordinates (c : DatumComponents D.toBased) :
    Additive (Character (W.factor c).pair.T.group) ≃ₗ[ℤ] (BlockVertices D.toBased c → ℤ) :=
  (W.based c).val.weightEquiv.symm.trans (W.coordinates.blocks c).weights

private def extendCoordinates (c : DatumComponents D.toBased)
    (χ : Additive (Character (W.factor c).pair.T.group)) (i : D.toBased.base.support) : ℤ :=
  @dite ℤ (component i = c) (Classical.propDecidable _) (fun h => factorWeightCoordinates W c χ ⟨i, h⟩)
    (fun _ => 0)

private def extendCharacter (c : DatumComponents D.toBased) :
    Additive (Character (W.factor c).pair.T.group) →ₗ[ℤ] Additive (Character P.pair.T.group) := by
  classical
  let x := W.coordinates.weights
  let L : Additive (Character (W.factor c).pair.T.group) →ₗ[ℤ] (D.toBased.base.support → ℤ) :=
    { toFun := extendCoordinates W c
      map_add' := fun χ ψ => funext fun i => by
        by_cases h : component i = c <;> simp [extendCoordinates, h]
      map_smul' := fun n χ => funext fun i => by
        by_cases h : component i = c <;> simp [extendCoordinates, h] }
  exact x.symm.toLinearMap.comp L

private theorem extendCharacter_apply (c : DatumComponents D.toBased)
    (χ : Additive (Character (W.factor c).pair.T.group)) (i : D.toBased.base.support) :
    letI := Classical.decEq (DatumComponents D.toBased)
    W.coordinates.weights (extendCharacter W c χ) i =
      if h : component i = c then factorWeightCoordinates W c χ ⟨i, h⟩ else 0 := by
  classical
  change W.coordinates.weights (W.coordinates.weights.symm (extendCoordinates W c χ)) i = _
  rw [LinearEquiv.apply_symm_apply]
  by_cases h : component i = c <;> simp [extendCoordinates, h]

private def restrictCharacter (c : DatumComponents D.toBased) :
    Additive (Character P.pair.T.group) →ₗ[ℤ] Additive (Character (W.factor c).pair.T.group) := by
  let L : Additive (Character P.pair.T.group) →ₗ[ℤ] (BlockVertices D.toBased c → ℤ) :=
    { toFun := fun χ i => W.coordinates.weights χ i.val
      map_add' := fun χ ψ => funext fun i => congrFun (map_add W.coordinates.weights χ ψ) i.val
      map_smul' := fun n χ => funext fun i => congrFun (map_smul W.coordinates.weights n χ) i.val }
  exact (factorWeightCoordinates W c).symm.toLinearMap.comp L

private theorem restrictCharacter_apply (c : DatumComponents D.toBased)
    (χ : Additive (Character P.pair.T.group)) (i : BlockVertices D.toBased c) :
    factorWeightCoordinates W c (restrictCharacter W c χ) i = W.coordinates.weights χ i.val :=
  congrFun ((factorWeightCoordinates W c).apply_symm_apply _) i

private theorem blockProjectionsLimit {I : Type u} [Fintype I]
    {T : GroupScheme F} {S : I → GroupScheme F}
    [IsCommMonObj T.X] [∀ i, IsCommMonObj (S i).X]
    (p : ∀ i, T ⟶ S i) (s : ∀ i, S i ⟶ T)
    (hdiag : ∀ i, s i ≫ p i = 𝟙 (S i))
    (hoff : ∀ i j, i ≠ j → s i ≫ p j = 0)
    (hsum : (∏ i, p i ≫ s i) = 𝟙 T) :
    Nonempty (IsLimit (Fan.mk T p)) := by
  classical
  have precomp_prod {X : GroupScheme F} (f : X ⟶ T) (g : I → (T ⟶ T)) :
      f ≫ (∏ i, g i) = ∏ i, f ≫ g i := by
    let m : (T ⟶ T) →* (X ⟶ T) :=
      { toFun := (f ≫ ·)
        map_one' := by apply Grp.hom_ext; exact MonObj.comp_one _
        map_mul' := fun _ _ => by apply Grp.hom_ext; exact MonObj.comp_mul _ _ _ }
    exact map_prod m _ _
  refine ⟨Fan.IsLimit.mk (Fan.mk T p) (fun q => (show q.pt ⟶ T from ∏ i, q.proj i ≫ s i)) ?_ ?_⟩
  · intro q j
    change postcompose (p j) (∏ i, q.proj i ≫ s i) = q.proj j
    rw [map_prod, Finset.prod_eq_single j]
    · change (q.proj j ≫ s j) ≫ p j = _
      rw [Category.assoc, hdiag, Category.comp_id]
    · intro i _ hij
      change (q.proj i ≫ s i) ≫ p j = 1
      rw [Category.assoc, hoff i j hij, comp_zero]
      rfl
    · simp
  · intro q m hm
    change (q.pt ⟶ T) at m
    change m = (show q.pt ⟶ T from ∏ i, q.proj i ≫ s i)
    have hmi (i : I) : m ≫ p i = q.proj i := hm i
    calc
      m = m ≫ (∏ i, p i ≫ s i) := by rw [hsum, Category.comp_id]
      _ = _ := by
        rw [precomp_prod]
        apply Finset.prod_congr rfl
        intro i _
        rw [← Category.assoc]
        exact congrArg (· ≫ s i) (hmi i)

set_option backward.isDefEq.respectTransparency false in
theorem splitTorusComponentProduct : SplitTorusComponentProduct.{u} := by
  classical
  intro F _ A P D W
  let C := DatumComponents D.toBased
  let T := P.pair.T.group
  let S (c : C) := (W.factor c).pair.T.group
  letI : Finite C := Quotient.finite _
  letI : Fintype C := Fintype.ofFinite C
  letI : IsCommMonObj T.X := D.comm
  letI : ∀ c, IsCommMonObj (S c).X := fun c => (W.attached c).comm
  choose p hp _ using fun c : C => torusMapOfCharacters P.pair.split
    (W.factor c).pair.split ((extendCharacter W c).toAddMonoidHom.toMultiplicative)
  choose s hs _ using fun c : C => torusMapOfCharacters (W.factor c).pair.split
    P.pair.split ((restrictCharacter W c).toAddMonoidHom.toMultiplicative)
  have hp' (c : C) (χ : Character (S c)) : Additive.ofMul (p c ≫ χ) =
      extendCharacter W c (Additive.ofMul χ) := DFunLike.congr_fun (hp c) χ
  have hs' (c : C) (χ : Character T) : Additive.ofMul (s c ≫ χ) =
      restrictCharacter W c (Additive.ofMul χ) := DFunLike.congr_fun (hs c) χ
  have hdiag (c : C) : s c ≫ p c = 𝟙 (S c) := by
    apply split_character_hom_ext (W.factor c).pair.split (W.factor c).pair.split
    intro χ
    rw [Category.assoc, Category.id_comp]
    apply (factorWeightCoordinates W c).injective
    funext i
    change factorWeightCoordinates W c (Additive.ofMul (s c ≫ p c ≫ χ)) i =
      factorWeightCoordinates W c (Additive.ofMul χ) i
    rw [hs' c (p c ≫ χ), restrictCharacter_apply, hp' c χ, extendCharacter_apply,
      dite_eq_left i.property]
  have hoff (c d : C) (h : c ≠ d) : s c ≫ p d = 0 := by
    apply split_character_hom_ext (W.factor c).pair.split (W.factor d).pair.split
    intro χ
    rw [Category.assoc, zero_comp]
    apply (factorWeightCoordinates W c).injective
    funext i
    change factorWeightCoordinates W c (Additive.ofMul (s c ≫ p d ≫ χ)) i =
      factorWeightCoordinates W c 0 i
    rw [hs' c (p d ≫ χ), restrictCharacter_apply, hp' d χ, extendCharacter_apply,
      dite_eq_right (i.property.trans_ne h)]
    exact (congrFun ((factorWeightCoordinates W c).map_zero) i).symm
  have hsum : (∏ i : C, p i ≫ s i) = 𝟙 T := by
    apply split_character_hom_ext P.pair.split P.pair.split
    intro χ
    change postcompose χ (∏ j : C, p j ≫ s j) = 𝟙 T ≫ χ
    rw [map_prod, Category.id_comp]
    have hχ (j : C) : Additive.ofMul ((p j ≫ s j) ≫ χ) =
        extendCharacter W j (restrictCharacter W j (Additive.ofMul χ)) := by
      rw [Category.assoc, hp', hs']
    let w : Additive (Character T) ≃ₗ[ℤ] (D.toBased.base.support → ℤ) := W.coordinates.weights
    apply (show Function.Injective (fun ψ : Character T => w (Additive.ofMul ψ))
      from w.injective)
    change w (Additive.ofMul (∏ j : C, (p j ≫ s j) ≫ χ)) = w (Additive.ofMul χ)
    rw [ofMul_prod]
    change w.toLinearMap _ = _
    rw [map_sum w.toLinearMap]
    funext i
    rw [Finset.sum_apply]
    let z : C → Additive (Character T) := fun j => Additive.ofMul ((p j ≫ s j) ≫ χ)
    change (∑ j : C, w (z j) i) = w (Additive.ofMul χ) i
    have ht (j : C) : w (z j) i =
        if h : component i = j then factorWeightCoordinates W j
          (restrictCharacter W j (Additive.ofMul χ)) ⟨i, h⟩ else 0 := by
      have ht := (congrArg (fun x : Additive (Character T) => w x i) (hχ j)).trans
        (extendCharacter_apply W j (restrictCharacter W j (Additive.ofMul χ)) i)
      by_cases h : component i = j <;> simpa only [h, dite_eq_left, dite_eq_right] using ht
    simp_rw [ht]
    rw [Finset.sum_eq_single (component i)]
    · rw [dite_eq_left rfl, restrictCharacter_apply]
      rfl
    · intro j _ hj
      exact dite_eq_right hj.symm
    · simp
  refine ⟨p, ?_, blockProjectionsLimit p s hdiag hoff hsum⟩
  intro c χ i
  exact (congrArg (fun z => W.coordinates.weights z i) (hp' c χ)).trans
    (extendCharacter_apply W c (Additive.ofMul χ) i)

end Tori

open Specs.Pinning (BasedIso)
open Specs.CharacterDescent (Character)
open Classification.Pinning (inducedBasedIso)
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence

set_option backward.isDefEq.respectTransparency false in
theorem pinnedFactorTransport : PinnedFactorTransport.{u} := by
  intro F Γ _ _ A P D W ω _ hρ
  obtain ⟨t, ht, _⟩ := basedComponentTransport D.toBased ω hρ
    (fun c => (W.coordinates.blocks c).block)
  let E (c : DatumComponents D.toBased) :
      (W.coordinates.blocks c).block.datum ≅ (W.attached c).toBased :=
    asIso (show (W.coordinates.blocks c).block.datum ⟶ (W.attached c).toBased from W.based c)
  let e (σ : Γ) (c : DatumComponents D.toBased) :
      BasedIso (W.attached c).toBased (W.attached (σ • c)).toBased :=
    (E c).inv ≫ t σ c ≫ (E (σ • c)).hom
  choose g hg using fun σ c => pinnedLift (W.factor c) (W.factor (σ • c))
    (W.attached c) (W.attached (σ • c)) (e σ c)
  have hmap (σ : Γ) (c : DatumComponents D.toBased) (χ : Character (W.factor c).pair.T.group) :
      (e σ c).val.weightEquiv (Additive.ofMul χ) =
        Additive.ofMul (transportCharacter (g σ c).torus χ) := by
    rw [← hg]
    rfl
  refine ⟨e, g, hmap, ?_⟩
  intro σ c i j hij
  let b := (W.coordinates.blocks c).block
  let b' := (W.coordinates.blocks (σ • c)).block
  let k := b.vertices.symm i
  let k' := b'.vertices.symm j
  have hk : (t σ c).val.indexEquiv k.val = k'.val := by
    apply (ht σ c k k').mpr
    change simplePermutation D.toBased (ω σ) (b.vertices (b.vertices.symm i)).val =
      (b'.vertices (b'.vertices.symm j)).val
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hcomp : (E c).hom ≫ e σ c = t σ c ≫ (E (σ • c)).hom := by
    change (E c).hom ≫ (E c).inv ≫ t σ c ≫ (E (σ • c)).hom = _
    rw [Iso.hom_inv_id_assoc]
  have hi := congrArg
    (fun l : b.datum ⟶ (W.attached (σ • c)).toBased => l.val.indexEquiv k.val) hcomp
  change (e σ c).val.indexEquiv ((W.based c).val.indexEquiv k.val) =
    (W.based (σ • c)).val.indexEquiv ((t σ c).val.indexEquiv k.val) at hi
  rw [hk] at hi
  let Δ := W.attached c
  let Δ' := W.attached (σ • c)
  letI := Δ.comm
  letI := Δ'.comm
  let α := (factorSimpleRoot W c i).val
  let β := (factorSimpleRoot W (σ • c) j).val
  have hindex : (e σ c).val.indexEquiv α = β := hi
  have hr := (e σ c).val.toHom.root_weightMap_apply Δ.toBased.datum Δ'.toBased.datum α
  change (e σ c).val.weightEquiv (Δ.datum.rootDatum.root α) =
    Δ'.datum.rootDatum.root ((e σ c).val.indexEquiv α) at hr
  rw [Δ.datum.root_eq, hindex, Δ'.datum.root_eq] at hr
  exact congrArg Additive.toMul ((hmap σ c α.val).symm.trans hr)

section Equivariance

open private split_character_hom_ext from LinearAlgebraicGroups.Classification.NormalizerComparison

open Specs.Pinning (BasedRootDatum SimpleRoot pinGraph)
open scoped CategoryTheory.MonObj

private theorem singlePairing {I : Type u} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (i : I) :
    (∑ j, (Pi.single i (1 : ℤ) : I → ℤ) j * a j) = a i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private theorem characterCoordinate_eq_pairing {D : BasedRootDatum.{u}}
    (C : ComponentCoordinates D) (χ : D.X) (i : D.base.support) :
    D.datum.toLinearMap χ (D.datum.coroot i.val) = C.weights χ i := by
  classical
  rw [C.pairing, C.simpleCoroot]
  exact singlePairing (C.weights χ) i

private theorem basedIso_pairing_coroot {D E : BasedRootDatum.{u}}
    (e : BasedIso D E) (χ : D.X) (i : D.I) :
    E.datum.toLinearMap (e.val.weightEquiv χ) (E.datum.coroot (e.val.indexEquiv i)) =
      D.datum.toLinearMap χ (D.datum.coroot i) := by
  have hp := DFunLike.congr_fun
    (e.val.toHom.weight_coweight_transpose_apply D.datum E.datum
      (E.datum.coroot (e.val.indexEquiv i))) χ
  change E.datum.toLinearMap (e.val.weightEquiv χ) (E.datum.coroot (e.val.indexEquiv i)) =
    D.datum.toLinearMap χ (e.val.coweightEquiv (E.datum.coroot (e.val.indexEquiv i))) at hp
  have h := e.val.toHom.coroot_coweightMap_apply D.datum E.datum (e.val.indexEquiv i)
  rw [e.val.indexEquiv.symm_apply_apply] at h
  rw [hp]
  exact congrArg (D.datum.toLinearMap χ) h

private theorem simpleCoordinates_transport {D : BasedRootDatum.{u}}
    (C : ComponentCoordinates D) (g : Aut D) (χ : D.X) (i : D.base.support) :
    C.weights (g.asIso.hom.val.weightEquiv χ) (simplePermutation D g i) = C.weights χ i := by
  rw [← characterCoordinate_eq_pairing, ← characterCoordinate_eq_pairing]
  exact basedIso_pairing_coroot g.asIso.hom χ i.val

variable {F : Type u} [Field F] {A : AdditiveLine F} {P : PinnedGroup A}
variable {D : AttachedDatum P.pair} (W : PinnedFactors D)

private theorem factorCharacterCoordinate_eq_pairing (c : DatumComponents D.toBased)
    (χ : (W.attached c).toBased.X) (i : BlockVertices D.toBased c) :
    (W.attached c).toBased.datum.toLinearMap χ
      ((W.attached c).toBased.datum.coroot (factorSimpleRoot W c i).val) =
      factorWeightCoordinates W c χ i := by
  classical
  let C := W.coordinates.blocks c
  let j := C.block.vertices.symm i
  let e := W.based c
  let a := e.val.weightEquiv.symm χ
  have hχ : e.val.weightEquiv a = χ := e.val.weightEquiv.apply_symm_apply χ
  have hj : (factorSimpleRoot W c i).val = e.val.indexEquiv j.val := rfl
  have hcoroot (j' : BlockVertices D.toBased c) :
      C.coweights (C.block.datum.datum.coroot j.val) j' = (Pi.single i 1 : BlockVertices D.toBased c → ℤ) j' := by
    change (C.coweights (C.block.datum.datum.coroot j.val)) j' = _
    rw [C.coroot_eq, C.base_eq j, C.block.vertices.apply_symm_apply, W.coordinates.simpleCoroot]
    by_cases h : i = j'
    · subst j'
      simp
    · have h' : i.val ≠ j'.val := fun h' => h (Subtype.ext h')
      simp [Pi.single_apply, Ne.symm h, Ne.symm h']
  calc
    _ = C.block.datum.datum.toLinearMap a (C.block.datum.datum.coroot j.val) := by
      have h := basedIso_pairing_coroot e a j.val
      simpa only [hχ, hj] using h
    _ = ∑ j', (Pi.single i 1 : BlockVertices D.toBased c → ℤ) j' * C.weights a j' := by
      rw [C.pairing]
      exact Finset.sum_congr (Finset.ext fun j' => by simp) fun j' _ =>
        congrArg (· * C.weights a j') (hcoroot j')
    _ = C.weights a i := singlePairing _ _
    _ = _ := rfl

private theorem pinnedCoordinate_transport {Q R : PinnedGroup A}
    (f : PinnedIso Q R) (i : SimpleRoot Q.pair) (j : SimpleRoot R.pair)
    (h : transportCharacter f.torus i.val.val = j.val.val) :
    pinnedCoordinate Q i ≫ f.group.hom = pinnedCoordinate R j := by
  have hmem : (transportCharacter f.torus i.val.val, pinnedCoordinate Q i ≫ f.group.hom)
      ∈ pinGraph R := by
    rw [← f.pin_comm]
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  obtain ⟨j', hj'⟩ := hmem
  have h' : j' = j := by
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg Prod.fst hj').trans h
  subst j'
  exact (congrArg Prod.snd hj').symm

set_option backward.isDefEq.respectTransparency false in
theorem torusProjectionEquivariance : TorusProjectionEquivariance.{u} := by
  classical
  intro F Γ _ _ A P D W ω _ hρ p hp
  obtain ⟨e, g, he, hg⟩ := pinnedFactorTransport W ω hρ
  refine ⟨g, fun σ c i j hij => pinnedCoordinate_transport (g σ c) _ _ (hg σ c i j hij), ?_⟩
  intro σ f hf c
  let d := σ • c
  let a := ω σ
  let b := e σ c
  let x : Additive (Character P.pair.T.group) ≃ₗ[ℤ] (D.toBased.base.support → ℤ) :=
    W.coordinates.weights
  apply split_character_hom_ext P.pair.split (W.factor d).pair.split
  intro χ
  rw [Category.assoc, Category.assoc]
  apply (show Function.Injective (fun z : Character P.pair.T.group => x (Additive.ofMul z)) from
    x.injective)
  funext i
  let j := simplePermutation D.toBased a i
  have hchar : a.asIso.hom.val.weightEquiv (Additive.ofMul (f.torus.hom ≫ p d ≫ χ)) =
      Additive.ofMul (p d ≫ χ) := by
    rw [hf]
    exact congrArg Additive.ofMul (f.torus.inv_hom_id_assoc (p d ≫ χ))
  have hi : x (Additive.ofMul (f.torus.hom ≫ p d ≫ χ)) i =
      x (Additive.ofMul (p d ≫ χ)) j := by
    have h := simpleCoordinates_transport W.coordinates a
      (Additive.ofMul (f.torus.hom ≫ p d ≫ χ)) i
    change x (a.asIso.hom.val.weightEquiv (Additive.ofMul (f.torus.hom ≫ p d ≫ χ))) j = _ at h
    rw [hchar] at h
    exact h.symm
  have hcomp : component j = d ↔ component i = c := by
    change component (simplePermutation D.toBased (ω σ) i) = σ • c ↔ _
    rw [← hρ, (MulAction.injective σ).eq_iff]
  change x (Additive.ofMul (f.torus.hom ≫ p d ≫ χ)) i =
    x (Additive.ofMul (p c ≫ (g σ c).torus.hom ≫ χ)) i
  rw [hi]
  have hleft := hp d χ j
  have hright := hp c ((g σ c).torus.hom ≫ χ) i
  change x (Additive.ofMul (p d ≫ χ)) j = _ at hleft
  change x (Additive.ofMul (p c ≫ (g σ c).torus.hom ≫ χ)) i = _ at hright
  rw [hleft, hright]
  by_cases h : component i = c
  · let i' : BlockVertices D.toBased c := ⟨i, h⟩
    let j' : BlockVertices D.toBased d := ⟨j, hcomp.mpr h⟩
    rw [dite_eq_left (hcomp.mpr h), dite_eq_left h]
    change factorWeightCoordinates W d (Additive.ofMul χ) j' =
      factorWeightCoordinates W c (Additive.ofMul ((g σ c).torus.hom ≫ χ)) i'
    rw [← factorCharacterCoordinate_eq_pairing, ← factorCharacterCoordinate_eq_pairing]
    have hχ : b.val.weightEquiv (Additive.ofMul ((g σ c).torus.hom ≫ χ)) = Additive.ofMul χ := by
      rw [he]
      exact congrArg Additive.ofMul ((g σ c).torus.inv_hom_id_assoc χ)
    let α := (factorSimpleRoot W c i').val
    let β := (factorSimpleRoot W d j').val
    have hindex : b.val.indexEquiv α = β := by
      have hroot := b.val.toHom.root_weightMap_apply (W.attached c).toBased.datum
        (W.attached d).toBased.datum α
      let E := W.attached c
      let E' := W.attached d
      letI := E.comm
      letI := E'.comm
      change b.val.weightEquiv (E.datum.rootDatum.root α) =
        E'.datum.rootDatum.root (b.val.indexEquiv α) at hroot
      rw [E.datum.root_eq, E'.datum.root_eq] at hroot
      have hm := he σ c α.val
      apply Subtype.ext
      exact congrArg Additive.toMul
        ((hroot.symm.trans hm).trans (congrArg Additive.ofMul (hg σ c i' j' rfl)))
    have hpair := basedIso_pairing_coroot b (Additive.ofMul ((g σ c).torus.hom ≫ χ)) α
    rw [hχ, hindex] at hpair
    exact hpair
  · rw [dite_eq_right (fun h' => h (hcomp.mp h')), dite_eq_right h]

private theorem productPermutationIso {C : Type*} [Category C]
    {I : Type u} [HasProductsOfShape I C] (H : I → C) {X : C}
    (p : ∀ i, X ⟶ H i) (hp : IsLimit (Fan.mk X p))
    (σ : Equiv.Perm I) (g : ∀ i, H i ≅ H (σ i)) :
    ∃ e : X ≅ X, ∀ i, e.hom ≫ p (σ i) = p i ≫ (g i).hom := by
  let a : X ≅ ∏ᶜ H := hp.conePointUniqueUpToIso (productIsProduct H)
  have ha (i : I) : a.hom ≫ Pi.π H i = p i :=
    hp.conePointUniqueUpToIso_hom_comp (productIsProduct H) ⟨i⟩
  have hb (i : I) : a.inv ≫ p i = Pi.π H i :=
    (productIsProduct H).conePointUniqueUpToIso_hom_comp hp ⟨i⟩
  let m := Pi.mapIso (f := H) (g := H ∘ σ) g
  let r := Pi.reindex σ H
  refine ⟨a ≪≫ m ≪≫ r ≪≫ a.symm, fun i => ?_⟩
  change (a.hom ≫ m.hom ≫ r.hom ≫ a.inv) ≫ p (σ i) = _
  simp only [Category.assoc, hb, r, Pi.reindex_hom_π, m, Pi.mapIso_hom_π]
  rw [← Category.assoc, ha]

private theorem automorphism_simpleCharacter {D : AttachedDatum P.pair}
    (g : Aut D.toBased) (f : PinnedIso P P) (h : LiftsBasedAutomorphism D g f)
    (i : D.toBased.base.support) :
    transportCharacter f.torus (labeledSimpleRoot D i).val.val =
      (labeledSimpleRoot D (simplePermutation D.toBased g i)).val.val := by
  let := D.comm
  let j := simplePermutation D.toBased g i
  have hr := g.asIso.hom.val.toHom.root_weightMap_apply D.toBased.datum D.toBased.datum i.val
  change g.asIso.hom.val.weightEquiv (D.datum.rootDatum.root i.val) =
    D.datum.rootDatum.root j.val at hr
  let α := (labeledSimpleRoot D i).val
  let β := (labeledSimpleRoot D j).val
  change g.asIso.hom.val.weightEquiv (D.datum.rootDatum.root α) = D.datum.rootDatum.root β at hr
  rw [D.datum.root_eq, D.datum.root_eq] at hr
  exact congrArg Additive.toMul ((h α.val).symm.trans hr)

set_option backward.isDefEq.respectTransparency false in
theorem productProjectionEquivariance : ProductProjectionEquivariance.{u} := by
  classical
  intro F _ A P D W p b t hp hb hB hT ht hpin hoff g f hf
  let C := DatumComponents D.toBased
  obtain ⟨ρ, hρ⟩ := basedComponentAction D.toBased (MonoidHom.id (Aut D.toBased))
  letI : MulAction (Aut D.toBased) C := ρ
  let σ : Equiv.Perm C := MulAction.toPerm g
  have hσ (i : D.toBased.base.support) :
      σ (component i) = component (simplePermutation D.toBased g i) := hρ g i
  obtain ⟨l, hl, htEquiv⟩ := torusProjectionEquivariance W (MonoidHom.id _) hρ t ht
  have hte (c : C) : f.torus.hom ≫ t (σ c) = t c ≫ (l g c).torus.hom :=
    htEquiv g f hf c
  obtain ⟨G, hG⟩ := productPermutationIso _ p hp σ (fun c => (l g c).group)
  obtain ⟨B, hB'⟩ := productPermutationIso _ b hb σ (fun c => (l g c).borel)
  have borel_square : P.pair.B.inclusion ≫ G.hom = B.hom ≫ P.pair.B.inclusion := by
    apply Fan.IsLimit.hom_ext hp
    intro d
    obtain ⟨c, rfl⟩ := σ.surjective d
    change (P.pair.B.inclusion ≫ G.hom) ≫ p (σ c) =
      (B.hom ≫ P.pair.B.inclusion) ≫ p (σ c)
    rw [Category.assoc, hG, ← Category.assoc, hB, Category.assoc,
      (l g c).borel_comm, Category.assoc, hB, ← Category.assoc]
    exact congrArg (· ≫ (W.factor (σ c)).pair.B.inclusion) (hB' c).symm
  have torus_square : P.pair.T.inclusion ≫ G.hom = f.torus.hom ≫ P.pair.T.inclusion := by
    apply Fan.IsLimit.hom_ext hp
    intro d
    obtain ⟨c, rfl⟩ := σ.surjective d
    change (P.pair.T.inclusion ≫ G.hom) ≫ p (σ c) =
      (f.torus.hom ≫ P.pair.T.inclusion) ≫ p (σ c)
    rw [Category.assoc, hG, ← Category.assoc, hT, Category.assoc,
      (l g c).torus_comm, Category.assoc, hT, ← Category.assoc]
    exact congrArg (· ≫ (W.factor (σ c)).pair.T.inclusion) (hte c).symm
  have pin_square (i : D.toBased.base.support) :
      pinnedCoordinate P (labeledSimpleRoot D i) ≫ G.hom =
      pinnedCoordinate P (labeledSimpleRoot D (simplePermutation D.toBased g i)) := by
    let j := simplePermutation D.toBased g i
    apply Fan.IsLimit.hom_ext hp
    intro d
    obtain ⟨c, rfl⟩ := σ.surjective d
    change (pinnedCoordinate P (labeledSimpleRoot D i) ≫ G.hom) ≫ p (σ c) =
      pinnedCoordinate P (labeledSimpleRoot D j) ≫ p (σ c)
    rw [Category.assoc, hG, ← Category.assoc]
    have hc : component j = σ c ↔ component i = c := by
      rw [← hσ i, σ.injective.eq_iff]
    by_cases h : component i = c
    · rw [hpin i c h, hpin j (σ c) (hc.mpr h)]
      exact hl g c ⟨i, h⟩ ⟨j, hc.mpr h⟩ rfl
    · rw [hoff i c h, zero_comp, hoff j (σ c) (fun hj => h (hc.mp hj))]
  let e : PinnedIso P P :=
    { group := G
      torus := f.torus
      borel := B
      torus_comm := torus_square
      borel_comm := borel_square
      pin_comm := by
        ext z
        constructor
        · rintro ⟨_, ⟨α, rfl⟩, rfl⟩
          let i : D.toBased.base.support := ⟨α.val, (D.simple_iff _).mpr α.property⟩
          let j := simplePermutation D.toBased g i
          exact ⟨labeledSimpleRoot D j,
            Prod.ext (automorphism_simpleCharacter g f hf i).symm (pin_square i).symm⟩
        · rintro ⟨β, rfl⟩
          let j : D.toBased.base.support := ⟨β.val, (D.simple_iff _).mpr β.property⟩
          obtain ⟨i, hi⟩ := (simplePermutation D.toBased g).surjective j
          refine ⟨_, ⟨labeledSimpleRoot D i, rfl⟩, Prod.ext ?_ ?_⟩
          · exact (automorphism_simpleCharacter g f hf i).trans
              (congrArg (fun k => (labeledSimpleRoot D k).val.val) hi)
          · exact (pin_square i).trans (congrArg (fun k => pinnedCoordinate P
              (labeledSimpleRoot D k)) hi) }
  have he : e = f := Classification.PinnedUniqueness.pinnedIsoUniqueness e f (fun _ => rfl)
  have hfg : G.hom = f.group.hom := congrArg (fun s : PinnedIso P P => s.group.hom) he
  exact ⟨σ, l g, hσ, fun c => hfg ▸ hG c, hte⟩

end Equivariance

section BinaryProducts

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSplitTorus IsMaximalTorus baseChangedSubgroup)
open Specs.Pinning (SplitBorelPair)
open private affineProduct from LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private reductive_of_groupIso from LinearAlgebraicGroups.RootData.RankOneFlag
open private productReductive productTorus splitProductTorus productTorus_geometricallyMaximal
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private splitBorelPair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private splitTorus_baseChange maximalTorus_of_geometricallyMaximal geometricallyMaximal_of_maximal_split
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private maximal_of_square from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components

variable {F : Type u} [Field F]

private theorem reductiveBinaryProduct (G H : AffineAlgebraicGroup F)
    (hG : IsReductive G) (hH : IsReductive H) : IsReductive (affineProduct G H) := by
  let K := AlgebraicClosure F
  let B := groupBaseChange F K
  let R := affineProduct G H
  letI := hG.1
  letI := hH.1
  letI := hG.2.1
  letI := hH.2.1
  have hs : Smooth R.val.X.hom := by
    change Smooth (G.val.X ⊗ H.val.X).hom
    rw [Over.tensorObj_hom]
    infer_instance
  have hc : GeometricallyConnected R.val.X.hom := by
    change GeometricallyConnected (G.val.X ⊗ H.val.X).hom
    rw [Over.tensorObj_hom]
    exact GeometricallyConnected.comp _ _
  let e : (GeometricGroup G).val ⊗ (GeometricGroup H).val ≅ (GeometricGroup R).val :=
    Functor.Monoidal.μIso B G.val H.val
  have hG' : IsReductive (GeometricGroup G) :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  have hH' : IsReductive (GeometricGroup H) :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) H hH.1 hH.2.1).mpr hH
  exact (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) R hs hc).mp
    (reductive_of_groupIso e (productReductive _ _ hG' hH'))

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
private def geometricSplitBorelPair (P : SplitBorelPair F) : SplitBorelPair (AlgebraicClosure F) := by
  let K := AlgebraicClosure F
  let B := groupBaseChange F K
  let h : IsClosedImmersion (B.map P.T.inclusion).hom.hom.left := P.maximal.choose
  let T : ClosedSubgroup (GeometricGroup P.G).val := baseChangedSubgroup K P.T h
  have hm : IsMaximalTorus T := P.maximal.choose_spec
  have hs : IsSplitTorus T.group := splitTorus_baseChange (K := K) P.split
  have hG : IsReductive (GeometricGroup P.G) :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) P.G
      P.reductive.1 P.reductive.2.1).mpr P.reductive
  exact splitBorelPair (GeometricGroup P.G) hG T hs
    (geometricallyMaximal_of_maximal_split (GeometricGroup P.G) T hm hs)

set_option backward.isDefEq.respectTransparency false in
theorem binarySplitReductiveProduct : BinarySplitReductiveProduct.{u} := by
  intro F _ P Q
  let R := affineProduct P.G Q.G
  let T := productTorus P Q
  refine ⟨R, Iso.refl _, T, Iso.refl _, ?_, reductiveBinaryProduct _ _
    P.reductive Q.reductive, splitProductTorus P Q, ?_⟩
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  let K := AlgebraicClosure F
  let B := groupBaseChange F K
  let P' := geometricSplitBorelPair P
  let Q' := geometricSplitBorelPair Q
  let R' := affineProduct P'.G Q'.G
  let T' := productTorus P' Q'
  let eg : R'.val ≅ (GeometricGroup R).val := Functor.Monoidal.μIso B P.G.val Q.G.val
  let et : T'.group ≅ B.obj T.group := Functor.Monoidal.μIso B P.T.group Q.T.group
  letI := T.isClosedImmersion
  have hclosed : IsClosedImmersion (B.map T.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback T.inclusion.hom.hom).flip inferInstance
  refine ⟨hclosed, ?_⟩
  let S := baseChangedSubgroup K T hclosed
  have hmax := maximalTorus_of_geometricallyMaximal R' T'
    (lattice_torus_of_split (splitProductTorus P' Q')) (productTorus_geometricallyMaximal P' Q')
  refine maximal_of_square eg T' S et ?_ hmax
  exact (Functor.LaxMonoidal.μ_natural B P.T.inclusion Q.T.inclusion).symm

end BinaryProducts

theorem emptyDiagramProduct : EmptyDiagramProduct.{u} := by
  intro F _ A P D M hD h
  let C := DatumComponents D.toBased
  letI : IsEmpty C := ⟨fun c => Quotient.inductionOn c h.false⟩
  obtain ⟨W⟩ := pinnedFactorsExist D hD
  let N : ∀ c, BorelPair (W.factor c).pair.G := fun c => isEmptyElim c
  obtain ⟨p⟩ := emptyMarkedSplitProduct P.pair D M hD h N
  refine ⟨W, N, fun c => isEmptyElim c, p, fun c => isEmptyElim c, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun c => isEmptyElim c
  · exact fun c => isEmptyElim c
  · exact fun _ c => isEmptyElim c
  · exact fun _ c => isEmptyElim c
  · intro _ _ _
    exact ⟨Equiv.refl C, fun c => isEmptyElim c, fun i => (h.false i).elim,
      fun c => isEmptyElim c, fun c => isEmptyElim c⟩

section InvariantLattices

open Specs.Pinning (BasedRootDatum)
open private corootFullRank from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private theorem nonzero_pairing_with_simple_root (D : BasedRootDatum.{u})
    (hY : Submodule.span ℤ (range D.datum.coroot) = ⊤)
    {y : D.Y} (hy : y ≠ 0) :
    ∃ i : D.base.support, D.datum.toLinearMap (D.datum.root i.val) y ≠ 0 := by
  classical
  let := D.finiteRoots
  let := D.freeX
  let := D.freeY
  let := D.finiteX
  let := D.finiteY
  let P := D.datum
  let L := Submodule.span ℤ (range P.root)
  have hf : Finite (D.X ⧸ L) := by
    apply (Submodule.finiteQuotient_iff L).mpr
    apply (corootFullRank P D.base).mp
    change finrank ℤ (Submodule.span ℤ (range P.coroot)) = finrank ℤ D.Y
    rw [hY, finrank_top]
  by_contra! hz
  let t : D.X →ₗ[ℤ] ℤ := P.toLinearMap.flip y
  have hL : L ≤ LinearMap.ker t := by
    change Submodule.span ℤ (range P.root) ≤ _
    rw [← D.base.span_int_root_support, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact LinearMap.mem_ker.mpr (hz ⟨i, hi⟩)
  let : Finite (D.X ⧸ L.toAddSubgroup) := hf
  have hn : (L.toAddSubgroup.index : ℤ) ≠ 0 :=
    Int.ofNat_ne_zero.mpr AddSubgroup.index_ne_zero_of_finite
  have ht (x : D.X) : t x = 0 := by
    have hx : L.toAddSubgroup.index • x ∈ L :=
      AddSubgroup.nsmul_index_mem L.toAddSubgroup x
    have h0 := LinearMap.mem_ker.mp (hL hx)
    rw [map_nsmul, nsmul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left hn
  apply hy
  apply P.flip.toPerfPair.injective
  ext x
  exact (ht x).trans (LinearMap.congr_fun (map_zero P.flip.toPerfPair).symm x)

theorem connectedCoreflectionInvariantLattice : ConnectedCoreflectionInvariantLattice.{u} := by
  classical
  intro D hY hconn M hsat hstab
  let P := D.datum
  let B := D.base
  let A := integralCartan P B
  let := D.finiteRoots
  by_cases h : M = ⊥
  · exact .inl h
  right
  obtain ⟨y, hy, hy0⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr h)
  have hy' : y ≠ 0 := by simpa using hy0
  obtain ⟨i, hi⟩ := nonzero_pairing_with_simple_root D hY hy'
  have coroot_of_detected (j : B.support) (z : D.Y) (hz : z ∈ M)
      (hj : P.toLinearMap (P.root j.val) z ≠ 0) : P.coroot j.val ∈ M := by
    apply hsat _ _ hj
    have h := M.sub_mem hz (hstab j z hz)
    rw [P.coreflection_apply, sub_sub_cancel] at h
    exact h
  have hc : P.coroot i.val ∈ M := coroot_of_detected i y hy hi
  have step (j l : B.support) (hj : (integralDiagram A).edges j l ≠ 0) :
      (P.coroot j.val ∈ M ↔ P.coroot l.val ∈ M) := by
    have ha := (diagramAdjacency P B j l).mpr hj
    have hz : A j l = 0 ↔ A l j = 0 := P.pairing_eq_zero_iff'
    have hn₁ : P.toLinearMap (P.root l.val) (P.coroot j.val) ≠ 0 := by
      change A j l ≠ 0
      exact fun h => ha.2.elim (fun h' => h' h) (fun h' => h' (hz.mp h))
    have hn₂ : P.toLinearMap (P.root j.val) (P.coroot l.val) ≠ 0 := by
      change A l j ≠ 0
      exact fun h => hn₁ (hz.mpr h)
    exact ⟨fun h => coroot_of_detected l _ h hn₁, fun h => coroot_of_detected j _ h hn₂⟩
  have walk {j l : B.support}
      (h : Relation.EqvGen (fun j l => (integralDiagram A).edges j l ≠ 0) j l) :
      P.coroot j.val ∈ M ↔ P.coroot l.val ∈ M := by
    induction h with
    | rel j l h => exact step j l h
    | refl j => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂
  have hM : Submodule.span ℤ (P.coroot '' (B.support : Set D.I)) ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    exact (walk (hconn.2 i ⟨j, hj⟩)).mp hc
  rw [B.span_int_coroot_support, hY] at hM
  exact top_le_iff.mp hM

end InvariantLattices

section NormalSubgroups

open Specs.GeometricRadicals (IsSemisimple IsTorus IsSmoothConnectedNormal IsMaximalTorus
  geometricSolvableRadical)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSolvable IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private normalRadicalOfNormal trivialOfSubgroup from LinearAlgebraicGroups.Reductive.CentralDerived
open private trivial_baseChange_iff solvable_of_iso
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected from LinearAlgebraicGroups.Solvable.WordDomainGeometry

theorem normalSubgroupSemisimplicity : NormalSubgroupSemisimplicity.{u} := by
  intro F _ _ G hG N hN
  let H := closedSubgroupAlgebraicGroup N
  letI : ConnectedSpace H.val.X.left := hN.2.1
  have hc : GeometricallyConnected H.val.X.hom := geometricallyConnected_of_connected H
  obtain ⟨U, hU, eU, _⟩ := Reductive.RadicalBaseChange.solvableRadicalPerfectDescent H hN.1 hc
  obtain ⟨R, hR, eR, _⟩ :=
    Reductive.RadicalBaseChange.solvableRadicalPerfectDescent G hG.1 hG.2.1
  let V := subgroupOfSubgroup N U
  have hv : IsSmoothConnectedNormal V :=
    ⟨hU.1.1, hU.1.2.1, normalRadicalOfNormal G hG.1 N hN.2.2
      (fun A => IsSolvable A.val) (fun e hsA hcA hsB hcB => solvable_of_iso e hsA hcA hsB hcB) U hU⟩
  have hr := (trivial_baseChange_iff (K := AlgebraicClosure F) R.group).mp (by
    obtain ⟨r⟩ := hG.2.2
    exact ⟨eR ≪≫ r⟩)
  have ht := trivialOfSubgroup (hR.2.2 V hv hU.2.1) hr
  have ht' : Nonempty (U.group ≅ Grp.trivial (SchemeOver F)) := ht
  obtain ⟨d⟩ := (trivial_baseChange_iff (K := AlgebraicClosure F) U.group).mpr ht'
  exact ⟨hN.1, hc, ⟨eU.symm ≪≫ d⟩⟩

open private definingIdeal definingIdeal_le factor_iso_of_definingIdeal_eq
  from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private torus_smooth_connected_solvable subgroupOf_trans
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

theorem torusInMaximalTorus : TorusInMaximalTorus.{u} := by
  classical
  intro F _ _ G T hT
  letI := G.property.1
  letI := G.property.2.1
  let hG := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
  letI : IsNoetherianRing Γ(G.val.X.left, ⊤) :=
    hG.component_noetherian ⟨⊤, isAffineOpen_top G.val.X.left⟩
  have prime (S : ClosedSubgroup G.val) (hs : IsTorus S.group) : (definingIdeal S).IsPrime := by
    let A := closedSubgroupAlgebraicGroup S
    have h := torus_smooth_connected_solvable A hs
    letI : IsIntegral S.group.X.left := WordDomainGeometry.smoothConnectedGroupIntegral A h.1 h.2.1
    exact RingHom.ker_isPrime _
  let height (S : ClosedSubgroup G.val) := (definingIdeal S).height.toNat
  let eligible n := ∃ S : ClosedSubgroup G.val,
    IsTorus S.group ∧ IsSubgroupOf T S ∧ height S = n
  have hex : ∃ n, eligible n := ⟨height T, T, hT, ⟨𝟙 _, Category.id_comp _⟩, rfl⟩
  obtain ⟨S, hs, hTS, hmin⟩ := Nat.find_spec hex
  refine ⟨S, ⟨hs, ?_⟩, hTS⟩
  intro R hr hSR
  have hTR := subgroupOf_trans hTS hSR
  obtain ⟨a, ha⟩ := hSR
  have hle : definingIdeal R ≤ definingIdeal S := definingIdeal_le a ha
  have hEq : definingIdeal S = definingIdeal R := by
    by_contra hne
    letI := prime R hr
    letI := prime S hs
    have hl := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hle (Ne.symm hne))
    have hmin' : height S ≤ height R :=
      hmin ▸ Nat.find_min' hex ⟨R, hr, hTR, rfl⟩
    have hl' : height R < height S := by
      apply ENat.natCast_lt_natCast.mp
      rw [ENat.natCast_toNat Ideal.height_ne_top_of_isPrime,
        ENat.natCast_toNat Ideal.height_ne_top_of_isPrime]
      exact hl
    exact (not_lt_of_ge hmin') hl'
  letI := factor_iso_of_definingIdeal_eq a ha hEq
  exact ⟨inv a, by rw [← ha, IsIso.inv_hom_id_assoc]⟩

end NormalSubgroups

end

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open Specs.Pinning (SplitBorelPair)
open Specs.AbstractPairing (Root)
open Specs.GeometricRadicals (IsReductive IsSplitTorus GeometricGroup IsMaximalTorus baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.CharacterDescent (Character)
open Specs.QuasiSplitPinnedProduct

open private affineProduct from LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private productTorus splitProductTorus productTorus_geometricallyMaximal
  productRootEquiv from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private splitBorelPair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private splitTorus_baseChange maximalTorus_of_geometricallyMaximal geometricallyMaximal_of_maximal_split
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private maximal_of_square from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F]

private def reindexFanLimit {C : Type*} [Category C] {I J : Type u}
    (e : I ≃ J) {K : J → C} {X : C} (p : ∀ j, X ⟶ K j)
    (h : IsLimit (Fan.mk X (fun i => p (e i)))) : IsLimit (Fan.mk X p) := by
  let q (s : Fan K) := fun i => s.proj (e i)
  refine Fan.IsLimit.mk _ (fun s => Fan.IsLimit.lift h (q s)) ?_ ?_
  · intro s j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact Fan.IsLimit.fac h (q s) i
  · intro s m hm
    apply Fan.IsLimit.hom_ext h
    intro i
    exact (hm (e i)).trans (Fan.IsLimit.fac h (q s) i).symm

private def optionFanLimit {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {I : Type u} (K : Option I → C) {X : C}
    (p : ∀ i, X ⟶ K (some i)) (h : IsLimit (Fan.mk X p)) :
    IsLimit (Fan.mk (K none ⊗ X)
      (fun i => (match i with
        | none => fst (K none) X
        | some j => snd (K none) X ≫ p j))) := by
  let q (s : Fan K) := fun i => s.proj (some i)
  refine Fan.IsLimit.mk _ (fun s => lift (s.proj none) (Fan.IsLimit.lift h (q s))) ?_ ?_
  · intro s j
    cases j with
    | none => exact lift_fst _ _
    | some j =>
      change lift (s.proj none) (Fan.IsLimit.lift h (q s)) ≫ snd _ _ ≫ p j = _
      rw [lift_snd_assoc]
      exact Fan.IsLimit.fac h (q s) j
  · intro s m hm
    apply CartesianMonoidalCategory.hom_ext
    · exact (hm none).trans (lift_fst _ _).symm
    · rw [lift_snd]
      apply Fan.IsLimit.hom_ext h
      intro i
      exact (Category.assoc _ _ _).trans ((hm (some i)).trans (Fan.IsLimit.fac h (q s) i).symm)

private def uniqueFanLimit {C : Type*} [Category C] {I : Type u} [Subsingleton I]
    (i : I) (H : I → C) :
    IsLimit (Fan.mk (H i) (fun j => eqToHom (congrArg H (Subsingleton.elim i j)))) := by
  refine Fan.IsLimit.mk _ (fun s => s.proj i) ?_ ?_
  · intro s j
    obtain rfl := Subsingleton.elim i j
    exact Category.comp_id _
  · intro s a ha
    have e := ha i
    rwa [show (Fan.mk (H i) (fun j => eqToHom (congrArg H (Subsingleton.elim i j)))).proj i =
      𝟙 _ from rfl, Category.comp_id] at e

set_option backward.isDefEq.respectTransparency false in
private theorem productTorus_maximal (P Q : SplitBorelPair F) :
    IsGeometricallyMaximal (productTorus P Q) := by
  let R := affineProduct P.G Q.G
  let T := productTorus P Q
  let K := AlgebraicClosure F
  let B := groupBaseChange F K
  let P' := geometricSplitBorelPair P
  let Q' := geometricSplitBorelPair Q
  let R' := affineProduct P'.G Q'.G
  let T' := productTorus P' Q'
  let eg : R'.val ≅ (GeometricGroup R).val := Functor.Monoidal.μIso B P.G.val Q.G.val
  let et : T'.group ≅ B.obj T.group := Functor.Monoidal.μIso B P.T.group Q.T.group
  letI := T.isClosedImmersion
  have hclosed : IsClosedImmersion (B.map T.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback T.inclusion.hom.hom).flip inferInstance
  refine ⟨hclosed, ?_⟩
  let S := baseChangedSubgroup K T hclosed
  have hmax := maximalTorus_of_geometricallyMaximal R' T'
    (lattice_torus_of_split (splitProductTorus P' Q')) (productTorus_geometricallyMaximal P' Q')
  refine maximal_of_square eg T' S et ?_ hmax
  exact (Functor.LaxMonoidal.μ_natural B P.T.inclusion Q.T.inclusion).symm

private structure SplitGroupProduct {I : Type u} (P : I → SplitBorelPair F) where
  pair : SplitBorelPair F
  projection : ∀ i, pair.G.val ⟶ (P i).G.val
  torusProjection : ∀ i, pair.T.group ⟶ (P i).T.group
  groupLimit : IsLimit (Fan.mk _ projection)
  torusLimit : IsLimit (Fan.mk _ torusProjection)
  torusSquare : ∀ i, pair.T.inclusion ≫ projection i = torusProjection i ≫ (P i).T.inclusion
  roots : (Σ i, Root (P i).T) ≃ Root pair.T
  root_eq : ∀ i a, (roots ⟨i, a⟩).val = torusProjection i ≫ a.val

private def SplitGroupProduct.reindex {I J : Type u}
    (e : I ≃ J) {P : J → SplitBorelPair F} (R : SplitGroupProduct (P ∘ e)) :
    SplitGroupProduct P := by
  let g (i : J) : R.pair.G.val ⟶ (P i).G.val :=
    R.projection (e.symm i) ≫ eqToHom (congrArg (fun j => (P j).G.val) (e.apply_symm_apply i))
  let t (i : J) : R.pair.T.group ⟶ (P i).T.group :=
    R.torusProjection (e.symm i) ≫ eqToHom (congrArg (fun j => (P j).T.group) (e.apply_symm_apply i))
  let r : (Σ i, Root ((P ∘ e) i).T) ≃ (Σ i, Root (P i).T) :=
    Equiv.sigmaCongr e fun _ => Equiv.refl _
  have changeIndex {K : J → GroupScheme F} {X : GroupScheme F}
      (p : ∀ i, X ⟶ K (e i)) (i j : I) (h : i = j) :
      p i ≫ eqToHom (congrArg (K ∘ e) h) = p j := by
    subst j
    exact Category.comp_id _
  have hg (i : I) : g (e i) = R.projection i :=
    @changeIndex (fun j => (P j).G.val) R.pair.G.val R.projection _ _ (e.symm_apply_apply i)
  have ht (i : I) : t (e i) = R.torusProjection i :=
    @changeIndex (fun j => (P j).T.group) R.pair.T.group R.torusProjection _ _ (e.symm_apply_apply i)
  refine ⟨R.pair, g, t, reindexFanLimit e g ?_, reindexFanLimit e t ?_, ?_,
    r.symm.trans R.roots, ?_⟩
  · rw [funext hg]
    exact R.groupLimit
  · rw [funext ht]
    exact R.torusLimit
  · intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    rw [hg, ht]
    exact R.torusSquare i
  · intro j a
    obtain ⟨i, rfl⟩ := e.surjective j
    rw [ht]
    have he : r (⟨i, a⟩ : Σ i, Root ((P ∘ e) i).T) = ⟨e i, a⟩ := rfl
    change (R.roots (r.symm ⟨e i, a⟩)).val = _
    rw [← he, Equiv.symm_apply_apply, R.root_eq]

private def SplitGroupProduct.singleton {I : Type u} [Subsingleton I]
    (i : I) (P : I → SplitBorelPair F) : SplitGroupProduct P := by
  let g (j : I) := eqToHom (congrArg (fun j => (P j).G.val) (Subsingleton.elim i j))
  let t (j : I) := eqToHom (congrArg (fun j => (P j).T.group) (Subsingleton.elim i j))
  let e : (Σ j, Root (P j).T) ≃ Root (P i).T := {
    toFun := fun a => cast (congrArg (fun j => Root (P j).T) (Subsingleton.elim a.1 i)) a.2
    invFun := fun a => ⟨i, a⟩
    left_inv := by
      rintro ⟨j, a⟩
      obtain rfl := Subsingleton.elim j i
      rfl
    right_inv := fun _ => rfl }
  refine ⟨P i, g, t, uniqueFanLimit i _, uniqueFanLimit i _, ?_, e, ?_⟩
  · intro j
    obtain rfl := Subsingleton.elim i j
    simp [g, t]
  · intro j a
    obtain rfl := Subsingleton.elim i j
    change a.val = 𝟙 _ ≫ a.val
    simp

set_option backward.isDefEq.respectTransparency false in
private def SplitGroupProduct.option {I : Type u}
    (P : Option I → SplitBorelPair F) (R : SplitGroupProduct (fun i => P (some i))) :
    SplitGroupProduct P := by
  let L := P none
  let Q := R.pair
  let S := affineProduct L.G Q.G
  let T := productTorus L Q
  let S' := splitBorelPair S (reductiveBinaryProduct _ _ L.reductive Q.reductive)
    T (splitProductTorus L Q) (productTorus_maximal L Q)
  let g (i : Option I) : S'.G.val ⟶ (P i).G.val := match i with
    | none => fst L.G.val Q.G.val
    | some j => snd L.G.val Q.G.val ≫ R.projection j
  let t (i : Option I) : S'.T.group ⟶ (P i).T.group := match i with
    | none => fst L.T.group Q.T.group
    | some j => snd L.T.group Q.T.group ≫ R.torusProjection j
  let e : (Σ i, Root (P i).T) ≃ Root L.T ⊕ Root Q.T :=
    { toFun := fun a => match a with
        | ⟨none, a⟩ => Sum.inl a
        | ⟨some i, a⟩ => Sum.inr (R.roots ⟨i, a⟩)
      invFun := fun a => match a with
        | Sum.inl a => ⟨none, a⟩
        | Sum.inr a => ⟨some (R.roots.symm a).1, (R.roots.symm a).2⟩
      left_inv := by
        rintro ⟨(_ | i), a⟩
        · rfl
        · change (⟨some (R.roots.symm (R.roots ⟨i, a⟩)).1, (R.roots.symm (R.roots ⟨i, a⟩)).2⟩ :
            Σ i, Root (P i).T) = ⟨some i, a⟩
          rw [Equiv.symm_apply_apply]
      right_inv := by
        rintro (a | a)
        · rfl
        · change Sum.inr (R.roots (R.roots.symm a)) = Sum.inr a
          rw [Equiv.apply_symm_apply] }
  refine ⟨S', g, t, ?_, ?_, ?_, e.trans (productRootEquiv L Q), ?_⟩
  · exact optionFanLimit (fun j => (P j).G.val) (X := Q.G.val) R.projection R.groupLimit
  · exact optionFanLimit (fun j => (P j).T.group) (X := Q.T.group) R.torusProjection R.torusLimit
  · intro i
    cases i with
    | none => exact tensorHom_fst _ _
    | some j =>
      change (L.T.inclusion ⊗ₘ Q.T.inclusion) ≫ snd L.G.val Q.G.val ≫ R.projection j =
        (snd L.T.group Q.T.group ≫ R.torusProjection j) ≫ (P (some j)).T.inclusion
      rw [tensorHom_snd_assoc, Category.assoc, R.torusSquare]
  · intro i a
    cases i with
    | none => rfl
    | some j =>
      change snd L.T.group Q.T.group ≫ (R.roots ⟨j, a⟩).val =
        (snd L.T.group Q.T.group ≫ R.torusProjection j) ≫ a.val
      rw [R.root_eq, Category.assoc]

private theorem splitGroupProduct {I : Type u} [Finite I]
    (P : I → SplitBorelPair F) (hn : Nonempty I) : Nonempty (SplitGroupProduct P) := by
  classical
  revert P hn
  induction I using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro P hn
    exact ⟨((ih (P ∘ e) ⟨e.symm hn.some⟩).some).reindex e⟩
  | h_empty => exact fun _ h => h.elim isEmptyElim
  | @h_option I _ ih =>
    intro P _
    cases isEmpty_or_nonempty I with
    | inl h =>
      letI := h
      exact ⟨SplitGroupProduct.singleton none P⟩
    | inr h =>
      exact ⟨SplitGroupProduct.option P (ih _ h).some⟩

end

open Specs.Pinning (SplitBorelPair)
open Specs.AbstractPairing (Root)
open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.QuasiSplitPinnedProduct
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots contractingSubgroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.RankOneFlag (SameSubgroup)
open CocharacterDynamics

open private affineProduct from LinearAlgebraicGroups.Classification.ReductiveProductWithSplitTorus
open private pointHom pointHom_injective affine_subgroup subgroupInclusionFactors
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private inclusion_mono subgroupIso pushSubgroup radical_transport
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private factor_group_through_subgroup subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F]

private theorem pointHom_comp {G H J : GroupScheme F} (f : G ⟶ H) (g : H ⟶ J)
    (R : TestAlgebra F) (x : GroupPoints G R) :
    pointHom g R (pointHom f R x) = pointHom (f ≫ g) R x :=
  Category.assoc x f.hom.hom g.hom.hom

private theorem pointHom_natural {G H : GroupScheme F} (f : G ⟶ H)
    {R S : TestAlgebra F} (a : R ⟶ S) (x : GroupPoints G R) :
    pointHom f S (mapPoints a x) = mapPoints a (pointHom f R x) := by
  change ((testSpec F).map a.op ≫ x) ≫ f.hom.hom = (testSpec F).map a.op ≫ (x ≫ f.hom.hom)
  exact Category.assoc _ _ _

private def underlyingFanLimit {I : Type u} [Finite I]
    {G : GroupScheme F} {H : I → GroupScheme F}
    (p : ∀ i, G ⟶ H i) (h : IsLimit (Fan.mk G p)) :
    IsLimit (Fan.mk G.X (fun i => (p i).hom.hom)) := by
  letI := Fintype.ofFinite I
  let U := Grp.forget (SchemeOver F)
  let e : (Discrete.functor H ⋙ U) ≅ Discrete.functor (fun i => (H i).X) :=
    Discrete.natIso (fun _ => Iso.refl _)
  let h' := (IsLimit.postcomposeHomEquiv e (U.mapCone (Fan.mk G p))).symm
    (isLimitOfPreserves U h)
  refine IsLimit.ofIsoLimit h' (Cone.ext (Iso.refl _) ?_)
  rintro ⟨i⟩
  exact Category.id_comp _ |>.symm

private theorem fanPoints_bijective {I : Type u} [Finite I] {G : GroupScheme F}
    {H : I → GroupScheme F} (p : ∀ i, G ⟶ H i) (h : IsLimit (Fan.mk G p))
    (R : TestAlgebra F) :
    Function.Bijective (fun (x : GroupPoints G R) i => pointHom (p i) R x) := by
  let l := underlyingFanLimit p h
  constructor
  · intro x y hxy
    exact Fan.IsLimit.hom_ext l x y (congrFun hxy)
  · intro x
    refine ⟨Fan.IsLimit.lift l x, funext fun i => ?_⟩
    exact Fan.IsLimit.fac l x i

private theorem orbit_map {G H : GroupScheme F} (f : G ⟶ H) (c : Cocharacter G)
    {R : TestAlgebra F} (x : GroupPoints G R) :
    pointHom f (laurentAlgebra R) (orbit c x) = orbit (c ≫ f) (pointHom f R x) := by
  unfold orbit cocharacterPoint
  rw [map_mul, map_mul, map_inv, pointHom_natural]
  have hc : pointHom f (laurentAlgebra R)
      (pointHom c (laurentAlgebra R) (unitPoint (laurentAlgebra R) (laurentParameter R))) =
      pointHom (c ≫ f) (laurentAlgebra R) (unitPoint (laurentAlgebra R) (laurentParameter R)) :=
    pointHom_comp _ _ _ _
  exact congrArg (fun (t : GroupPoints H (laurentAlgebra R)) =>
    t * (show GroupPoints H (laurentAlgebra R) from mapPoints (laurentConstants R) (pointHom f R x)) * t⁻¹) hc

private theorem hasLimit_product_iff {I : Type u} [Finite I] {G : GroupScheme F}
    {H : I → GroupScheme F} (p : ∀ i, G ⟶ H i) (h : IsLimit (Fan.mk G p)) (c : Cocharacter G)
    {R : TestAlgebra F} (x z : GroupPoints G R) :
    HasLimit c x z ↔
      ∀ i, HasLimit (c ≫ p i) (pointHom (p i) R x) (pointHom (p i) R z) := by
  constructor
  · rintro ⟨w, hw, hz⟩ i
    refine ⟨pointHom (p i) (polynomialAlgebra R) w, ?_, ?_⟩
    · rw [← pointHom_natural, hw, orbit_map]
    · rw [← pointHom_natural, hz]
  · intro he
    choose y hy hz using he
    obtain ⟨w, hw⟩ := (fanPoints_bijective p h (polynomialAlgebra R)).surjective y
    have hw' (i : I) : pointHom (p i) (polynomialAlgebra R) w = y i := congrFun hw i
    refine ⟨w, (fanPoints_bijective p h (laurentAlgebra R)).injective ?_,
      (fanPoints_bijective p h R).injective ?_⟩
    · funext i
      rw [pointHom_natural, hw' i, hy, orbit_map]
    · funext i
      rw [pointHom_natural, hw' i, hz]

private theorem hasExtension_product_iff {I : Type u} [Finite I] {G : GroupScheme F}
    {H : I → GroupScheme F} (p : ∀ i, G ⟶ H i) (h : IsLimit (Fan.mk G p)) (c : Cocharacter G)
    {R : TestAlgebra F} (x : GroupPoints G R) :
    HasExtension c x ↔ ∀ i, HasExtension (c ≫ p i) (pointHom (p i) R x) := by
  constructor
  · rintro ⟨z, hz⟩ i
    exact ⟨_, (hasLimit_product_iff p h c x z).mp hz i⟩
  · intro he
    choose z hz using he
    obtain ⟨y, hy⟩ := (fanPoints_bijective p h R).surjective z
    refine ⟨y, (hasLimit_product_iff p h c x y).mpr (fun i => ?_)⟩
    have hyi : pointHom (p i) R y = z i := congrFun hy i
    rw [hyi]
    exact hz i

private theorem represents_of_sameSubgroup {G : GroupScheme F}
    {S T : ClosedSubgroup G} (h : SameSubgroup S T)
    {q : ∀ R : TestAlgebra F, GroupPoints G R → Prop}
    (hq : RepresentsOnAlgebras T q) : RepresentsOnAlgebras S q := by
  intro R x
  rw [hq]
  obtain ⟨f, hf⟩ := h.1
  obtain ⟨g, hg⟩ := h.2
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨pointHom g R y, (pointHom_comp _ _ _ _).trans (by rw [hg])⟩
  · rintro ⟨y, rfl⟩
    exact ⟨pointHom f R y, (pointHom_comp _ _ _ _).trans (by rw [hf])⟩

private theorem borelLimitDescriptions (P : SplitBorelPair F)
    (B : ClosedSubgroup P.G.val) (hB : IsKBorel B) (hTB : IsSubgroupOf P.T B)
    (U : ClosedSubgroup B.group) (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U)
    (c : Cocharacter P.T.group) (hc : IsRegular P.T c)
    (hr : positiveRoots P.T c = subgroupRoots P.T B) :
    RepresentsOnAlgebras B (fun _ x => HasExtension (c ≫ P.T.inclusion) x) ∧
    RepresentsOnAlgebras (subgroupOfSubgroup B U)
      (fun _ x => HasLimit (c ≫ P.T.inclusion) x 1) := by
  obtain ⟨D⟩ := existsLimitDecomposition P.G (c ≫ P.T.inclusion)
  obtain ⟨_, hdB, hdT, hdRoots, hdU, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel P.G P.reductive P.T P.split P.maximal c hc D
  have hs := (RootData.BorelsAndChambers.positiveSystemsFromCocharacters P.G P.reductive
    P.T P.split P.maximal _).mpr ⟨c, hc, rfl⟩
  obtain ⟨C, _, _, _, hC⟩ := ((RootData.BorelsAndChambers.borelsThroughT P.G P.reductive
    P.T P.split P.maximal).2 _).mp hs
  have hBC := hC B hB hTB hr.symm
  have hDC := hC D.parabolic hdB hdT hdRoots
  have hBD : SameSubgroup B D.parabolic :=
    ⟨subgroupOf_trans hBC.2 hDC.1,
      subgroupOf_trans hDC.2 hBC.1⟩
  let b := subgroupIso (A := B) (B := D.parabolic) hBD
  let hBD' := b.val
  have he : hBD'.hom ≫ D.parabolic.inclusion = B.inclusion := b.property
  let V := pushSubgroup hBD' U
  have hv : IsUnipotentRadical (closedSubgroupAlgebraicGroup D.parabolic) V :=
    radical_transport (A := closedSubgroupAlgebraicGroup B)
      (B := closedSubgroupAlgebraicGroup D.parabolic) hBD' U hU
  have huv : SameSubgroup V (contractingSubgroup D) :=
    ⟨hdU.2.2 _ hv.1 hv.2.1, hv.2.2 _ hdU.1 hdU.2.1⟩
  have hcomm : V.inclusion ≫ D.parabolic.inclusion = U.inclusion ≫ B.inclusion := by
    change (U.inclusion ≫ hBD'.hom) ≫ D.parabolic.inclusion = _
    rw [Category.assoc, he]
  have he' : (contractingSubgroup D).inclusion ≫ D.parabolic.inclusion = D.contracting.inclusion :=
    D.contracting_in_G
  have hUD : SameSubgroup (subgroupOfSubgroup B U) D.contracting := by
    obtain ⟨f, hf⟩ := huv.1
    obtain ⟨g, hg⟩ := huv.2
    constructor
    · refine ⟨f, ?_⟩
      change f ≫ D.contracting.inclusion = U.inclusion ≫ B.inclusion
      rw [← he', ← Category.assoc, hf, hcomm]
    · refine ⟨g, ?_⟩
      change g ≫ U.inclusion ≫ B.inclusion = D.contracting.inclusion
      rw [← hcomm, ← Category.assoc, hg, he']
  exact ⟨represents_of_sameSubgroup hBD D.parabolic_points,
    represents_of_sameSubgroup hUD D.contracting_points⟩
private theorem productOfSubgroups {I : Type u} [Finite I]
    {G : AffineAlgebraicGroup F} {H : I → AffineAlgebraicGroup F}
    (p : ∀ i, G.val ⟶ (H i).val) (hp : IsLimit (Fan.mk _ p))
    (S : ClosedSubgroup G.val) (T : ∀ i, ClosedSubgroup (H i).val)
    (hS : ∀ (R : TestAlgebra F) (x : GroupPoints G.val R),
      (∃ y, pointHom S.inclusion R y = x) ↔
        ∀ i, ∃ z, pointHom (T i).inclusion R z = pointHom (p i) R x) :
    ∃ q : ∀ i, S.group ⟶ (T i).group,
      (∀ i, S.inclusion ≫ p i = q i ≫ (T i).inclusion) ∧
      Nonempty (IsLimit (Fan.mk _ q)) := by
  have hex (i : I) := subgroupInclusionFactors
    (affine_subgroup G.property.1 S) (T i) (S.inclusion ≫ p i) (by
      intro R x
      rw [← pointHom_comp]
      exact (hS R _).mp ⟨x, rfl⟩ i)
  choose q hq using hex
  let j (s : Fan (fun i => (T i).group)) : s.pt ⟶ G.val :=
    Fan.IsLimit.lift hp (fun i => s.proj i ≫ (T i).inclusion)
  have hj (s : Fan (fun i => (T i).group)) (i : I) :
      j s ≫ p i = s.proj i ≫ (T i).inclusion := Fan.IsLimit.fac hp _ i
  have hb' (s : Fan (fun i => (T i).group)) : ∃ b : s.pt ⟶ S.group,
      b ≫ S.inclusion = j s := by
    obtain ⟨b, hb⟩ := (factorsThroughClosed_iff S.inclusion.hom.hom S.isClosedImmersion
      (j s).hom.hom).mpr (by
        intro R x
        apply (hS R _).mpr
        intro i
        refine ⟨pointHom (s.proj i) R x, ?_⟩
        change pointHom (T i).inclusion R (pointHom (s.proj i) R x) =
          pointHom (p i) R (pointHom (j s) R x)
        rw [pointHom_comp, pointHom_comp, hj])
    exact factor_group_through_subgroup S (j s) b hb
  choose b hb using hb'
  have hbi (s : Fan (fun i => (T i).group)) (i : I) : b s ≫ q i = s.proj i := by
    letI := inclusion_mono (T i)
    apply (cancel_mono (T i).inclusion).mp
    rw [Category.assoc, hq, ← Category.assoc, hb, hj]
  refine ⟨q, fun i => (hq i).symm, ⟨Fan.IsLimit.mk _ b hbi ?_⟩⟩
  intro s m hm
  letI := inclusion_mono S
  apply (cancel_mono S.inclusion).mp
  apply Fan.IsLimit.hom_ext hp
  intro i
  change (m ≫ S.inclusion) ≫ p i = (b s ≫ S.inclusion) ≫ p i
  have hmi : m ≫ q i = s.proj i := hm i
  rw [Category.assoc m, ← hq, ← Category.assoc m, hmi, hb, hj]

private theorem representedBorelProducts {I : Type u} [Finite I]
    {G : AffineAlgebraicGroup F} {H : I → AffineAlgebraicGroup F}
    (p : ∀ i, G.val ⟶ (H i).val) (hp : IsLimit (Fan.mk _ p))
    (c : Cocharacter G.val)
    (B U : ClosedSubgroup G.val) (Bi Ui : ∀ i, ClosedSubgroup (H i).val)
    (hB : RepresentsOnAlgebras B (fun _ x => HasExtension c x))
    (hU : RepresentsOnAlgebras U (fun _ x => HasLimit c x 1))
    (hBi : ∀ i, RepresentsOnAlgebras (Bi i) (fun _ x => HasExtension (c ≫ p i) x))
    (hUi : ∀ i, RepresentsOnAlgebras (Ui i) (fun _ x => HasLimit (c ≫ p i) x 1)) :
    (∃ b : ∀ i, B.group ⟶ (Bi i).group,
        (∀ i, B.inclusion ≫ p i = b i ≫ (Bi i).inclusion) ∧
          Nonempty (IsLimit (Fan.mk _ b))) ∧
    (∃ u : ∀ i, U.group ⟶ (Ui i).group,
        (∀ i, U.inclusion ≫ p i = u i ≫ (Ui i).inclusion) ∧
          Nonempty (IsLimit (Fan.mk _ u))) := by
  constructor
  · apply productOfSubgroups p hp B Bi
    intro R x
    exact (hB R x).symm.trans ((hasExtension_product_iff p hp c x).trans
      (forall_congr' fun i => hBi i _ _))
  · apply productOfSubgroups p hp U Ui
    intro R x
    exact (hU R x).symm.trans ((hasLimit_product_iff p hp c x 1).trans
      (forall_congr' fun i => by rw [map_one]; exact hUi i _ _))

open Specs.Pinning (PinnedGroup)
open Specs.RootGroups (AdditiveLine)

private theorem markedProductOfRegularProjections {I : Type u} [Finite I]
    (P : SplitBorelPair F) (Q : I → SplitBorelPair F)
    (M : BorelPair P.G) (N : ∀ i, BorelPair (Q i).G)
    (hT : M.torus = P.T) (hTi : ∀ i, (N i).torus = (Q i).T)
    (p : ∀ i, P.G.val ⟶ (Q i).G.val) (hp : IsLimit (Fan.mk _ p))
    (t : ∀ i, P.T.group ⟶ (Q i).T.group) (ht : IsLimit (Fan.mk _ t))
    (hsq : ∀ i, P.T.inclusion ≫ p i = t i ≫ (Q i).T.inclusion)
    (c d : Cocharacter P.T.group) (hc : IsRegular P.T c) (hd : IsRegular P.T d)
    (hpos : positiveRoots P.T c = subgroupRoots P.T M.positive)
    (hneg : positiveRoots P.T d = subgroupRoots P.T M.negative)
    (hci : ∀ i, IsRegular (Q i).T (c ≫ t i)) (hdi : ∀ i, IsRegular (Q i).T (d ≫ t i))
    (hposi : ∀ i, positiveRoots (Q i).T (c ≫ t i) = subgroupRoots (Q i).T (N i).positive)
    (hnegi : ∀ i, positiveRoots (Q i).T (d ≫ t i) = subgroupRoots (Q i).T (N i).negative) :
    ∃ B : MarkedProduct M N, B.projection = p := by
  have hcomm (a : Cocharacter P.T.group) (i : I) :
      (a ≫ P.T.inclusion) ≫ p i = (a ≫ t i) ≫ (Q i).T.inclusion := by
    rw [Category.assoc, hsq, Category.assoc]
  obtain ⟨hB, hU⟩ := borelLimitDescriptions P M.positive M.positiveBorel
    (hT ▸ M.torusInPositive) M.positiveRadical M.positiveUnipotentRadical c hc hpos
  obtain ⟨hC, hV⟩ := borelLimitDescriptions P M.negative M.negativeBorel
    (hT ▸ M.torusInNegative) M.negativeRadical M.negativeUnipotentRadical d hd hneg
  have hfB i := borelLimitDescriptions (Q i) (N i).positive (N i).positiveBorel
    (hTi i ▸ (N i).torusInPositive) (N i).positiveRadical (N i).positiveUnipotentRadical
    (c ≫ t i) (hci i) (hposi i)
  have hfC i := borelLimitDescriptions (Q i) (N i).negative (N i).negativeBorel
    (hTi i ▸ (N i).torusInNegative) (N i).negativeRadical (N i).negativeUnipotentRadical
    (d ≫ t i) (hdi i) (hnegi i)
  obtain ⟨⟨pb, hb, ⟨lb⟩⟩, ⟨pu, hu, ⟨lu⟩⟩⟩ := representedBorelProducts p hp
    (c ≫ P.T.inclusion) M.positive (M.subgroup .positiveRadical)
    (fun i => (N i).positive) (fun i => (N i).subgroup .positiveRadical)
    hB hU (fun i => (hcomm c i).symm ▸ (hfB i).1)
    (fun i => (hcomm c i).symm ▸ (hfB i).2)
  obtain ⟨⟨pc, hpc, ⟨lc⟩⟩, ⟨pv, hv, ⟨lv⟩⟩⟩ := representedBorelProducts p hp
    (d ≫ P.T.inclusion) M.negative (M.subgroup .negativeRadical)
    (fun i => (N i).negative) (fun i => (N i).subgroup .negativeRadical)
    hC hV (fun i => (hcomm d i).symm ▸ (hfC i).1)
    (fun i => (hcomm d i).symm ▸ (hfC i).2)
  let t' (i : I) : M.torus.group ⟶ (N i).torus.group :=
    eqToHom (congrArg Specs.ClosedSubgroup.group hT) ≫ t i ≫
      eqToHom (congrArg Specs.ClosedSubgroup.group (hTi i).symm)
  have hts : ∀ i, M.torus.inclusion ≫ p i = t' i ≫ (N i).torus.inclusion := by
    intro i
    have he {G : GroupScheme F} {S T : ClosedSubgroup G} (h : S = T) :
        eqToHom (congrArg Specs.ClosedSubgroup.group h) ≫ T.inclusion = S.inclusion := by
      subst T
      simp
    dsimp only [t']
    simp only [Category.assoc, he (hTi i).symm]
    rw [← hsq i, ← Category.assoc, he hT]
  have ht' : IsLimit (Fan.mk M.torus.group t') := by
    let v : M.torus.group ≅ P.T.group := eqToIso (congrArg Specs.ClosedSubgroup.group hT)
    let w (i : I) : (Q i).T.group ≅ (N i).torus.group :=
      eqToIso (congrArg Specs.ClosedSubgroup.group (hTi i).symm)
    let f (s : Fan (fun i => (N i).torus.group)) :=
      Fan.IsLimit.lift ht (fun i => s.proj i ≫ (w i).inv)
    have hf (s : Fan (fun i => (N i).torus.group)) (i : I) :
        f s ≫ t i = s.proj i ≫ (w i).inv := Fan.IsLimit.fac ht _ i
    refine Fan.IsLimit.mk _ (fun s => f s ≫ v.inv) ?_ ?_
    · intro s i
      change (f s ≫ v.inv) ≫ v.hom ≫ t i ≫ (w i).hom = s.proj i
      rw [Category.assoc, v.inv_hom_id_assoc, ← Category.assoc, hf,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · intro s m hm
      apply (cancel_mono v.hom).mp
      simp only [Category.assoc, v.inv_hom_id, Category.comp_id]
      apply Fan.IsLimit.hom_ext ht
      intro i
      change (m ≫ v.hom) ≫ t i = f s ≫ t i
      rw [hf]
      apply (cancel_mono (w i).hom).mp
      rw [Category.assoc (s.proj i), Iso.inv_hom_id, Category.comp_id]
      exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (hm i))
  refine ⟨{ projection := p
            subgroupProjection := fun m => match m with
              | .positive => pb
              | .negative => pc
              | .torus => t'
              | .positiveRadical => pu
              | .negativeRadical => pv
            commutes := ?_
            product := hp
            subgroupProduct := ?_ }, rfl⟩
  · intro m
    cases m
    exacts [hb, hpc, hts, hu, hv]
  · intro m
    cases m
    exacts [lb, lc, ht', lu, lv]

end

open Specs.QuasiSplitPinnedProduct Specs.AbsoluteDynkinTypes
open Specs.Pinning (BasedRootDatum AttachedDatum PinnedGroup transportCharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.AbstractPairing (Root)
open Specs.BorelsAndChambers (subgroupRoots)

open private basedIso_base_iff base_isPos_iff_subgroupRoots
  from LinearAlgebraicGroups.Classification.PinnedEquivalence

noncomputable section

set_option maxHeartbeats 600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F] {A : AdditiveLine F} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} (W : PinnedFactors D)

private abbrev rootsOfFactors {D : AttachedDatum P.pair} (W : PinnedFactors D) :=
  (Σ c : DatumComponents D.toBased, Root (W.factor c).pair.T)

private def blockRoot (c : DatumComponents D.toBased) (a : Root (W.factor c).pair.T) :=
  (W.coordinates.blocks c).roots ((W.based c).val.indexEquiv.symm a)

private def blockRootEquiv : rootsOfFactors W ≃ Root P.pair.T := by
  refine Equiv.ofBijective (fun a => (blockRoot W a.1 a.2).val) ⟨?_, ?_⟩
  · rintro ⟨c, a⟩ ⟨d, b⟩ hab
    change (blockRoot W c a).val = (blockRoot W d b).val at hab
    have h := W.coordinates.supported (blockRoot W c a).val
    have hb : SupportedOn {j | component j = d}
        (W.coordinates.weights (D.toBased.datum.root (blockRoot W c a).val),
         W.coordinates.coweights (D.toBased.datum.coroot (blockRoot W c a).val)) :=
      hab ▸ (blockRoot W d b).property
    have hcd : c = d := h.unique (blockRoot W c a).property hb
    subst d
    exact congrArg (Sigma.mk c) ((W.based c).val.indexEquiv.symm.injective
      ((W.coordinates.blocks c).roots.injective (Subtype.ext hab)))
  · intro a
    obtain ⟨c, hc, _⟩ := W.coordinates.supported a
    refine ⟨⟨c, (W.based c).val.indexEquiv ((W.coordinates.blocks c).roots.symm ⟨a, hc⟩)⟩, ?_⟩
    change (blockRoot W c ((W.based c).val.indexEquiv _)).val = a
    simp only [blockRoot, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

private theorem blockRootEquiv_simple (c : DatumComponents D.toBased) (a : Root (W.factor c).pair.T) :
    a ∈ (W.attached c).toBased.base.support ↔ blockRootEquiv W ⟨c, a⟩ ∈ D.toBased.base.support := by
  let B := (W.coordinates.blocks c).block
  let d := (W.coordinates.blocks c)
  let e := W.based c
  let j := e.val.indexEquiv.symm a
  have ha : e.val.indexEquiv j = a := e.val.indexEquiv.apply_symm_apply a
  have hj (hj : j ∈ B.datum.base.support) :
      blockRootEquiv W ⟨c, a⟩ = (B.vertices ⟨j, hj⟩).val.val :=
    d.base_eq ⟨j, hj⟩
  constructor
  · intro h
    have h' := (basedIso_base_iff e j).mpr (ha.symm ▸ h)
    exact (hj h') ▸ (B.vertices ⟨j, h'⟩).val.property
  · intro h
    let r : D.toBased.base.support := ⟨blockRootEquiv W ⟨c, a⟩, h⟩
    have hr : component r = c := by
      by_contra hn
      have he := (blockRoot W c a).property r hn
      have hsingle := W.coordinates.simpleCoroot r
      have hval := congrFun hsingle r
      have hz : W.coordinates.coweights (D.toBased.datum.coroot r.val) r = 0 := he.2
      classical
      rw [hz, Pi.single_eq_same] at hval
      exact zero_ne_one hval
    let i := B.vertices.symm ⟨r, hr⟩
    have hv : (B.vertices i).val.val = r.val :=
      congrArg (fun v : BlockVertices D.toBased c => v.val.val) (B.vertices.apply_symm_apply _)
    have heq : (d.roots i.val).val = (d.roots j).val := (d.base_eq i).trans hv
    have hi : i.val = j := d.roots.injective (Subtype.ext heq)
    have hj' : j ∈ B.datum.base.support := hi ▸ i.property
    have := (basedIso_base_iff e j).mp hj'
    exact ha ▸ this

private theorem blockRootEquiv_factorSimpleRoot
    (c : DatumComponents D.toBased) (i : BlockVertices D.toBased c) :
    blockRootEquiv W ⟨c, (factorSimpleRoot W c i).val⟩ = i.val.val := by
  let B := (W.coordinates.blocks c).block
  let j := B.vertices.symm i
  change ((W.coordinates.blocks c).roots
    ((W.based c).val.indexEquiv.symm ((W.based c).val.indexEquiv j.val))).val = _
  rw [Equiv.symm_apply_apply, (W.coordinates.blocks c).base_eq j]
  exact congrArg (fun z : BlockVertices D.toBased c => z.val.val) (B.vertices.apply_symm_apply _)

private theorem blockRootEquiv_character (c : DatumComponents D.toBased)
    (t : P.pair.T.group ⟶ (W.factor c).pair.T.group) (ht : IsBlockTorusProjection W c t)
    (a : Root (W.factor c).pair.T) :
    (blockRootEquiv W ⟨c, a⟩).val = t ≫ a.val := by
  classical
  letI := D.comm
  letI := (W.attached c).comm
  let e := W.based c
  let b := W.coordinates.blocks c
  let j := e.val.indexEquiv.symm a
  have hroot := e.val.toHom.root_weightMap_apply b.block.datum.datum (W.attached c).toBased.datum j
  change e.val.weightEquiv (b.block.datum.datum.root j) =
    (W.attached c).datum.rootDatum.root (e.val.indexEquiv j) at hroot
  rw [show e.val.indexEquiv j = a from e.val.indexEquiv.apply_symm_apply a,
    (W.attached c).datum.root_eq] at hroot
  have hweight : e.val.weightEquiv.symm (Additive.ofMul a.val) = b.block.datum.datum.root j :=
    e.val.weightEquiv.symm_apply_eq.mpr hroot.symm
  apply (show Function.Injective (fun (χ : Character P.pair.T.group) =>
    W.coordinates.weights (Additive.ofMul χ)) from W.coordinates.weights.injective)
  funext i
  change W.coordinates.weights (Additive.ofMul (blockRootEquiv W ⟨c, a⟩).val) i =
    W.coordinates.weights (Additive.ofMul (t ≫ a.val)) i
  rw [ht a.val i, hweight]
  let r := blockRoot W c a
  have hr : D.toBased.datum.root r.val = Additive.ofMul (blockRootEquiv W ⟨c, a⟩).val :=
    D.datum.root_eq r.val
  have h₁ := congrArg (fun x : D.toBased.X => W.coordinates.weights x i) hr
  refine h₁.symm.trans ?_
  by_cases hi : component i = c
  · rw [dite_eq_left hi]
    exact (congrFun (b.root_eq j) ⟨i, hi⟩).symm
  · rw [dite_eq_right hi]
    exact (r.property i hi).1

private theorem pairingAlong {T S : GroupScheme F} (t : T ⟶ S)
    (c : Cocharacter T) (χ : Character S) :
    pairing S χ (c ≫ t) = pairing T (t ≫ χ) c := by
  apply ((RootData.CharacterPairing.characterPairingComposition S χ (c ≫ t)).1 _).mp
  simpa only [Specs.CharacterDescent.compositionPairing, Category.assoc] using
    ((RootData.CharacterPairing.characterPairingComposition T (t ≫ χ) c).1 _).mpr rfl

/-- A functional positive on each simple root detects precisely the positive roots. -/
private theorem positive_of_simple (E : BasedRootDatum.{u}) (l : E.X →ₗ[ℤ] ℤ)
    (hs : ∀ i ∈ E.base.support, 0 < l (E.datum.root i)) (i : E.I) :
    E.base.IsPos i ↔ 0 < l (E.datum.root i) := by
  letI := E.finiteRoots
  let pos (j : E.I) (h : E.base.IsPos j) : 0 < l (E.datum.root j) := by
    refine h.induction_on_add hs ?_
    intro a b c hroot ha hb
    rw [hroot, map_add]
    exact add_pos ha (hs b hb)
  refine ⟨pos i, fun h => ?_⟩
  by_contra hn
  let j := E.datum.reflectionPerm i i
  have hj : E.base.IsPos j := (RootPairing.Base.IsPos.neg_iff_not E.base i).mpr hn
  have hp := pos j hj
  have he : E.datum.root j = -E.datum.root i := E.datum.root_eq_neg_iff.mpr rfl
  rw [he, map_neg] at hp
  omega

end

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable {F : Type u} [Field F]
section PinnedProducts

open Specs.Pinning (AttachedDatum BasedIso PinnedGroup PinnedIso SimpleRoot transportCharacter IsSimple RootCoordinate)
open Specs.RootGroups (AdditiveLine HasScalarAction rootPoint)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.CharacterPairing (characterValue)
open Specs.SimplyConnectedLattice (corootLattice)
open Specs.GeometricRadicals (IsSplitTorus)
open Classification.Pinning (attachedDatum inducedBasedIso)
open private charactersOfIso from LinearAlgebraicGroups.RootData.CharacterPairing
open private pointPost_zero characterValue_pullback rootEquivOfRootMap
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private rootSubgroup_of_coordinate
  from LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private pinnedLift basedIso_base_iff base_isPos_iff_subgroupRoots
  from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private split_character_hom_ext from LinearAlgebraicGroups.Classification.NormalizerComparison
open private corootFullRank from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private def isoFanLimit {C : Type*} [Category C] {I : Type u}
    {X Y : C} (e : X ≅ Y) {H : I → C} (p : ∀ i, Y ⟶ H i)
    (h : IsLimit (Fan.mk Y p)) : IsLimit (Fan.mk X (fun i => e.hom ≫ p i)) := by
  refine Fan.IsLimit.mk _ (fun s => Fan.IsLimit.lift h (fun i => s.proj i) ≫ e.inv) ?_ ?_
  · intro s i
    change (_ ≫ e.inv) ≫ e.hom ≫ p i = s.proj i
    rw [Category.assoc, e.inv_hom_id_assoc]
    exact Fan.IsLimit.fac h _ i
  · intro s m hm
    apply (cancel_mono e.hom).mp
    let a : s.pt ⟶ Y := Fan.IsLimit.lift h (fun i => s.proj i)
    change m ≫ e.hom = (a ≫ e.inv) ≫ e.hom
    have ha : (a ≫ e.inv) ≫ e.hom = a := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    rw [ha]
    apply Fan.IsLimit.hom_ext h
    intro i
    have hf : a ≫ p i = s.proj i := Fan.IsLimit.fac h _ i
    exact (Category.assoc _ _ _).trans ((hm i).trans hf.symm)

private def SplitGroupProduct.inclusion {I : Type u} {P : I → SplitBorelPair F}
    (R : SplitGroupProduct P) (i : I) : (P i).G.val ⟶ R.pair.G.val := by
  classical
  exact Fan.IsLimit.lift R.groupLimit (fun j =>
    if h : i = j then eqToHom (congrArg (fun k => (P k).G.val) h) else 0)

private theorem SplitGroupProduct.inclusion_projection_same {I : Type u} {P : I → SplitBorelPair F}
    (R : SplitGroupProduct P) (i : I) : R.inclusion i ≫ R.projection i = 𝟙 _ := by
  classical
  exact (Fan.IsLimit.fac R.groupLimit _ i).trans (dite_eq_left rfl)

private theorem SplitGroupProduct.inclusion_projection_ne {I : Type u} {P : I → SplitBorelPair F}
    (R : SplitGroupProduct P) (i j : I) (h : i ≠ j) :
    R.inclusion i ≫ R.projection j = 0 := by
  classical
  exact (Fan.IsLimit.fac R.groupLimit _ j).trans (dite_eq_right h)

private theorem SplitGroupProduct.isClosedImmersion_inclusion {I : Type u}
    {P : I → SplitBorelPair F} (R : SplitGroupProduct P) (i : I) :
    IsClosedImmersion (R.inclusion i).hom.hom.left := by
  apply RootData.RootGroups.isClosedImmersion_of_injectivePoints (P i).G R.pair.G
  intro B x y h
  have he := congrArg (pointHom (R.projection i) B) h
  change pointHom (R.projection i) B (pointHom (R.inclusion i) B x) =
    pointHom (R.projection i) B (pointHom (R.inclusion i) B y) at he
  rw [pointHom_comp, pointHom_comp, R.inclusion_projection_same] at he
  exact he

private theorem SplitGroupProduct.scalarAction {I : Type u} [Finite I]
    {P : I → SplitBorelPair F} (R : SplitGroupProduct P) (i : I)
    {χ : Character (P i).T.group} {A : AdditiveLine F}
    {x : A.group ⟶ (P i).G.val} (hx : HasScalarAction (P i).T χ x) :
    HasScalarAction R.pair.T (R.torusProjection i ≫ χ) (x ≫ R.inclusion i) := by
  classical
  intro S t a
  dsimp only
  apply (fanPoints_bijective R.projection R.groupLimit S).injective
  funext j
  change pointHom (R.projection j) S
      ((pointHom R.pair.T.inclusion S t) *
         rootPoint (x ≫ R.inclusion i) S a * (pointHom R.pair.T.inclusion S t)⁻¹) =
    pointHom (R.projection j) S (rootPoint (x ≫ R.inclusion i) S
      (characterValue (R.torusProjection i ≫ χ) S t * a))
  have rootPoint_projection (s : S) :
      pointHom (R.projection j) S (rootPoint (x ≫ R.inclusion i) S s) =
        pointHom (R.inclusion i ≫ R.projection j) S (rootPoint x S s) := by
    rw [rootPoint_comp]
    exact pointHom_comp _ _ _ _
  rw [map_mul, map_mul, map_inv, pointHom_comp, R.torusSquare, ← pointHom_comp,
    rootPoint_projection, rootPoint_projection]
  by_cases hij : i = j
  · subst j
    rw [R.inclusion_projection_same, characterValue_pullback]
    have he (z : GroupPoints (P i).G.val S) :
        pointHom (𝟙 (P i).G.val) S z = z := Category.comp_id z
    simp only [he]
    exact hx S (pointHom (R.torusProjection i) S t) a
  · rw [R.inclusion_projection_ne i j hij]
    simp only [pointPost_zero, mul_one, mul_inv_cancel]

private theorem simpleRootComparison {P Q : SplitBorelPair F} (e : Root P.T ≃ Root Q.T)
    (f : Character P.T.group ≃* Character Q.T.group) (he : ∀ i, f i.val = (e i).val)
    (h : ∀ i, i ∈ subgroupRoots P.T P.B ↔ e i ∈ subgroupRoots Q.T Q.B)
    (i : Root P.T) : IsSimple P i ↔ IsSimple Q (e i) := by
  constructor
  · rintro ⟨hi, hsum⟩
    refine ⟨(h i).mp hi, ?_⟩
    intro b hb c hc hbc
    obtain ⟨a, rfl⟩ := e.surjective b
    obtain ⟨a', rfl⟩ := e.surjective c
    apply hsum a ((h a).mpr hb) a' ((h a').mpr hc)
    apply f.injective
    simpa only [map_mul, he] using hbc
  · rintro ⟨hi, hsum⟩
    refine ⟨(h i).mpr hi, ?_⟩
    intro b hb c hc hbc
    apply hsum (e b) ((h b).mp hb) (e c) ((h c).mp hc)
    simpa only [map_mul, he] using (congrArg f hbc)

private def withBorel (P : SplitBorelPair F) (B : ClosedSubgroup P.G.val)
    (hB : IsKBorel B) (hTB : IsSubgroupOf P.T B) : SplitBorelPair F :=
  { P with B := B, borel := hB, containsTorus := hTB }

private theorem productPinning {I : Type u} [Finite I] {A : AdditiveLine F}
    {Q : I → PinnedGroup A} (R : SplitGroupProduct (fun i => (Q i).pair))
    (B : ClosedSubgroup R.pair.G.val) (hB : IsKBorel B) (hTB : IsSubgroupOf R.pair.T B)
    (e : SimpleRoot (withBorel R.pair B hB hTB) → (Σ i, SimpleRoot (Q i).pair))
    (he : ∀ a, a.val.val = R.torusProjection (e a).1 ≫ (e a).2.val.val) :
    let S := withBorel R.pair B hB hTB
    ∃ (U : RootSubgroupFamily S.T) (pin : Specs.Pinning.Pinning A S U),
      ∀ a, pinnedCoordinate ⟨S, U, pin⟩ a =
        pinnedCoordinate (Q (e a).1) (e a).2 ≫ R.inclusion (e a).1 := by
  classical
  dsimp only
  let S := withBorel R.pair B hB hTB
  obtain ⟨U, _⟩ := Classification.Pinning.pinningsExist A S
  have hl (a : SimpleRoot S) : ∃ z : RootCoordinate A S.T (U a.val).val a.val.val,
      z.val.hom ≫ (U a.val).val.inclusion =
        pinnedCoordinate (Q (e a).1) (e a).2 ≫ R.inclusion (e a).1 := by
    let i := (e a).1
    let b := (e a).2
    let V := ((Q i).roots b.val).val
    let x := ((Q i).pin b).val
    let V' : ClosedSubgroup S.G.val :=
      ⟨V.group, V.inclusion ≫ R.inclusion i, by
        letI := V.isClosedImmersion
        letI := R.isClosedImmersion_inclusion i
        exact IsClosedImmersion.comp _ _⟩
    have hscalar : HasScalarAction S.T a.val.val (x.hom ≫ V'.inclusion) := by
      change HasScalarAction R.pair.T a.val.val
        (x.hom ≫ V.inclusion ≫ R.inclusion i)
      rw [he a, ← Category.assoc]
      exact R.scalarAction i ((Q i).pin b).property
    have hV := ((Q i).roots b.val).property
    have hV' := rootSubgroup_of_coordinate
      (⟨x, hscalar⟩ : RootCoordinate A S.T V' a.val.val) hV.1 hV.2.1
    obtain ⟨Z, _, _, _, _, hZ⟩ :=
      ((RootData.RootGroups.rootSubgroups S.G S.reductive S.T S.split S.maximal).2
        a.val.val a.val.property).2.2
    have hUV := hZ (U a.val).val (U a.val).property
    have hVV := hZ V' hV'
    let isom := subgroupIso (A := V') (B := (U a.val).val)
      ⟨subgroupOf_trans hVV.2 hUV.1, subgroupOf_trans hUV.2 hVV.1⟩
    let z := x ≪≫ isom.val
    have hcoord : z.hom ≫ (U a.val).val.inclusion = x.hom ≫ V'.inclusion := by
      change (x.hom ≫ isom.val.hom) ≫ _ = _
      rw [Category.assoc, isom.property]
    refine ⟨⟨z, hcoord.symm ▸ hscalar⟩, ?_⟩
    exact hcoord.trans (Category.assoc _ _ _).symm
  choose pin hp using hl
  exact ⟨U, pin, hp⟩

variable {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}

private theorem pinnedProductProjections (W : PinnedFactors D)
    (hn : Nonempty (DatumComponents D.toBased))
    (hD : corootLattice D = ⊤)
    (t : ∀ c, P.pair.T.group ⟶ (W.factor c).pair.T.group)
    (ht : IsLimit (Fan.mk _ t)) (ht' : ∀ c, IsBlockTorusProjection W c (t c)) :
    ∃ p : ∀ c, P.pair.G.val ⟶ (W.factor c).pair.G.val,
      Nonempty (IsLimit (Fan.mk _ p)) ∧
      (∀ c, P.pair.T.inclusion ≫ p c = t c ≫ (W.factor c).pair.T.inclusion) ∧
      (∀ (i : D.toBased.base.support) c (h : component i = c),
        pinnedCoordinate P (labeledSimpleRoot D i) ≫ p c =
          pinnedCoordinate (W.factor c) (factorSimpleRoot W c ⟨i, h⟩)) ∧
      ∀ (i : D.toBased.base.support) c, component i ≠ c →
        pinnedCoordinate P (labeledSimpleRoot D i) ≫ p c = 0 := by
  classical
  let C := DatumComponents D.toBased
  letI : Finite C := Quotient.finite _
  letI := D.comm
  letI := D.toBased.finiteRoots
  letI := D.toBased.freeX
  letI := D.toBased.finiteX
  letI := D.toBased.freeY
  letI := D.toBased.finiteY
  obtain ⟨R⟩ := splitGroupProduct (fun c => (W.factor c).pair) hn
  let τ : P.pair.T.group ≅ R.pair.T.group := ht.conePointUniqueUpToIso R.torusLimit
  have hτ (c : C) : τ.hom ≫ R.torusProjection c = t c :=
    ht.conePointUniqueUpToIso_hom_comp R.torusLimit ⟨c⟩
  let g := blockRootEquiv W
  let e : Root P.pair.T ≃ Root R.pair.T := g.symm.trans R.roots
  let w := charactersOfIso τ
  have he (a : Root P.pair.T) : w a.val = (e a).val := by
    obtain ⟨⟨c, b⟩, rfl⟩ := g.surjective a
    change τ.inv ≫ (g ⟨c, b⟩).val = (R.roots (g.symm (g ⟨c, b⟩))).val
    rw [g.symm_apply_apply, R.root_eq, blockRootEquiv_character W c (t c) (ht' c) b,
      ← hτ]
    simp only [Category.assoc, τ.inv_hom_id_assoc]
  obtain ⟨c, _, hc, _, hcB⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.pair.G P.pair.reductive
      P.pair.T P.pair.split P.pair.maximal).1 P.pair.B P.pair.borel P.pair.containsTorus
  let d : Cocharacter R.pair.T.group := c ≫ τ.hom
  have hp (a : Root P.pair.T) : pairing R.pair.T.group (e a).val d = pairing P.pair.T.group a.val c := by
    rw [← he a]
    change pairing R.pair.T.group (τ.inv ≫ a.val) (c ≫ τ.hom) = _
    rw [pairingAlong, τ.hom_inv_id_assoc]
  have hd : IsRegular R.pair.T d := by
    intro b
    obtain ⟨a, rfl⟩ := e.surjective b
    change pairing R.pair.T.group (e a).val d ≠ 0
    rw [hp]
    exact hc a
  obtain ⟨L⟩ := existsLimitDecomposition R.pair.G (d ≫ R.pair.T.inclusion)
  obtain ⟨_, hB, hTB, hroots, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel R.pair.G R.pair.reductive R.pair.T
      R.pair.split R.pair.maximal d hd L
  let S := withBorel R.pair L.parabolic hB hTB
  have hsign (a : Root P.pair.T) : a ∈ subgroupRoots P.pair.T P.pair.B ↔
      e a ∈ subgroupRoots S.T S.B := by
    rw [hcB]
    change a ∈ positiveRoots P.pair.T c ↔ e a ∈ subgroupRoots R.pair.T L.parabolic
    rw [hroots]
    change 0 < pairing P.pair.T.group a.val c ↔ 0 < pairing R.pair.T.group (e a).val d
    rw [hp]
  have hsimple (a : Root P.pair.T) : IsSimple P.pair a ↔ IsSimple S (e a) :=
    simpleRootComparison (P := P.pair) (Q := S) e w he hsign a
  have hfactor (c : C) (a : Root (W.factor c).pair.T) :
      IsSimple (W.factor c).pair a ↔ IsSimple S (R.roots ⟨c, a⟩) := by
    have hh : e (g ⟨c, a⟩) = R.roots ⟨c, a⟩ := congrArg R.roots (g.symm_apply_apply _)
    rw [← hh, ← hsimple, ← D.simple_iff, ← (W.attached c).simple_iff]
    exact blockRootEquiv_simple W c a
  let j (a : SimpleRoot S) : Σ c : C, SimpleRoot (W.factor c).pair :=
    let z := R.roots.symm a.val
    ⟨z.1, ⟨z.2, (hfactor z.1 z.2).mpr (R.roots.apply_symm_apply a.val ▸ a.property)⟩⟩
  have hj (a : SimpleRoot S) :
      a.val.val = R.torusProjection (j a).1 ≫ (j a).2.val.val := by
    let z := R.roots.symm a.val
    change a.val.val = R.torusProjection z.1 ≫ z.2.val
    exact (congrArg Subtype.val (R.roots.apply_symm_apply a.val)).symm.trans (R.root_eq z.1 z.2)
  obtain ⟨U, pin, hpin⟩ := productPinning R L.parabolic hB hTB j hj
  let Q : PinnedGroup A := ⟨S, U, pin⟩
  let E := attachedDatum S
  letI := E.comm
  let f : D.toBased.X ≃ₗ[ℤ] E.toBased.X := w.toAdditive.toIntLinearEquiv
  have hfin : Finite (D.toBased.X ⧸ Submodule.span ℤ (range D.toBased.datum.root)) := by
    apply (Submodule.finiteQuotient_iff _).mpr
    exact (corootFullRank D.toBased.datum D.toBased.base).mp (by
      change finrank ℤ (corootLattice D) = _
      rw [hD, finrank_top]
      rfl)
  have hmap (a : Root P.pair.T) : f (D.toBased.datum.root a) = E.toBased.datum.root (e a) := by
    change f (D.datum.rootDatum.root a) = E.datum.rootDatum.root (e a)
    rw [D.datum.root_eq, E.datum.root_eq]
    exact congrArg Additive.ofMul (he a)
  let e' : BasedIso D.toBased E.toBased :=
    ⟨rootEquivOfRootMap D.toBased.datum E.toBased.datum hfin e f hmap, by
      ext b
      obtain ⟨a, rfl⟩ := e.surjective b
      change e a ∈ e '' (D.base.support : Set (Root P.pair.T)) ↔ _
      rw [Set.mem_image_equiv, e.symm_apply_apply]
      exact (D.simple_iff a).trans ((hsimple a).trans (E.simple_iff (e a)).symm)⟩
  obtain ⟨l, hl⟩ := pinnedLift P Q D E e'
  have hlt (χ : Character P.pair.T.group) :
      transportCharacter l.torus χ = transportCharacter τ χ := by
    have ht := congrArg (fun v : BasedIso D.toBased E.toBased =>
      v.val.weightEquiv (Additive.ofMul χ)) hl
    exact congrArg Additive.toMul ht
  have hτ' : l.torus = τ := by
    have hInv := split_character_hom_ext S.split P.pair.split l.torus.inv τ.inv hlt
    exact (Iso.ext hInv : l.torus.symm = τ.symm) |> congrArg Iso.symm
  let p (c : C) : P.pair.G.val ⟶ (W.factor c).pair.G.val := l.group.hom ≫ R.projection c
  have hs (c : C) : P.pair.T.inclusion ≫ p c = t c ≫ (W.factor c).pair.T.inclusion := by
    change P.pair.T.inclusion ≫ l.group.hom ≫ R.projection c = _
    rw [← Category.assoc, l.torus_comm]
    change (l.torus.hom ≫ R.pair.T.inclusion) ≫ R.projection c = _
    rw [Category.assoc, R.torusSquare, ← Category.assoc, hτ', hτ]
  have hcoord (i : D.toBased.base.support) (c : C) (hm : component i = c) :
      pinnedCoordinate P (labeledSimpleRoot D i) ≫ l.group.hom =
        pinnedCoordinate (W.factor c) (factorSimpleRoot W c ⟨i, hm⟩) ≫ R.inclusion c := by
    let a : SimpleRoot S := ⟨e i.val, (hsimple _).mp ((D.simple_iff _).mp i.property)⟩
    have hlc := pinnedCoordinate_transport l (labeledSimpleRoot D i) a
      ((hlt i.val.val).trans (he i.val))
    have hroot : g ⟨c, (factorSimpleRoot W c ⟨i, hm⟩).val⟩ = i.val :=
      blockRootEquiv_factorSimpleRoot W c ⟨i, hm⟩
    have hji : j a = ⟨c, factorSimpleRoot W c ⟨i, hm⟩⟩ := by
      have hz : R.roots.symm a.val = ⟨c, (factorSimpleRoot W c ⟨i, hm⟩).val⟩ := by
        change R.roots.symm (R.roots (g.symm i.val)) = _
        rw [R.roots.symm_apply_apply, ← hroot, g.symm_apply_apply]
      have hinj : Function.Injective (fun b : (Σ d : C, SimpleRoot (W.factor d).pair) =>
          (⟨b.1, b.2.val⟩ : rootsOfFactors W)) := by
        rintro ⟨d, a⟩ ⟨d', b⟩ heq
        obtain rfl := congrArg Sigma.fst heq
        exact congrArg (Sigma.mk d) (Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.mp heq).2))
      exact hinj hz
    have hh := hpin a
    change pinnedCoordinate Q a = pinnedCoordinate (W.factor (j a).1) (j a).2 ≫
      R.inclusion (j a).1 at hh
    rw [hji] at hh
    exact hlc.trans hh
  refine ⟨p, ⟨isoFanLimit l.group _ R.groupLimit⟩, hs, ?_, ?_⟩
  · intro i c hm
    change pinnedCoordinate P (labeledSimpleRoot D i) ≫ l.group.hom ≫ R.projection c = _
    rw [← Category.assoc, hcoord i c hm, Category.assoc, R.inclusion_projection_same, Category.comp_id]
  · intro i c hm
    change pinnedCoordinate P (labeledSimpleRoot D i) ≫ l.group.hom ≫ R.projection c = _
    rw [← Category.assoc, hcoord i (component i) rfl, Category.assoc,
      R.inclusion_projection_ne _ _ hm, comp_zero]

section MarkedPinnedProducts

open Specs.OpenCell (AreOpposite)
open private base_isPos_iff_subgroupRoots from LinearAlgebraicGroups.Classification.PinnedEquivalence

private theorem markedPinnedProductForFactors (W : PinnedFactors D)
    (M : BorelPair P.pair.G) (N : ∀ i, BorelPair (W.factor i).pair.G)
    (hB : M.positive = P.pair.B) (hT : M.torus = P.pair.T)
    (hBi : ∀ i, (N i).positive = (W.factor i).pair.B)
    (hTi : ∀ i, (N i).torus = (W.factor i).pair.T)
    (hn : Nonempty (DatumComponents D.toBased)) (hD : corootLattice D = ⊤) :
    ∃ (p : MarkedProduct M N)
      (t : ∀ i, P.pair.T.group ⟶ (W.factor i).pair.T.group),
      (∀ i, P.pair.T.inclusion ≫ p.projection i = t i ≫ (W.factor i).pair.T.inclusion) ∧
      (∀ i, IsBlockTorusProjection W i (t i)) ∧
      (∀ (i : D.toBased.base.support) c (h : component i = c),
        pinnedCoordinate P (labeledSimpleRoot D i) ≫ p.projection c =
          pinnedCoordinate (W.factor c) (factorSimpleRoot W c ⟨i, h⟩)) ∧
      ∀ (i : D.toBased.base.support) c, component i ≠ c →
        pinnedCoordinate P (labeledSimpleRoot D i) ≫ p.projection c = 0 := by
  classical
  let C := DatumComponents D.toBased
  letI : Finite C := Quotient.finite _
  obtain ⟨t, ht, ⟨lt⟩⟩ := splitTorusComponentProduct W
  obtain ⟨p, ⟨hp⟩, hs, hpin, hoff⟩ := pinnedProductProjections W hn hD t lt ht
  obtain ⟨c, _, hc, _, hcB⟩ := (RootData.BorelsAndChambers.borelsThroughT P.pair.G
    P.pair.reductive P.pair.T P.pair.split P.pair.maximal).1 P.pair.B P.pair.borel P.pair.containsTorus
  obtain ⟨d, _, hd, _, hdB⟩ := (RootData.BorelsAndChambers.borelsThroughT P.pair.G
    P.pair.reductive P.pair.T P.pair.split P.pair.maximal).1 M.negative M.negativeBorel
      (hT ▸ M.torusInNegative)
  have hpair (v : Cocharacter P.pair.T.group) (i : C) (a : Root (W.factor i).pair.T) :
      pairing (W.factor i).pair.T.group a.val (v ≫ t i) =
        pairing P.pair.T.group (blockRootEquiv W ⟨i, a⟩).val v := by
    rw [pairingAlong, blockRootEquiv_character W i (t i) (ht i) a]
  have hreg (v : Cocharacter P.pair.T.group) (hv : IsRegular P.pair.T v) (i : C) :
      IsRegular (W.factor i).pair.T (v ≫ t i) := by
    intro a
    change pairing (W.factor i).pair.T.group a.val (v ≫ t i) ≠ 0
    rw [hpair]
    exact hv (blockRootEquiv W ⟨i, a⟩)
  have hpos (i : C) : positiveRoots (W.factor i).pair.T (c ≫ t i) =
      subgroupRoots (W.factor i).pair.T (N i).positive := by
    let Q := (W.factor i).pair
    let E := W.attached i
    letI := E.comm
    let l : E.toBased.X →ₗ[ℤ] ℤ :=
      E.toBased.datum.toLinearMap.flip (Additive.ofMul (c ≫ t i))
    have hl (a : Root Q.T) : l (E.toBased.datum.root a) =
        pairing Q.T.group a.val (c ≫ t i) := by
      change E.datum.rootDatum.toLinearMap (E.datum.rootDatum.root a) _ = _
      rw [E.datum.root_eq a]
      exact E.datum.pairing_eq a.val (c ≫ t i)
    have hsimple (a : Root Q.T) (ha : a ∈ E.toBased.base.support) :
        0 < l (E.toBased.datum.root a) := by
      rw [hl, hpair]
      have hh := (D.simple_iff _).mp ((blockRootEquiv_simple W i a).mp ha)
      have h' := hh.1
      rw [hcB] at h'
      exact h'
    obtain ⟨_, _, _, hcorr, _⟩ :=
      RootData.BorelPositivity.borelPositivity Q.G Q.reductive Q.T Q.split Q.maximal
    have hp := (hcorr.1 Q.B Q.borel Q.containsTorus)
    ext a
    rw [hBi i]
    change 0 < pairing Q.T.group a.val (c ≫ t i) ↔ a ∈ subgroupRoots Q.T Q.B
    rw [← hl a]
    exact (positive_of_simple E.toBased l hsimple a).symm.trans
      (base_isPos_iff_subgroupRoots E hp a)
  have hneg (i : C) : positiveRoots (W.factor i).pair.T (d ≫ t i) =
      subgroupRoots (W.factor i).pair.T (N i).negative := by
    have hM := M.opposite
    have hN := (N i).opposite
    unfold AreOpposite at hM hN
    rw [hT, hB, hcB, hdB] at hM
    rw [hTi i, ← hpos i] at hN
    rw [hN]
    ext a
    change 0 < pairing (W.factor i).pair.T.group a.val (d ≫ t i) ↔
      ¬ 0 < pairing (W.factor i).pair.T.group a.val (c ≫ t i)
    rw [hpair, hpair]
    exact (Set.ext_iff.mp hM (blockRootEquiv W ⟨i, a⟩))
  obtain ⟨B, hBp⟩ := markedProductOfRegularProjections P.pair (fun i => (W.factor i).pair)
    M N hT hTi p hp t lt hs c d hc hd (hB.symm ▸ hcB.symm) hdB.symm
      (hreg c hc) (hreg d hd) hpos hneg
  exact ⟨B, t, hBp.symm ▸ hs, ht, hBp.symm ▸ hpin, hBp.symm ▸ hoff⟩

open private inclusion_mono from LinearAlgebraicGroups.RootData.OrderedRootProducts

private def fanLimitOfIsos {C : Type*} [Category C] {I : Type u}
    {X Y : C} {H K : I → C} (e : X ≅ Y) (a : ∀ i, H i ≅ K i)
    (p : ∀ i, Y ⟶ H i) (hp : IsLimit (Fan.mk Y p)) :
    IsLimit (Fan.mk X fun i => e.hom ≫ p i ≫ (a i).hom) := by
  let f (s : Fan K) : s.pt ⟶ Y := Fan.IsLimit.lift hp (fun i => s.proj i ≫ (a i).inv)
  have hf (s : Fan K) (i : I) : f s ≫ p i = s.proj i ≫ (a i).inv :=
    Fan.IsLimit.fac hp _ i
  refine Fan.IsLimit.mk _ (fun s => f s ≫ e.inv) ?_ ?_
  · intro s i
    change (f s ≫ e.inv) ≫ e.hom ≫ p i ≫ (a i).hom = s.proj i
    rw [Category.assoc, e.inv_hom_id_assoc, ← Category.assoc, hf,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro s m hm
    apply (cancel_mono e.hom).mp
    have he : (f s ≫ e.inv) ≫ e.hom = f s := by
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    change m ≫ e.hom = (f s ≫ e.inv) ≫ e.hom
    rw [he]
    apply Fan.IsLimit.hom_ext hp
    intro i
    change (m ≫ e.hom) ≫ p i = f s ≫ p i
    rw [hf]
    apply (cancel_mono (a i).hom).mp
    rw [Category.assoc (s.proj i), Iso.inv_hom_id, Category.comp_id]
    exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (hm i))

private theorem positiveBorelProjections (W : PinnedFactors D)
    {M : BorelPair P.pair.G} {N : ∀ i, BorelPair (W.factor i).pair.G}
    (B : MarkedProduct M N) (hB : M.positive = P.pair.B)
    (hBi : ∀ i, (N i).positive = (W.factor i).pair.B) :
    ∃ b : ∀ i, P.pair.B.group ⟶ (W.factor i).pair.B.group,
      (∀ i, P.pair.B.inclusion ≫ B.projection i = b i ≫ (W.factor i).pair.B.inclusion) ∧
      Nonempty (IsLimit (Fan.mk _ b)) := by
  let e : P.pair.B.group ≅ M.positive.group :=
    eqToIso (congrArg Specs.ClosedSubgroup.group hB.symm)
  let a (i : DatumComponents D.toBased) : (N i).positive.group ≅ (W.factor i).pair.B.group :=
    eqToIso (congrArg Specs.ClosedSubgroup.group (hBi i))
  refine ⟨(fun i => e.hom ≫ B.subgroupProjection .positive i ≫ (a i).hom), ?_,
    ⟨fanLimitOfIsos e a _ (B.subgroupProduct .positive)⟩⟩
  intro i
  have he {G : GroupScheme F} {C H : ClosedSubgroup G} (h : C = H) :
      eqToHom (congrArg Specs.ClosedSubgroup.group h) ≫ H.inclusion = C.inclusion := by
    subst H
    simp
  have h := B.commutes .positive i
  change M.positive.inclusion ≫ B.projection i =
    B.subgroupProjection .positive i ≫ (N i).positive.inclusion at h
  have e' : e.hom ≫ M.positive.inclusion = P.pair.B.inclusion := he hB.symm
  have a' : (a i).hom ≫ (W.factor i).pair.B.inclusion = (N i).positive.inclusion := he (hBi i)
  rw [← e', Category.assoc, h]
  simp only [Category.assoc, a']

end MarkedPinnedProducts

end PinnedProducts

end

/-- The pinned equivalence identifies the ambient split group with the
finite product whose factors are the actual connected blocks. -/
theorem markedSplitPinnedProduct : MarkedSplitPinnedProduct.{u} := by
  classical
  intro F _ A P D M hB hT hD
  cases isEmpty_or_nonempty D.toBased.base.support with
  | inl h =>
    obtain ⟨W, N, hN, hp⟩ := emptyDiagramProduct P D M hD h
    exact ⟨W, N, fun c => (hN c).2, hp⟩
  | inr h =>
    have hn : Nonempty (DatumComponents D.toBased) := h.map (fun i => component i)
    obtain ⟨W⟩ := pinnedFactorsExist D hD
    choose N hN using fun c => splitMarkingsExist (W.factor c).pair
    obtain ⟨B, t, hs, ht, hpin, hoff⟩ := markedPinnedProductForFactors W M N hB hT
      (fun c => (hN c).1) (fun c => (hN c).2) hn hD
    obtain ⟨b, hb, ⟨lb⟩⟩ := positiveBorelProjections W B hB (fun c => (hN c).1)
    exact ⟨W, N, hN, B, t, hs, ht, hpin, hoff,
      productProjectionEquivariance W B.projection b t B.product lb hb hs ht hpin hoff⟩

section AbsoluteSimplicity

open scoped CategoryTheory.MonObj Polynomial

open Specs.QuasiSplitPinnedProduct Specs.AbsoluteDynkinTypes
open _root_.LinearAlgebraicGroups.Specs (SubgroupSections IsNormalSubgroup)
open Specs.Pinning (SplitBorelPair BasedRootDatum BasedIso AttachedDatum)
open Specs.AbstractPairing (Root)
open Specs.GeometricRadicals (IsSemisimple IsReductive IsTorus IsSplitTorus IsMaximalTorus
  IsSmoothConnectedNormal GeometricGroup)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup ConjugatesSubgroups)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing characterValue)
open Specs.SimplyConnectedLattice (corootLattice)
open Specs.DiagonalizableGroups (IntegerCharacters groupAlgebra)
open CocharacterDynamics

open private unitEquiv unitEquiv_unitPoint unitPointHom unitPointHom_apply pointHom
  subgroupInclusionFactors affine_subgroup from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private exists_coordinateCocharacter torusPointEquiv
  from LinearAlgebraicGroups.Reductive.ConnectedTorusCentralizer
open private splitPresentation from LinearAlgebraicGroups.RootData.CharacterPairing
open private basedIso_base_iff from LinearAlgebraicGroups.Classification.PinnedEquivalence
open private inclusion_mono cocharacterPoint_postcompose from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private trivial_split_torus_of_characters from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {F : Type u} [Field F]

private abbrev multiplicativeLine (F : Type u) [Field F] : GroupScheme F :=
  specGroup (groupAlgebra F IntegerCharacters.{u})

local notation "𝔾ₘ" => multiplicativeLine F

private theorem connectedDiagram_of_basedIso {D E : BasedRootDatum.{u}} (e : BasedIso D E)
    (h : (integralDiagram (RootData.integralCartan D.datum D.base)).IsConnected) :
    (integralDiagram (RootData.integralCartan E.datum E.base)).IsConnected := by
  classical
  let v : D.base.support ≃ E.base.support := e.val.indexEquiv.subtypeEquiv (basedIso_base_iff e)
  let A := RootData.integralCartan D.datum D.base
  let B := RootData.integralCartan E.datum E.base
  have hA (i j : D.base.support) : B (v i) (v j) = A i j := by
    change E.datum.toLinearMap (E.datum.root (e.val.indexEquiv j.val))
      (E.datum.coroot (e.val.indexEquiv i.val)) = D.datum.toLinearMap _ _
    rw [← e.val.toHom.root_weightMap_apply D.datum E.datum j.val]
    exact basedIso_pairing_coroot e _ _
  have hd (i j : D.base.support) :
      (integralDiagram B).edges (v i) (v j) = (integralDiagram A).edges i j := by
    repeat rw [LinearAlgebraicGroups.Specs.AbsoluteDynkinTypes.integralDiagram]
    have he : v i = v j ↔ i = j := v.injective.eq_iff
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, (not_congr he).mpr hij, hA]
  refine ⟨h.1.map v, ?_⟩
  intro a b
  obtain ⟨i, rfl⟩ := v.surjective a
  obtain ⟨j, rfl⟩ := v.surjective b
  induction h.2 i j with
  | rel k l hk => exact .rel _ _ ((hd k l).symm ▸ hk)
  | refl k => exact .refl _
  | symm k l _ ih => exact .symm _ _ ih
  | trans k l m _ _ h₁ h₂ => exact .trans _ _ _ h₁ h₂

private theorem units_zpow_surjective [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun z : Fˣ => z ^ n) := by
  suffices h : Function.Surjective (fun z : Fˣ => z ^ n.natAbs) by
    rcases Int.natAbs_eq n with hp | hp
    · intro x
      obtain ⟨z, hz⟩ := h x
      refine ⟨z, ?_⟩
      exact (congrArg (fun a : ℤ => z ^ a) hp).trans
        ((zpow_natCast z n.natAbs).trans hz)
    · intro x
      obtain ⟨z, hz⟩ := h x⁻¹
      refine ⟨z, ?_⟩
      calc
        z ^ n = z ^ (-(n.natAbs : ℤ)) := congrArg (fun a : ℤ => z ^ a) hp
        _ = x := by rw [zpow_neg, zpow_natCast, show z ^ n.natAbs = x⁻¹ from hz, inv_inv]
  intro x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) (Int.natAbs_pos.mpr hn)
  have hz' : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (Int.natAbs_ne_zero.mpr hn)] at hz
    exact x.ne_zero hz.symm
  exact ⟨Units.mk0 z hz', Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_mk0] using hz)⟩

private theorem exists_units_zpow_ne_one [Infinite F] {n : ℤ} (hn : n ≠ 0) :
    ∃ z : Fˣ, z ^ n ≠ 1 := by
  by_contra! h
  have hpow (z : Fˣ) : z ^ n.natAbs = 1 := by
    rcases Int.natAbs_eq n with h₁ | h₁
    · exact (zpow_natCast z n.natAbs).symm.trans
        ((congrArg (fun a : ℤ => z ^ a) h₁).symm.trans (h z))
    · have hz : (z ^ n.natAbs)⁻¹ = 1 := by
        rw [← zpow_natCast, ← zpow_neg, ← h₁]
        exact h z
      exact inv_eq_one.mp hz
  let p : F[X] := Polynomial.X ^ n.natAbs
  have he : p = 1 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.finite_singleton (0 : F)).infinite_compl.mono
    intro z hz
    have hz' : z ≠ 0 := hz
    have h' := congrArg (fun u : Fˣ => (u : F)) (hpow (Units.mk0 z hz'))
    simpa [p] using h'
  have e := congrArg (Polynomial.eval (0 : F)) he
  simp [p, zero_pow (Int.natAbs_ne_zero.mpr hn)] at e

private theorem character_detected_on_a_cocharacter {P : SplitBorelPair F}
    (D : AttachedDatum P) (χ : Character P.T.group) (hχ : χ ≠ 1) :
    ∃ c : Cocharacter P.T.group, pairing P.T.group χ c ≠ 0 := by
  letI := D.comm
  by_contra! h
  apply hχ
  have h' : Additive.ofMul χ = (0 : D.toBased.X) := by
    apply D.toBased.datum.toPerfPair.injective
    rw [D.toBased.datum.toPerfPair.map_zero]
    apply LinearMap.ext
    intro y
    let c := Additive.toMul y
    change D.datum.rootDatum.toLinearMap (Additive.ofMul χ) (Additive.ofMul c) = 0
    rw [D.datum.pairing_eq, h c]
  exact congrArg Additive.toMul h'

private theorem nontrivialTorus_has_cocharacter {P : SplitBorelPair F}
    (D : AttachedDatum P) (hn : ¬ IsZero P.T.group) :
    ∃ c : Cocharacter P.T.group, c ≠ 0 := by
  letI := D.comm
  by_contra! h
  letI : Subsingleton (Character P.T.group) := ⟨fun χ ψ => by
    have hp (χ : Character P.T.group) : χ = 1 := by
      by_contra hχ
      obtain ⟨c, hc⟩ := character_detected_on_a_cocharacter D χ hχ
      apply hc
      rw [h c, ← D.datum.pairing_eq]
      exact map_zero (D.datum.rootDatum.toLinearMap (Additive.ofMul χ))
    exact (hp χ).trans (hp ψ).symm⟩
  exact hn (trivial_split_torus_of_characters P.split)

private theorem normalContainsTorus_of_cocharacters {P : SplitBorelPair F}
    (N : ClosedSubgroup P.G.val)
    (h : ∀ c : Cocharacter P.T.group, ∃ b : 𝔾ₘ ⟶ N.group,
      b ≫ N.inclusion = c ≫ P.T.inclusion) :
    IsSubgroupOf P.T N := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := P.split
  let I := ULift.{u} (Fin r)
  choose c hc using fun j : I => exists_coordinateCocharacter (k := F) j
  choose v hv using fun j : I => h (c j ≫ e.inv)
  apply subgroupInclusionFactors (affine_subgroup P.G.property.1 P.T) N P.T.inclusion
  intro R x
  let b := torusPointEquiv I R
  let t := pointHom e.hom R x
  let u (j : I) := (unitEquiv R).symm (b t j)
  let xj (j : I) := pointHom (c j) R (u j)
  have hxj (j : I) : b (xj j) = Pi.mulSingle j (b t j) := by
    rw [show b (xj j) = Pi.mulSingle j (unitEquiv R (u j)) from hc j R (u j)]
    exact congrArg (Pi.mulSingle j) ((unitEquiv R).apply_symm_apply _)
  let f : (I → Rˣ) →* GroupPoints P.G.val R :=
    (pointHom (e.inv ≫ P.T.inclusion) R).comp b.symm.toMonoidHom
  let K := (SubgroupSections N ((testSpec F).obj (Opposite.op R))).comap f
  have hmem (j : I) : Pi.mulSingle j (b t j) ∈ K := by
    rw [← hxj]
    refine ⟨pointHom (v j) R (u j), ?_⟩
    change pointHom N.inclusion R (pointHom (v j) R (u j)) = f (b (xj j))
    rw [show f (b (xj j)) = pointHom (e.inv ≫ P.T.inclusion) R (xj j) from congrArg
      (pointHom (e.inv ≫ P.T.inclusion) R) (b.symm_apply_apply (xj j)).symm |>.symm]
    exact congrArg (fun g : 𝔾ₘ ⟶ P.G.val => pointHom g R (u j))
      ((hv j).trans (Category.assoc _ _ _))
  have hy : b t ∈ K := by
    rw [← Finset.univ_prod_mulSingle (b t)]
    exact K.prod_mem fun j _ => hmem j
  obtain ⟨z, hz⟩ := hy
  refine ⟨z, ?_⟩
  change pointHom N.inclusion R z = f (b t) at hz
  rw [hz]
  have ht : f (b t) = pointHom (e.inv ≫ P.T.inclusion) R t :=
    congrArg (pointHom (e.inv ≫ P.T.inclusion) R) (b.symm_apply_apply t)
  rw [ht]
  change (x ≫ e.hom.hom.hom) ≫ (e.inv ≫ P.T.inclusion).hom.hom = x ≫ P.T.inclusion.hom.hom
  simp only [Grp.comp_hom_hom, Category.assoc]
  change x ≫ (e.hom ≫ e.inv ≫ P.T.inclusion).hom.hom = _
  rw [e.hom_inv_id_assoc]

open Specs.DatumAndWeyl (Identification)
open Specs.OrderedRootProducts (RootSubgroupFamily Enumerates rootProduct rootCellMap)
open Specs.BorelsAndChambers (positiveRoots)
open Specs.RootGroups (AdditiveLine rootPoint HasScalarAction)
open Specs.GeometricRadicals (IsUnipotentRadical)
open private factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private isReduced_of_smooth_over_field
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private factors_through_closed_of_rational_points
  from LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private rationalWeylLabel_surjective rationalWeylLabel_conjugation
  from LinearAlgebraicGroups.RootData.BorelPositivity
open private maximalTorus_of_geometricallyMaximal
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private splitBorelPair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple rootless_torus_inclusion
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private split_of_torus from LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private lattice_torus_of_split from LinearAlgebraicGroups.RootData.RankOneFlag
open private rootPoint_comp rootPoint_eq from LinearAlgebraicGroups.RootData.RootGroups
open private characterValue_one from LinearAlgebraicGroups.RootData.CharacterPairing
open private isIso_of_schemeIso from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private existsEnumeration from LinearAlgebraicGroups.Flag.OpenCell

private def normalCocharacterLattice {P : SplitBorelPair F} [IsCommMonObj P.T.group.X]
    (N : ClosedSubgroup P.G.val) : Submodule ℤ (Additive (Cocharacter P.T.group)) :=
  ((SubgroupSections N (multiplicativeLine F).X).comap
    (show Cocharacter P.T.group →* ((multiplicativeLine F).X ⟶ P.G.val.X) from
      { toFun := fun c => c.hom.hom ≫ P.T.inclusion.hom.hom
        map_one' := MonObj.one_comp _
        map_mul' := fun _ _ => MonObj.mul_comp _ _ _ })).toAddSubgroup.toIntSubmodule

private theorem mem_normalCocharacterLattice {P : SplitBorelPair F} [IsCommMonObj P.T.group.X]
    (N : ClosedSubgroup P.G.val) (c : Cocharacter P.T.group) :
    Additive.ofMul c ∈ normalCocharacterLattice (P := P) N ↔
      ∃ f : 𝔾ₘ ⟶ N.group, f ≫ N.inclusion = c ≫ P.T.inclusion := by
  constructor
  · rintro ⟨j, hj⟩
    exact factor_group_through_subgroup N (c ≫ P.T.inclusion) j hj
  · rintro ⟨f, hf⟩
    exact ⟨f.hom.hom, congrArg (fun m : 𝔾ₘ ⟶ P.G.val => m.hom.hom) hf⟩

private def baseTestIso :
    (testSpec F).obj (Opposite.op (CommAlgCat.of F F)) ≅ 𝟙_ (SchemeOver F) := by
  let X := (testSpec F).obj (Opposite.op (CommAlgCat.of F F))
  have hx : X.hom = 𝟙 (Spec (CommRingCat.of F)) := by
    change Spec.map (CommRingCat.ofHom (algebraMap F F)) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  let e : X ≅ Over.mk (𝟙 (Spec (CommRingCat.of F))) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of F))) (by
      change 𝟙 (Spec (CommRingCat.of F)) ≫ 𝟙 _ = X.hom
      rw [Category.id_comp, hx])
  exact e ≪≫ Over.mkIdTerminal.uniqueUpToIso isTerminalTensorUnit

private theorem normalCocharacterLattice_saturated [IsAlgClosed F] {P : SplitBorelPair F}
    [IsCommMonObj P.T.group.X] (N : ClosedSubgroup P.G.val)
    (n : ℤ) (y : Additive (Cocharacter P.T.group)) (hn : n ≠ 0)
    (hy : n • y ∈ normalCocharacterLattice (P := P) N) : y ∈ normalCocharacterLattice (P := P) N := by
  let c := Additive.toMul y
  obtain ⟨f, hf⟩ := (mem_normalCocharacterLattice (P := P) N (c ^ n)).mp hy
  let K := 𝔾ₘ
  haveI : UniqueProds IntegerCharacters.{u} :=
    UniqueProds.of_injective_mulHom (MulEquiv.ulift (α := Multiplicative ℤ)).toMulHom
      MulEquiv.ulift.injective inferInstance
  haveI : IsReduced K.X.left := by
    change IsReduced (Spec (CommRingCat.of (MonoidAlgebra F IntegerCharacters.{u})))
    infer_instance
  haveI : LocallyOfFiniteType K.X.hom := by
    change LocallyOfFiniteType (Specs.DiagonalizableGroups.diagonalGroup F IntegerCharacters.{u}).val.X.hom
    exact (Specs.DiagonalizableGroups.diagonalGroup F IntegerCharacters.{u}).property.2.1
  obtain ⟨j, hj⟩ := factors_through_closed_of_rational_points N.inclusion.hom.hom N.isClosedImmersion
    (c ≫ P.T.inclusion).hom.hom (by
      intro r
      let R := CommAlgCat.of F F
      let q : GroupPoints K R := (baseTestIso (F := F)).hom ≫ r
      let x := unitEquiv R q
      obtain ⟨z, hz⟩ := units_zpow_surjective hn x
      let a := unitPoint R z
      have ha : a ^ n = q := by
        apply (unitEquiv R).injective
        rw [map_zpow, unitEquiv_unitPoint]
        exact hz
      have hf' : a ≫ f.hom.hom ≫ N.inclusion.hom.hom = q ≫ (c ≫ P.T.inclusion).hom.hom := by
        rw [← Grp.comp_hom_hom, hf, Grp.comp_hom_hom,
          Grp.Hom.hom_hom_zpow, GrpObj.zpow_comp, GrpObj.comp_zpow]
        change (a ≫ (c ≫ P.T.inclusion).hom.hom) ^ n = q ≫ _
        rw [← GrpObj.zpow_comp, ha]
      refine ⟨(baseTestIso (F := F)).inv ≫ a ≫ f.hom.hom, ?_⟩
      simp only [Category.assoc]
      exact (congrArg ((baseTestIso (F := F)).inv ≫ ·) hf').trans (by
        change (baseTestIso (F := F)).inv ≫ ((baseTestIso (F := F)).hom ≫ r) ≫ _ = _
        simp only [Category.assoc, Iso.inv_hom_id_assoc]))
  exact (mem_normalCocharacterLattice (P := P) N c).mpr (factor_group_through_subgroup N _ j hj)

private theorem normalCocharacterLattice_weyl {P : SplitBorelPair F} (D : AttachedDatum P) :
    letI := D.comm
    ∀ (W : Identification D.datum) (N : ClosedSubgroup P.G.val),
      IsNormalSubgroup N.inclusion → ∀ i : D.base.support,
      ∀ y ∈ normalCocharacterLattice (P := P) N,
        D.datum.rootDatum.coreflection i.val y ∈ normalCocharacterLattice (P := P) N := by
  letI := D.comm
  intro W N hN i y hy
  let w := RootPairing.weylGroup.ofIdx D.datum.rootDatum i.val
  let v := W.labelEquiv w
  let c := Additive.toMul y
  obtain ⟨n, hn⟩ := rationalWeylLabel_surjective W w
  let g := n ≫ W.normalizer.inclusion.hom.hom
  let e := W.image.conjugation v
  have he := rationalWeylLabel_conjugation W n
  rw [hn] at he
  have hy' := W.cocharacterAction w c
  change (RootPairing.Equiv.reflection D.datum.rootDatum i.val).coweightEquiv.symm y =
    Additive.ofMul (c ≫ e.hom) at hy'
  rw [RootPairing.Equiv.reflection_coweightEquiv, RootPairing.coreflection, Module.reflection_symm] at hy'
  have hy'' : D.datum.rootDatum.coreflection i.val y = Additive.ofMul (c ≫ e.hom) := hy'
  rw [hy'']
  obtain ⟨f, hf⟩ := (mem_normalCocharacterLattice (P := P) N c).mp hy
  obtain ⟨j, hconj⟩ := normalSubgroup_conjugate_sections hN
    (toUnit (multiplicativeLine F).X ≫ g) f.hom.hom
  refine ⟨j, ?_⟩
  change j ≫ N.inclusion.hom.hom = (c ≫ e.hom ≫ P.T.inclusion).hom.hom
  rw [hconj, ← Grp.comp_hom_hom, hf]
  have he' : (e.hom ≫ P.T.inclusion).hom.hom =
      (toUnit P.T.group.X ≫ g) * P.T.inclusion.hom.hom * (toUnit P.T.group.X ≫ g)⁻¹ := he
  have hunit : c.hom.hom ≫ toUnit P.T.group.X = toUnit (multiplicativeLine F).X :=
    isTerminalTensorUnit.hom_ext _ _
  change _ = c.hom.hom ≫ (e.hom ≫ P.T.inclusion).hom.hom
  rw [he']
  simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, hunit]
  rfl

private theorem normalCocharacterLattice_nontrivial [IsAlgClosed F]
    {P : SplitBorelPair F} (D : AttachedDatum P) (hG : IsSemisimple P.G) :
    letI := D.comm
    ∀ (N : ClosedSubgroup P.G.val), IsSmoothConnectedNormal N →
      ¬ IsZero N.group → normalCocharacterLattice (P := P) N ≠ ⊥ := by
  letI := D.comm
  intro N hN hN0 hbot
  let H := closedSubgroupAlgebraicGroup N
  have hH := normalSubgroupSemisimplicity P.G hG N hN
  obtain ⟨S, hS, hSmax⟩ := MaximalToriExist.geometricallyMaximalTorusExists H hN.1 hN.2.1
  have hsplit : IsSplitTorus S.group :=
    split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup S)).mp hS)
  let Q := splitBorelPair H (reductive_of_semisimple H hH) S hsplit hSmax
  let E := Classification.Pinning.attachedDatum Q
  have hs0 : ¬ IsZero S.group := by
    intro hz
    letI : IsEmpty (Root Q.T) := ⟨fun a => a.property.1 (hz.eq_of_src _ _)⟩
    letI : IsIso Q.T.inclusion := rootless_torus_inclusion Q
    exact hN0 (hz.of_iso (asIso Q.T.inclusion).symm)
  obtain ⟨c, hc⟩ := nontrivialTorus_has_cocharacter E hs0
  let T₀ := subgroupOfSubgroup N S
  obtain ⟨T', hT', j, hj⟩ := torusInMaximalTorus P.G T₀ hS
  letI := hG.2.1
  obtain ⟨g, e, he⟩ := MaximalToriConjugate.maximalToriConjugate P.G hG.1
    (GeometricallyConnected.connectedSpace_of_subsingleton P.G.val.X.hom)
    T' P.T hT' (maximalTorus_of_geometricallyMaximal P.G P.T
      (lattice_torus_of_split P.split) P.maximal)
  let f := j ≫ e.hom
  letI : Mono T₀.inclusion := inclusion_mono T₀
  letI : Mono j := mono_of_mono_fac hj
  have hf : (f ≫ P.T.inclusion).hom.hom =
      (toUnit T₀.group.X ≫ g) * T₀.inclusion.hom.hom * (toUnit T₀.group.X ≫ g)⁻¹ := by
    rw [show f ≫ P.T.inclusion = j ≫ e.hom ≫ P.T.inclusion from Category.assoc _ _ _]
    change j.hom.hom ≫ (e.hom ≫ P.T.inclusion).hom.hom = _
    rw [he]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, comp_toUnit,
      ← Grp.comp_hom_hom, hj]
  have hc0 : c ≫ f ≠ 0 := by
    intro h
    apply hc
    have h' : (c ≫ j) ≫ e.hom = (0 : 𝔾ₘ ⟶ S.group) ≫ j ≫ e.hom := by
      simpa only [Category.assoc, zero_comp] using h
    exact (cancel_mono j).mp ((cancel_mono e.hom).mp h')
  have hmem : Additive.ofMul (c ≫ f) ∈ normalCocharacterLattice (P := P) N := by
    obtain ⟨w, hw⟩ := normalSubgroup_conjugate_sections hN.2.2
      (toUnit (multiplicativeLine F).X ≫ g) (c.hom.hom ≫ S.inclusion.hom.hom)
    refine ⟨w, ?_⟩
    change w ≫ N.inclusion.hom.hom = (c ≫ f ≫ P.T.inclusion).hom.hom
    rw [hw, Grp.comp_hom_hom, hf]
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
    have hunit : c.hom.hom ≫ toUnit T₀.group.X = toUnit (multiplicativeLine F).X :=
      isTerminalTensorUnit.hom_ext _ _
    rw [hunit]
    rfl
  rw [hbot, Submodule.mem_bot] at hmem
  exact hc0 (congrArg Additive.toMul hmem)

open private rootPoint_surjective rootPoint_zero from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private additivePoints_add from LinearAlgebraicGroups.RootData.RootGroups
open private irreducible_of_geometricallyConnected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem rootInNormalSubgroup [IsAlgClosed F] {P : SplitBorelPair F}
    (D : AttachedDatum P) (N : ClosedSubgroup P.G.val) (hN : IsNormalSubgroup N.inclusion)
    (hT : IsSubgroupOf P.T N)
    (a : Root P.T) (U : ClosedSubgroup P.G.val) (hU : Specs.RootGroups.IsRootSubgroup P.T U a.val)
    (A : AdditiveLine F) (e : A.group ≅ U.group)
    (he : HasScalarAction P.T a.val (e.hom ≫ U.inclusion)) : IsSubgroupOf U N := by
  let R := CommAlgCat.of F F
  let b := baseTestIso (F := F)
  let x := e.hom ≫ U.inclusion
  obtain ⟨m, hm⟩ := character_detected_on_a_cocharacter D a.val a.property.1
  obtain ⟨z, hz⟩ := exists_units_zpow_ne_one (F := F) hm
  let t := cocharacterPoint m R z
  let g : GroupPoints P.G.val R := pointHom P.T.inclusion R t
  let C := SubgroupSections N ((testSpec F).obj (Opposite.op R))
  have hval : characterValue a.val R t ≠ 1 := by
    rw [(RootData.CharacterPairing.characterPairingComposition P.T.group a.val m).2 R z]
    exact fun h => hz (Units.ext h)
  obtain ⟨j, hj⟩ := hT
  have hg : g ∈ C := by
    refine ⟨t ≫ j.hom.hom, ?_⟩
    change (t ≫ j.hom.hom) ≫ N.inclusion.hom.hom = t ≫ P.T.inclusion.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hj]
  have hadd (r s : R) : rootPoint x R (r + s) = rootPoint x R r * rootPoint x R s := by
    simp only [rootPoint_eq, additivePoints_add]
    exact MonObj.mul_comp _ _ _
  have hneg (r : R) : rootPoint x R (-r) = (rootPoint x R r)⁻¹ := by
    have h' := hadd r (-r)
    rw [add_neg_cancel, rootPoint_zero] at h'
    exact (mul_eq_one_iff_inv_eq.mp h'.symm).symm
  have hroot (s : R) : rootPoint x R s ∈ C := by
    let v := (characterValue a.val R t - 1)⁻¹ * s
    let w := rootPoint x R v
    obtain ⟨a₁, ha₁⟩ := C.inv_mem hg
    have h₁ : w * g⁻¹ * w⁻¹ ∈ C := by
      obtain ⟨a₂, ha₂⟩ := normalSubgroup_conjugate_sections hN w a₁
      refine ⟨a₂, ?_⟩
      change a₁ ≫ N.inclusion.hom.hom = g⁻¹ at ha₁
      change a₂ ≫ N.inclusion.hom.hom = w * g⁻¹ * w⁻¹
      rw [ha₂, ha₁]
    have h₂ : g * (w * g⁻¹ * w⁻¹) ∈ C := C.mul_mem hg h₁
    have h₃ : g * (w * g⁻¹ * w⁻¹) = rootPoint x R s := by
      calc
        _ = g * w * g⁻¹ * w⁻¹ := by simp [mul_assoc]
        _ = rootPoint x R (characterValue a.val R t * v) * rootPoint x R (-v) := by
          exact congrArg₂ (· * ·) (he R t v) (hneg v).symm
        _ = rootPoint x R s := by
          rw [← hadd]
          congr 1
          have hn : characterValue a.val R t - 1 ≠ 0 := sub_ne_zero.mpr hval
          change characterValue a.val R t * v + -v = s
          rw [← sub_eq_add_neg, ← sub_one_mul, show v = (characterValue a.val R t - 1)⁻¹ * s from rfl,
            ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
    exact h₃ ▸ h₂
  letI : Smooth U.group.X.hom := hU.1
  letI : IsReduced U.group.X.left := isReduced_of_smooth_over_field U.group.X.hom
  letI : LocallyOfFiniteType U.group.X.hom := (closedSubgroupAlgebraicGroup U).property.2.1
  obtain ⟨f, hf⟩ := factors_through_closed_of_rational_points N.inclusion.hom.hom N.isClosedImmersion
    U.inclusion.hom.hom (by
      intro p
      let q : GroupPoints U.group R := b.hom ≫ p
      obtain ⟨s, hs⟩ := rootPoint_surjective e R q
      obtain ⟨v, hv⟩ := hroot s
      have hv' : v ≫ N.inclusion.hom.hom = (b.hom ≫ p) ≫ U.inclusion.hom.hom := by
        change v ≫ N.inclusion.hom.hom = q ≫ U.inclusion.hom.hom
        change v ≫ N.inclusion.hom.hom = rootPoint x R s at hv
        rw [hv, rootPoint_comp, hs]
      refine ⟨b.inv ≫ v, ?_⟩
      rw [Category.assoc, hv', Category.assoc, b.inv_hom_id_assoc])
  exact factor_group_through_subgroup N U.inclusion f hf

private theorem containsSplitRootCell_isIso {P : SplitBorelPair F} (D : AttachedDatum P)
    (U : RootSubgroupFamily P.T) (N : ClosedSubgroup P.G.val)
    (hT : IsSubgroupOf P.T N) (hU : ∀ a, IsSubgroupOf (U a).val N) :
    IsIso N.inclusion := by
  letI := D.comm
  letI := D.datum.finiteRoots
  obtain ⟨c, _, hc, _, _⟩ := (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive
    P.T P.split P.maximal).1 P.B P.borel P.containsTorus
  obtain ⟨l, hl⟩ := existsEnumeration (positiveRoots P.T c)
  obtain ⟨m, hm⟩ := existsEnumeration (positiveRoots P.T (oppositeCocharacter c))
  have ho := RootData.OrderedRootProducts.regularRootCell P.G P.reductive P.T P.split P.maximal c hc U m l hm hl
  let X := Specs.OrderedRootProducts.product (fun a => (U a).val.group.X)
  have hf (l : List (Root P.T)) : ∃ f : X l ⟶ N.group.X, f ≫ N.inclusion.hom.hom = rootProduct U l := by
    induction l with
    | nil =>
      exact ⟨1, MonObj.one_comp _⟩
    | cons a l ih =>
      obtain ⟨j, hj⟩ := hU a
      obtain ⟨f, hf⟩ := ih
      refine ⟨(fst _ _ ≫ j.hom.hom) * (snd _ _ ≫ f), ?_⟩
      have hj' := congrArg (fun k : (U a).val.group ⟶ P.G.val => k.hom.hom) hj
      simp only [rootProduct, MonObj.mul_comp, Category.assoc, ← Grp.comp_hom_hom, hj, hf]
      rfl
  obtain ⟨j, hj⟩ := hT
  obtain ⟨fm, hfm⟩ := hf m
  obtain ⟨fl, hfl⟩ := hf l
  let v : X m ⊗ (P.T.group.X ⊗ X l) ⟶ N.group.X :=
    (fst _ _ ≫ fm) * (snd _ _ ≫ ((fst _ _ ≫ j.hom.hom) * (snd _ _ ≫ fl)))
  have hv : v ≫ N.inclusion.hom.hom = rootCellMap P.T U m l := by
    simp only [v, rootCellMap, MonObj.mul_comp, Category.assoc,
      ← Grp.comp_hom_hom, hj, hfm, hfl]
    rfl
  have hasPoint (l : List (Root P.T)) : Nonempty (𝟙_ (SchemeOver F) ⟶ X l) := by
    induction l with
    | nil => exact ⟨𝟙 _⟩
    | cons a l ih => exact ⟨lift η[(U a).val.group.X] ih.some⟩
  let s : 𝟙_ (SchemeOver F) ⟶ X m ⊗ (P.T.group.X ⊗ X l) :=
    lift (hasPoint m).some (lift η[P.T.group.X] (hasPoint l).some)
  have hne : (Set.range (rootCellMap P.T U m l).left).Nonempty :=
    ⟨_, s.left (IsLocalRing.closedPoint F), rfl⟩
  letI := P.G.property.2.1
  letI := P.G.property.2.2
  letI := P.reductive.2.1
  letI : IrreducibleSpace P.G.val.X.left := irreducible_of_geometricallyConnected P.G.val
  letI := ho
  have hd : Dense (Set.range (rootCellMap P.T U m l).left) :=
    (IsOpenImmersion.isOpen_range _).dense hne
  letI := N.isClosedImmersion
  have hall := N.inclusion.hom.hom.left.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
    (show Set.range (rootCellMap P.T U m l).left ⊆ Set.range N.inclusion.hom.hom.left from by
      rw [← hv, Over.comp_left]
      rintro _ ⟨x, rfl⟩
      exact ⟨v.left x, rfl⟩)
  rw [hd.closure_eq] at hall
  letI : Surjective N.inclusion.hom.hom.left := ⟨fun x => hall (Set.mem_univ x)⟩
  letI := P.reductive.1
  letI : IsReduced P.G.val.X.left := isReduced_of_smooth_over_field P.G.val.X.hom
  letI : IsIso N.inclusion.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  exact isIso_of_schemeIso N.inclusion

private theorem connectedSplitNormalSubgroup [IsAlgClosed F]
    {P : SplitBorelPair F} (D : AttachedDatum P)
    (hG : IsSemisimple P.G) (hD : corootLattice D = ⊤)
    (hc : (integralDiagram (RootData.integralCartan D.toBased.datum D.toBased.base)).IsConnected) :
    letI := D.comm
    ∀ (W : Identification D.datum) (N : ClosedSubgroup P.G.val),
      IsSmoothConnectedNormal N → IsZero N.group ∨ IsIso N.inclusion := by
  classical
  letI := D.comm
  intro W N hN
  by_cases hn : IsZero N.group
  · exact Or.inl hn
  right
  let M : Submodule ℤ D.toBased.Y := normalCocharacterLattice (P := P) N
  rcases connectedCoreflectionInvariantLattice D.toBased hD hc M
    (normalCocharacterLattice_saturated N) (normalCocharacterLattice_weyl D W N hN.2.2) with hm | hm
  · exact (normalCocharacterLattice_nontrivial D hG N hN hn hm).elim
  have hT : IsSubgroupOf P.T N := normalContainsTorus_of_cocharacters N (fun c => by
    have hc' : Additive.ofMul c ∈ M := by rw [hm]; exact Submodule.mem_top
    exact (mem_normalCocharacterLattice N c).mp hc')
  have hroot (a : Root P.T) : ∃ (U : ClosedSubgroup P.G.val),
      Specs.RootGroups.IsRootSubgroup P.T U a.val ∧ IsSubgroupOf U N := by
    obtain ⟨U, hU, _, _, ⟨A, x, hx⟩, _⟩ :=
      ((RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split P.maximal).2
        a.val a.property).2.2
    exact ⟨U, hU, rootInNormalSubgroup D N hN.2.2 hT a U hU A x hx⟩
  choose U hU hN' using hroot
  exact containsSplitRootCell_isIso D (fun a => ⟨U a, hU a⟩) N hT hN'


open Specs.Pinning (PinnedGroup PinnedIso)
open private fibreTowerIso of_fullCorootLattice from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private coroot_span_of_equiv nontrivial_of_root
  from LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
open private normal_postcompose_iso pushSubgroup from LinearAlgebraicGroups.RootData.OrderedRootProducts

/-- Compare the chosen split datum with both fibres of the same integral
model, so the connected diagram used over the algebraic closure is the
given diagram. -/
private theorem connectedDatumAbsolutelyAlmostSimple {P : SplitBorelPair F}
    (D : AttachedDatum P) (hG : IsSemisimple P.G) (hD : corootLattice D = ⊤)
    (hc : (integralDiagram (RootData.integralCartan D.toBased.datum D.toBased.base)).IsConnected) :
    IsAbsolutelyAlmostSimple P.G := by
  letI := D.comm
  letI := D.toBased.finiteRoots
  let K := AlgebraicClosure F
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨A, R, e, _⟩ := M.fieldFibre F
  obtain ⟨A', R', e', _⟩ := M.fieldFibre K
  obtain ⟨f⟩ := ((Classification.PinnedEquivalence.pinnedEquivalence.2 F).2.1
    P R.pinned.pair D R.attached).mpr ⟨R.datumIso.val⟩
  let g : (GeometricGroup P.G).val ≅ R'.pinned.pair.G.val :=
    (groupBaseChange F K).mapIso (f ≪≫ e.symm) ≪≫
      ((fibreTowerIso F K).app M.group).symm ≪≫ e'
  obtain ⟨_, _, E, ⟨W⟩⟩ := RootData.AbsoluteDynkinTypes.splitPinnedComparison A' R'.pinned.pair
  letI := E.comm
  let e0 : D.toBased ⟶ R'.attached.toBased := R'.datumIso
  let e1 : R'.attached.toBased ⟶ E.toBased :=
    Classification.Pinning.inducedBasedIso (PinnedIso.refl R'.pinned) R'.attached E
  let eD : D.toBased ⟶ E.toBased := e0 ≫ e1
  have hEc := connectedDiagram_of_basedIso eD hc
  have hE : corootLattice E = ⊤ := coroot_span_of_equiv _ _ eD.val hD
  have hG' := of_fullCorootLattice R'.pinned.pair E hE
  obtain ⟨i⟩ := hEc.1
  refine ⟨hG, fun hz => nontrivial_of_root R'.pinned.pair i.val (hz.of_iso g.symm), ?_⟩
  intro N hN
  let V := pushSubgroup g N
  have hv : IsSmoothConnectedNormal (G := R'.pinned.pair.G) V :=
    ⟨hN.1, hN.2.1, normal_postcompose_iso N.inclusion g hN.2.2⟩
  rcases connectedSplitNormalSubgroup E hG' hE hEc W V hv with hz | hi
  · exact .inl hz
  · right
    letI : IsIso (N.inclusion ≫ g.hom) := hi
    exact IsIso.of_isIso_comp_right N.inclusion g.hom

/-- A diagram component is connected over the algebraic closure and gives
an absolutely almost simple factor. -/
theorem pinnedFactorsAbsolutelyAlmostSimple : PinnedFactorsAbsolutelyAlmostSimple.{u} := by
  intro F _ A P D W c
  let E := W.attached c
  let B := (W.coordinates.blocks c).block
  letI := B.datum.finiteRoots
  letI := E.comm
  exact connectedDatumAbsolutelyAlmostSimple E (W.semisimple c)
    (coroot_span_of_equiv _ _ (W.based c).val B.fullCorootLattice)
    (connectedDiagram_of_basedIso (W.based c) (componentDiagramConnected D.toBased (c := c) B))

/-- Split pinned product decomposition, with the prescribed Borel pair
and the equivariance of all actual component projections. -/
theorem splitPinnedProduct : Statement.{u} := by
  intro F _ A P D M hB hT _ hD
  obtain ⟨W, N, hN, hp⟩ := markedSplitPinnedProduct P D M hB hT hD
  exact ⟨W, N, fun c => ⟨pinnedFactorsAbsolutelyAlmostSimple W c, hN c⟩, hp⟩

end
end AbsoluteSimplicity

end LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedProduct
