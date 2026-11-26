import Specs.LinearAlgebraicGroups.Solvable.LieKolchin
import LinearAlgebraicGroups.Solvable.Triangularization
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct commutatorElement

universe u

namespace LinearAlgebraicGroups.LieKolchin

noncomputable section

open _root_.LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.RationalRepresentations
open private closedSubgroupAlgebraic from LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private HasEigenvectors flags_of_eigenvectors stable_line
  from LinearAlgebraicGroups.Solvable.Triangularization

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option Elab.async false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [IsAlgClosed k]

private abbrev base := 𝟙_ (SchemeOver k)
private abbrev sections (G : Specs.GroupScheme k) := (base (k := k)) ⟶ G.X

private abbrev globalFunctions (X : SchemeOver k) := Γ(X.left, ⊤)

private def valueAt {X : SchemeOver k} (p : base (k := k) ⟶ X) :
    globalFunctions X →+* k :=
  (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom


private theorem valueAt_comp {X Y : SchemeOver k} (f : X ⟶ Y) (p : base ⟶ X)
    (a : globalFunctions Y) :
    valueAt (p ≫ f) a = valueAt p (f.left.appTop a) := by
  simp only [valueAt, Over.comp_left, Scheme.Hom.comp_appTop, Category.assoc,
    CommRingCat.hom_comp, RingHom.comp_apply]

private theorem functions_separated (X : SchemeOver k) [LocallyOfFiniteType X.hom]
    [IsReduced X.left] (a : globalFunctions X) (h : ∀ p : base ⟶ X, valueAt p a = 0) :
    a = 0 := by
  by_contra ha
  have hU : Set.Nonempty (X.left.basicOpen a : Set X.left) := by
    by_contra h
    exact ha ((AlgebraicGeometry.basicOpen_eq_bot_iff a).mp
      ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp h))
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, hx, hclosed⟩ := nonempty_inter_closedPoints hU
    (X.left.basicOpen a).2.isLocallyClosed
  let p : base ⟶ X :=
    Over.homMk (pointOfClosedPoint X.hom x hclosed) (pointOfClosedPoint_comp X.hom x hclosed)
  have hp : p.left (IsLocalRing.closedPoint k) = x := pointOfClosedPoint_apply X.hom x hclosed _
  have hz : p.left.appTop a = 0 :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective (by
      rw [map_zero]
      exact h p)
  have hm : IsLocalRing.closedPoint k ∈ p.left ⁻¹ᵁ X.left.basicOpen a := by
    change p.left (IsLocalRing.closedPoint k) ∈ X.left.basicOpen a
    rwa [hp]
  rw [Scheme.preimage_basicOpen_top, hz, Scheme.basicOpen_zero] at hm
  exact hm

private theorem finite_zero_choice (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    {Idx : Type*} [Finite Idx] (a : Idx → globalFunctions G.val.X)
    (h : ∀ p : sections G.val, ∃ i, valueAt p (a i) = 0) :
    ∃ i, a i = 0 := by
  classical
  letI : IsIntegral G.val.X.left := WordDomainGeometry.smoothConnectedGroupIntegral G hs hc
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  letI := Fintype.ofFinite Idx
  have hp : ∏ i, a i = 0 := by
    apply functions_separated
    intro p
    obtain ⟨i, hi⟩ := h p
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
  exact ⟨i, hi⟩

private def pointMap {G H : Specs.GroupScheme k} (f : G ⟶ H) : sections G →* sections H :=
  ((yonedaGrp.map f).app (op base)).hom

private def Regular {G : Specs.GroupScheme k} {V : Type u} [AddCommGroup V] [Module k V]
    (π : sections G →* Module.End k V) : Prop :=
  ∀ (x : V) (ℓ : V →ₗ[k] k), ∃ a : globalFunctions G.X, ∀ p, valueAt p a = ℓ (π p x)

private theorem Regular.comp {G H : Specs.GroupScheme k} {V : Type u}
    [AddCommGroup V] [Module k V] {π : sections G →* Module.End k V}
    (h : Regular π) (f : H ⟶ G) : Regular (π.comp (pointMap f)) := by
  intro x ℓ
  obtain ⟨a, ha⟩ := h x ℓ
  exact ⟨f.hom.hom.left.appTop a, fun p ↦
    (valueAt_comp f.hom.hom p a).symm.trans (ha (pointMap f p))⟩

private def HasCommonEigenvectors (G : Specs.GroupScheme k) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (π : sections G →* Module.End k V), Regular π →
      ∃ v : V, v ≠ 0 ∧ ∀ g, ∃ c : k, π g v = c • v

private theorem apply_ne_zero {H : Type*} [Group H] {V : Type u}
    [AddCommGroup V] [Module k V] (π : H →* Module.End k V) (p : H)
    {v : V} (hv : v ≠ 0) : π p v ≠ 0 := by
  intro hz
  apply hv
  have h := congrArg (fun t : Module.End k V ↦ t v) (map_mul π p⁻¹ p)
  simpa [Module.End.mul_apply, hz] using h

private theorem commuting_commonEigenvector {I : Type*} {V : Type u}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (f : I → Module.End k V) (h : ∀ i j, Commute (f i) (f j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : k, f i v = c • v := by
  generalize hd : Module.finrank k V = n
  induction n using Nat.strongRecOn generalizing V with
  | ind n ih =>
    by_cases hf : ∀ i, ∃ c : k, f i = c • (1 : Module.End k V)
    · obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact ⟨v, hv, fun i ↦ by obtain ⟨c, hc⟩ := hf i; exact ⟨c, by rw [hc]; rfl⟩⟩
    push Not at hf
    obtain ⟨i, hi⟩ := hf
    obtain ⟨c, hce⟩ := (f i).exists_eigenvalue
    let W := (f i).eigenspace c
    have hne : W ≠ ⊤ := by
      intro hw
      apply hi c
      ext v
      exact Module.End.mem_eigenspace_iff.mp (hw ▸ Submodule.mem_top : v ∈ W)
    letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hce
    have hW (j : I) : ∀ x ∈ W, f j x ∈ W := by
      intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change (f i * f j) x = _
      rw [(h i j).eq, Module.End.mul_apply, hx, map_smul]
    let fW (j : I) := (f j).restrict (hW j)
    have hcom (i j : I) : Commute (fW i) (fW j) := by
      ext x
      exact DFunLike.congr_fun (h i j).eq x.val
    obtain ⟨v, hv, he⟩ := ih (Module.finrank k W) (hd ▸ Submodule.finrank_lt hne)
      fW hcom rfl
    exact ⟨v, fun hz ↦ hv (Subtype.ext hz), fun i ↦
      let ⟨a, ha⟩ := he i
      ⟨a, congrArg Subtype.val ha⟩⟩

/-- An irreducible group orbit contained in finitely many eigenspaces lies in a
single one. This is the finite closed-cover argument applied to the orbit of
one vector. -/
private theorem orbit_in_eigenspace (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (π : sections G.val →* Module.End k V) (hπ : Regular π)
    (f : Module.End k V) {v : V} (hv : v ≠ 0) {c : k} (he : f v = c • v)
    (horb : ∀ g, ∃ a : k, f (π g v) = a • π g v) :
    ∀ g, f (π g v) = c • π g v := by
  classical
  let I := {a : k // f.HasEigenvalue a}
  letI : Finite I := f.finite_hasEigenvalue.to_subtype
  suffices h : ∃ a : I, ∀ g, f (π g v) = (a : k) • π g v by
    obtain ⟨a, ha⟩ := h
    have e := ha 1
    rw [map_one] at e
    change f v = (a : k) • v at e
    have eq : (a : k) = c := smul_left_injective k hv (e.symm.trans he)
    simpa only [eq] using ha
  by_contra! h
  choose g hg using h
  have hx (a : I) : f (π (g a) v) - (a : k) • π (g a) v ≠ 0 :=
    sub_ne_zero.mpr (hg a)
  choose ℓ hℓ using fun a ↦ Module.Projective.exists_dual_ne_zero k (hx a)
  choose s hsec using fun a : I ↦ hπ v ((ℓ a).comp (f - (a : k) • 1))
  have hz (a : I) (p : sections G.val) :
      valueAt p (s a) = ℓ a (f (π p v) - (a : k) • π p v) := hsec a p
  obtain ⟨a, ha⟩ := finite_zero_choice G hs hc s (fun p ↦ by
    obtain ⟨b, hb⟩ := horb p
    have heigen : f.HasEigenvalue b :=
      Module.End.hasEigenvalue_of_hasEigenvector (x := π p v)
        ⟨Module.End.mem_eigenspace_iff.mpr hb, apply_ne_zero π p hv⟩
    exact ⟨⟨b, heigen⟩, by rw [hz, hb, sub_self, map_zero]⟩)
  exact hℓ a (by rw [← hz, ha, map_zero])

private theorem valueAt_const {X : SchemeOver k} (p : base ⟶ X) (c : k) :
    valueAt p (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) = c := by
  have h : p.left ≫ X.hom = 𝟙 (Spec (CommRingCat.of k)) := Over.w p
  have he := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] at he
  change (X.hom.appTop ≫ p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom)
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) = c
  rw [← Category.assoc, he, Category.id_comp]
  exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.apply_symm_apply c

private theorem regular_root_constant (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (a : globalFunctions G.val.X) (m : ℕ) (hm : 0 < m)
    (h : ∀ p : sections G.val, valueAt p a ^ m = 1) :
    ∀ p : sections G.val, valueAt p a = valueAt (1 : sections G.val) a := by
  let I := {c : k // c ^ m = 1}
  have hI : Set.Finite {c : k | c ^ m = 1} := by
    simpa [Polynomial.IsRoot.def, sub_eq_zero] using
      Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hm (1 : k))
  letI : Finite I := hI.to_subtype
  let b (c : I) := a - G.val.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c.val)
  have hb (c : I) (p : sections G.val) : valueAt p (b c) = valueAt p a - c.val := by
    rw [map_sub, valueAt_const]
  obtain ⟨c, hc'⟩ := finite_zero_choice G hs hc b (fun p ↦
    ⟨⟨valueAt p a, h p⟩, by rw [hb, sub_self]⟩)
  have he (p : sections G.val) : valueAt p a = c.val := by
    apply sub_eq_zero.mp
    rw [← hb, hc', map_zero]
  exact fun p ↦ (he p).trans (he 1).symm

private theorem derived_step (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (D : ClosedSubgroup G.val) (hsD : Smooth D.group.X.hom)
    (hcD : ConnectedSpace D.group.X.left)
    (hcomm : SubgroupSections D base = commutator (sections G.val))
    (ih : HasCommonEigenvectors D.group) : HasCommonEigenvectors G.val := by
  intro V _ _ _ _ π hπ
  let j := pointMap D.inclusion
  have hJ : j.range = commutator (sections G.val) := hcomm
  have : j.range.Normal := by rw [hJ]; infer_instance
  obtain ⟨v, hv, h⟩ := ih V (π.comp j) (hπ.comp D.inclusion)
  choose χ hχ using h
  change ∀ n, π (j n) v = χ n • v at hχ
  -- Work on the entire common eigenspace for the character of the chosen vector.
  let W : Submodule k V := ⨅ n : sections D.group, (π (j n)).eigenspace (χ n)
  have hW (x : V) : x ∈ W ↔ ∀ n, π (j n) x = χ n • x := by
    simp only [W, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hvW : v ∈ W := (hW v).mpr hχ
  letI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr
    (fun e ↦ hv ((Submodule.eq_bot_iff _).mp e v hvW))
  have hpres (g : sections G.val) (x : V) (hx : x ∈ W) : π g x ∈ W := by
    by_cases hx0 : x = 0
    · simp [hx0]
    apply (hW _).mpr
    intro n
    apply orbit_in_eigenspace G hs hc π hπ (π (j n)) hx0 ((hW x).mp hx n) _ g
    intro p
    have ht : p⁻¹ * j n * p ∈ j.range := by
      simpa only [inv_inv] using
        (inferInstance : j.range.Normal).conj_mem (j n) ⟨n, rfl⟩ p⁻¹
    obtain ⟨n', hn'⟩ := ht
    have hmul : j n * p = p * j n' := by
      rw [hn']
      simp only [mul_assoc, mul_inv_cancel_left]
    refine ⟨χ n', ?_⟩
    change (π (j n) * π p) x = _
    rw [← map_mul, hmul, map_mul, Module.End.mul_apply, (hW x).mp hx n', map_smul]
  let πW : sections G.val →* Module.End k W :=
    { toFun := fun g ↦ (π g).restrict (hpres g)
      map_one' := by ext x; exact DFunLike.congr_fun (map_one π) x.val
      map_mul' := fun g p ↦ by ext x; exact DFunLike.congr_fun (map_mul π g p) x.val }
  have hscalar (n : sections D.group) : πW (j n) = χ n • 1 := by
    ext x
    exact (hW x.val).mp x.property n
  -- The determinant on this invariant space kills the abstract commutator subgroup.
  let δ := (LinearMap.det.comp πW).toHomUnits
  have hker : commutator (sections G.val) ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hpow (n : sections D.group) : χ n ^ Module.finrank k W = 1 := by
    have hn : δ (j n) = 1 := hker (by rw [← hJ]; exact ⟨n, rfl⟩)
    have hd := congrArg (fun z : kˣ ↦ z.val) hn
    change LinearMap.det (πW (j n)) = 1 at hd
    simpa [hscalar, LinearMap.det_smul] using hd
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one k hv
  obtain ⟨a, ha⟩ := (hπ.comp D.inclusion) v ℓ
  have ha' (n : sections D.group) : valueAt n a = χ n := by
    rw [ha]
    change ℓ (π (j n) v) = χ n
    simp [hχ, hℓ]
  have hconstant := regular_root_constant (closedSubgroupAlgebraic G D) hsD hcD
    a (Module.finrank k W) (Module.finrank_pos (R := k) (M := W))
    (fun n ↦ by rw [ha', hpow])
  have hχ1 : χ 1 = 1 := by
    apply smul_left_injective k hv
    simpa using (hχ 1).symm
  have htriv (n : sections D.group) : πW (j n) = 1 := by
    rw [hscalar, ← ha' n, hconstant n, ha' 1, hχ1, one_smul]
  have hcom (g p : sections G.val) : Commute (πW g) (πW p) := by
    have ht : ⁅g, p⁆ ∈ j.range := hJ.symm ▸
      Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top p)
    obtain ⟨n, hn⟩ := ht
    have he : g * p = ⁅g, p⁆ * (p * g) := by
      simp only [commutatorElement_def, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    calc
      πW g * πW p = πW (g * p) := (map_mul _ _ _).symm
      _ = πW p * πW g := by rw [he, map_mul, ← hn, htriv, one_mul, map_mul]
  obtain ⟨w, hw, hEigen⟩ := commuting_commonEigenvector πW hcom
  exact ⟨w, fun hz ↦ hw (Subtype.ext hz), fun p ↦
    let ⟨c, he⟩ := hEigen p
    ⟨c, congrArg Subtype.val he⟩⟩

private theorem derived_series (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    {n : ℕ} {H : Specs.GroupScheme k} (h : Specs.SchemeDerivedGroup.DerivedSeries G.val n H) :
    (IsAffine H.X.left ∧ LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom) ∧
      Smooth H.X.hom ∧ ConnectedSpace H.X.left ∧
      (HasCommonEigenvectors H → HasCommonEigenvectors G.val) := by
  induction h with
  | zero => exact ⟨G.property, hs, hc, id⟩
  | @succ n H _ D hd ih =>
    obtain ⟨hA, hS, hC, hprev⟩ := ih
    let H' : AffineAlgebraicGroup k := ⟨H, hA⟩
    obtain ⟨hDs, hDc, hDcomm⟩ := LinearAlgebraicGroups.SchemeDerivedGroup.derivedSubgroupOverAlgClosed H' D hd hS hC
    exact ⟨(closedSubgroupAlgebraic H' D).property, hDs, hDc, fun hD ↦
      hprev (derived_step H' hS hC D hDs hDc hDcomm hD)⟩

private theorem solvable_commonEigenvectors (G : AffineAlgebraicGroup k)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (h : Specs.SchemeDerivedGroup.IsSolvable G.val) : HasCommonEigenvectors G.val := by
  obtain ⟨n, H, hn, ⟨e⟩⟩ := h
  apply (derived_series G hs hc hn).2.2.2
  intro V _ _ _ _ π _
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨v, hv, fun p ↦ ⟨1, ?_⟩⟩
  have hp : p = 1 := by
    have he := (Grp.forget (SchemeOver k)).mapIso e
    apply (cancel_mono he.hom).mp
    apply isTerminalTensorUnit.hom_ext
  rw [hp, map_one]
  exact (one_smul k v).symm

private abbrev fieldTest (k : Type u) [Field k] := CommAlgCat.of k k

private def baseIso : (testSpec k).obj (op (fieldTest k)) ≅ base := by
  refine Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) ?_
  change 𝟙 (Spec (CommRingCat.of k)) ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom (algebraMap k k))
  rw [Category.id_comp, Algebra.algebraMap_self]
  exact ((Scheme.Spec).map_id (op (CommRingCat.of k))).symm

private def spectrumPoints (A : HopfAlgebraCategory k) {G : Specs.GroupScheme k}
    (e : (specGroup A) ≅ G) :
    (convolutionPoints A).obj (fieldTest k) ≃* sections G := by
  let I := (hopfSpecPointIso A).app (fieldTest k) ≪≫
    ((groupPointsFunctor k).mapIso e).app (fieldTest k)
  let J := (yonedaGrp.obj G).mapIso (baseIso (k := k)).symm.op
  exact I.groupIsoToMulEquiv.trans J.groupIsoToMulEquiv

private theorem spectrumPoints_apply_left (A : HopfAlgebraCategory k)
    {G : Specs.GroupScheme k} (e : specGroup A ≅ G)
    (g : (convolutionPoints A).obj (fieldTest k)) :
    (spectrumPoints A e g).left =
      Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫ e.hom.hom.hom.left := by
  change 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫ e.hom.hom.hom.left) = _
  exact Category.id_comp _

private def presentedFunction (A : HopfAlgebraCategory k) {G : Specs.GroupScheme k}
    (e : specGroup A ≅ G) (a : A) : globalFunctions G.X :=
  e.inv.hom.hom.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)

private theorem valueAt_presentedFunction (A : HopfAlgebraCategory k)
    {G : Specs.GroupScheme k} (e : specGroup A ≅ G)
    (g : (convolutionPoints A).obj (fieldTest k)) (a : A) :
    valueAt (spectrumPoints A e g) (presentedFunction A e a) = g.ofConv a := by
  let g' := CommRingCat.ofHom g.ofConv.toRingHom
  have he : e.hom.hom.hom.left ≫ e.inv.hom.hom.left = 𝟙 (Spec (CommRingCat.of A)) :=
    ((Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e).hom_inv_id
  change (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ e.inv.hom.hom.left.appTop) ≫
    (spectrumPoints A e g).left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) a = g' a
  have hf : e.inv.hom.hom.left.appTop ≫ (spectrumPoints A e g).left.appTop =
      (Spec.map g').appTop := by
    rw [← Scheme.Hom.comp_appTop, spectrumPoints_apply_left, Category.assoc, he, Category.comp_id]
  rw [Category.assoc, ← Category.assoc e.inv.hom.hom.left.appTop, hf,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

private def tensorCoefficient {A : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V] (ℓ : V →ₗ[k] k) : V ⊗[k] A →ₗ[k] A :=
  (TensorProduct.lid k A).toLinearMap.comp (ℓ.rTensor A)

private def evaluateTensor {A : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V] (g : A →ₐ[k] k) : V ⊗[k] A →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp (g.toLinearMap.lTensor V)

private theorem evaluateTensor_tmul {A : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V] (g : A →ₐ[k] k) (x : V) (a : A) :
    evaluateTensor (A := A) g (x ⊗ₜ[k] a) = g a • x := rfl

private theorem evaluate_tensorCoefficient {A : HopfAlgebraCategory k} {V : Type u}
    [AddCommGroup V] [Module k V] (g : A →ₐ[k] k) (ℓ : V →ₗ[k] k) (t : V ⊗[k] A) :
    g (tensorCoefficient (A := A) ℓ t) = ℓ (evaluateTensor (A := A) g t) := by
  refine TensorProduct.inductionOn
    (motive := fun t ↦ g (tensorCoefficient (A := A) ℓ t) = ℓ (evaluateTensor (A := A) g t))
    t (fun x a ↦ ?_) (fun a b ha hb ↦ ?_)
  · change g (ℓ x • a) = ℓ (evaluateTensor (A := A) g (x ⊗ₜ[k] a))
    rw [evaluateTensor_tmul, Algebra.smul_def, map_mul, AlgHom.commutes, map_smul,
      smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  · simp only [map_add, ha, hb]

private def coactionRepresentation (A : HopfAlgebraCategory k) {V Idx : Type u}
    [AddCommGroup V] [Module k V] [Fintype Idx] [DecidableEq Idx]
    (b : Module.Basis Idx k V) (ρ : RightComodule k A V) :
    (convolutionPoints A).obj (fieldTest k) →* Module.End k V :=
  (Matrix.toLinAlgEquiv b).toMonoidHom.comp
    ((Units.coeHom _).comp
      (((matrixPointHom A (coefficients A b ρ) (coefficients_isCoactionMatrix A b ρ)).app
        (fieldTest k)).hom))

private theorem coactionRepresentation_apply (A : HopfAlgebraCategory k) {V Idx : Type u}
    [AddCommGroup V] [Module k V] [Fintype Idx] [DecidableEq Idx]
    (b : Module.Basis Idx k V) (ρ : RightComodule k A V)
    (g : (convolutionPoints A).obj (fieldTest k)) (x : V) :
    coactionRepresentation A b ρ g x = evaluateTensor (A := A) g.ofConv (ρ.coaction x) := by
  suffices h : coactionRepresentation A b ρ g = (evaluateTensor (A := A) g.ofConv).comp ρ.coaction from
    DFunLike.congr_fun h x
  apply b.ext
  intro j
  change Matrix.toLinAlgEquiv b (g.ofConv.mapMatrix (coefficients A b ρ)) (b j) =
    evaluateTensor (A := A) g.ofConv (ρ.coaction (b j))
  rw [Matrix.toLinAlgEquiv_self, coaction_apply_basis, map_sum]
  simp only [evaluateTensor_tmul, AlgHom.mapMatrix_apply, Matrix.map_apply]

private theorem comodule_eigenvector (G : AffineAlgebraicGroup k)
    (A : HopfAlgebraCategory k) (e : specGroup A ≅ G.val)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (h : Specs.SchemeDerivedGroup.IsSolvable G.val) : HasEigenvectors A := by
  intro V _ _ _ _ ρ
  classical
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank k V))) k V :=
    (Module.finBasis k V).reindex Equiv.ulift.symm
  let E := spectrumPoints A e
  let π := (coactionRepresentation A b ρ).comp E.symm.toMonoidHom
  have heval (p : sections G.val) (x : V) :
      π p x = evaluateTensor (A := A) (E.symm p).ofConv (ρ.coaction x) :=
    coactionRepresentation_apply A b ρ _ x
  have hπ : Regular π := by
    intro x ℓ
    let a := tensorCoefficient (A := A) ℓ (ρ.coaction x)
    refine ⟨presentedFunction A e a, fun p ↦ ?_⟩
    have h' := valueAt_presentedFunction A e (E.symm p) a
    rw [show spectrumPoints A e (E.symm p) = p from E.apply_symm_apply p] at h'
    rw [h', heval, ← evaluate_tensorCoefficient]
  obtain ⟨v, hv, hEigen⟩ := solvable_commonEigenvectors G hs hc h V π hπ
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one k hv
  let a := tensorCoefficient (A := A) ℓ (ρ.coaction v)
  refine ⟨v, hv, a, ?_⟩
  let t := ρ.coaction v - v ⊗ₜ[k] a
  suffices hz : t = 0 from sub_eq_zero.mp hz
  have hz (p : sections G.val) : evaluateTensor (A := A) (E.symm p).ofConv t = 0 := by
    obtain ⟨c, hcv⟩ := hEigen p
    have hca : (E.symm p).ofConv a = c := by
      rw [evaluate_tensorCoefficient, ← heval, hcv, map_smul, hℓ, smul_eq_mul, mul_one]
    rw [map_sub, evaluateTensor_tmul, ← heval, hcv, hca, sub_self]
  letI : IsIntegral G.val.X.left := WordDomainGeometry.smoothConnectedGroupIntegral G hs hc
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
  change tensorCoefficient (A := A) (b.coord i) t = 0
  let c := tensorCoefficient (A := A) (b.coord i) t
  have hzero : presentedFunction A e c = 0 := by
    apply functions_separated
    intro p
    have h' := valueAt_presentedFunction A e (E.symm p) c
    rw [show spectrumPoints A e (E.symm p) = p from E.apply_symm_apply p] at h'
    rw [h', evaluate_tensorCoefficient, hz, map_zero]
  let invScheme := ((Grp.forget (SchemeOver k) ⋙ Over.forget _).mapIso e).inv
  letI : IsIso invScheme := inferInstance
  let f := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ invScheme.appTop
  haveI : IsIso f := inferInstance
  apply (asIso f).commRingCatIsoToRingEquiv.injective
  rw [map_zero]
  exact hzero

/-- A nonzero finite-dimensional rational representation has an invariant line. -/
theorem invariantLine : Specs.LieKolchin.InvariantLine.{u} := by
  intro k _ _ G A e hs hc h V _ _ _ _ ρ
  obtain ⟨v, hv, a, ha⟩ := comodule_eigenvector G A e hs hc h V ρ
  exact ⟨k ∙ v, finrank_span_singleton hv, stable_line ρ v a ha⟩

/-- Every finite-dimensional rational representation has a full invariant flag. -/
theorem invariantFullFlag : Specs.LieKolchin.InvariantFullFlag.{u} := by
  intro k _ _ G A e hs hc h
  exact flags_of_eigenvectors (comodule_eigenvector G A e hs hc h)

end
end LinearAlgebraicGroups.LieKolchin
