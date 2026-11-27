import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.ShiftCone
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Telescope

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum

universe u v w

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.Telescope (subMap comp_subMap subMap_comp subMap_eq_zero_iff
  oneSubSuccessor_sumToSequence coneKernelInclusion_comp)

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N P : RightDGModule A}
variable {X : ℕ → RightDGModule A} (step : ∀ j, X j ⟶ X (j+1))

abbrev successor := @Specs.DerivedFormalization.DG.Telescope.successor
abbrev oneSubSuccessor := @Specs.DerivedFormalization.DG.Telescope.oneSubSuccessor
abbrev sumToSequence := @Specs.DerivedFormalization.DG.Telescope.sumToSequence
abbrev coneComparison := @Specs.DerivedFormalization.DG.Telescope.coneComparison
abbrev coneKernelInclusion := @Specs.DerivedFormalization.DG.Telescope.coneKernelInclusion
abbrev telescopeComparison := @Specs.DerivedFormalization.DG.Telescope.telescopeComparison

@[reassoc] theorem inj_successor {U : Cofan X} (hU : IsColimit U) (j : ℕ) :
    U.inj j ≫ successor step hU = step j ≫ U.inj (j+1) :=
  Specs.DerivedFormalization.DG.Telescope.inj_successor step hU j

@[reassoc] theorem inj_sumToSequence {U : Cofan X} (hU : IsColimit U)
    (L : Cocone (Functor.ofSequence step)) (j : ℕ) :
    U.inj j ≫ sumToSequence step hU L = L.ι.app j :=
  Specs.DerivedFormalization.DG.Telescope.inj_sumToSequence step hU L j

@[reassoc] theorem coneInclusion_coneComparison (f : M ⟶ N) (p : N ⟶ P) (hp : f ≫ p = 0) :
    coneInclusion f ≫ coneComparison f p hp = p := by
  apply RightDGModuleModel.hom_ext
  intro a
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rfl

/-- A left-to-right successor matrix on a countable direct sum has no nonzero fixed point. -/
private theorem module_one_sub_injective {Y : ℕ → ModuleCat.{v} k}
    (t : ∀ j, Y j ⟶ Y (j+1)) {U : Cofan Y} (hU : IsColimit U)
    (s : U.pt ⟶ U.pt) (hs : ∀ j, U.inj j ≫ s = t j ≫ U.inj (j+1)) :
    Function.Injective (𝟙 U.pt - s : U.pt ⟶ U.pt) := by
  let D := ModuleCat.of k (Π₀ j, Y j)
  let V : Cofan Y := Cofan.mk D (fun j => ModuleCat.ofHom (DFinsupp.lsingle (R := k) (M := fun j => ↑(Y j)) j))
  let descend (W : Cofan Y) : (Π₀ j, ↑(Y j)) →ₗ[k] W.pt :=
    DFinsupp.lsum ℕ fun j => (W.inj j).hom
  let hV : IsColimit V := Cofan.IsColimit.mk V
    (fun W => ModuleCat.ofHom (descend W))
    (fun W j => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change descend W (DFinsupp.single j x) = W.inj j x
      exact DFinsupp.lsum_single ℕ (fun j => (W.inj j).hom) j x)
    (fun W f hf => by
      apply ModuleCat.hom_ext
      apply DFinsupp.lhom_ext
      intro j x
      change f (DFinsupp.single j x) = descend W (DFinsupp.single j x)
      rw [show descend W (DFinsupp.single j x) = W.inj j x from
        DFinsupp.lsum_single ℕ (fun j => (W.inj j).hom) j x]
      exact CategoryTheory.congr_fun (hf j) x)
  let e := hU.coconePointUniqueUpToIso hV
  have he (j : ℕ) : U.inj j ≫ e.hom = V.inj j :=
    IsColimit.comp_coconePointUniqueUpToIso_hom hU hV ⟨j⟩
  let coord (j : ℕ) : U.pt ⟶ Y j := e.hom ≫ ModuleCat.ofHom (DFinsupp.lapply (R := k) (M := fun j => ↑(Y j)) j)
  have hcoord (j n : ℕ) (x : Y j) :
      coord n (U.inj j x) = DFinsupp.single (β := fun j => ↑(Y j)) j x n := by
    have h := CategoryTheory.congr_fun (he j) x
    change e.hom (U.inj j x) = DFinsupp.single j x at h
    exact congrArg (fun y : D => y n) h
  have hz : s ≫ coord 0 = 0 := by
    apply hU.hom_ext
    rintro ⟨j⟩
    change U.inj j ≫ s ≫ coord 0 = U.inj j ≫ 0
    rw [← Category.assoc, hs, Category.assoc, comp_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change coord 0 (U.inj (j+1) (t j x)) = 0
    rw [hcoord, DFinsupp.single_eq_of_ne (by omega)]
  have hsucc (n : ℕ) : s ≫ coord (n+1) = coord n ≫ t n := by
    apply hU.hom_ext
    rintro ⟨j⟩
    change U.inj j ≫ s ≫ coord (n+1) = U.inj j ≫ coord n ≫ t n
    rw [← Category.assoc, hs, Category.assoc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change coord (n+1) (U.inj (j+1) (t j x)) = t n (coord n (U.inj j x))
    rw [hcoord, hcoord]
    by_cases h : j = n
    · subst j
      rw [DFinsupp.single_eq_same, DFinsupp.single_eq_same]
    · rw [DFinsupp.single_eq_of_ne (by omega), DFinsupp.single_eq_of_ne (Ne.symm h), map_zero]
  apply (injective_iff_map_eq_zero ((𝟙 U.pt - s).hom)).2
  intro x hx
  change x - s x = 0 at hx
  have hfix : x = s x := sub_eq_zero.mp hx
  have hall (n : ℕ) : coord n x = 0 := by
    induction n with
    | zero => exact (congrArg (coord 0) hfix).trans (CategoryTheory.congr_fun hz x)
    | succ n ih =>
      calc
        coord (n+1) x = coord (n+1) (s x) := congrArg _ hfix
        _ = t n (coord n x) := CategoryTheory.congr_fun (hsucc n) x
        _ = 0 := by rw [ih, map_zero]
  have he0 : e.hom x = 0 := DFinsupp.ext hall
  exact (ModuleCat.mono_iff_injective e.hom).1 inferInstance (he0.trans (map_zero _).symm)

/-- For any strict sequence, the telescope differential map is injective in each degree. -/
theorem oneSubSuccessor_injective : Specs.DerivedFormalization.DG.Telescope.OneSubSuccessorInjective.{u,v,w} := by
  intro k _ A X step U hU a i
  let F := degree (A := A) a i
  let V : Cofan (fun j => F.obj (X j)) := Cofan.mk (F.obj U.pt) fun j => F.map (U.inj j)
  have hV : IsColimit V :=
    (Cofan.isColimitMapCoconeEquiv F X U).1 (isColimitOfPreserves F hU)
  have heq (j : ℕ) :
      V.inj j ≫ F.map (successor step hU) = F.map (step j) ≫ V.inj (j+1) := by
    change F.map (U.inj j) ≫ F.map (successor step hU) =
      F.map (step j) ≫ F.map (U.inj (j+1))
    rw [← F.map_comp, ← F.map_comp, inj_successor]
  exact module_one_sub_injective (fun j => F.map (step j)) hV _ heq

/-- A map from the sum killing the telescope relations is a cocone on the sequence. -/
private abbrev sequenceCocone {U : Cofan X} (hU : IsColimit U) {Q : RightDGModule A}
    (p : U.pt ⟶ Q) (hp : oneSubSuccessor step hU ≫ p = 0) :
    Cocone (Functor.ofSequence step) where
  pt := Q
  ι := NatTrans.ofSequence (fun j => U.inj j ≫ p) (by
    intro j
    rw [Functor.ofSequence_map_homOfLE_succ]
    change step j ≫ U.inj (j + 1) ≫ p = (U.inj j ≫ p) ≫ 𝟙 Q
    rw [Category.comp_id]
    have e := congrArg (fun f : U.pt ⟶ Q => U.inj j ≫ f) hp
    change U.inj j ≫ (subMap (𝟙 _) (successor step hU) ≫ p) = U.inj j ≫ 0 at e
    rw [← Category.assoc, comp_zero, comp_subMap, subMap_comp,
      Category.comp_id, inj_successor, Category.assoc] at e
    exact ((subMap_eq_zero_iff _ _).1 e).symm)

/-- The canonical map from the coproduct to the sequential colimit is the cokernel of 1−s. -/
def sequenceCokernel {U : Cofan X} (hU : IsColimit U)
    {L : Cocone (Functor.ofSequence step)} (hL : IsColimit L) :
    IsColimit (CokernelCofork.ofπ (sumToSequence step hU L)
      (oneSubSuccessor_sumToSequence step hU L)) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun p hp => hL.desc (sequenceCocone step hU p hp)) ?_ ?_
  · intro Q p hp
    apply hU.hom_ext
    rintro ⟨j⟩
    change U.inj j ≫ sumToSequence step hU L ≫ _ = U.inj j ≫ p
    rw [inj_sumToSequence_assoc]
    exact hL.fac (sequenceCocone step hU p hp) j
  · intro Q p hp q hq
    apply hL.hom_ext
    intro j
    rw [hL.fac]
    change L.ι.app j ≫ q = U.inj j ≫ p
    calc
      _ = (U.inj j ≫ sumToSequence step hU L) ≫ q :=
        congrArg (fun m : X j ⟶ L.pt => m ≫ q) (inj_sumToSequence step hU L j).symm
      _ = U.inj j ≫ p := by rw [Category.assoc, hq]

theorem sequence_isCokernel : Specs.DerivedFormalization.DG.Telescope.SequenceIsCokernel.{u,v,w} :=
  by
    intro k _ A X step U hU L hL
    exact ⟨sequenceCokernel step hU hL⟩

/-- The identity cone admits the right-linear contraction (y,x) ↦ (0,y). -/
theorem identityCone_contractible : Specs.DerivedFormalization.DG.Telescope.IdentityConeContractible.{u,v,w} := by
  intro k _ A M
  let C := cone (𝟙 M)
  let h : GradedHom C C (-1) :=
    GradedHom.mk (fun a i q e => by
      obtain rfl : q+1 = i := by omega
      exact ModuleCat.ofHom ((LinearMap.inr _ _ _).comp (LinearMap.fst _ _ _))) (by
      intro a b i j n ir nr e ei en x z
      obtain rfl : ir+1 = i := by omega
      obtain rfl : nr+1 = n := by omega
      change (0, M.act (ir+1) j (nr+1) _ x.1 z) =
        (M.act ir j nr _ 0 z, M.act (ir+1) j (nr+1) _ x.1 z)
      simp)
  have hh (a : A.Obj) (i : ℤ) (q : (C.complex a).X (i+1)) :
      h.app a (i+1) i (by omega) q = (0, q.1) := rfl
  have hEq (a : A.Obj) (i j : ℤ) (e : i + (-1) = j) (e' : j+1 = i)
      (q : (C.complex a).X i) :
      q - 0 = (C.complex a).d j i (h.app a i j e q) +
        h.app a (i+1) i (by omega) ((C.complex a).d i (i+1) q) := by
    subst i
    rw [hh, hh]
    change _ = ((cone (𝟙 M)).complex a).d j (j+1) (0, q.1) +
      (0, (((cone (𝟙 M)).complex a).d (j+1) (j+1+1) q).1)
    rw [cone_d, cone_d]
    apply Prod.ext <;> simp [C]
  exact ⟨h, fun a i q => hEq a i (i-1) (by omega) (by omega) q, hh⟩

/-- A strict map with isomorphisms in every component has a strict inverse. -/
private theorem isIso_of_degreewise_isIso (f : M ⟶ N)
    (hf : ∀ a i, IsIso ((f.app a).f i)) : IsIso f := by
  have happ (a : A.Obj) : IsIso (f.app a) := by
    let : ∀ i, IsIso ((f.app a).f i) := hf a
    exact HomologicalComplex.Hom.isIso_of_components _
  have cancel (a : A.Obj) (i : ℤ) (x : (N.complex a).X i) :
      (f.app a).f i ((inv (f.app a)).f i x) = x :=
    congrArg (fun g : N.complex a ⟶ N.complex a => g.f i x) (IsIso.inv_hom_id (f.app a))
  let g : N ⟶ M :=
    { app := fun a => inv (f.app a)
      comm_act := by
        intro a b i j n e x z
        have := hf a n
        apply (ModuleCat.mono_iff_injective ((f.app a).f n)).1 inferInstance
        rw [cancel, f.comm_act, cancel] }
  exact ⟨⟨g, RightDGModuleModel.hom_ext (fun a => IsIso.hom_inv_id (f.app a)),
    RightDGModuleModel.hom_ext (fun a => IsIso.inv_hom_id (f.app a))⟩⟩

private theorem coneComparison_degree_shortExact (f : M ⟶ N)
    (hf : ∀ a i, Function.Injective ((f.app a).f i))
    (p : N ⟶ P) (hp : f ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hp))
    (a : A.Obj) (i : ℤ) :
    (ShortComplex.mk (coneKernelInclusion f) (coneComparison f p hp)
      (coneKernelInclusion_comp f p hp) |>.map (degree a i)).ShortExact := by
  let F := degree (A := A) a i
  let S := (ShortComplex.mk f p hp).map F
  have hQ : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    CokernelCofork.mapIsColimit _ hc F
  have h_exact := (ShortComplex.moduleCat_exact_iff S).1 (S.exact_of_g_is_cokernel hQ)
  have h_surj : Function.Surjective S.g :=
    (ModuleCat.epi_iff_surjective _).1 (epi_of_isColimit_cofork hQ)
  apply ModuleCat.shortComplex_shortExact
  · intro q
    change (p.app a).f i q.1 = 0 ↔
      ∃ r : ((cone (𝟙 M)).complex a).X i, ((f.app a).f i r.1, r.2) = q
    constructor
    · intro hq
      obtain ⟨x, hx⟩ := h_exact q.1 hq
      exact ⟨(x, q.2), Prod.ext hx rfl⟩
    · rintro ⟨r, rfl⟩
      exact congrArg (fun g : M ⟶ P => (g.app a).f i r.1) hp
  · intro x y e
    change ((f.app a).f i x.1, x.2) = ((f.app a).f i y.1, y.2) at e
    exact Prod.ext (hf a i (congrArg Prod.fst e))
      (congrArg (fun q : ((cone f).complex a).X i => q.2) e)
  · intro x
    obtain ⟨y, hy⟩ := h_surj x
    exact ⟨(y, 0), hy⟩

/-- The inclusion of the identity cone exhibits the strict kernel of the cone comparison. -/
noncomputable def coneComparisonKernel (f : M ⟶ N)
    (hf : ∀ a i, Function.Injective ((f.app a).f i))
    (p : N ⟶ P) (hp : f ≫ p = 0) (hc : IsColimit (CokernelCofork.ofπ p hp)) :
    IsLimit (KernelFork.ofι (coneKernelInclusion f) (coneKernelInclusion_comp f p hp)) := by
  let g := coneComparison f p hp
  let j := coneKernelInclusion f
  let w : j ≫ g = 0 := coneKernelInclusion_comp f p hp
  let q := kernel.lift g j w
  have hq (a : A.Obj) (i : ℤ) : IsIso ((q.app a).f i) := by
    let F := degree (A := A) a i
    let S := (ShortComplex.mk j g w).map F
    have hS : S.ShortExact := coneComparison_degree_shortExact f hf p hp hc a i
    let hl : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
    let hr := isLimitOfHasKernelOfPreservesLimit F g
    let e := hl.conePointUniqueUpToIso hr
    have he : e.hom ≫ F.map (kernel.ι g) = F.map j :=
      IsLimit.conePointUniqueUpToIso_hom_comp hl hr WalkingParallelPair.zero
    have eq : F.map q = e.hom := by
      have : Mono (F.map (kernel.ι g)) := mono_of_isLimit_fork hr
      apply (cancel_mono (F.map (kernel.ι g))).1
      rw [he, ← F.map_comp, kernel.lift_ι]
    change IsIso (F.map q)
    rw [eq]
    infer_instance
  letI := isIso_of_degreewise_isIso q hq
  exact kernel.isoKernel g j (asIso q) (kernel.lift_ι _ _ _)

private theorem quasiIso_of_shortExact_acyclic_left {S : ShortComplex (ModuleCochain.{u,v} k)}
    (hS : S.ShortExact) (h : S.X₁.Acyclic) : QuasiIso S.g := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h₁ := (h i).isZero_homology
  have h₂ := (h (i+1)).isZero_homology
  have : Mono (homologyMap S.g i) :=
    (ShortComplex.exact_iff_mono _ (h₁.eq_of_src _ _)).1 (hS.homology_exact₂ i)
  have : Epi (homologyMap S.g i) :=
    (ShortComplex.exact_iff_epi _ (h₂.eq_of_tgt _ _)).1 (hS.homology_exact₃ i (i+1) rfl)
  exact isIso_of_mono_of_epi _

/-- The cone-to-cokernel map of a degreewise injection is an objectwise quasi-isomorphism. -/
theorem coneToCokernel : Specs.DerivedFormalization.DG.Telescope.ConeToCokernel.{u,v,w} := by
  intro k _ A M N P f hf p hp hc
  refine ⟨⟨coneComparisonKernel f hf p hp hc⟩, fun a => ?_⟩
  let S := (ShortComplex.mk (coneKernelInclusion f) (coneComparison f p hp)
    (coneKernelInclusion_comp f p hp)).map (eval a)
  have hs : S.ShortExact :=
    shortExact_of_degreewise_shortExact S (fun i => coneComparison_degree_shortExact f hf p hp hc a i)
  have hId : IsQuasiIso (𝟙 M) := fun b => by
    change QuasiIso (𝟙 (M.complex b))
    infer_instance
  exact quasiIso_of_shortExact_acyclic_left hs ((quasiIso_iff_cone_acyclic (𝟙 M)).1 hId a)

/-- For every sequence of strict maps, the canonical telescope map is an objectwise quasi-isomorphism. -/
theorem telescope_quasiIso : Specs.DerivedFormalization.DG.Telescope.TelescopeQuasiIso.{u,v,w} := by
  intro k _ A X step U hU L hL
  exact (coneToCokernel _ (oneSubSuccessor_injective step hU) _
    (oneSubSuccessor_sumToSequence step hU L) (sequenceCokernel step hU hL)).2

end DerivedFormalization.RightDGModule
