import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.BasicFundamentalGroups
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.FundamentalGroupoid
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CoveringLifting
import Mathlib.Topology.Covering.FundamentalGroupCircle
import Mathlib.Topology.Homotopy.Product
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.VanKampen
namespace P202.Topology
open P202Specs.Topology
open P202Specs.Topology.BasicFundamentalGroups
open scoped unitInterval EuclideanSpace
universe u v
noncomputable section

theorem pointedMap_ext {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    {f g : PointedMap X Y x y} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The isomorphism induced by a homeomorphism with its specified basepoint. -/
def pointedHomeomorphEquiv {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (x : X) (y : Y) (h : e x = y) : Pi1 X x ≃* Pi1 Y y := by
  let f : PointedMap X Y x y := ⟨⟨e, e.continuous⟩, h⟩
  let g : PointedMap Y X y x := ⟨⟨e.symm, e.symm.continuous⟩, by rw [← h]; simp⟩
  have hgf : g.comp f = PointedMap.id x := by
    apply pointedMap_ext
    ext z
    exact e.symm_apply_apply z
  have hfg : f.comp g = PointedMap.id y := by
    apply pointedMap_ext
    ext z
    exact e.apply_symm_apply z
  exact {
    toFun := f.induced
    invFun := g.induced
    left_inv := fun a => by
      have hh := congrArg (fun k : PointedMap X X x x => k.induced a) hgf
      simpa only [induced_comp, MonoidHom.comp_apply, induced_id, MonoidHom.id_apply] using hh
    right_inv := fun a => by
      have hh := congrArg (fun k : PointedMap Y Y y y => k.induced a) hfg
      simpa only [induced_comp, MonoidHom.comp_apply, induced_id, MonoidHom.id_apply] using hh
    map_mul' := f.induced.map_mul }

/-- The normalized exponential factors through the actual circle homeomorphism. -/
theorem circleCover_eq (t : ℝ) :
    circleCover t = AddCircle.homeomorphCircle (T := 1) one_ne_zero (t : AddCircle (1 : ℝ)) := by
  simp [circleCover, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]

theorem circleCovering :
    BasicFundamentalGroups.Expected.circleCovering := by
  refine ⟨?_, fun t => rfl⟩
  apply (coveringBridge ℝ Circle circleCover).mpr
  have hf := (AddCircle.isCoveringMap_coe (1 : ℝ)).homeomorph_comp
    (AddCircle.homeomorphCircle (T := 1) one_ne_zero)
  have heq : (circleCover : ℝ → Circle) =
      AddCircle.homeomorphCircle one_ne_zero ∘ ((↑) : ℝ → AddCircle (1 : ℝ)) :=
    funext circleCover_eq
  rw [heq]
  exact ⟨hf, (AddCircle.homeomorphCircle one_ne_zero).surjective.comp
    (QuotientAddGroup.mk_surjective)⟩


/-- Winding number on the actual complex unit circle, with normalized lift. -/
theorem windingNumber :
    BasicFundamentalGroups.Expected.windingNumber := by
  let H := AddCircle.homeomorphCircle (T := 1) one_ne_zero
  have hH : H (0 : AddCircle (1 : ℝ)) = 1 := by
    simp [H, AddCircle.homeomorphCircle_apply]
  have hp : H.symm 1 = 0 := by rw [← hH]; exact H.symm_apply_apply 0
  let f : PointedMap Circle (AddCircle (1 : ℝ)) 1 0 :=
    ⟨⟨H.symm, H.symm.continuous⟩, hp⟩
  let e := (pointedHomeomorphEquiv H.symm 1 0 hp).trans
    ((oppositeEquiv (AddCircle.windingNumberIso (0 : AddCircle (1 : ℝ)))).trans
      MulOpposite.opMulEquiv.symm)
  refine ⟨e, ?_⟩
  intro a L hL hL0
  let b : Path (0 : AddCircle (1 : ℝ)) 0 :=
    (a.map H.symm.continuous).cast hp.symm hp.symm
  have hb : ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ L = b := by
    funext t
    change (L t : AddCircle (1 : ℝ)) = H.symm (a t)
    apply H.injective
    rw [H.apply_symm_apply]
    exact (circleCover_eq (L t)).symm.trans (hL t)
  have hw := AddCircle.windingNumber_eq_div b L hb
  change (AddCircle.windingNumber ((f.induced (loopClass a)).unop) : ℝ) = L 1
  rw [inducedFormula Circle (AddCircle (1 : ℝ)) 1 0 f a]
  change (AddCircle.windingNumber (.of (.mk b)) : ℝ) = L 1
  simpa only [hL0, sub_zero, div_one] using hw

/-- Coordinatewise construction on path classes, transported to the source groups. -/
def fundamentalGroupPiEquiv {ι : Type u} (X : ι → Type v)
    [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i) :
    Pi1 (∀ i, X i) x ≃* (∀ i, Pi1 (X i) (x i)) where
  toFun a i := (coordinate X x i).induced a
  invFun a := ofClass (Path.Homotopic.pi (fun i => pathClass (a i)))
  left_inv a := by
    apply pathClass_injective
    simpa only [pathClass_ofClass, induced_pathClass,
      coordinate, first, second, Path.Homotopic.Quotient.cast_rfl_rfl] using
      Path.Homotopic.pi_proj (pathClass a)
  right_inv a := by
    funext i
    apply pathClass_injective
    simpa only [induced_pathClass, pathClass_ofClass,
      coordinate, first, second, Path.Homotopic.Quotient.cast_rfl_rfl] using
      Path.Homotopic.proj_pi i (fun j => pathClass (a j))
  map_mul' a b := by funext i; exact (coordinate X x i).induced.map_mul a b

theorem productFundamentalGroup :
    BasicFundamentalGroups.Expected.product.{u,v} := by
  intro ι X _ x
  exact ⟨fundamentalGroupPiEquiv X x, fun _ _ => rfl⟩

def fundamentalGroupProdEquiv (X : Type u) (Y : Type v)
    [TopologicalSpace X] [TopologicalSpace Y] (x : X) (y : Y) :
    Pi1 (X × Y) (x,y) ≃* (Pi1 X x × Pi1 Y y) where
  toFun a := ((first X Y x y).induced a, (second X Y x y).induced a)
  invFun a := ofClass (Path.Homotopic.prod (pathClass a.1) (pathClass a.2))
  left_inv a := by
    apply pathClass_injective
    simpa only [pathClass_ofClass, induced_pathClass,
      coordinate, first, second, Path.Homotopic.Quotient.cast_rfl_rfl] using
      Path.Homotopic.prod_projLeft_projRight (pathClass a)
  right_inv a := by
    apply Prod.ext <;> apply pathClass_injective
    · simpa only [induced_pathClass, pathClass_ofClass,
        coordinate, first, second, Path.Homotopic.Quotient.cast_rfl_rfl] using
        Path.Homotopic.projLeft_prod (pathClass a.1) (pathClass a.2)
    · simpa only [induced_pathClass, pathClass_ofClass,
        coordinate, first, second, Path.Homotopic.Quotient.cast_rfl_rfl] using
        Path.Homotopic.projRight_prod (pathClass a.1) (pathClass a.2)
  map_mul' a b := Prod.ext ((first X Y x y).induced.map_mul a b)
    ((second X Y x y).induced.map_mul a b)

theorem binaryProductFundamentalGroup :
    BasicFundamentalGroups.Expected.binaryProduct.{u,v} := by
  intro X Y _ _ x y
  exact ⟨fundamentalGroupProdEquiv X Y x y, fun _ => ⟨rfl, rfl⟩⟩


/-- The pushout of two trivial fundamental groups is trivial. -/
theorem simplyConnected_of_two_contractible
    (hVK : P202Specs.Topology.VanKampen.Expected.vanKampen.{u})
    {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (hinter : IsPathConnected (U ∩ V))
    [ContractibleSpace U] [ContractibleSpace V] : SimplyConnectedSpace X := by
  obtain ⟨x, hx⟩ := hinter.nonempty
  have hup : IsPathConnected U := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hvp : IsPathConnected V := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  obtain ⟨_, hpush⟩ := hVK X U V hU hV hcover hup hvp hinter x hx
  let A := Pi1 X x
  have hleft : (VanKampen.ambientMap U x hx.1).induced = (1 : Pi1 U ⟨x,hx.1⟩ →* A) := by
    ext a
    simpa only [map_one, MonoidHom.one_apply] using
      congrArg (VanKampen.ambientMap U x hx.1).induced (Subsingleton.elim a 1)
  have hright : (VanKampen.ambientMap V x hx.2).induced = (1 : Pi1 V ⟨x,hx.2⟩ →* A) := by
    ext a
    simpa only [map_one, MonoidHom.one_apply] using
      congrArg (VanKampen.ambientMap V x hx.2).induced (Subsingleton.elim a 1)
  obtain ⟨h, _, huniq⟩ := hpush A 1 1 (by ext; rfl)
  have hid : MonoidHom.id A = (1 : A →* A) :=
    (huniq (MonoidHom.id A) (by simpa using And.intro hleft hright)).trans
      (huniq 1 (by constructor <;> ext <;> rfl)).symm
  have htriv (a : A) : a = 1 := DFunLike.congr_fun hid a
  let : Subsingleton A := ⟨fun a b => (htriv a).trans (htriv b).symm⟩
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, fun y a => ?_⟩
  have ha : loopClass a = 1 := by
    apply (changeBasepoint (PathConnectedSpace.somePath x y)).injective
    exact Subsingleton.elim _ _
  rw [← Path.Homotopic.Quotient.eq]
  exact congrArg pathClass ha


/-- Universe lifting permits using the frozen van Kampen premise at its exact universe. -/
theorem simplyConnected_of_two_contractible_lift
    (hVK : P202Specs.Topology.VanKampen.Expected.vanKampen.{u})
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (hinter : IsPathConnected (U ∩ V))
    [ContractibleSpace U] [ContractibleSpace V] : SimplyConnectedSpace X := by
  let e : ULift.{u} X ≃ₜ X := Homeomorph.ulift
  let U' := e ⁻¹' U
  let V' := e ⁻¹' V
  have : PathConnectedSpace (ULift.{u} X) := e.symm.pathConnectedSpace
  let eU : U' ≃ₜ U := e.subtype (fun _ => Iff.rfl)
  let eV : V' ≃ₜ V := e.subtype (fun _ => Iff.rfl)
  have : ContractibleSpace U' := eU.contractibleSpace
  have : ContractibleSpace V' := eV.contractibleSpace
  have : SimplyConnectedSpace (ULift.{u} X) :=
    simplyConnected_of_two_contractible hVK U' V' (hU.preimage e.continuous)
      (hV.preimage e.continuous)
      (by simp only [U', V', ← Set.preimage_union, hcover, Set.preimage_univ])
      (by simpa only [U', V', ← Set.preimage_inter] using
        e.isPathConnected_preimage.mpr hinter)
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

/-- Stereographic projection identifies each pole complement with Euclidean n-space. -/
def puncturedSphereHomeomorph (n : ℕ) (v : Sphere n) :
    ↥({v}ᶜ : Set (Sphere n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
  let e := stereographic' n v
  exact (Homeomorph.setCongr (stereographic'_source (n := n) v).symm).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target (n := n) v)).trans (Homeomorph.Set.univ _)))

theorem sphere_neg_ne_self {n : ℕ} (v : Sphere n) : -v ≠ v := by
  intro h
  apply ne_zero_of_mem_unit_sphere v
  have hval : -(v : EuclideanSpace ℝ (Fin (n+1))) = v := congrArg Subtype.val h
  have hh : (2 : ℝ) • (v : EuclideanSpace ℝ (Fin (n+1))) = 0 := by
    rw [two_smul]
    nth_rw 1 [← hval]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

/-- The two-pole complement is the continuous image of punctured n-space. -/
theorem sphere_pole_intersection_pathConnected {n : ℕ} (hn : 2 ≤ n) (v : Sphere n) :
    IsPathConnected (({v}ᶜ : Set (Sphere n)) ∩ {-v}ᶜ) := by
  let e := stereographic' n v
  have hneg : -v ∈ e.source := by simpa [e] using sphere_neg_ne_self v
  have he0 : e (-v) = 0 := by simp [e, stereographic']
  have hi0 : e.symm 0 = -v := by rw [← he0]; exact e.left_inv hneg
  have hc : Continuous e.symm := continuousOn_univ.mp (by simpa [e] using e.continuousOn_symm)
  have hp : IsPathConnected ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
    isPathConnected_compl_singleton_of_one_lt_rank
      (Module.one_lt_rank_of_one_lt_finrank (by simpa using (show 1 < n by omega))) 0
  have himage : e.symm '' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) =
      ({v}ᶜ : Set (Sphere n)) ∩ {-v}ᶜ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [e] using e.map_target (show y ∈ e.target by simp [e])
      · intro h
        have hh := congrArg e h
        rw [e.right_inv (by simp [e]), he0] at hh
        exact hy hh
    · rintro ⟨hx, hxneg⟩
      have hxs : x ∈ e.source := by simpa [e] using hx
      refine ⟨e x, ?_, e.left_inv hxs⟩
      intro hz
      have hh := congrArg e.symm hz
      rw [e.left_inv hxs, hi0] at hh
      exact hxneg hh
  rw [← himage]
  exact hp.image hc

theorem spheresSimplyConnected :
    BasicFundamentalGroups.Expected.spheres := by
  intro n hn
  have hs : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
    isPathConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simpa using (show 1 < n+1 by omega))) 0 zero_le_one
  have : PathConnectedSpace (Sphere n) := isPathConnected_iff_pathConnectedSpace.mp hs
  obtain ⟨v⟩ := (inferInstance : Nonempty (Sphere n))
  have : ContractibleSpace (↥({v}ᶜ : Set (Sphere n))) := (puncturedSphereHomeomorph n v).contractibleSpace
  have : ContractibleSpace (↥({-v}ᶜ : Set (Sphere n))) := (puncturedSphereHomeomorph n (-v)).contractibleSpace
  refine ⟨inferInstance, simplyConnected_of_two_contractible vanKampen.{0}
    {v}ᶜ {-v}ᶜ isOpen_compl_singleton isOpen_compl_singleton ?_
      (sphere_pole_intersection_pathConnected hn v)⟩
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases hx : x = v
  · right
    rw [hx]
    exact (sphere_neg_ne_self v).symm
  · exact Or.inl hx

end
end P202.Topology
