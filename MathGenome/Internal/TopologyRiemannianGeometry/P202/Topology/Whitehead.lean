import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.Whitehead
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.WhiteheadSubcomplexRetraction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.HigherHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellTopology
import Mathlib.Topology.Homotopy.Equiv

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellularApproximation
/-! Work toward the general-map case of Whitehead's theorem.
No original target declaration is defined here: the cellular-approximation
interfaces are available only as explicit conditional assumptions. -/

noncomputable section
open Set Topology
open scoped unitInterval
universe u v w

namespace P202.Topology
open P202.Cellular P202Specs.Topology

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Moving basepoints causes no loss of the weak-equivalence hypothesis. -/
theorem weakHomotopyEquivalence_of_homotopic {f g : C(X, Y)}
    (H : f.Homotopic g) (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence g := by
  obtain ⟨H⟩ := H
  constructor
  · rw [← (higherComponents.2 X Y f g ⟨H⟩)]
    exact hf.1
  · intro n x
    obtain ⟨E, _, hE⟩ := higherUnbasedHomotopy n X Y f g H x
    have hb := E.bijective.comp (hf.2 n x)
    have he : (fun a => E (higherInduced n
        (⟨f, rfl⟩ : PointedMap X Y x (f x)) a)) =
        higherInduced n (⟨g, rfl⟩ : PointedMap X Y x (g x)) :=
      congrArg DFunLike.coe hE
    change Function.Bijective (fun a => E (higherInduced n
      (⟨f, rfl⟩ : PointedMap X Y x (f x)) a)) at hb
    rwa [he] at hb

theorem weakHomotopyEquivalence_homotopic_iff {f g : C(X, Y)}
    (H : f.Homotopic g) :
    IsWeakHomotopyEquivalence f ↔ IsWeakHomotopyEquivalence g :=
  ⟨weakHomotopyEquivalence_of_homotopic H,
    weakHomotopyEquivalence_of_homotopic H.symm⟩

@[simp] theorem componentMap_id : componentMap (ContinuousMap.id X) = id := by
  funext a
  exact Quotient.inductionOn a (fun _ => rfl)

@[simp] theorem componentMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    componentMap (g.comp f) = componentMap g ∘ componentMap f := by
  funext a
  exact Quotient.inductionOn a (fun _ => rfl)

/-- A homotopy retraction induces bijections at every basepoint, including
points away from the section. The unbased homotopy supplies their transport. -/
theorem weakHomotopyEquivalence_of_deformation (r : C(X, Y)) (j : C(Y, X))
    (hj : Function.LeftInverse r j)
    (H : (ContinuousMap.id X).Homotopy (j.comp r)) :
    IsWeakHomotopyEquivalence r := by
  have hsection : r.comp j = ContinuousMap.id Y := by ext y; exact hj y
  have hc₁ : componentMap r ∘ componentMap j = id := by
    rw [← componentMap_comp, hsection, componentMap_id]
  have hc₂ : componentMap j ∘ componentMap r = id := by
    rw [← componentMap_comp, ← higherComponents.2 X X _ _ ⟨H⟩, componentMap_id]
  constructor
  · exact ⟨(show Function.LeftInverse (componentMap j) (componentMap r) from
        congrFun hc₂).injective,
      (show Function.RightInverse (componentMap j) (componentMap r) from
        congrFun hc₁).surjective⟩
  · intro n x
    let r₀ : PointedMap X Y x (r x) := ⟨r, rfl⟩
    let j₀ : PointedMap Y X (r x) (j (r x)) := ⟨j, rfl⟩
    let r₁ : PointedMap X Y (j (r x)) (r x) := ⟨r, hj _⟩
    have hp : r₁.comp j₀ = PointedMap.id (r x) := by
      change PointedMap.mk (r.comp j) _ = PointedMap.mk (ContinuousMap.id Y) _
      congr 1
    have hi : Function.Injective (higherInduced n j₀) := by
      have he : (higherInduced n r₁).comp (higherInduced n j₀) =
          MonoidHom.id (HigherPi (n + 1) Y (r x)) := by
        rw [← higherInduced_comp, hp, higherInduced_id]
      have hl : Function.LeftInverse (higherInduced n r₁) (higherInduced n j₀) :=
        DFunLike.congr_fun he
      exact hl.injective
    obtain ⟨E, _, hE⟩ := higherUnbasedHomotopy n X X (ContinuousMap.id X) (j.comp r) H x
    dsimp only [ContinuousMap.id_apply, ContinuousMap.comp_apply] at E hE
    change E.toMonoidHom.comp (higherInduced n (PointedMap.id x)) =
      higherInduced n (j₀.comp r₀) at hE
    rw [higherInduced_id, MonoidHom.comp_id, higherInduced_comp] at hE
    have hb : Function.Bijective ((higherInduced n j₀).comp (higherInduced n r₀)) := by
      rw [← hE]
      exact E.bijective
    change Function.Bijective (⇑(higherInduced n j₀) ∘ ⇑(higherInduced n r₀)) at hb
    exact hb.of_comp_left hi

theorem weakHomotopyEquivalence_comp (f : C(X, Y)) (g : C(Y, Z))
    (hf : IsWeakHomotopyEquivalence f) (hg : IsWeakHomotopyEquivalence g) :
    IsWeakHomotopyEquivalence (g.comp f) := by
  constructor
  · simpa only [componentMap_comp] using hg.1.comp hf.1
  · intro n x
    let f₀ : PointedMap X Y x (f x) := ⟨f, rfl⟩
    let g₀ : PointedMap Y Z (f x) (g (f x)) := ⟨g, rfl⟩
    change Function.Bijective (higherInduced n (g₀.comp f₀))
    simpa only [higherInduced_comp, MonoidHom.coe_comp] using (hg.2 n (f x)).comp (hf.2 n x)

theorem homeomorph_weakHomotopyEquivalence (e : X ≃ₜ Y) :
    IsWeakHomotopyEquivalence (e : C(X, Y)) := by
  apply weakHomotopyEquivalence_of_deformation (e : C(X, Y)) (e.symm : C(Y, X))
    e.apply_symm_apply
  have he : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
    ext x
    exact e.symm_apply_apply x
  rw [he]
  exact ContinuousMap.Homotopy.refl _

/-- Cancellation against a weak equivalence of codomains. -/
theorem weakHomotopyEquivalence_of_comp (f : C(X, Y)) (g : C(Y, Z))
    (hg : IsWeakHomotopyEquivalence g)
    (hgf : IsWeakHomotopyEquivalence (g.comp f)) : IsWeakHomotopyEquivalence f := by
  constructor
  · exact (hg.1.of_comp_iff' (componentMap f)).mp (by simpa using hgf.1)
  · intro n x
    let f₀ : PointedMap X Y x (f x) := ⟨f, rfl⟩
    let g₀ : PointedMap Y Z (f x) (g (f x)) := ⟨g, rfl⟩
    apply ((hg.2 n (f x)).of_comp_iff' (higherInduced n f₀)).mp
    have h := hgf.2 n x
    change Function.Bijective (higherInduced n (g₀.comp f₀)) at h
    simpa only [higherInduced_comp, MonoidHom.coe_comp] using h

/-- A homotopy inverse of a homotopic replacement is an inverse of the
original map, with the homotopies composed in the required direction. -/
theorem homotopyInverse_of_homotopic {f g : C(X, Y)}
    (H : f.Homotopic g) (hg : HasHomotopyInverse g) :
    HasHomotopyInverse f := by
  obtain ⟨r, hl, hr⟩ := hg
  exact ⟨r, ((ContinuousMap.Homotopic.refl r).comp H).trans hl,
    (H.comp (ContinuousMap.Homotopic.refl r)).trans hr⟩

theorem homotopyInverse_comp (f : C(X, Y)) (g : C(Y, Z))
    (hf : HasHomotopyInverse f) (hg : HasHomotopyInverse g) :
    HasHomotopyInverse (g.comp f) := by
  obtain ⟨r, hr₁, hr₂⟩ := hf
  obtain ⟨s, hs₁, hs₂⟩ := hg
  refine ⟨r.comp s, ?_, ?_⟩
  · exact (((ContinuousMap.Homotopic.refl r).comp hs₁).comp
      (ContinuousMap.Homotopic.refl f)).trans hr₁
  · exact (((ContinuousMap.Homotopic.refl g).comp hr₂).comp
      (ContinuousMap.Homotopic.refl s)).trans hs₂

theorem homeomorph_hasHomotopyInverse (e : X ≃ₜ Y) :
    HasHomotopyInverse (e : C(X, Y)) :=
  ⟨(e.symm : C(Y, X)), e.toHomotopyEquiv.left_inv, e.toHomotopyEquiv.right_inv⟩

/-- The supplied inclusion theorem gives an inverse for the actual inclusion
map, with the homotopy read in the library's time-first convention. -/
theorem subcomplexInclusion_hasHomotopyInverse [CWStructure X]
    (A : Subcomplex X) (hA : IsWeakHomotopyEquivalenceInclusion A.carrier) :
    HasHomotopyInverse (subspaceInclusion A.carrier) := by
  obtain ⟨r, H, hr, hzero, hone, _⟩ := whiteheadSubcomplexRetraction A hA
  refine ⟨r, ?_, ?_⟩
  · have he : r.comp (subspaceInclusion A.carrier) = ContinuousMap.id A := by
      ext a
      exact congrArg Subtype.val (hr a)
    rw [he]
  · exact ⟨(squareHomotopy (ContinuousMap.id X)
      ((subspaceInclusion A.carrier).comp r) H hzero hone).symm⟩

/-- The empty subcomplex, including for an empty ambient CW complex. -/
def emptySubcomplex (X : Type u) [TopologicalSpace X] [CWStructure X] : Subcomplex X where
  cells _ := ∅
  contains_closures := by simp

@[simp] theorem emptySubcomplex_carrier [CWStructure X] :
    (emptySubcomplex X).carrier = ∅ := by
  ext x
  simp [Subcomplex.carrier, emptySubcomplex]

/-- Conditional cellular replacement retains the full weak-equivalence
hypothesis. Only the full relative approximation premise is needed here. -/
theorem exists_cellular_weakHomotopyEquivalence
    (happrox : P202Specs.Topology.CellularApproximation.cellularApproximation.{u,v})
    [CWStructure X] [CWStructure Y] (f : C(X, Y))
    (hf : IsWeakHomotopyEquivalence f) :
    ∃ g : C(X, Y), IsCellular g ∧ f.Homotopic g ∧ IsWeakHomotopyEquivalence g := by
  have hon : IsCellularOn f (emptySubcomplex X) := by
    intro n x hx
    simpa using hx.1
  obtain ⟨g, hg, ⟨H⟩⟩ := happrox (emptySubcomplex X) f hon
  exact ⟨g, hg, ⟨H.toHomotopy⟩,
    weakHomotopyEquivalence_of_homotopic ⟨H.toHomotopy⟩ hf⟩


namespace DiskCylinder

/-- Separate the first coordinate, including the case of a zero-dimensional
remaining cube. -/
def cubeSucc (n : ℕ) : UnitCube (n + 1) ≃ₜ UnitCube n × Interval where
  toFun z := (fun i => z i.succ, z 0)
  invFun p := Fin.cons p.2 p.1
  left_inv z := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  right_inv p := by rfl
  continuous_toFun := (continuous_pi fun i => continuous_apply i.succ).prodMk
    (continuous_apply 0)
  continuous_invFun := Continuous.finCons (A := fun _ : Fin (n + 1) => Interval)
    continuous_snd continuous_fst

@[simp] theorem cubeSucc_boundary (n : ℕ) (z : UnitCube (n + 1)) :
    z ∈ CubeBoundary (n + 1) ↔
      (cubeSucc n z).1 ∈ CubeBoundary n ∨ (cubeSucc n z).2 = 0 ∨
        (cubeSucc n z).2 = 1 := by
  change (∃ i, z i = 0 ∨ z i = 1) ↔
    (∃ i : Fin n, z i.succ = 0 ∨ z i.succ = 1) ∨ z 0 = 0 ∨ z 0 = 1
  constructor
  · rintro ⟨i, hi⟩
    exact Fin.cases (fun h => Or.inr h) (fun i h => Or.inl ⟨i, h⟩) i hi
  · rintro (⟨i, hi⟩ | hi | hi)
    · exact ⟨i.succ, hi⟩
    · exact ⟨0, Or.inl hi⟩
    · exact ⟨0, Or.inr hi⟩

/-- Disk-cube parametrization using the same literal disk model as the CW
characteristic maps. -/
def cube (n : ℕ) : Disk n ≃ₜ UnitCube n :=
  (cellularDiskHomeomorph n).trans (Classical.choose (DiskCube.exists_pair_homeomorph n)).symm

@[simp] theorem cube_boundary (n : ℕ) (z : Disk n) :
    cube n z ∈ CubeBoundary n ↔ ‖z.val‖ = 1 := by
  have h := Classical.choose_spec (DiskCube.exists_pair_homeomorph n) (cube n z)
  simp only [cube, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    DiskBoundary, mem_setOf_eq] at h ⊢
  change _ ↔ ‖z.val‖ = 1 at h
  exact h

/-- The pair homeomorphism needed for the cylinder cells. -/
def parametrization (n : ℕ) : Disk (n + 1) ≃ₜ Disk n × Interval :=
  ((cube (n + 1)).trans (cubeSucc n)).trans
    ((cube n).symm.prodCongr (Homeomorph.refl Interval))

/-- Its boundary is exactly the side and the two ends, also for n = 0. -/
theorem parametrization_boundary (n : ℕ) (z : Disk (n + 1)) :
    ‖z.val‖ = 1 ↔
      ‖(parametrization n z).1.val‖ = 1 ∨
        (parametrization n z).2 = 0 ∨ (parametrization n z).2 = 1 := by
  rw [← cube_boundary, cubeSucc_boundary]
  have hb := cube_boundary n ((parametrization n z).1)
  have he : cube n ((parametrization n z).1) = (cubeSucc n (cube (n + 1) z)).1 :=
    (cube n).apply_symm_apply _
  rw [he] at hb
  exact or_congr hb Iff.rfl

theorem parametrization_interior (n : ℕ) (z : Disk (n + 1)) :
    ‖z.val‖ < 1 ↔
      ‖(parametrization n z).1.val‖ < 1 ∧
        0 < (parametrization n z).2 ∧ (parametrization n z).2 < 1 := by
  have hz : ‖z.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  have hx : ‖(parametrization n z).1.val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (parametrization n z).1.property
  have hb := parametrization_boundary n z
  constructor
  · intro hi
    have hn : ¬ (‖(parametrization n z).1.val‖ = 1 ∨
        (parametrization n z).2 = 0 ∨ (parametrization n z).2 = 1) :=
      fun h => (ne_of_lt hi) (hb.mpr h)
    exact ⟨lt_of_le_of_ne hx (fun h => hn (Or.inl h)),
      lt_of_le_of_ne bot_le (fun h => hn (Or.inr (Or.inl h.symm))),
      lt_of_le_of_ne le_top (fun h => hn (Or.inr (Or.inr h)))⟩
  · rintro ⟨hx, ht₀, ht₁⟩
    apply lt_of_le_of_ne hz
    intro he
    rcases hb.mp he with he | he | he
    · exact (ne_of_lt hx) he
    · exact (ne_of_gt ht₀) he
    · exact (ne_of_lt ht₁) he

/-- Restriction of the disk-cylinder parametrization to the interiors. -/
def interiorParametrization (n : ℕ) :
    OpenDisk (n + 1) ≃ₜ OpenDisk n × Set.Ioo (0 : Interval) 1 where
  toFun z :=
    let p := parametrization n (interiorInclusion (n + 1) z)
    have h := (parametrization_interior n (interiorInclusion (n + 1) z)).mp
      (by simpa only [Metric.mem_ball, dist_zero_right, interiorInclusion] using z.property)
    (⟨p.1.val, by simpa only [Metric.mem_ball, dist_zero_right] using h.1⟩,
      ⟨p.2, h.2⟩)
  invFun p :=
    let z := (parametrization n).symm (interiorInclusion n p.1, p.2.val)
    have h : ‖z.val‖ < 1 := (parametrization_interior n z).mpr (by
      rw [(parametrization n).apply_symm_apply]
      exact ⟨by simpa only [Metric.mem_ball, dist_zero_right, interiorInclusion] using p.1.property,
        p.2.property⟩)
    ⟨z.val, by simpa only [Metric.mem_ball, dist_zero_right] using h⟩
  left_inv z := by
    apply Subtype.ext
    change ((parametrization n).symm (parametrization n
      (interiorInclusion (n + 1) z))).val = z.val
    rw [(parametrization n).symm_apply_apply]
    rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun q : Disk n × Interval => q.1.val)
        ((parametrization n).apply_symm_apply (interiorInclusion n p.1, p.2.val))
    · apply Subtype.ext
      exact congrArg Prod.snd
        ((parametrization n).apply_symm_apply (interiorInclusion n p.1, p.2.val))
  continuous_toFun := by
    have h : Continuous (fun z : OpenDisk (n + 1) =>
        parametrization n (interiorInclusion (n + 1) z)) :=
      (parametrization n).continuous.comp (continuous_subtype_val.subtype_mk _)
    exact (h.fst.subtype_val.subtype_mk _).prodMk (h.snd.subtype_mk _)
  continuous_invFun := by
    have h : Continuous (fun p : OpenDisk n × Set.Ioo (0 : Interval) 1 =>
        (parametrization n).symm (interiorInclusion n p.1, p.2.val)) :=
      (parametrization n).symm.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
          (continuous_subtype_val.comp continuous_snd))
    exact h.subtype_val.subtype_mk _

@[simp] theorem interiorParametrization_val (n : ℕ) (z : OpenDisk (n + 1)) :
    (interiorInclusion n (interiorParametrization n z).1,
      (interiorParametrization n z).2.val) =
        parametrization n (interiorInclusion (n + 1) z) := rfl

end DiskCylinder

namespace MappingCylinder

/-- The adjunction relation identifies only the top of each cylinder line
with its prescribed image. `Quot` supplies exactly the generated quotient. -/
inductive Relation (f : C(X, Y)) : (X × Interval ⊕ Y) → (X × Interval ⊕ Y) → Prop
  | attach (x : X) : Relation f (Sum.inl (x, 1)) (Sum.inr (f x))

/-- The ordinary topological mapping cylinder, with its quotient topology. -/
def Space (f : C(X, Y)) := Quot (Relation f)

instance (f : C(X, Y)) : TopologicalSpace (Space f) :=
  inferInstanceAs (TopologicalSpace (Quot (Relation f)))

variable (f : C(X, Y))

def projection : C(X × Interval ⊕ Y, Space f) :=
  ⟨Quot.mk _, continuous_quot_mk⟩

theorem projection_quotient : IsQuotientMap (projection f) := isQuotientMap_quot_mk

def cylinder : C(X × Interval, Space f) :=
  (projection f).comp ⟨Sum.inl, continuous_inl⟩

def top : C(Y, Space f) :=
  (projection f).comp ⟨Sum.inr, continuous_inr⟩

def bottom : C(X, Space f) :=
  (cylinder f).comp ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩

@[simp] theorem cylinder_one (x : X) : cylinder f (x, 1) = top f (f x) :=
  Quot.sound (Relation.attach x)

/-- Descent for the actual adjunction quotient. -/
def descend (a : C(X × Interval, Z)) (b : C(Y, Z))
    (h : ∀ x, a (x, 1) = b (f x)) : C(Space f, Z) where
  toFun := Quot.lift (Sum.elim a b) (by
    intro p q hpq
    cases hpq with | attach x => exact h x)
  continuous_toFun := continuous_quot_lift _ (a.continuous.sumElim b.continuous)

@[simp] theorem descend_cylinder (a : C(X × Interval, Z)) (b : C(Y, Z))
    (h : ∀ x, a (x, 1) = b (f x)) (p : X × Interval) :
    descend f a b h (cylinder f p) = a p := rfl

@[simp] theorem descend_top (a : C(X × Interval, Z)) (b : C(Y, Z))
    (h : ∀ x, a (x, 1) = b (f x)) (y : Y) :
    descend f a b h (top f y) = b y := rfl

/-- The adjunction has exactly the disk-and-cylinder continuity test. This
is for the ordinary product topology, also for infinite CW complexes. -/
theorem continuous_iff [CWStructure X] [CWStructure Y] (h : Space f → Z) :
    Continuous h ↔
      (∀ n (c : Cell Y n), Continuous (h ∘ top f ∘ characteristic Y n c)) ∧
      (∀ n (c : Cell X n),
        Continuous (h ∘ cylinder f ∘ Prod.map (characteristic X n c) id)) := by
  constructor
  · intro hh
    exact ⟨fun n c => (hh.comp (top f).continuous).comp (characteristic Y n c).continuous,
      fun n c => ((hh.comp (cylinder f).continuous).comp
        ((characteristic X n c).continuous.prodMap continuous_id))⟩
  · rintro ⟨hy, hx⟩
    apply (projection_quotient f).continuous_iff.mpr
    apply continuous_sum_dom.mpr
    exact ⟨continuous_on_characteristic_products (h ∘ cylinder f) hx,
      (continuityTest (h ∘ top f)).mpr hy⟩

/-- Closed-set version of the disk-cylinder product test. -/
theorem isClosed_characteristic_product_iff [CWStructure X] (T : Set (X × Interval)) :
    IsClosed T ↔ ∀ n (c : Cell X n),
      IsClosed (Prod.map (characteristic X n c) (id : Interval → Interval) ⁻¹' T) := by
  have hq := quotientProductInterval (diskProjection X) (characteristicDiskQuotient (X := X))
  rw [← hq.isCoinducing.isClosed_preimage]
  constructor
  · intro h n c
    exact h.preimage (((continuous_sigmaMk.comp continuous_sigmaMk).comp continuous_fst).prodMk
      continuous_snd)
  · intro h
    apply (Homeomorph.sigmaProdDistrib (X := fun n => Σ _ : Cell X n, Disk n)
      (Y := Interval)).symm.isClosed_preimage.mp
    apply isClosed_sigma_iff.mpr
    intro n
    apply (Homeomorph.sigmaProdDistrib (X := fun _ : Cell X n => Disk n)
      (Y := Interval)).symm.isClosed_preimage.mp
    exact isClosed_sigma_iff.mpr (h n)

/-- The quotient topology is the weak topology tested on target disks and
source characteristic cylinders; no CW structure on the quotient is assumed. -/
theorem isClosed_iff [CWStructure X] [CWStructure Y] (S : Set (Space f)) :
    IsClosed S ↔
      (∀ n (c : Cell Y n), IsClosed ((top f ∘ characteristic Y n c) ⁻¹' S)) ∧
      (∀ n (c : Cell X n),
        IsClosed ((cylinder f ∘ Prod.map (characteristic X n c) id) ⁻¹' S)) := by
  rw [← (projection_quotient f).isCoinducing.isClosed_preimage, isClosed_sum_iff]
  change IsClosed ((cylinder f) ⁻¹' S) ∧ IsClosed ((top f) ⁻¹' S) ↔ _
  rw [isClosed_characteristic_product_iff, CWStructure.weak_topology]
  exact and_comm

/-- The standard projection to the codomain. -/
def retract : C(Space f, Y) :=
  descend f (f.comp ⟨Prod.fst, continuous_fst⟩) (ContinuousMap.id Y) (fun _ => rfl)

@[simp] theorem retract_cylinder (p : X × Interval) :
    retract f (cylinder f p) = f p.1 := rfl

@[simp] theorem retract_top (y : Y) : retract f (top f y) = y := rfl

@[simp] theorem retract_bottom (x : X) : retract f (bottom f x) = f x := rfl

/-- The height survives the adjunction, since the codomain is at height one. -/
def height : C(Space f, Interval) :=
  descend f ⟨Prod.snd, continuous_snd⟩ (ContinuousMap.const Y 1) (fun _ => rfl)

@[simp] theorem height_cylinder (p : X × Interval) : height f (cylinder f p) = p.2 := rfl
@[simp] theorem height_top (y : Y) : height f (top f y) = 1 := rfl
@[simp] theorem height_bottom (x : X) : height f (bottom f x) = 0 := rfl

private def bottomCoordinates : Space f → Option X :=
  Quot.lift (Sum.elim (fun p => if p.2 = 1 then none else some p.1) (fun _ => none))
    (by intro p q h; cases h; simp)

private theorem bottomCoordinates_bottom (x : X) :
    bottomCoordinates f (bottom f x) = some x := by
  change (if (0 : Interval) = 1 then none else some x) = some x
  simp

theorem bottom_injective : Function.Injective (bottom f) := by
  intro x x' h
  have he := congrArg (bottomCoordinates f) h
  simpa only [bottomCoordinates_bottom, Option.some.injEq] using he

theorem bottom_image_preimage (S : Set X) :
    (projection f) ⁻¹' ((bottom f) '' S) =
      Sum.inl '' (S ×ˢ ({0} : Set Interval)) := by
  ext p
  cases p with
  | inl p =>
    constructor
    · rintro ⟨x, hx, he⟩
      have ht : (0 : Interval) = p.2 := congrArg (height f) he
      obtain ⟨y, t⟩ := p
      dsimp at ht
      subst t
      have he' : bottom f x = bottom f y := he
      have hxy := bottom_injective f he'
      subst y
      exact ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, he⟩
      have ht' : t = 0 := ht
      subst t
      cases he
      exact ⟨x, hx, rfl⟩
  | inr y =>
    constructor
    · rintro ⟨x, _, he⟩
      have ht : (0 : Interval) = 1 := congrArg (height f) he
      exact (zero_ne_one ht).elim
    · rintro ⟨p, _, he⟩
      cases he

/-- Both end spaces have their actual original subspace topology. -/
theorem bottom_closedEmbedding : IsClosedEmbedding (bottom f) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (bottom f).continuous (bottom_injective f)
  intro S hS
  apply (projection_quotient f).isCoinducing.isClosed_preimage.mp
  rw [bottom_image_preimage]
  exact isClosedMap_inl _ (hS.prod isClosed_singleton)

theorem top_embedding : IsEmbedding (top f) :=
  (show Function.LeftInverse (retract f) (top f) from fun _ => rfl).isEmbedding
    (retract f).continuous (top f).continuous

theorem top_range : range (top f) = (height f) ⁻¹' {1} := by
  ext z
  induction z using Quot.ind with | _ p =>
  cases p with
  | inl p =>
    constructor
    · rintro ⟨y, he⟩
      have ht := congrArg (height f) he
      exact ht.symm
    · intro ht
      have ht' : p.2 = 1 := ht
      refine ⟨f p.1, ?_⟩
      change top f (f p.1) = cylinder f p
      rcases p with ⟨x, t⟩
      dsimp at ht'
      subst t
      exact (cylinder_one f x).symm
  | inr y => exact ⟨fun _ => rfl, fun _ => ⟨y, rfl⟩⟩

theorem top_closedEmbedding : IsClosedEmbedding (top f) :=
  ⟨top_embedding f, by rw [top_range]; exact isClosed_singleton.preimage (height f).continuous⟩


/-- Below height one no adjunction identifications occur. -/
theorem cylinder_injective_below {p q : X × Interval} (hp : p.2 ≠ 1)
    (h : cylinder f p = cylinder f q) : p = q := by
  have ht : p.2 = q.2 := congrArg (height f) h
  have hq : q.2 ≠ 1 := fun he => hp (ht.trans he)
  have hc := congrArg (bottomCoordinates f) h
  change (if p.2 = 1 then none else some p.1) =
    (if q.2 = 1 then none else some q.1) at hc
  simp only [hp, hq, if_false, Option.some.injEq] at hc
  exact Prod.ext hc ht

/-- The open cylinder with its attaching end deleted. -/
def lowerCylinder : C({p : X × Interval // p.2 ≠ 1}, Space f) :=
  (cylinder f).comp ⟨Subtype.val, continuous_subtype_val⟩

theorem lowerCylinder_injective : Function.Injective (lowerCylinder f) := by
  intro p q h
  exact Subtype.ext (cylinder_injective_below f p.property h)

theorem lowerCylinder_image_preimage (S : Set {p : X × Interval // p.2 ≠ 1}) :
    (projection f) ⁻¹' ((lowerCylinder f) '' S) =
      Sum.inl '' ((Subtype.val : {p : X × Interval // p.2 ≠ 1} → X × Interval) '' S) := by
  ext p
  cases p with
  | inl p =>
    constructor
    · rintro ⟨q, hq, he⟩
      have heq : q.val = p := cylinder_injective_below f q.property he
      exact ⟨p, ⟨q, hq, heq⟩, rfl⟩
    · rintro ⟨p', ⟨q, hq, rfl⟩, he⟩
      cases he
      exact ⟨q, hq, rfl⟩
  | inr y =>
    constructor
    · rintro ⟨q, _, he⟩
      exact (q.property (congrArg (height f) he)).elim
    · rintro ⟨q, _, he⟩
      cases he

/-- Its image has exactly the product topology and is open in the actual
adjunction topology, without any CW or local finiteness assumption. -/
theorem lowerCylinder_openEmbedding : IsOpenEmbedding (lowerCylinder f) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    (lowerCylinder f).continuous (lowerCylinder_injective f)
  intro S hS
  apply (projection_quotient f).isOpen_preimage.mp
  rw [lowerCylinder_image_preimage]
  apply isOpenMap_inl
  exact (isOpen_ne.preimage (continuous_snd : Continuous (Prod.snd : X × Interval → Interval))).isOpenEmbedding_subtypeVal.isOpenMap S hS

theorem lower_or_top (z : Space f) :
    (∃ p, lowerCylinder f p = z) ∨ ∃ y, top f y = z := by
  induction z using Quot.ind with | _ p =>
  cases p with
  | inl p =>
    by_cases h : p.2 = 1
    · right
      refine ⟨f p.1, ?_⟩
      rw [show p = (p.1, 1) from Prod.ext rfl h]
      exact (cylinder_one f _).symm
    · exact Or.inl ⟨⟨p, h⟩, rfl⟩
  | inr y => exact Or.inr ⟨y, rfl⟩

/-- Hausdorffness is proved for the quotient topology itself. Equal heights
below the top can be separated in the open product chart; at the top the
projection to the Hausdorff target separates points. -/
instance [T2Space X] [T2Space Y] : T2Space (Space f) where
  t2 z w hne := by
    by_cases hh : height f z = height f w
    · rcases lower_or_top f z with ⟨p, rfl⟩ | ⟨y, rfl⟩
      · rcases lower_or_top f w with ⟨q, rfl⟩ | ⟨y, rfl⟩
        · exact separated_by_isOpenEmbedding (lowerCylinder_openEmbedding f)
            (fun he => hne (congrArg (lowerCylinder f) he))
        · exact (p.property hh).elim
      · apply separated_by_continuous (retract f).continuous
        intro he
        have hw : w ∈ range (top f) := by
          rw [top_range]
          exact hh.symm
        obtain ⟨y', rfl⟩ := hw
        exact hne (congrArg (top f) he)
    · exact separated_by_continuous (height f).continuous hh


/-- Sliding to `max t s` is a continuous upward deformation with no
arithmetic parametrization and is stationary on the codomain. -/
def slideAt (t : Interval) : C(Space f, Space f) :=
  descend f
    ((cylinder f).comp ⟨fun p => (p.1, max t p.2),
      continuous_fst.prodMk (continuous_const.max continuous_snd)⟩)
    (top f) (by
      intro x
      change cylinder f (x, max t 1) = top f (f x)
      rw [max_eq_right (show t ≤ 1 from le_top)]
      exact cylinder_one f x)

@[simp] theorem slideAt_cylinder (t : Interval) (p : X × Interval) :
    slideAt f t (cylinder f p) = cylinder f (p.1, max t p.2) := rfl

@[simp] theorem slideAt_top (t : Interval) (y : Y) :
    slideAt f t (top f y) = top f y := rfl

theorem continuous_slide : Continuous (fun p : Interval × Space f => slideAt f p.1 p.2) := by
  apply (projection_quotient f).continuous_lift_prod_right
  let a : Interval × (X × Interval) → Space f :=
    fun p => cylinder f (p.2.1, max p.1 p.2.2)
  let b : Interval × Y → Space f := fun p => top f p.2
  have ha : Continuous a := (cylinder f).continuous.comp
      ((continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.max (continuous_snd.comp continuous_snd)))
  have hb : Continuous b := (top f).continuous.comp continuous_snd
  convert (ha.sumElim hb).comp
    (Homeomorph.prodSumDistrib : Interval × ((X × Interval) ⊕ Y) ≃ₜ
      (Interval × (X × Interval)) ⊕ (Interval × Y)).continuous using 1
  funext p
  rcases p with ⟨t, p⟩
  cases p <;> rfl

def slide : (ContinuousMap.id (Space f)).Homotopy ((top f).comp (retract f)) where
  toFun p := slideAt f p.1 p.2
  continuous_toFun := continuous_slide f
  map_zero_left z := by
    induction z using Quot.ind with | _ p =>
    cases p with
    | inl p => exact congrArg (cylinder f) (Prod.ext rfl (max_eq_right (show 0 ≤ p.2 from bot_le)))
    | inr y => rfl
  map_one_left z := by
    induction z using Quot.ind with | _ p =>
    cases p with
    | inl p =>
      change cylinder f (p.1, max 1 p.2) = top f (f p.1)
      rw [max_eq_left (show p.2 ≤ 1 from le_top)]
      exact cylinder_one f p.1
    | inr y => rfl

/-- This is a homotopy equivalence for every continuous map, independently
of CW structures or any cellularity hypothesis. -/
def retractEquivalence : ContinuousMap.HomotopyEquiv (Space f) Y where
  toFun := retract f
  invFun := top f
  left_inv := ⟨(slide f).symm⟩
  right_inv := by
    have he : (retract f).comp (top f) = ContinuousMap.id Y := by ext y; rfl
    rw [he]

theorem retract_weakHomotopyEquivalence : IsWeakHomotopyEquivalence (retract f) :=
  weakHomotopyEquivalence_of_deformation (retract f) (top f) (fun _ => rfl) (slide f)

theorem bottom_weakHomotopyEquivalence (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence (bottom f) := by
  apply weakHomotopyEquivalence_of_comp (bottom f) (retract f)
    (retract_weakHomotopyEquivalence f)
  have he : (retract f).comp (bottom f) = f := by ext x; rfl
  rwa [he]

/-- Once the CW construction makes the bottom a subcomplex with this
carrier, all remaining homotopy-theoretic steps follow from proved results.
This lemma does not assert the existence of that CW construction. -/
theorem homotopyInverse_of_bottomSubcomplex [CWStructure (Space f)]
    (A : Subcomplex (Space f)) (hA : A.carrier = range (bottom f))
    (hf : IsWeakHomotopyEquivalence f) : HasHomotopyInverse f := by
  let e : X ≃ₜ A := (bottom_closedEmbedding f).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hA.symm)
  have he : (subspaceInclusion A.carrier).comp (e : C(X, A)) = bottom f := by
    ext x
    rfl
  have hi : (bottom f).comp (e.symm : C(A, X)) = subspaceInclusion A.carrier := by
    ext a
    exact congrArg Subtype.val (e.apply_symm_apply a)
  have hweak : IsWeakHomotopyEquivalenceInclusion A.carrier := by
    change IsWeakHomotopyEquivalence (subspaceInclusion A.carrier)
    rw [← hi]
    exact weakHomotopyEquivalence_comp _ _ (homeomorph_weakHomotopyEquivalence e.symm)
      (bottom_weakHomotopyEquivalence f hf)
  have hb : HasHomotopyInverse (bottom f) := by
    rw [← he]
    exact homotopyInverse_comp _ _ (homeomorph_hasHomotopyInverse e)
      (subcomplexInclusion_hasHomotopyInverse A hweak)
  have hr : HasHomotopyInverse (retract f) :=
    ⟨top f, (retractEquivalence f).left_inv, (retractEquivalence f).right_inv⟩
  have heq : (retract f).comp (bottom f) = f := by ext x; rfl
  rw [← heq]
  exact homotopyInverse_comp _ _ hb hr

/-- Distinct labels for the two end complexes and the open prisms. -/
inductive CellLabel (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    [CellStructure X] [CellStructure Y] : ℕ → Type (max u v)
  | bottom {n} : Cell X n → CellLabel X Y n
  | top {n} : Cell Y n → CellLabel X Y n
  | prism {n} : Cell X n → CellLabel X Y (n + 1)

/-- The characteristic maps are maps to the actual mapping-cylinder quotient. -/
@[reducible] def cellStructure [CellStructure X] [CellStructure Y] : CellStructure (Space f) where
  Cell := CellLabel X Y
  characteristic _ c := match c with
    | .bottom c => (bottom f).comp (characteristic X _ c)
    | .top c => (top f).comp (characteristic Y _ c)
    | .prism c => (cylinder f).comp
        ((⟨Prod.map (characteristic X _ c) id,
          (characteristic X _ c).continuous.prodMap continuous_id⟩ :
            C(Disk _ × Interval, X × Interval)).comp
          ⟨DiskCylinder.parametrization _, (DiskCylinder.parametrization _).continuous⟩)

namespace Cells
variable [CWStructure X] [CWStructure Y]
@[reducible] local instance cylinderCellStructure : CellStructure (Space f) := cellStructure f

@[simp] theorem openCell_bottom (n : ℕ) (c : Cell X n) :
    openCell (Space f) n (CellLabel.bottom c) = bottom f '' openCell X n c := by
  change range (bottom f ∘ interiorMap X n c) = _
  exact Set.range_comp _ _

@[simp] theorem openCell_top (n : ℕ) (c : Cell Y n) :
    openCell (Space f) n (CellLabel.top c) = top f '' openCell Y n c := by
  change range (top f ∘ interiorMap Y n c) = _
  exact Set.range_comp _ _

@[simp] theorem openCell_prism (n : ℕ) (c : Cell X n) :
    openCell (Space f) (n + 1) (CellLabel.prism c) =
      cylinder f '' (openCell X n c ×ˢ Set.Ioo (0 : Interval) 1) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    let p := DiskCylinder.interiorParametrization n a
    refine ⟨(interiorMap X n c p.1, p.2.val), ⟨⟨p.1, rfl⟩, p.2.property⟩, ?_⟩
    rfl
  · rintro ⟨⟨x, t⟩, ⟨⟨a, rfl⟩, ht⟩, rfl⟩
    let p : OpenDisk n × Set.Ioo (0 : Interval) 1 := (a, ⟨t, ht⟩)
    refine ⟨(DiskCylinder.interiorParametrization n).symm p, ?_⟩
    have h := DiskCylinder.interiorParametrization_val n
      ((DiskCylinder.interiorParametrization n).symm p)
    rw [(DiskCylinder.interiorParametrization n).apply_symm_apply] at h
    change cylinder f (Prod.map (characteristic X n c) id
      (DiskCylinder.parametrization n (interiorInclusion (n + 1) _))) = _
    rw [← h]
    rfl

theorem interior_embedding : ∀ n (c : Cell (Space f) n),
    IsEmbedding (interiorMap (Space f) n c) := by
  intro n c
  cases c with
  | bottom c =>
    exact (bottom_closedEmbedding f).isEmbedding.comp (CWStructure.interior_embedding _ c)
  | top c => exact (top_embedding f).comp (CWStructure.interior_embedding _ c)
  | @prism n c =>
    let a : OpenDisk n × Set.Ioo (0 : Interval) 1 →
        {p : X × Interval // p.2 ≠ 1} :=
      fun p => ⟨(interiorMap X n c p.1, p.2.val), ne_of_lt p.2.property.2⟩
    have ha : IsEmbedding a :=
      ((CWStructure.interior_embedding n c).prodMap
        (show IsEmbedding (Subtype.val : Set.Ioo (0 : Interval) 1 → Interval) from
          IsEmbedding.subtypeVal)).codRestrict {p : X × Interval | p.2 ≠ 1}
            (fun p => ne_of_lt p.2.property.2)
    exact ((lowerCylinder_openEmbedding f).isEmbedding.comp ha).comp
      (DiskCylinder.interiorParametrization n).isEmbedding

theorem cover : ⋃ (n : ℕ) (c : Cell (Space f) n), openCell (Space f) n c = univ := by
  apply Set.eq_univ_of_forall
  intro z
  rcases lower_or_top f z with ⟨p, rfl⟩ | ⟨y, rfl⟩
  · have hx : p.val.1 ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
      rw [CWStructure.cover]; trivial
    obtain ⟨n, c, hc⟩ := mem_iUnion₂.mp hx
    by_cases ht : p.val.2 = 0
    · apply mem_iUnion₂.mpr
      refine ⟨n, CellLabel.bottom c, ?_⟩
      rw [openCell_bottom]
      refine ⟨p.val.1, hc, ?_⟩
      change cylinder f (p.val.1, 0) = cylinder f p.val
      exact congrArg (cylinder f) (Prod.ext rfl ht.symm)
    · apply mem_iUnion₂.mpr
      refine ⟨n + 1, CellLabel.prism c, ?_⟩
      rw [openCell_prism]
      exact ⟨p.val, ⟨hc, lt_of_le_of_ne bot_le (Ne.symm ht),
        lt_of_le_of_ne le_top p.property⟩, rfl⟩
  · have hy : y ∈ ⋃ (n : ℕ) (c : Cell Y n), openCell Y n c := by
      rw [CWStructure.cover]; trivial
    obtain ⟨n, c, hc⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨n, CellLabel.top c, by rw [openCell_top]; exact ⟨y, hc, rfl⟩⟩

/-- The product weak topology agrees with the topology tested by these
characteristic disks; the prism maps test every characteristic cylinder. -/
theorem weak_topology (S : Set (Space f)) : IsClosed S ↔
    ∀ n (c : Cell (Space f) n), IsClosed (characteristic (Space f) n c ⁻¹' S) := by
  constructor
  · intro h n c
    exact h.preimage (characteristic (Space f) n c).continuous
  · intro h
    apply (MappingCylinder.isClosed_iff f S).mpr
    refine ⟨fun n c => h n (CellLabel.top c), fun n c => ?_⟩
    exact (DiskCylinder.parametrization n).isClosed_preimage.mp (h (n + 1) (CellLabel.prism c))

theorem cell_unique {n m : ℕ} (c : Cell (Space f) n) (d : Cell (Space f) m)
    {z : Space f} (hc : z ∈ openCell (Space f) n c)
    (hd : z ∈ openCell (Space f) m d) : (⟨n, c⟩ : Σ k, Cell (Space f) k) = ⟨m, d⟩ := by
  cases c with
  | bottom c =>
    rw [openCell_bottom] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    cases d with
    | bottom d =>
      rw [openCell_bottom] at hd
      obtain ⟨y, hy, he⟩ := hd
      have hxy := bottom_injective f he
      subst y
      have hec := (CWStructure.disjoint_interiors (X := X)).elim_set (mem_univ ⟨_, c⟩)
        (mem_univ ⟨_, d⟩) x hx hy
      exact congrArg (fun a : Σ k, Cell X k =>
        (⟨a.1, CellLabel.bottom a.2⟩ : Σ k, Cell (Space f) k)) hec
    | top d =>
      rw [openCell_top] at hd
      obtain ⟨y, _, he⟩ := hd
      exact (one_ne_zero (congrArg (height f) he)).elim
    | prism d =>
      rw [openCell_prism] at hd
      obtain ⟨⟨y, t⟩, ⟨_, ht⟩, he⟩ := hd
      exact ((ne_of_gt ht.1) (congrArg (height f) he)).elim
  | top c =>
    rw [openCell_top] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    cases d with
    | bottom d =>
      rw [openCell_bottom] at hd
      obtain ⟨y, _, he⟩ := hd
      exact (zero_ne_one (congrArg (height f) he)).elim
    | top d =>
      rw [openCell_top] at hd
      obtain ⟨y, hy, he⟩ := hd
      have hxy := (top_embedding f).injective he
      subst y
      have hec := (CWStructure.disjoint_interiors (X := Y)).elim_set (mem_univ ⟨_, c⟩)
        (mem_univ ⟨_, d⟩) x hx hy
      exact congrArg (fun a : Σ k, Cell Y k =>
        (⟨a.1, CellLabel.top a.2⟩ : Σ k, Cell (Space f) k)) hec
    | prism d =>
      rw [openCell_prism] at hd
      obtain ⟨⟨y, t⟩, ⟨_, ht⟩, he⟩ := hd
      exact ((ne_of_lt ht.2) (congrArg (height f) he)).elim
  | prism c =>
    rw [openCell_prism] at hc
    obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hc
    cases d with
    | bottom d =>
      rw [openCell_bottom] at hd
      obtain ⟨y, _, he⟩ := hd
      exact ((ne_of_gt ht.1) (congrArg (height f) he).symm).elim
    | top d =>
      rw [openCell_top] at hd
      obtain ⟨y, _, he⟩ := hd
      exact ((ne_of_lt ht.2) (congrArg (height f) he).symm).elim
    | prism d =>
      rw [openCell_prism] at hd
      obtain ⟨⟨y, s⟩, ⟨hy, hs⟩, he⟩ := hd
      have hxy : y = x := congrArg Prod.fst
        (cylinder_injective_below f (ne_of_lt hs.2) he)
      subst y
      have hec := (CWStructure.disjoint_interiors (X := X)).elim_set (mem_univ ⟨_, c⟩)
        (mem_univ ⟨_, d⟩) x hx hy
      exact congrArg (fun a : Σ k, Cell X k =>
        (⟨a.1 + 1, CellLabel.prism a.2⟩ : Σ k, Cell (Space f) k)) hec

theorem disjoint_interiors :
    (univ : Set (Σ n, Cell (Space f) n)).PairwiseDisjoint
      (fun c => openCell (Space f) c.1 c.2) := by
  intro a _ b _ hne
  exact Set.disjoint_left.mpr fun z hz hz' => hne (cell_unique f a.2 b.2 hz hz')

theorem bottom_skeletonLT {n : ℕ} {x : X} (hx : x ∈ skeletonLT X n) :
    bottom f x ∈ skeletonLT (Space f) n := by
  obtain ⟨m, hmn, c, hc⟩ := mem_iUnion.mp hx |>.imp fun m h =>
    mem_iUnion.mp h |>.imp fun hmn h => mem_iUnion.mp h
  exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn, mem_iUnion.mpr ⟨CellLabel.bottom c,
    by rw [openCell_bottom]; exact ⟨x, hc, rfl⟩⟩⟩⟩

theorem top_skeletonLT {n : ℕ} {y : Y} (hy : y ∈ skeletonLT Y n) :
    top f y ∈ skeletonLT (Space f) n := by
  obtain ⟨m, hmn, c, hc⟩ := mem_iUnion.mp hy |>.imp fun m h =>
    mem_iUnion.mp h |>.imp fun hmn h => mem_iUnion.mp h
  exact mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨hmn, mem_iUnion.mpr ⟨CellLabel.top c,
    by rw [openCell_top]; exact ⟨y, hc, rfl⟩⟩⟩⟩

theorem cellular_skeletonLT (hf : IsCellular f) {n : ℕ} {x : X}
    (hx : x ∈ skeletonLT X n) : f x ∈ skeletonLT Y n := by
  by_cases hn : n = 0
  · subst n
    simpa [skeletonLT] using hx
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [← skeletonIndexing] at hx ⊢
    exact hf m hx

theorem cylinder_skeletonLT (hf : IsCellular f) {n : ℕ} {x : X}
    (hx : x ∈ skeletonLT X n) (t : Interval) :
    cylinder f (x, t) ∈ skeletonLT (Space f) (n + 1) := by
  by_cases ht₀ : t = 0
  · subst t
    exact (show skeletonLT (Space f) n ⊆ skeletonLT (Space f) (n + 1) from
      fun x hx => (oldSkeletonInclusion (Space f) n ⟨x, hx⟩).property)
        (bottom_skeletonLT f hx)
  by_cases ht₁ : t = 1
  · subst t
    rw [cylinder_one]
    exact (oldSkeletonInclusion (Space f) n
      ⟨_, top_skeletonLT f (cellular_skeletonLT f hf hx)⟩).property
  · obtain ⟨m, hmn, c, hc⟩ := mem_iUnion.mp hx |>.imp fun m h =>
      mem_iUnion.mp h |>.imp fun hmn h => mem_iUnion.mp h
    apply mem_iUnion.mpr
    refine ⟨m + 1, mem_iUnion.mpr ⟨Nat.add_lt_add_right hmn 1, mem_iUnion.mpr
      ⟨CellLabel.prism c, ?_⟩⟩⟩
    rw [openCell_prism]
    exact ⟨(x, t), ⟨hc, lt_of_le_of_ne bot_le (Ne.symm ht₀),
      lt_of_le_of_ne le_top ht₁⟩, rfl⟩

theorem boundary_lands (hf : IsCellular f) : ∀ n (c : Cell (Space f) n),
    MapsTo (boundaryMap (Space f) n c) univ (skeletonLT (Space f) n) := by
  intro n c z _
  cases c with
  | bottom c => exact bottom_skeletonLT f (CWStructure.boundary_lands _ c (mem_univ z))
  | top c => exact top_skeletonLT f (CWStructure.boundary_lands _ c (mem_univ z))
  | @prism n c =>
    let p := DiskCylinder.parametrization n (boundaryInclusion (n + 1) z)
    have hb : ‖(boundaryInclusion (n + 1) z).val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right, boundaryInclusion] using z.property
    have hp := (DiskCylinder.parametrization_boundary n _).mp hb
    change cylinder f (characteristic X n c p.1, p.2) ∈ _
    rcases hp with hs | hb | ht
    · apply cylinder_skeletonLT f hf
      exact CWStructure.boundary_lands n c
        (mem_univ (⟨p.1.val, by simpa only [Metric.mem_sphere, dist_zero_right] using hs⟩ : Sphere n))
    · change p.2 = 0 at hb
      rw [hb]
      exact bottom_skeletonLT f (characteristic_mem_skeletonLT n c p.1)
    · change p.2 = 1 at ht
      rw [ht, cylinder_one]
      exact top_skeletonLT f (cellular_skeletonLT f hf
        (characteristic_mem_skeletonLT n c p.1))

/-- Compact characteristic images meet finitely many target cells. -/
private theorem finite_support (n : ℕ) (h : C(Disk n, Y)) :
    ∃ F : Finset (Σ m, Cell Y m), range h ⊆ ⋃ d ∈ F, openCell Y d.1 d.2 := by
  classical
  obtain ⟨A, hA, hmem⟩ := compactImageFiniteSupport h
  change {d : Σ m, Cell Y m | d.2 ∈ A.cells d.1}.Finite at hA
  refine ⟨hA.toFinset, ?_⟩
  intro y hy
  obtain ⟨m, c, hc⟩ := mem_iUnion₂.mp (hmem hy)
  exact mem_iUnion₂.mpr ⟨⟨m, c.val⟩, hA.mem_toFinset.mpr c.property, hc⟩

theorem closure_finite : ∀ n (c : Cell (Space f) n),
    ∃ F : Finset (Σ m, Cell (Space f) m),
      closedCell (Space f) n c ⊆ ⋃ d ∈ F, openCell (Space f) d.1 d.2 := by
  classical
  intro n c
  let B : (Σ m, Cell X m) → (Σ m, Cell (Space f) m) :=
    fun a => ⟨a.1, CellLabel.bottom a.2⟩
  let P : (Σ m, Cell X m) → (Σ m, Cell (Space f) m) :=
    fun a => ⟨a.1 + 1, CellLabel.prism a.2⟩
  let T : (Σ m, Cell Y m) → (Σ m, Cell (Space f) m) :=
    fun a => ⟨a.1, CellLabel.top a.2⟩
  cases c with
  | @bottom n c =>
    obtain ⟨F, hF⟩ := CWStructure.closure_finite n c
    refine ⟨F.image B, ?_⟩
    rintro z ⟨a, rfl⟩
    obtain ⟨d, hd, hx⟩ := mem_iUnion₂.mp (hF (mem_range_self a))
    refine mem_iUnion₂.mpr ⟨B d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    rw [show openCell (Space f) (B d).1 (B d).2 = bottom f '' openCell X d.1 d.2 from
      openCell_bottom f d.1 d.2]
    exact ⟨characteristic X n c a, hx, rfl⟩
  | @top n c =>
    obtain ⟨F, hF⟩ := CWStructure.closure_finite n c
    refine ⟨F.image T, ?_⟩
    rintro z ⟨a, rfl⟩
    obtain ⟨d, hd, hx⟩ := mem_iUnion₂.mp (hF (mem_range_self a))
    refine mem_iUnion₂.mpr ⟨T d, Finset.mem_image.mpr ⟨d, hd, rfl⟩, ?_⟩
    rw [show openCell (Space f) (T d).1 (T d).2 = top f '' openCell Y d.1 d.2 from
      openCell_top f d.1 d.2]
    exact ⟨characteristic Y n c a, hx, rfl⟩
  | @prism n c =>
    obtain ⟨F, hF⟩ := CWStructure.closure_finite n c
    obtain ⟨G, hG⟩ := finite_support n (f.comp (characteristic X n c))
    refine ⟨(F.image B ∪ F.image P) ∪ G.image T, ?_⟩
    rintro z ⟨a, rfl⟩
    let p := DiskCylinder.parametrization n a
    change cylinder f (characteristic X n c p.1, p.2) ∈ _
    obtain ⟨d, hd, hx⟩ := mem_iUnion₂.mp (hF (mem_range_self p.1))
    by_cases ht₀ : p.2 = 0
    · rw [ht₀]
      refine mem_iUnion₂.mpr ⟨B d, Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)), ?_⟩
      rw [show openCell (Space f) (B d).1 (B d).2 = bottom f '' openCell X d.1 d.2 from
        openCell_bottom f d.1 d.2]
      exact ⟨_, hx, rfl⟩
    by_cases ht₁ : p.2 = 1
    · rw [ht₁, cylinder_one]
      obtain ⟨d, hd, hx⟩ := mem_iUnion₂.mp (hG (mem_range_self p.1))
      refine mem_iUnion₂.mpr ⟨T d, Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨d, hd, rfl⟩), ?_⟩
      rw [show openCell (Space f) (T d).1 (T d).2 = top f '' openCell Y d.1 d.2 from
        openCell_top f d.1 d.2]
      exact ⟨_, hx, rfl⟩
    · refine mem_iUnion₂.mpr ⟨P d, Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)), ?_⟩
      rw [show openCell (Space f) (P d).1 (P d).2 =
          cylinder f '' (openCell X d.1 d.2 ×ˢ Set.Ioo (0 : Interval) 1) from
        openCell_prism f d.1 d.2]
      exact ⟨_, ⟨hx, lt_of_le_of_ne bot_le (Ne.symm ht₀),
        lt_of_le_of_ne le_top ht₁⟩, rfl⟩

/-- The ordinary mapping cylinder of a cellular map is a CW complex. Its
cells, characteristic maps and topology are the explicit ones above. -/
@[reducible] def cwStructure (hf : IsCellular f) : CWStructure (Space f) :=
  cwStructureOfWeak (interior_embedding f) (disjoint_interiors f) (cover f)
    (boundary_lands f hf) (closure_finite f) (weak_topology f)

end Cells

/-- The bottom cell selection contains the closures of its cells. -/
def bottomSubcomplex [CWStructure X] [CWStructure Y] (hf : IsCellular f) :
    @Subcomplex (Space f) _ (Cells.cwStructure f hf) := by
  letI := Cells.cwStructure f hf
  refine {
    cells := fun n => {c | ∃ d : Cell X n, c = CellLabel.bottom d}
    contains_closures := ?_
  }
  intro n c hc
  obtain ⟨d, rfl⟩ := hc
  rw [closureOpenCell]
  rintro z ⟨a, rfl⟩
  have hx : characteristic X n d a ∈ ⋃ (m : ℕ) (c : Cell X m), openCell X m c := by
    rw [CWStructure.cover]; trivial
  obtain ⟨m, e, he⟩ := mem_iUnion₂.mp hx
  refine mem_iUnion₂.mpr ⟨m, ⟨CellLabel.bottom e, ⟨e, rfl⟩⟩, ?_⟩
  change bottom f (characteristic X n d a) ∈
    @openCell (Space f) _ (cellStructure f) m (CellLabel.bottom e)
  rw [Cells.openCell_bottom]
  exact ⟨_, he, rfl⟩

theorem bottomSubcomplex_carrier [CWStructure X] [CWStructure Y] (hf : IsCellular f) :
    letI := Cells.cwStructure f hf
    (bottomSubcomplex f hf).carrier = range (bottom f) := by
  letI := Cells.cwStructure f hf
  ext z
  constructor
  · intro hz
    obtain ⟨n, c, hc⟩ := mem_iUnion₂.mp hz
    obtain ⟨d, hd⟩ := c.property
    have hc' : z ∈ @openCell (Space f) _ (cellStructure f) n (CellLabel.bottom d) := by
      simpa only [hd] using hc
    rw [Cells.openCell_bottom] at hc'
    obtain ⟨x, _, rfl⟩ := hc'
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    have hx : x ∈ ⋃ (n : ℕ) (c : Cell X n), openCell X n c := by
      rw [CWStructure.cover]; trivial
    obtain ⟨n, c, hc⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨n, ⟨CellLabel.bottom c, ⟨c, rfl⟩⟩, ?_⟩
    change bottom f x ∈ @openCell (Space f) _ (cellStructure f) n (CellLabel.bottom c)
    rw [Cells.openCell_bottom]
    exact ⟨x, hc, rfl⟩

end MappingCylinder

/-- Conditional derivation of Whitehead's theorem from the six full frozen
cellular-approximation interfaces, in the contract's prescribed order.
This is not the closed original target. -/
theorem whitehead_conditional
    (_hbasedApprox : P202Specs.Topology.CellularApproximation.basedCellularApproximation.{u,v})
    (_hbasedHomotopy : P202Specs.Topology.CellularApproximation.basedHomotopyIntoSkeleton.{u,v})
    (_hbasedMap : P202Specs.Topology.CellularApproximation.basedMapIntoSkeleton.{u,v})
    (happrox : P202Specs.Topology.CellularApproximation.cellularApproximation.{u,v})
    (_hhomotopy : P202Specs.Topology.CellularApproximation.homotopyIntoSkeleton.{u,v})
    (_hmap : P202Specs.Topology.CellularApproximation.mapIntoSkeleton.{u,v}) :
    P202Specs.Topology.Whitehead.whitehead.{u,v} := by
  intro X Y _ _ _ _ f hf
  obtain ⟨g, hg, H, hweak⟩ := exists_cellular_weakHomotopyEquivalence happrox f hf
  letI := MappingCylinder.Cells.cwStructure g hg
  exact homotopyInverse_of_homotopic H
    (MappingCylinder.homotopyInverse_of_bottomSubcomplex g
      (MappingCylinder.bottomSubcomplex g hg)
      (MappingCylinder.bottomSubcomplex_carrier g hg) hweak)

end P202.Topology

universe v8_closure_1f5d7611d40d4fa9_u0 v8_closure_1f5d7611d40d4fa9_u1
theorem _root_.«P202».«Topology».«whitehead» : _root_.«P202Specs».«Topology».«Whitehead».«whitehead».{v8_closure_1f5d7611d40d4fa9_u0, v8_closure_1f5d7611d40d4fa9_u1} :=
  @_root_.«P202».«Topology».«whitehead_conditional».{v8_closure_1f5d7611d40d4fa9_u0, v8_closure_1f5d7611d40d4fa9_u1} (@_root_.«P202».«Topology».«basedCellularApproximation».{v8_closure_1f5d7611d40d4fa9_u0, v8_closure_1f5d7611d40d4fa9_u1}) (@_root_.«P202».«Topology».«basedHomotopyIntoSkeleton».{v8_closure_1f5d7611d40d4fa9_u0, v8_closure_1f5d7611d40d4fa9_u1}) (@_root_.«P202».«Topology».«basedMapIntoSkeleton».{v8_closure_1f5d7611d40d4fa9_u0, v8_closure_1f5d7611d40d4fa9_u1}) (@_root_.«P202».«Topology».«cellularApproximation».{v8_closure_1f5d7611d40d4fa9_u0, v8_closure_1f5d7611d40d4fa9_u1}) (@_root_.«P202».«Topology».«homotopyIntoSkeleton».{v8_closure_1f5d7611d40d4fa9_u0, v8_closure_1f5d7611d40d4fa9_u1}) (@_root_.«P202».«Topology».«mapIntoSkeleton».{v8_closure_1f5d7611d40d4fa9_u0, v8_closure_1f5d7611d40d4fa9_u1})
