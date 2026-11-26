import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RealPolarFixedPoints
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.CompactRealForm
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.Instances.Matrix
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.RealPolarFixedPoints

open Module
open LieAlgebrasAndRepresentations.RealForms
open LieAlgebrasAndRepresentations.PolarRealStructures
open _root_.Specs.LieAlgebrasAndRepresentations.PolarRealStructures
open LinearAlgebraicGroups.Specs.RealPolarFixedPoints
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

open private sandwich hermitianCore real_eigenbasis positive_adjoint_product
  adjoint_product_symmetric equiv_ext_basis conjugation_of_power
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PolarRealStructures

attribute [local instance] automorphismGroup

universe u v
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]

local notation "A" => L ≃ₗ⁅ℂ⁆ L

private def adjointEquiv (ω : Conjugation L) (g : A) : A := sandwich ω ω g.symm

private def adjointProduct (ω : Conjugation L) (g : A) : A := adjointEquiv ω g * g

private noncomputable def positivePower (ω : Conjugation L) (hω : IsCompact ω)
    (g : A) (s : ℝ) : A :=
  (adjoint_product_power ω hω g s).exists.choose

private theorem positivePower_apply (ω : Conjugation L) (hω : IsCompact ω)
    (g : A) (s r : ℝ) (x : L) (hx : adjointProduct ω g x = (r : ℂ) • x) :
    positivePower ω hω g s x = ((r ^ s : ℝ) : ℂ) • x :=
  (adjoint_product_power ω hω g s).exists.choose_spec r x hx

private theorem adjointProduct_eigenbasis (ω : Conjugation L) (hω : IsCompact ω) (g : A) :
    ∃ (b : Basis (Fin (finrank ℂ L)) ℂ L) (r : Fin (finrank ℂ L) → ℝ),
      (∀ i, adjointProduct ω g (b i) = (r i : ℂ) • b i) ∧ ∀ i, 0 < r i := by
  obtain ⟨b, r, hb⟩ :=
    real_eigenbasis ω hω (adjointProduct ω g) (adjoint_product_symmetric ω g)
  exact ⟨b, r, hb, fun i => positive_adjoint_product ω hω g (b.ne_zero i) (hb i)⟩

private theorem positivePower_zero (ω : Conjugation L) (hω : IsCompact ω) (g : A) :
    positivePower ω hω g 0 = 1 := by
  obtain ⟨b, r, hb, _⟩ := adjointProduct_eigenbasis ω hω g
  apply equiv_ext_basis b
  intro i
  rw [positivePower_apply ω hω g 0 _ _ (hb i), Real.rpow_zero, Complex.ofReal_one, one_smul]
  rfl

private theorem positivePower_one (ω : Conjugation L) (hω : IsCompact ω) (g : A) :
    positivePower ω hω g 1 = adjointProduct ω g := by
  obtain ⟨b, r, hb, _⟩ := adjointProduct_eigenbasis ω hω g
  apply equiv_ext_basis b
  intro i
  rw [positivePower_apply ω hω g 1 _ _ (hb i), Real.rpow_one, hb]

private theorem positivePower_add (ω : Conjugation L) (hω : IsCompact ω) (g : A) (s t : ℝ) :
    positivePower ω hω g (s + t) = positivePower ω hω g s * positivePower ω hω g t := by
  obtain ⟨b, r, hb, hr⟩ := adjointProduct_eigenbasis ω hω g
  apply equiv_ext_basis b
  intro i
  change positivePower ω hω g (s + t) (b i) =
    positivePower ω hω g s (positivePower ω hω g t (b i))
  rw [positivePower_apply ω hω g (s + t) _ _ (hb i),
    positivePower_apply ω hω g t _ _ (hb i), map_smul,
    positivePower_apply ω hω g s _ _ (hb i), smul_smul, ← Complex.ofReal_mul,
    Real.rpow_add (hr i), mul_comm (r i ^ s)]

private theorem positivePower_compact_conjugation (ω : Conjugation L) (hω : IsCompact ω)
    (g : A) (s : ℝ) (x : L) :
    ω.map (positivePower ω hω g s x) = (positivePower ω hω g s).symm (ω.map x) := by
  obtain ⟨b, r, hb, _⟩ := adjointProduct_eigenbasis ω hω g
  have hωP (z : L) : adjointProduct ω g (ω.map z) =
      ω.map ((adjointProduct ω g).symm z) := rfl
  apply conjugation_of_power ω (adjointProduct ω g) _ b r hb hωP (t := s)
  intro q z hz
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hq := positive_adjoint_product ω hω g hz0 hz
    simpa only [abs_of_pos hq] using positivePower_apply ω hω g s q z hz

private theorem positivePower_adjoint (ω : Conjugation L) (hω : IsCompact ω) (g : A) (s : ℝ) :
    adjointEquiv ω (positivePower ω hω g s) = positivePower ω hω g s := by
  apply LieEquiv.ext
  intro x
  change ω.map ((positivePower ω hω g s).symm (ω.map x)) = _
  rw [← positivePower_compact_conjugation, ω.involutive]

private theorem positivePower_commutes {F : Type*} [FunLike F L L] [AddMonoidHomClass F L L]
    (ω : Conjugation L) (hω : IsCompact ω) (g : A) (s : ℝ)
    (f : F) (χ : ℂ → ℂ) (hχ : ∀ r : ℝ, χ (r : ℂ) = r)
    (hsmul : ∀ (c : ℂ) (x : L), f (c • x) = χ c • f x)
    (hf : ∀ x, f (adjointProduct ω g x) = adjointProduct ω g (f x)) (x : L) :
    f (positivePower ω hω g s x) = positivePower ω hω g s (f x) := by
  classical
  obtain ⟨b, r, hb, _⟩ := adjointProduct_eigenbasis ω hω g
  have he (i) : adjointProduct ω g (f (b i)) = (r i : ℂ) • f (b i) := by
    rw [← hf, hb, hsmul, hχ]
  have h (i) (c : ℂ) :
      f (positivePower ω hω g s (c • b i)) =
        positivePower ω hω g s (f (c • b i)) := by
    rw [map_smul, positivePower_apply ω hω g s _ _ (hb i),
      hsmul, hsmul, hsmul, hχ, map_smul, positivePower_apply ω hω g s _ _ (he i)]
  rw [← b.sum_repr x]
  simp only [map_sum, h]

private noncomputable def polarPath (ω : Conjugation L) (hω : IsCompact ω)
    (g : A) (t : ℝ) : A := g * positivePower ω hω g (-(t / 2))

private theorem polarPath_zero (ω : Conjugation L) (hω : IsCompact ω) (g : A) :
    polarPath ω hω g 0 = g := by
  simp [polarPath, positivePower_zero]

private theorem polarPath_one_compact (ω : Conjugation L) (hω : IsCompact ω) (g : A) :
    Intertwines ω ω (polarPath ω hω g 1) := by
  let q := positivePower ω hω g (-(1 / 2))
  have h : adjointProduct ω g * q = q⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← positivePower_one ω hω g]
    dsimp only [q]
    rw [← positivePower_add, ← positivePower_add]
    norm_num [positivePower_zero]
  have hq (x : L) : adjointProduct ω g (q x) = q.symm x :=
    congrArg (fun a : A => a x) h
  intro x
  change ω.map (g (q x)) = g (q (ω.map x))
  calc
    _ = (adjointEquiv ω g).symm (ω.map (q x)) := by
      change _ = ω.map (g (ω.map (ω.map (q x))))
      rw [ω.involutive]
    _ = (adjointEquiv ω g).symm (adjointProduct ω g (q (ω.map x))) := by
      rw [hq, positivePower_compact_conjugation]
    _ = _ := (adjointEquiv ω g).symm_apply_apply _

private theorem polarPath_of_compact (ω : Conjugation L) (hω : IsCompact ω)
    (g : A) (hg : Intertwines ω ω g) (t : ℝ) : polarPath ω hω g t = g := by
  have hP : adjointProduct ω g = 1 := by
    apply LieEquiv.ext
    intro x
    change ω.map (g.symm (ω.map (g x))) = x
    rw [hg, g.symm_apply_apply, ω.involutive]
  have hq : positivePower ω hω g (-(t / 2)) = 1 := by
    apply LieEquiv.ext
    intro x
    have hx : adjointProduct ω g x = ((1 : ℝ) : ℂ) • x := by
      rw [hP, Complex.ofReal_one, one_smul]
      rfl
    rw [positivePower_apply ω hω g _ _ _ hx, Real.one_rpow, Complex.ofReal_one, one_smul]
    rfl
  rw [polarPath, hq, mul_one]

omit [FiniteDimensional ℂ L] in
private theorem adjointProduct_commutes (ω : Conjugation L) (g : A)
    (f : L → L) (hω : ∀ x, f (ω.map x) = ω.map (f x))
    (hg : ∀ x, f (g x) = g (f x)) (x : L) :
    f (adjointProduct ω g x) = adjointProduct ω g (f x) := by
  have hi (z : L) : f (g.symm z) = g.symm (f z) := by
    apply g.injective
    change g (f (g.symm z)) = g (g.symm (f z))
    rw [← hg, g.apply_symm_apply, g.apply_symm_apply]
  change f (ω.map (g.symm (ω.map (g x)))) = ω.map (g.symm (ω.map (g (f x))))
  rw [hω, hi, hω, hg]

private theorem polarPath_commutes (ω : Conjugation L) (hω : IsCompact ω)
    (g : A) (t : ℝ) (a : A) (ha : Intertwines ω ω a) (hg : Commute g a) :
    Commute (polarPath ω hω g t) a := by
  have hg' (x : L) : a (g x) = g (a x) :=
    congrArg (fun e : A => e x) hg.eq.symm
  have h (x : L) := positivePower_commutes ω hω g (-(t / 2)) a id
    (fun _ => rfl) (map_smul a) (adjointProduct_commutes ω g a (fun x => (ha x).symm) hg') x
  apply LieEquiv.ext
  intro x
  change g (positivePower ω hω g (-(t / 2)) (a x)) =
    a (g (positivePower ω hω g (-(t / 2)) x))
  rw [hg', h]

private theorem polarPath_intertwines (ω τ : Conjugation L) (hω : IsCompact ω)
    (hcompat : ∀ x, τ.map (ω.map x) = ω.map (τ.map x))
    (g : A) (hg : Intertwines τ τ g) (t : ℝ) :
    Intertwines τ τ (polarPath ω hω g t) := by
  intro x
  have h := positivePower_commutes ω hω g (-(t / 2)) τ.map star (fun r => by simp)
    τ.antilinear (adjointProduct_commutes ω g τ.map hcompat hg) x
  change τ.map (g (positivePower ω hω g (-(t / 2)) x)) =
    g (positivePower ω hω g (-(t / 2)) (τ.map x))
  rw [hg, h]


private def linearMap (g : A) : L →ₗ[ℂ] L := g.toLinearEquiv.toLinearMap

private noncomputable def coordinates {n : ℕ} (b : Basis (Fin n) ℂ L) :
    A →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := LinearMap.toMatrix b b (linearMap g)
  map_one' := LinearMap.toMatrix_one b
  map_mul' g h := LinearMap.toMatrix_mul b (linearMap g) (linearMap h)

omit [FiniteDimensional ℂ L] in
private theorem coordinates_apply {n : ℕ} (b : Basis (Fin n) ℂ L) (g : A) (i j : Fin n) :
    coordinates b g i j = b.repr (g (b j)) i :=
  LinearMap.toMatrix_apply b b (linearMap g) i j

omit [FiniteDimensional ℂ L] in
private theorem coordinates_change {n m : ℕ} (b : Basis (Fin n) ℂ L)
    (c : Basis (Fin m) ℂ L) (g : A) :
    coordinates c g = LinearMap.toMatrix b c 1 *
      (coordinates b g * LinearMap.toMatrix c b 1) := by
  change LinearMap.toMatrix c c (linearMap g) = LinearMap.toMatrix b c 1 *
    (LinearMap.toMatrix b b (linearMap g) * LinearMap.toMatrix c b 1)
  rw [← LinearMap.toMatrix_comp c b b, ← LinearMap.toMatrix_comp c b c]
  change LinearMap.toMatrix c c (linearMap g) =
    LinearMap.toMatrix c c (LinearMap.id.comp ((linearMap g).comp LinearMap.id))
  simp

omit [FiniteDimensional ℂ L] in
private theorem continuous_coordinates_change {X : Type v} [TopologicalSpace X] {n m : ℕ}
    (b : Basis (Fin n) ℂ L) (c : Basis (Fin m) ℂ L) {f : X → A}
    (hf : Continuous fun x => coordinates b (f x)) :
    Continuous fun x => coordinates c (f x) := by
  simp only [coordinates_change b c]
  exact continuous_const.matrix_mul (hf.matrix_mul continuous_const)

omit [FiniteDimensional ℂ L] in
private theorem continuous_coordinates_iff {X : Type v} [TopologicalSpace X] {n : ℕ}
    (b : Basis (Fin n) ℂ L) (f : X → A) :
    Continuous[inferInstance, automorphismTopology b] f ↔
      Continuous (fun x => coordinates b (f x)) := by
  unfold automorphismTopology
  rw [continuous_induced_rng]
  simp only [Function.comp_def, ← coordinates_apply]
  rfl

omit [FiniteDimensional ℂ L] in
private theorem continuous_coordinates {n : ℕ} (b : Basis (Fin n) ℂ L) :
    Continuous[automorphismTopology b, inferInstance] (coordinates b) := by
  let : TopologicalSpace A := automorphismTopology b
  exact (continuous_coordinates_iff b id).mp continuous_id

private theorem continuous_polarPath {n : ℕ} (b : Basis (Fin n) ℂ L)
    (ω : Conjugation L) (hω : IsCompact ω) (g : A) :
    Continuous[inferInstance, automorphismTopology b] (polarPath ω hω g) := by
  obtain ⟨c, r, hc, hr⟩ := adjointProduct_eigenbasis ω hω g
  apply (continuous_coordinates_iff b _).mpr
  apply continuous_coordinates_change c b
  apply continuous_matrix
  intro i j
  have h (t : ℝ) : coordinates c (polarPath ω hω g t) i j =
      (((r j ^ (-(t / 2) : ℝ) : ℝ) : ℂ) * c.repr (g (c j)) i) := by
    rw [coordinates_apply]
    change c.repr (g (positivePower ω hω g (-(t / 2)) (c j))) i = _
    rw [positivePower_apply ω hω g _ _ _ (hc j), map_smul, map_smul]
    rfl
  simp only [h]
  exact (Complex.continuous_ofReal.comp
    ((Real.continuous_const_rpow (hr j).ne').comp
      ((continuous_id.div_const (2 : ℝ)).neg))).mul continuous_const

private theorem coordinates_star (ω : Conjugation L) (hω : IsCompact ω) :
    let core := hermitianCore ω hω
    letI : NormedAddCommGroup L := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ L := InnerProductSpace.ofCore core.toCore
    ∀ {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ L) (g : A),
      star (coordinates b.toBasis g) = coordinates b.toBasis (adjointEquiv ω g) := by
  dsimp only
  let core := hermitianCore ω hω
  let : NormedAddCommGroup L := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ L := InnerProductSpace.ofCore core.toCore
  intro n b g
  have h : (linearMap g).adjoint = linearMap (adjointEquiv ω g) := by
    ext x
    refine ext_inner_left ℂ (fun y => ?_)
    rw [LinearMap.adjoint_inner_right]
    exact adjoint_identity ω g y x
  change (LinearMap.toMatrix b.toBasis b.toBasis (linearMap g))ᴴ =
    LinearMap.toMatrix b.toBasis b.toBasis (linearMap (adjointEquiv ω g))
  rw [← LinearMap.toMatrix_adjoint, h]

private theorem coordinates_positive_sqrt (ω : Conjugation L) (hω : IsCompact ω) :
    let core := hermitianCore ω hω
    letI : NormedAddCommGroup L := core.toNormedAddCommGroup
    letI : InnerProductSpace ℂ L := InnerProductSpace.ofCore core.toCore
    ∀ {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ L) (g : A),
      CFC.sqrt (star (coordinates b.toBasis g) * coordinates b.toBasis g) =
        coordinates b.toBasis (positivePower ω hω g (1 / 2)) := by
  dsimp only
  let core := hermitianCore ω hω
  let : NormedAddCommGroup L := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ L := InnerProductSpace.ofCore core.toCore
  intro n b g
  have hsquare (s t : ℝ) (h : s + s = t) :
      coordinates b.toBasis (positivePower ω hω g s) *
        coordinates b.toBasis (positivePower ω hω g s) =
      coordinates b.toBasis (positivePower ω hω g t) := by
    rw [← map_mul, ← positivePower_add, h]
  apply CFC.sqrt_unique
  · rw [hsquare _ 1 (by norm_num), positivePower_one, coordinates_star ω hω b,
      ← map_mul, adjointProduct]
  · -- The half power is the adjoint of the quarter power times the quarter power.
    let a := coordinates b.toBasis (positivePower ω hω g (1 / 4))
    have hstar : star a = a := by
      rw [show a = coordinates b.toBasis (positivePower ω hω g (1 / 4)) from rfl,
        coordinates_star ω hω b, positivePower_adjoint]
    rw [← hsquare (1 / 4) _ (by norm_num)]
    change 0 ≤ a * a
    simpa only [hstar] using star_mul_self_nonneg a

omit [FiniteDimensional ℂ L] in
private theorem coordinates_inverse {n : ℕ} (b : Basis (Fin n) ℂ L) (g : A) :
    Ring.inverse (coordinates b g) = coordinates b g⁻¹ := by
  let u : Aˣ := ⟨g, g⁻¹, mul_inv_cancel g, inv_mul_cancel g⟩
  exact Ring.inverse_unit (Units.map (coordinates b) u)

omit [FiniteDimensional ℂ L] in
private theorem coordinates_inverse_continuousAt {n : ℕ} (b : Basis (Fin n) ℂ L) (g : A) :
    ContinuousAt Ring.inverse (coordinates b g) := by
  let u : Aˣ := ⟨g, g⁻¹, mul_inv_cancel g, inv_mul_cancel g⟩
  exact NormedRing.inverse_continuousAt (Units.map (coordinates b) u)

private theorem continuous_polarEndpoint {n : ℕ} (b : Basis (Fin n) ℂ L)
    (ω : Conjugation L) (hω : IsCompact ω) :
    Continuous[automorphismTopology b, automorphismTopology b]
      (fun g => polarPath ω hω g 1) := by
  let : TopologicalSpace A := automorphismTopology b
  let core := hermitianCore ω hω
  let : NormedAddCommGroup L := core.toNormedAddCommGroup
  let : InnerProductSpace ℂ L := InnerProductSpace.ofCore core.toCore
  let c := stdOrthonormalBasis ℂ L
  have hc : Continuous (coordinates c.toBasis) :=
    continuous_coordinates_change b c.toBasis (f := id) (continuous_coordinates b)
  have hpos : Continuous (fun g : A =>
      coordinates c.toBasis (positivePower ω hω g (1 / 2))) := by
    simp only [← coordinates_positive_sqrt ω hω c]
    exact CFC.continuousOn_sqrt.comp_continuous (hc.star.matrix_mul hc)
      (fun g => star_mul_self_nonneg (coordinates c.toBasis g))
  have hneg : Continuous (fun g : A =>
      coordinates c.toBasis (positivePower ω hω g (-(1 / 2)))) := by
    have he (g : A) : positivePower ω hω g (-(1 / 2)) =
        (positivePower ω hω g (1 / 2))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← positivePower_add]
      norm_num [positivePower_zero]
    simp only [he, ← coordinates_inverse]
    exact continuous_iff_continuousAt.mpr fun g =>
      (coordinates_inverse_continuousAt c.toBasis
        (positivePower ω hω g (1 / 2))).comp'
        (f := fun x => coordinates c.toBasis (positivePower ω hω x (1 / 2))) hpos.continuousAt
  apply (continuous_coordinates_iff b _).mpr
  apply continuous_coordinates_change c.toBasis b
  simp only [polarPath, map_mul]
  exact hc.matrix_mul hneg


omit [FiniteDimensional ℂ L] in
private theorem involution_fixed_iff (ω : Conjugation L) (a : A)
    (ha : Intertwines ω ω a) (ha₂ : Function.Involutive a)
    (g : A) (hg : Intertwines ω ω g) :
    Intertwines (involutionConjugation ω a ha ha₂)
        (involutionConjugation ω a ha ha₂) g ↔ Commute g a := by
  constructor
  · intro h
    apply LieEquiv.ext
    intro x
    have hx := h (ω.map x)
    change a (ω.map (g (ω.map x))) = g (a (ω.map (ω.map x))) at hx
    rw [hg, ω.involutive] at hx
    exact hx.symm
  · intro h x
    change a (ω.map (g x)) = g (a (ω.map x))
    rw [hg]
    exact congrArg (fun e : A => e (ω.map x)) h.eq.symm

/-- The polar endpoint retracts the complex centralizer onto its compact
part. Each real fixed element is joined to that part within the real group. -/
private theorem connected_reduced_fixed_points {n : ℕ} (b : Basis (Fin n) ℂ L)
    (ω : Conjugation L) (hω : IsCompact ω) (a : A)
    (ha : Intertwines ω ω a) (ha₂ : Function.Involutive a) :
    let := automorphismTopology b
    ConnectedSpace {g : A // Commute g a} →
    ConnectedSpace {g : A // Intertwines (involutionConjugation ω a ha ha₂)
      (involutionConjugation ω a ha ha₂) g} := by
  dsimp only
  let : TopologicalSpace A := automorphismTopology b
  intro hcentralizer
  let : ConnectedSpace {g : A // Commute g a} := hcentralizer
  let τ := involutionConjugation ω a ha ha₂
  let K := {g : A // Commute g a ∧ Intertwines ω ω g}
  let S := {g : A // Intertwines τ τ g}
  let retract (g : {g : A // Commute g a}) : K :=
    ⟨polarPath ω hω g.val 1, polarPath_commutes ω hω g.val 1 a ha g.property,
      polarPath_one_compact ω hω g.val⟩
  have hretract : Continuous retract :=
    ((continuous_polarEndpoint b ω hω).comp continuous_subtype_val).subtype_mk _
  have hsurj : Function.Surjective retract := by
    intro g
    refine ⟨⟨g.val, g.property.1⟩, Subtype.ext ?_⟩
    exact polarPath_of_compact ω hω g.val g.property.2 1
  let : ConnectedSpace K := hsurj.connectedSpace hretract
  let includeCompact (g : K) : S :=
    ⟨g.val, (involution_fixed_iff ω a ha ha₂ g.val g.property.2).mpr g.property.1⟩
  have hK : IsConnected (Set.range includeCompact) :=
    isConnected_range (continuous_subtype_val.subtype_mk _)
  have hcompat (x : L) : τ.map (ω.map x) = ω.map (τ.map x) := by
    change a (ω.map (ω.map x)) = ω.map (a (ω.map x))
    rw [ha]
  let path (g : S) (t : ℝ) : S :=
    ⟨polarPath ω hω g.val t, polarPath_intertwines ω τ hω hcompat g.val g.property t⟩
  have hpath (g : S) : IsConnected (Set.range (path g)) :=
    isConnected_range ((continuous_polarPath b ω hω g.val).subtype_mk _)
  have hzero (g : S) : path g 0 = g := Subtype.ext (polarPath_zero ω hω g.val)
  have hone (g : S) : path g 1 ∈ Set.range includeCompact := by
    have hc := polarPath_one_compact ω hω g.val
    have ht := (path g 1).property
    exact ⟨⟨_, (involution_fixed_iff ω a ha ha₂ _ hc).mp ht, hc⟩, Subtype.ext rfl⟩
  change ConnectedSpace S
  rw [connectedSpace_iff_univ]
  refine ⟨hK.nonempty.mono (Set.subset_univ _), isPreconnected_of_forall_pair ?_⟩
  intro g _ k _
  refine ⟨(Set.range (path g) ∪ Set.range includeCompact) ∪ Set.range (path k),
    Set.subset_univ _, Or.inl (Or.inl ⟨0, hzero g⟩), Or.inr ⟨0, hzero k⟩, ?_⟩
  have hleft : (Set.range (path g) ∩ Set.range includeCompact).Nonempty :=
    ⟨path g 1, ⟨1, rfl⟩, hone g⟩
  have hright : ((Set.range (path g) ∪ Set.range includeCompact) ∩
      Set.range (path k)).Nonempty :=
    ⟨path k 1, Or.inr (hone k), ⟨1, rfl⟩⟩
  exact (IsConnected.union hright (IsConnected.union hleft (hpath g) hK)
    (hpath k)).isPreconnected

omit [FiniteDimensional ℂ L] in
private theorem intertwines_conjugate (σ τ : Conjugation L) (p g : A)
    (hp : Intertwines σ τ p) (hg : Intertwines σ σ g) :
    Intertwines τ τ (p * g * p⁻¹) := by
  have hi (x : L) : σ.map (p.symm x) = p.symm (τ.map x) := by
    apply p.injective
    change p (σ.map (p.symm x)) = p (p.symm (τ.map x))
    rw [← hp, p.apply_symm_apply, p.apply_symm_apply]
  intro x
  change τ.map (p (g (p.symm x))) = p (g (p.symm (τ.map x)))
  rw [hp, hg, hi]

omit [FiniteDimensional ℂ L] in
private theorem connected_fixed_points_of_intertwines {n : ℕ} (b : Basis (Fin n) ℂ L)
    (σ τ : Conjugation L) (p : A) (hp : Intertwines σ τ p) :
    let := automorphismTopology b
    ConnectedSpace {g : A // Intertwines τ τ g} →
    ConnectedSpace {g : A // Intertwines σ σ g} := by
  dsimp only
  let : TopologicalSpace A := automorphismTopology b
  intro hconn
  let : ConnectedSpace {g : A // Intertwines τ τ g} := hconn
  have hi : Intertwines τ σ p⁻¹ := by
    intro x
    change σ.map (p.symm x) = p.symm (τ.map x)
    apply p.injective
    change p (σ.map (p.symm x)) = p (p.symm (τ.map x))
    rw [← hp, p.apply_symm_apply, p.apply_symm_apply]
  let f (g : {g : A // Intertwines τ τ g}) : {g : A // Intertwines σ σ g} :=
    ⟨p⁻¹ * g.val * (p⁻¹)⁻¹, intertwines_conjugate τ σ p⁻¹ g.val hi g.property⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply (continuous_coordinates_iff b _).mpr
    simp only [map_mul]
    exact (continuous_const.matrix_mul
      ((continuous_coordinates b).comp continuous_subtype_val)).matrix_mul continuous_const
  have hsurj : Function.Surjective f := by
    intro g
    refine ⟨⟨p * g.val * p⁻¹, intertwines_conjugate σ τ p g.val hp g.property⟩, Subtype.ext ?_⟩
    change p⁻¹ * (p * g.val * p⁻¹) * (p⁻¹)⁻¹ = g.val
    simp [mul_assoc]
  exact hsurj.connectedSpace hf

/-- Connectedness transfers from the complex centralizers of square-one
automorphisms to the fixed group of an arbitrary real conjugation. -/
theorem connected_fixed_points : connectedFixedPointsType := by
  intro L _ _ _ σ n b
  let : TopologicalSpace (L ≃ₗ⁅ℂ⁆ L) := automorphismTopology b
  intro hsemisimple hcentralizers
  obtain ⟨ω, _, hω⟩ :=
    LieAlgebrasAndRepresentations.CompactRealForm.compact_real_form hsemisimple
  have hcompact : IsCompact ω := hω
  obtain ⟨_, a, ha, ha₂, p, _, _, hp⟩ := polar_reduction ω hcompact σ
  have ha_square : a * a = 1 := LieEquiv.ext ha₂
  exact connected_fixed_points_of_intertwines b σ _ p hp
    (connected_reduced_fixed_points b ω hcompact a ha ha₂ (hcentralizers a ha_square))

end LinearAlgebraicGroups.Arithmetic.RealPolarFixedPoints
