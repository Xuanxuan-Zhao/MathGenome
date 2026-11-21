import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.SurfaceCupPairing
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SurfaceHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.UniversalCoefficientsCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.PoincareDuality
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open CategoryTheory HomologicalComplex
open scoped BigOperators

namespace P202.SurfaceCupPairing
open P202Specs.SurfaceCupPairing P202Specs.SingularChains
open P202Specs.CupProduct P202Specs.CohomologyPairs

/-- Anticommutativity becomes alternatingness after evaluation in ℤ,
where twice an integer can vanish only when that integer vanishes. -/
theorem alternating : Expected.alternating := by
  intro X C μ a
  have h := C.graded_commutative 1 1 a a
  have h' : C.product 1 1 a a = -(C.product 1 1 a a) := by
    have he := (Sigma.mk.inj_iff.mp h).2.eq
    simpa using he
  have he := congrArg (topEvaluation X μ) h'
  change pairing X C μ a a = 0
  change topEvaluation X μ (C.product 1 1 a a) = 0
  rw [map_neg] at he
  omega


section IntegralAlgebra
variable {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {V : Type} [AddCommGroup V] [Module R V]

/-- The simultaneous orthogonal complement of a pair. -/
def pairComplement (B : LinearMap.BilinForm R V) (u v : V) : Submodule R V :=
  LinearMap.ker (B u) ⊓ LinearMap.ker (B v)

lemma remainder_mem (B : LinearMap.BilinForm R V) (hB : B.IsAlt)
    (u v : V) (huv : B u v = 1) (x : V) :
    x - B x v • u + B x u • v ∈ pairComplement B u v := by
  have hvu : B v u = -1 := by rw [← hB.neg_eq, huv]
  constructor <;> change _ = 0
  · simp only [map_add, map_sub, map_smul, smul_eq_mul, hB.self_eq_zero,
      huv, mul_zero, mul_one, sub_zero]
    rw [← hB.neg_eq x u]
    ring
  · simp only [map_add, map_sub, map_smul, smul_eq_mul, hB.self_eq_zero,
      hvu, mul_zero, add_zero]
    rw [← hB.neg_eq x v]
    ring

/-- A unit-valued pair splits off over the integers without division. -/
def splitPair (B : LinearMap.BilinForm R V) (hB : B.IsAlt)
    (u v : V) (huv : B u v = 1) :
    ((R × R) × pairComplement B u v) ≃ₗ[R] V := by
  let f : (R × R) × pairComplement B u v →ₗ[R] V :=
    { toFun := fun p => p.1.1 • u + p.1.2 • v + p.2
      map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add,
        Submodule.coe_add, add_smul]; abel
      map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd,
        Submodule.coe_smul_of_tower, smul_add, smul_smul, smul_eq_mul, RingHom.id_apply] }
  have hvu : B v u = -1 := by rw [← hB.neg_eq, huv]
  apply LinearEquiv.ofBijective f
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    have hu := congrArg (fun x => B u x) hp
    have hv := congrArg (fun x => B v x) hp
    have hw₁ : B u (p.2 : V) = 0 := p.2.property.1
    have hw₂ : B v (p.2 : V) = 0 := p.2.property.2
    change B u (p.1.1 • u + p.1.2 • v + (p.2 : V)) = B u 0 at hu
    change B v (p.1.1 • u + p.1.2 • v + (p.2 : V)) = B v 0 at hv
    simp only [map_add, map_smul, smul_eq_mul, hB.self_eq_zero, huv,
      mul_zero, mul_one, zero_add, hw₁, add_zero, map_zero] at hu
    simp only [map_add, map_smul, smul_eq_mul, hB.self_eq_zero, hvu,
      mul_zero, hw₂, add_zero, map_zero, mul_neg, mul_one, neg_eq_zero] at hv
    have hw : (p.2 : V) = 0 := by simpa [f, hu, hv] using hp
    exact Prod.ext (Prod.ext hv hu) (Subtype.ext hw)
  · intro x
    refine ⟨((B x v, -B x u), ⟨_, remainder_mem B hB u v huv x⟩), ?_⟩
    change B x v • u + (-B x u) • v + (x - B x v • u + B x u • v) = x
    rw [neg_smul]
    abel

lemma splitPair_apply (B : LinearMap.BilinForm R V) (hB : B.IsAlt)
    (u v : V) (huv : B u v = 1) (p : (R × R) × pairComplement B u v) :
    splitPair B hB u v huv p = p.1.1 • u + p.1.2 • v + p.2 := rfl

lemma splitPair_value (B : LinearMap.BilinForm R V) (hB : B.IsAlt)
    (u v : V) (huv : B u v = 1) (p q : (R × R) × pairComplement B u v) :
    B (splitPair B hB u v huv p) (splitPair B hB u v huv q) =
      p.1.1 * q.1.2 - p.1.2 * q.1.1 + B p.2 q.2 := by
  have hvu : B v u = -1 := by rw [← hB.neg_eq, huv]
  have hp₁ : B u (p.2 : V) = 0 := p.2.property.1
  have hp₂ : B v (p.2 : V) = 0 := p.2.property.2
  have hq₁ : B u (q.2 : V) = 0 := q.2.property.1
  have hq₂ : B v (q.2 : V) = 0 := q.2.property.2
  have hp₃ : B (p.2 : V) u = 0 := (hB.eq_iff).mp hp₁
  have hp₄ : B (p.2 : V) v = 0 := (hB.eq_iff).mp hp₂
  simp only [splitPair_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero, huv, hvu,
    hp₃, hp₄, hq₁, hq₂]
  ring

/-- Restriction to the complement preserves integral perfection. A functional
on the complement is extended along the explicit integral projection. -/
lemma complement_perfect (B : LinearMap.BilinForm R V) (hB : B.IsAlt)
    (hP : Function.Bijective B) (u v : V) (huv : B u v = 1) :
    Function.Bijective (B.restrict (pairComplement B u v)) := by
  let W := pairComplement B u v
  let f := splitPair B hB u v huv
  let π : V →ₗ[R] W := (LinearMap.snd R (R × R) W).comp f.symm.toLinearMap
  have hf (w : W) : f ((0, 0), w) = w := by simp [f, splitPair_apply]
  have hπ (w : W) : π w = w := by
    change (f.symm (w : V)).2 = w
    rw [← hf w, f.symm_apply_apply]
  have h0 (w : W) (x : V) : B w x = B w (π x : V) := by
    conv_lhs => rw [← f.apply_symm_apply x]
    rw [show f (f.symm x) = (f.symm x).1.1 • u + (f.symm x).1.2 • v +
      ((f.symm x).2 : V) from rfl]
    have hwu : B (w : V) u = 0 := (hB.eq_iff).mp w.property.1
    have hwv : B (w : V) v = 0 := (hB.eq_iff).mp w.property.2
    simp only [map_add, map_smul, smul_eq_mul, hwu, hwv, mul_zero, zero_add]
    rfl
  constructor
  · intro w z h
    apply Subtype.ext
    apply hP.1
    ext x
    rw [h0 w x, h0 z x]
    exact LinearMap.congr_fun h (π x)
  · intro φ
    obtain ⟨x, hx⟩ := hP.2 (φ.comp π)
    refine ⟨π x, ?_⟩
    ext w
    change B (π x : V) (w : V) = φ w
    calc
      B (π x : V) (w : V) = - B (w : V) (π x : V) := (hB.neg_eq _ _).symm
      _ = - B (w : V) x := congrArg Neg.neg (h0 w x).symm
      _ = B x (w : V) := hB.neg_eq _ _
      _ = φ w := (LinearMap.congr_fun hx w).trans (congrArg φ (hπ w))

abbrev PairCoordinates (R : Type) (g : ℕ) := Fin g → R × R

def coordinateValue {g : ℕ} (x y : PairCoordinates R g) : R :=
  ∑ i, ((x i).1 * (y i).2 - (x i).2 * (y i).1)

def prependPair (R : Type) [CommRing R] (g : ℕ) : ((R × R) × PairCoordinates R g) ≃ₗ[R] PairCoordinates R (g+1) where
  toFun p := Fin.cons p.1 p.2
  invFun p := (p 0, fun i => p i.succ)
  left_inv p := by simp
  right_inv p := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  map_add' p q := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  map_smul' a p := by funext i; exact Fin.cases rfl (fun _ => rfl) i

lemma prependPair_value {g : ℕ} (p q : (R × R) × PairCoordinates R g) :
    coordinateValue (prependPair R g p) (prependPair R g q) =
      p.1.1 * q.1.2 - p.1.2 * q.1.1 + coordinateValue p.2 q.2 := by
  simp [coordinateValue, prependPair, Fin.sum_univ_succ]
  ring

/-- Perfection produces a unit-valued pair, using a basis coordinate
functional rather than dividing by a possibly nonunit integer. -/
lemma exists_unit_pair [Module.Free R V] [Module.Finite R V]
    (B : LinearMap.BilinForm R V) (hP : Function.Surjective B)
    (hn : 0 < Module.finrank R V) : ∃ u v, B u v = 1 := by
  let b := Module.finBasis R V
  let i : Fin (Module.finrank R V) := ⟨0, hn⟩
  obtain ⟨u, hu⟩ := hP (b.coord i)
  exact ⟨u, b i, by rw [hu]; simp⟩

/-- Integral symplectic Gram–Schmidt, with no rationalization. -/
theorem symplecticCoordinates (g : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module R V] [Module.Free R V]
      [Module.Finite R V] (B : LinearMap.BilinForm R V), B.IsAlt →
      Function.Bijective B → Module.finrank R V = 2*g →
      ∃ e : V ≃ₗ[R] PairCoordinates R g,
        ∀ x y, B x y = coordinateValue (e x) (e y) := by
  induction g with
  | zero =>
    intro V _ _ _ _ B hB hP hn
    haveI : Subsingleton V := Module.finrank_zero_iff.mp (by simpa using hn)
    let e : V ≃ₗ[R] PairCoordinates R 0 := LinearEquiv.ofSubsingleton (R := R) V (PairCoordinates R 0)
    refine ⟨e, ?_⟩
    intro x y
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx, coordinateValue]
  | succ g ih =>
    intro V _ _ _ _ B hB hP hn
    obtain ⟨u, v, huv⟩ := exists_unit_pair B hP.2 (by omega)
    let W := pairComplement B u v
    let f := splitPair B hB u v huv
    have hdim : Module.finrank R V = 2 + Module.finrank R W := by
      rw [← f.finrank_eq, Module.finrank_prod, Module.finrank_prod]
      simp only [Module.finrank_self, Nat.one_add]
      rfl
    have hW : (B.restrict W).IsAlt := fun x => hB x
    obtain ⟨e, he⟩ := ih W (B.restrict W) hW (complement_perfect B hB hP u v huv)
      (by omega)
    let k := f.symm.trans ((LinearEquiv.refl R (R × R)).prodCongr e)
    refine ⟨k.trans (prependPair R g), ?_⟩
    intro x y
    change B x y = coordinateValue (prependPair R g (k x)) (prependPair R g (k y))
    rw [prependPair_value]
    have h := splitPair_value B hB u v huv (f.symm x) (f.symm y)
    change B (f (f.symm x)) (f (f.symm y)) = _ at h
    simp only [LinearEquiv.apply_symm_apply] at h
    change B x y = (f.symm x).1.1 * (f.symm y).1.2 -
      (f.symm x).1.2 * (f.symm y).1.1 +
      coordinateValue (e (f.symm x).2) (e (f.symm y).2)
    rw [← he]
    exact h

/-- Flatten the coordinates while retaining the order within each pair. -/
def flattenCoordinates (R : Type) [CommRing R] (g : ℕ) : PairCoordinates R g ≃ₗ[R] (Fin g × Fin 2 → R) where
  toFun p ij := if ij.2 = 0 then (p ij.1).1 else (p ij.1).2
  invFun p i := (p (i, 0), p (i, 1))
  left_inv p := by funext i; apply Prod.ext <;> simp
  right_inv p := by funext ⟨i,j⟩; fin_cases j <;> simp
  map_add' p q := by funext ⟨i,j⟩; fin_cases j <;> simp
  map_smul' a p := by funext ⟨i,j⟩; fin_cases j <;> simp

lemma flatten_single {g : ℕ} (i : Fin g) (j : Fin 2) :
    (flattenCoordinates R g).symm (Pi.single (i, j) 1) =
      Pi.single i (Module.Basis.finTwoProd R j) := by
  funext k
  apply Prod.ext <;> fin_cases j <;>
    simp [flattenCoordinates, Pi.single_apply, apply_ite, eq_comm]

lemma coordinateValue_single {g : ℕ} (i k : Fin g) (j l : Fin 2) :
    coordinateValue (Pi.single i (Module.Basis.finTwoProd R j))
      (Pi.single k (Module.Basis.finTwoProd R l)) = (standardValue g (i,j) (k,l) : R) := by
  fin_cases j <;> fin_cases l <;>
    simp [coordinateValue, standardValue, Pi.single_apply, apply_ite, eq_comm]

/-- Every integral perfect alternating form of rank 2g has the requested
basis, including the empty basis in rank zero. -/
theorem integralSymplectic : Expected.integralSymplectic := by
  intro V _ _ _ _ B hB hP g hn
  obtain ⟨e, he⟩ := symplecticCoordinates (R := ℤ) g V B hB hP hn
  let b := Module.Basis.ofEquivFun (e.trans (flattenCoordinates ℤ g))
  have hb (i : Fin g × Fin 2) : e (b i) =
      (flattenCoordinates ℤ g).symm (Pi.single i 1) := by
    rw [Module.Basis.coe_ofEquivFun]
    change e (e.symm _) = _
    exact e.apply_symm_apply _
  refine ⟨b, ?_⟩
  rintro ⟨i,j⟩ ⟨k,l⟩
  rw [he, hb, hb, flatten_single, flatten_single, coordinateValue_single]
  simp

end IntegralAlgebra

section SingularBridges
open P202Specs.UniversalCoefficientsCohomology

/-- UCT evaluation on categorical cycle representatives, with no grading or
scalar changes hidden in the statement. -/
lemma evaluation_class (R : Type) [CommRing R]
    (K : ChainComplex (ModuleCat.{0} R) ℤ) (n : ℤ)
    (a : (dualChain R R K).cycles n) (z : K.cycles n) :
    evaluation R R K n ((dualChain R R K).homologyπ n a) (K.homologyπ n z) =
      (show K.X n →ₗ[R] R from (dualChain R R K).iCycles n a) (K.iCycles n z) := by
  let a' : Algebraic.cycles (dualChain R R K) n :=
    ((dualChain R R K).sc n).moduleCatCyclesIso.hom a
  let z' : Algebraic.cycles K n := (K.sc n).moduleCatCyclesIso.hom z
  have h := P202.UniversalCoefficientsCohomology.evaluation_formula R R K n a' z'
  rw [P202.UniversalCoefficientsCohomology.cycleClass_eq,
    P202.UniversalCoefficientsCohomology.cycleClass_eq] at h
  have ha : (a' : (dualChain R R K).X n) = (dualChain R R K).iCycles n a :=
    congrArg (fun f => f a) ((dualChain R R K).sc n).moduleCatCyclesIso_hom_i
  have hz : (z' : K.X n) = K.iCycles n z :=
    congrArg (fun f => f z) (K.sc n).moduleCatCyclesIso_hom_i
  simpa only [a', z', Iso.hom_inv_id_apply, ha, hz] using h

/-- The degree-one integral UCT evaluation is an isomorphism when H₀ is
free. The actual Ext endpoint vanishes because its first argument is
projective. -/
lemma evaluation_one_bijective (X : TopCat.{0})
    [Module.Free ℤ (homology ℤ ℤ X 0)] :
    Function.Bijective (evaluation ℤ ℤ (ordinaryComplex ℤ ℤ X) 1) := by
  let K := ordinaryComplex ℤ ℤ X
  let N := AlgebraicExt.resolutionFamily ℤ (K.homology 0)
  haveI : Subsingleton (actualExt ℤ ℤ K 0) :=
    P103.Ch11.VanishingAndFlatness.ext_projective ℤ (K.homology 0) ℤ
      inferInstance N.val N.property 0
  obtain ⟨α, σ, hα, hx, hs, hσ⟩ :=
    (P202.UniversalCoefficientsCohomology.all_degrees ℤ ℤ).1 X 1
  refine ⟨?_, hs⟩
  intro a b hab
  apply sub_eq_zero.mp
  have hzero : evaluation ℤ ℤ K 1 (a-b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨x, hx⟩ := (hx (a-b)).mp hzero
  have hx0 : x = (0 : actualExt ℤ ℤ K 0) :=
    @Subsingleton.elim (actualExt ℤ ℤ K 0) inferInstance x 0
  rw [hx0, map_zero] at hx
  exact hx.symm

/-- Evaluation in finite singular chain coordinates agrees with the
ordinary integer-graded dual. -/
lemma cocycleValue_apply (X : TopCat.{0}) (n : ℕ)
    (a : (ordinaryCochains ℤ ℤ X).cycles (n : ℤ))
    (z : (ordinaryComplex ℤ ℤ X).X (n : ℤ)) :
    cocycleValue ℤ X n a ((ordinaryNonnegativeIso ℤ ℤ X n).hom z) =
      (show (ordinaryComplex ℤ ℤ X).X (n : ℤ) →ₗ[ℤ] ℤ from
        (ordinaryCochains ℤ ℤ X).iCycles (n : ℤ) a) z := by
  change (show (ordinaryComplex ℤ ℤ X).X (n : ℤ) →ₗ[ℤ] ℤ from
    (ordinaryCochains ℤ ℤ X).iCycles (n : ℤ) a)
    ((ordinaryNonnegativeIso ℤ ℤ X n).inv ((ordinaryNonnegativeIso ℤ ℤ X n).hom z)) = _
  rw [Iso.hom_inv_id_apply]

/-- The cap/cup evaluation identity in degrees (1,1,2), on the actual
ordinary integer-graded objects. -/
lemma cap_cup_evaluation (X : TopCat.{0})
    (a b : (ordinaryCochains ℤ ℤ X).cycles 1)
    (z : (ordinaryComplex ℤ ℤ X).X 2) :
    (show (ordinaryComplex ℤ ℤ X).X 1 →ₗ[ℤ] ℤ from
      (ordinaryCochains ℤ ℤ X).iCycles 1 b)
      (P202Specs.CapProducts.cap ℤ X 1 2 (cocycleValue ℤ X 1 a) z) =
    P202Specs.CupProduct.cup ℤ X 1 1 (cocycleValue ℤ X 1 a) (cocycleValue ℤ X 1 b)
      ((ordinaryNonnegativeIso ℤ ℤ X 2).hom z) := by
  have h := P202.CapProducts.cap_nonnegative ℤ X 1 2 1 rfl (cocycleValue ℤ X 1 a) z
  have he := congrArg (fun c => cocycleValue ℤ X 1 b
    ((ordinaryNonnegativeIso ℤ ℤ X 1).hom c)) h
  simp only [P202Specs.CapProducts.castOrdinary, eqToIso_refl,
    Iso.refl_hom, ModuleCat.id_apply, Iso.inv_hom_id_apply, cocycleValue_apply] at he
  exact he.trans (P202.CapProducts.pairing ℤ X 1 2 1 rfl
      (cocycleValue ℤ X 1 a) (cocycleValue ℤ X 1 b)
      ((ordinaryNonnegativeIso ℤ ℤ X 2).hom z))

end SingularBridges

open P202Specs.UniversalCoefficientsCohomology

/-- Surface cup pairing, with the sign fixed by the prescribed orientation.
Perfection comes from UCT evaluation composed with the dual of the actual
cap isomorphism. The final basis uses integral symplectic Gram–Schmidt. -/
theorem surfacePairing : Expected.surfacePairing := by
  classical
  intro g A o C
  let X := space g
  let K := ordinaryComplex ℤ ℤ X
  let Q := ordinaryCochains ℤ ℤ X
  let d := P202.CompactSupport.dualityData ℤ
  letI : CompactSpace (P202Specs.SurfaceHomology.OrientedSurface g) :=
    inferInstanceAs (CompactSpace (Quotient
      (P202Specs.SurfaceHomology.polygonSetoid (P202Specs.SurfaceHomology.orientedWord g))))
  have hM : IsCompact (Set.univ : Set (P202Specs.SurfaceHomology.OrientedSurface g)) :=
    isCompact_univ
  obtain ⟨hf, μ, hμ, hrep⟩ := P202.PoincareDuality.compactIdentification ℤ d 2
    (P202Specs.SurfaceHomology.OrientedSurface g) A o hM
  have hd := P202.PoincareDuality.duality ℤ d 2
    (P202Specs.SurfaceHomology.OrientedSurface g) A o
  let e₁ : H ℤ X 1 ≃ₗ[ℤ] homology ℤ ℤ X 1 :=
    (LinearEquiv.ofBijective
      (P202Specs.PoincareDuality.forgetSupport ℤ
        (P202Specs.SurfaceHomology.OrientedSurface g) 1) (hf 1)).symm.trans
      (LinearEquiv.ofBijective
        (d.D 2 (P202Specs.SurfaceHomology.OrientedSurface g) A o 1) (hd 1))
  let e₂ : H ℤ X 2 ≃ₗ[ℤ] homology ℤ ℤ X 0 :=
    (LinearEquiv.ofBijective
      (P202Specs.PoincareDuality.forgetSupport ℤ
        (P202Specs.SurfaceHomology.OrientedSurface g) 2) (hf 2)).symm.trans
      (LinearEquiv.ofBijective
        (d.D 2 (P202Specs.SurfaceHomology.OrientedSurface g) A o 2) (hd 2))
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 2)).mp inferInstance μ
  let aug := P202.PoincareDuality.DegreeZero.augmentationH0Equiv ℤ X
  have htop (a : H ℤ X 2) : topEvaluation X μ a = aug (e₂ a) := by
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ 2)).mp inferInstance a
    obtain ⟨w, hw, he⟩ := hrep 2 a z hz
    change evaluation ℤ ℤ K 2 (Q.homologyπ 2 a) μ = aug (e₂ (Q.homologyπ 2 a))
    erw [← hz, evaluation_class]
    change (show K.X 2 →ₗ[ℤ] ℤ from Q.iCycles 2 a) (K.iCycles 2 z) = _
    change e₂ (Q.homologyπ 2 a) = K.homologyπ 0 w at he
    erw [he, P202.PoincareDuality.DegreeZero.augmentationH0Equiv_class, hw]
    have hcap := (P202.PoincareDuality.DegreeZero.augmentation_cap ℤ X 2
      (cocycleValue ℤ X 2 a) (K.iCycles 2 z)).symm
    change cocycleValue ℤ X 2 a ((ordinaryNonnegativeIso ℤ ℤ X 2).hom (K.iCycles 2 z)) =
      augmentationLinear ℤ ℤ X ((ordinaryNonnegativeIso ℤ ℤ X 0).hom
        (P202Specs.CapProducts.cap ℤ X 2 2 (cocycleValue ℤ X 2 a) (K.iCycles 2 z))) at hcap
    rw [cocycleValue_apply] at hcap
    exact hcap
  have htopBij : Function.Bijective (topEvaluation X μ) := by
    have heq : topEvaluation X μ = aug.toLinearMap.comp e₂.toLinearMap := by
      ext a
      exact htop a
    rw [heq]
    exact aug.bijective.comp e₂.bijective
  have hpair (a b : H ℤ X 1) :
      pairing X C μ a b = evaluation ℤ ℤ K 1 b (e₁ a) := by
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ 1)).mp inferInstance a
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ 1)).mp inferInstance b
    obtain ⟨w, hw, he⟩ := hrep 1 a z hz
    obtain ⟨c, hc, hp⟩ := C.represents 1 1 a b
    change evaluation ℤ ℤ K 2 (C.product 1 1 (Q.homologyπ 1 a) (Q.homologyπ 1 b)) μ = _
    erw [hp, ← hz, evaluation_class]
    change e₁ (Q.homologyπ 1 a) = K.homologyπ 1 w at he
    erw [he, evaluation_class, hw]
    erw [← cocycleValue_apply X 2 c (K.iCycles 2 z), hc]
    exact (cap_cup_evaluation X a b (K.iCycles 2 z)).symm
  obtain ⟨h₀, h₁, h₂, habove⟩ := P202.Homology.SurfaceHomology.orientedHomology g
  let q₀ := Classical.choice h₀
  letI : Module.Free ℤ (homology ℤ ℤ X 0) := Module.Free.of_equiv q₀.symm
  have hEv := evaluation_one_bijective X
  have hflip : (pairing X C μ).flip =
      e₁.dualMap.toLinearMap.comp (evaluation ℤ ℤ K 1) := by
    ext a b
    exact hpair b a
  have hflipBij : Function.Bijective (pairing X C μ).flip := by
    rw [hflip]
    exact e₁.dualMap.bijective.comp hEv
  have halt := alternating X C μ
  have hneg : pairing X C μ = -(pairing X C μ).flip := by
    ext a b
    exact (halt.neg_eq b a).symm
  have hBij : Function.Bijective (pairing X C μ) := by
    rw [hneg]
    exact neg_bijective.comp hflipBij
  let e := e₁.trans (Classical.choice h₁)
  letI : Module.Free ℤ (H ℤ X 1) := Module.Free.of_equiv e.symm
  letI : Module.Finite ℤ (H ℤ X 1) := Module.Finite.equiv e.symm
  have hdim : Module.finrank ℤ (H ℤ X 1) = 2*g := by
    rw [e.finrank_eq]
    simp [Module.finrank_pi_fintype]
  obtain ⟨b, hb⟩ := integralSymplectic (H ℤ X 1) (pairing X C μ) halt hBij g hdim
  exact ⟨μ, hμ, htopBij, hBij, halt, b, hb⟩

end P202.SurfaceCupPairing
