import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.PresentationSymmetries
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.SerrePresentation
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Coproduct

noncomputable section

namespace LieNotes.Quantum.Coproduct

open Presentation
open Specs.LieNotes.Quantum.SerrePresentation (serrePolynomial)

universe u v

section Counit

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
variable (C : Cartan A T) (e : T →ₐ[A] A) (hD : ∀ i, e (C.D i) = 0)

include hD in
private theorem counitBasic :
    SatisfiesBasic C e (fun _ => 0) (fun _ => 0) where
  cartanF _ _ := by simp
  eCartan _ _ := by simp
  comm i j := by
    by_cases hij : i = j <;> simp [Specs.LieNotes.Quantum.Presentation.mixed, hij, hD]

private theorem counitSerre : SatisfiesSerre C.q (B := A) (fun _ => 0) (fun _ => 0) where
  pos _ _ _ := by simp [serrePolynomial]
  neg _ _ _ := by simp [serrePolynomial]

/-- A Cartan augmentation killing the mixed commutator coefficients extends
to the whole presentation by sending the root generators to zero. -/
def counitFromCartan : U C →ₐ[A] A :=
  liftU C e (fun _ => 0) (fun _ => 0) (counitBasic C e hD) (counitSerre C)

@[simp] theorem counitFromCartan_cartan (t : T) :
    counitFromCartan C e hD (cartan C t) = e t := by
  simp [counitFromCartan]

@[simp] theorem counitFromCartan_E (i : Root) :
    counitFromCartan C e hD (E C i) = 0 := by
  simp [counitFromCartan]

@[simp] theorem counitFromCartan_F (i : Root) :
    counitFromCartan C e hD (F C i) = 0 := by
  simp [counitFromCartan]

end Counit


section SerreCalculation

variable {A B : Type*} [CommRing A] [Ring B] [Algebra A B]

private def rootVector (q : Aˣ) (a b : B) : B :=
  a * b - (↑q⁻¹ : A) • (b * a)

private theorem serre_eq_rootVector (q : Aˣ) (a b : B) :
    serrePolynomial q a b = a * rootVector q a b - (q : A) • (rootVector q a b * a) := by
  simp only [serrePolynomial, rootVector, pow_two, mul_sub, sub_mul, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, smul_sub, smul_smul, Units.mul_inv, one_smul, mul_assoc]
  module

/-- The two mixed copies of the root vector give a single correction
term, whose contribution cancels the remaining mixed commutator. -/
private theorem serre_add_pair (q : Aˣ) (x u y v : B)
    (hux : u * x = (↑q : A)^2 • (x * u))
    (huy : u * y = (↑q⁻¹ : A) • (y * u))
    (hvx : v * x = (↑q⁻¹ : A) • (x * v))
    (hxy : serrePolynomial q x y = 0) (huv : serrePolynomial q u v = 0) :
    serrePolynomial q (x + u) (y + v) = 0 := by
  let p : A := ↑q
  let s : A := ↑q⁻¹
  have hps : p * s = 1 := Units.mul_inv q
  have hp2s : p^2 * s = p := by rw [pow_two, mul_assoc, hps, mul_one]
  have hsp2 : s * p^2 = p := by rw [mul_comm, hp2s]
  change u * x = p^2 • (x * u) at hux
  change u * y = s • (y * u) at huy
  change v * x = s • (x * v) at hvx
  let z := rootVector q x y
  let w := rootVector q u v
  have hsplit : rootVector q (x + u) (y + v) = z + w + (1 - s^2) • (x * v) := by
    simp only [z, w, rootVector, add_mul, mul_add]
    change x*y + u*y + (x*v + u*v) - s • (y*x + v*x + (y*u + v*u)) =
      x*y - s • (y*x) + (u*v - s • (v*u)) + (1-s^2) • (x*v)
    rw [huy, hvx]
    module
  have huz : u * z = p • (z * u) := by
    change u * (x*y - s • (y*x)) = p • ((x*y - s • (y*x)) * u)
    have ha : u * (x*y) = p • (x*y*u) := by
      rw [← mul_assoc, hux, Algebra.smul_mul_assoc, mul_assoc, huy,
        Algebra.mul_smul_comm, smul_smul, hp2s, ← mul_assoc]
    have hb : u * (y*x) = p • (y*x*u) := by
      rw [← mul_assoc, huy, Algebra.smul_mul_assoc, mul_assoc, hux,
        Algebra.mul_smul_comm, smul_smul, hsp2, ← mul_assoc]
    rw [mul_sub, Algebra.mul_smul_comm, ha, hb, sub_mul, Algebra.smul_mul_assoc]
    rw [smul_sub, smul_comm s p]
  have hwx : w * x = p • (x * w) := by
    change (u*v - s • (v*u)) * x = p • (x * (u*v - s • (v*u)))
    have ha : (u*v)*x = p • (x*(u*v)) := by
      rw [mul_assoc, hvx, Algebra.mul_smul_comm, ← mul_assoc, hux,
        Algebra.smul_mul_assoc, smul_smul, hsp2, mul_assoc]
    have hb : (v*u)*x = p • (x*(v*u)) := by
      rw [mul_assoc, hux, Algebra.mul_smul_comm, ← mul_assoc, hvx,
        Algebra.smul_mul_assoc, smul_smul, hp2s, mul_assoc]
    rw [sub_mul, Algebra.smul_mul_assoc, ha, hb, mul_sub, Algebra.mul_smul_comm]
    rw [smul_sub, smul_comm s p]
  have hxv : p • ((x*v)*x) = x*(x*v) := by
    rw [mul_assoc, hvx, Algebra.mul_smul_comm, smul_smul, hps, one_smul]
  have huv' : u*(x*v) - p • ((x*v)*u) = p^2 • (x*w) := by
    change u*(x*v) - p • ((x*v)*u) = p^2 • (x*(u*v-s • (v*u)))
    simp only [← mul_assoc, hux, Algebra.smul_mul_assoc, mul_sub, Algebra.mul_smul_comm,
      smul_sub, smul_smul, hp2s]
  rw [serre_eq_rootVector] at hxy huv ⊢
  change x*z - p • (z*x) = 0 at hxy
  change u*w - p • (w*u) = 0 at huv
  rw [hsplit]
  calc
    _ = (x*z - p • (z*x)) + (u*w - p • (w*u)) +
        (u*z - p • (z*u)) + (x*w - p • (w*x)) +
        (1-s^2) • (x*(x*v) - p • ((x*v)*x)) +
        (1-s^2) • (u*(x*v) - p • ((x*v)*u)) := by
      change (x+u)*(z+w+(1-s^2) • (x*v)) -
        p • ((z+w+(1-s^2) • (x*v))*(x+u)) = _
      simp only [add_mul, mul_add, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
      module
    _ = 0 := by
      simp only [hxy, huv, huz, hwx, hxv, huv', sub_self, smul_zero, zero_add, add_zero]
      match_scalars
      linear_combination -(p*s + 1) * hps

end SerreCalculation


section Descent

open scoped TensorProduct
open Algebra.TensorProduct (map map_tmul map_comp tmul_mul_tmul includeLeft includeRight)
open Specs.LieNotes.Quantum.Coproduct (Data K)
open Specs.LieNotes.Quantum.PresentationSymmetries (InvertsCartan)
open LieNotes.Quantum.PresentationSymmetries (omega omega_cartan omega_E omega_F)

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

private abbrev square (A : Type*) [CommRing A] (B : Type*) [Ring B] [Algebra A B] :=
  B ⊗[A] B

/-- Cartan maps and the identities needed to extend them through the presentation. -/
private structure CartanMaps (C : Cartan A T) where
  delta : T →ₐ[A] square A T
  aug : T →ₐ[A] A
  shift_left (i : Root) :
    (map (C.tau i).symm.toAlgHom (AlgHom.id A T)).comp delta =
      delta.comp (C.tau i).symm.toAlgHom
  shift_right (i : Root) :
    (map (AlgHom.id A T) (C.tau i).symm.toAlgHom).comp delta =
      delta.comp (C.tau i).symm.toAlgHom
  delta_K (i : Root) : delta (C.K i : T) = (C.K i : T) ⊗ₜ[A] (C.K i : T)
  aug_K (i : Root) : aug (C.K i : T) = 1
  delta_D (i : Root) :
    delta (C.D i) = C.D i ⊗ₜ[A] (↑((C.K i)⁻¹) : T) + (C.K i : T) ⊗ₜ[A] C.D i
  aug_D (i : Root) : aug (C.D i) = 0
  coassoc : (Algebra.TensorProduct.assoc A A A T T T).toAlgHom.comp
      ((map delta (AlgHom.id A T)).comp delta) =
    (map (AlgHom.id A T) delta).comp delta
  left_counit : (map aug (AlgHom.id A T)).comp delta =
    (Algebra.TensorProduct.lid A T).symm
  right_counit : (map (AlgHom.id A T) aug).comp delta =
    (Algebra.TensorProduct.rid A A T).symm

private theorem map_inv_of_tmul {P B S : Type*} [Ring P] [Ring B] [Ring S]
    [Algebra A P] [Algebra A B] [Algebra A S]
    (f : P →ₐ[A] (B ⊗[A] S)) (a : Pˣ) (b : Bˣ) (c : Sˣ)
    (h : f (a : P) = (b : B) ⊗ₜ[A] (c : S)) :
    f (↑a⁻¹ : P) = (↑b⁻¹ : B) ⊗ₜ[A] (↑c⁻¹ : S) := by
  have hbc : (Units.map f.toMonoidHom a : B ⊗[A] S) =
      (b : B) ⊗ₜ[A] (c : S) := h
  symm
  change (↑b⁻¹ : B) ⊗ₜ[A] (↑c⁻¹ : S) = ↑((Units.map f.toMonoidHom a)⁻¹)
  apply (Units.map f.toMonoidHom a).eq_inv_of_mul_eq_one_left
  rw [hbc, tmul_mul_tmul, Units.mul_inv, Units.mul_inv]
  rfl

variable (C : Cartan A T)

private abbrev kValue (i : Root) : U C := cartan C (C.K i : T)
private abbrev kInverse (i : Root) : U C := cartan C (↑((C.K i)⁻¹) : T)

private def positiveImage (i : Root) : square A (U C) :=
  E C i ⊗ₜ[A] 1 + kValue C i ⊗ₜ[A] E C i

private def negativeImage (i : Root) : square A (U C) :=
  F C i ⊗ₜ[A] kInverse C i + 1 ⊗ₜ[A] F C i

private def cartanImage (d : CartanMaps C) : T →ₐ[A] square A (U C) :=
  (map (cartan C) (cartan C)).comp d.delta

private theorem cartanImage_D (d : CartanMaps C) (i : Root) :
    cartanImage C d (C.D i) = cartan C (C.D i) ⊗ₜ[A] kInverse C i +
      kValue C i ⊗ₜ[A] cartan C (C.D i) := by
  simp only [cartanImage, AlgHom.comp_apply, d.delta_D, map_add, map_tmul]

private theorem tensor_semiconj {R B S : Type*} [CommRing R] [Ring B] [Ring S]
    [Algebra R B] [Algebra R S] {T₁ T₂ : Type*} [Ring T₁] [Ring T₂]
    [Algebra R T₁] [Algebra R T₂]
    {f f' : T₁ →ₐ[R] B} {g g' : T₂ →ₐ[R] S} {a : B} {b : S}
    (hf : ∀ t, SemiconjBy a (f t) (f' t)) (hg : ∀ t, SemiconjBy b (g t) (g' t))
    (z : T₁ ⊗[R] T₂) :
    SemiconjBy (a ⊗ₜ[R] b) (map f g z) (map f' g' z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact (hf x).tmul (hg y)
  | add x y hx hy => simpa only [map_add] using hx.add_right hy

private theorem cartan_commute (x y : T) : Commute (cartan C x) (cartan C y) :=
  (Commute.all x y).map (cartan C)

private theorem cartan_shift_left (d : CartanMaps C) (i : Root) (t : T) :
    map ((cartan C).comp (C.tau i).symm.toAlgHom) (cartan C) (d.delta t) =
      cartanImage C d ((C.tau i).symm t) := by
  let g := cartan C
  let σ := (C.tau i).symm.toAlgHom
  calc
    _ = (map g g).comp (map σ (AlgHom.id A T)) (d.delta t) :=
      DFunLike.congr_fun (map_comp g σ g (AlgHom.id A T)) (d.delta t)
    _ = _ := congrArg (map g g) (DFunLike.congr_fun (d.shift_left i) t)

private theorem cartan_shift_right (d : CartanMaps C) (i : Root) (t : T) :
    map (cartan C) ((cartan C).comp (C.tau i).symm.toAlgHom) (d.delta t) =
      cartanImage C d ((C.tau i).symm t) := by
  let g := cartan C
  let σ := (C.tau i).symm.toAlgHom
  calc
    _ = (map g g).comp (map (AlgHom.id A T) σ) (d.delta t) :=
      DFunLike.congr_fun (map_comp g (AlgHom.id A T) g σ) (d.delta t)
    _ = _ := congrArg (map g g) (DFunLike.congr_fun (d.shift_right i) t)

private theorem image_eCartan (d : CartanMaps C) (i : Root) (t : T) :
    positiveImage C i * cartanImage C d t =
      cartanImage C d ((C.tau i).symm t) * positiveImage C i := by
  let g := cartan C
  let σ := (C.tau i).symm.toAlgHom
  have hE (a : T) : SemiconjBy (E C i) (g a) (g (σ a)) := (relations C).eCartan i a
  have hx := tensor_semiconj (f := g) (f' := g.comp σ) (g := g) (g' := g) hE
    (fun a => Commute.one_left (g a)) (d.delta t)
  have hu := tensor_semiconj (f := g) (f' := g) (g := g) (g' := g.comp σ)
    (fun a => cartan_commute C (C.K i : T) a) hE (d.delta t)
  change SemiconjBy _ _ (map ((cartan C).comp (C.tau i).symm.toAlgHom) (cartan C) (d.delta t)) at hx
  change SemiconjBy _ _ (map (cartan C) ((cartan C).comp (C.tau i).symm.toAlgHom) (d.delta t)) at hu
  rw [cartan_shift_left C d i t] at hx
  rw [cartan_shift_right C d i t] at hu
  exact hx.add_left hu

private theorem image_cartanF (d : CartanMaps C) (i : Root) (t : T) :
    cartanImage C d t * negativeImage C i =
      negativeImage C i * cartanImage C d ((C.tau i).symm t) := by
  let g := cartan C
  let σ := (C.tau i).symm.toAlgHom
  have hF (a : T) : SemiconjBy (F C i) (g (σ a)) (g a) :=
    ((relations C).cartanF a i).symm
  have hx := tensor_semiconj (f := g.comp σ) (f' := g) (g := g) (g' := g) hF
    (fun a => cartan_commute C (↑((C.K i)⁻¹) : T) a) (d.delta t)
  have hu := tensor_semiconj (f := g) (f' := g) (g := g.comp σ) (g' := g)
    (fun a => Commute.one_left (g a)) hF (d.delta t)
  change SemiconjBy _ (map ((cartan C).comp (C.tau i).symm.toAlgHom) (cartan C) (d.delta t)) _ at hx
  change SemiconjBy _ (map (cartan C) ((cartan C).comp (C.tau i).symm.toAlgHom) (d.delta t)) _ at hu
  rw [cartan_shift_left C d i t] at hx
  rw [cartan_shift_right C d i t] at hu
  exact (hx.add_left hu).eq.symm

private abbrev HasCartanWeights : Prop :=
  ∀ i l : Root, C.tau i (C.K l : T) =
    (↑(C.q ^ cartanMatrix l i) : A) • (C.K l : T)

private theorem weight_E (hs : HasCartanWeights C) (i l : Root) :
    kValue C l * E C i =
      (↑(C.q ^ cartanMatrix l i) : A) • (E C i * kValue C l) := by
  have h := (relations C).eCartan i (C.tau i (C.K l : T))
  rw [AlgEquiv.symm_apply_apply, hs i l, map_smul, Algebra.mul_smul_comm] at h
  exact h.symm

private theorem weight_F (hs : HasCartanWeights C) (j l : Root) :
    F C j * kValue C l =
      (↑(C.q ^ cartanMatrix l j) : A) • (kValue C l * F C j) := by
  have h := (relations C).cartanF (C.tau j (C.K l : T)) j
  rw [AlgEquiv.symm_apply_apply, hs j l, map_smul, Algebra.smul_mul_assoc] at h
  exact h.symm

private theorem weight_E_inv (hs : HasCartanWeights C) (i l : Root) :
    E C i * kInverse C l =
      (↑(C.q ^ cartanMatrix l i) : A) • (kInverse C l * E C i) := by
  have h₁ : kInverse C l * kValue C l = 1 := (K C l).inv_mul
  have h₂ : kValue C l * kInverse C l = 1 := (K C l).mul_inv
  calc
    _ = kInverse C l * (kValue C l * E C i) * kInverse C l := by
      rw [← mul_assoc (kInverse C l), h₁, one_mul]
    _ = _ := by
      rw [weight_E C hs i l, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      simp only [mul_assoc, h₂, mul_one]

private theorem image_comm (d : CartanMaps C) (hs : HasCartanWeights C) (i j : Root) :
    positiveImage C i * negativeImage C j - negativeImage C j * positiveImage C i =
      cartanImage C d (mixed C i j) := by
  -- Move a common Cartan weight from one tensor factor to the other.
  have hcross : (kValue C i * F C j) ⊗ₜ[A] (E C i * kInverse C j) =
      (F C j * kValue C i) ⊗ₜ[A] (kInverse C j * E C i) := by
    rw [weight_F C hs j i, weight_E_inv C hs i j, TensorProduct.smul_tmul]
    rw [show cartanMatrix j i = cartanMatrix i j by
      simp [cartanMatrix, Specs.LieNotes.Quantum.Presentation.cartanMatrix, eq_comm]]
  have hcomm := (relations C).comm i j
  calc
    _ = (E C i * F C j - F C j * E C i) ⊗ₜ[A] kInverse C j +
        kValue C i ⊗ₜ[A] (E C i * F C j - F C j * E C i) := by
      simp only [positiveImage, negativeImage, add_mul, mul_add, tmul_mul_tmul,
        mul_one, one_mul, TensorProduct.sub_tmul, TensorProduct.tmul_sub, hcross]
      abel
    _ = _ := by
      rw [hcomm]
      by_cases h : i = j
      · subst j
        simpa [Specs.LieNotes.Quantum.Presentation.mixed] using
          (cartanImage_D C d i).symm
      · simp [Specs.LieNotes.Quantum.Presentation.mixed, h]

private theorem image_basic (d : CartanMaps C) (hs : HasCartanWeights C) :
    SatisfiesBasic C (cartanImage C d) (positiveImage C) (negativeImage C) :=
  ⟨fun t i => image_cartanF C d i t, image_eCartan C d, image_comm C d hs⟩

private theorem image_serre_pos (hs : HasCartanWeights C) (i j : Root) (hij : i ≠ j) :
    serrePolynomial C.q (positiveImage C i) (positiveImage C j) = 0 := by
  have hij' : j ≠ i := Ne.symm hij
  have hK := (cartan_commute C (C.K i : T) (C.K j : T)).eq
  apply serre_add_pair
  · simp only [tmul_mul_tmul, one_mul, mul_one, weight_E C hs i i, TensorProduct.smul_tmul']
    simp [cartanMatrix, Specs.LieNotes.Quantum.Presentation.cartanMatrix, zpow_ofNat]
  · simp only [tmul_mul_tmul, one_mul, mul_one, weight_E C hs j i, TensorProduct.smul_tmul']
    simp [cartanMatrix, Specs.LieNotes.Quantum.Presentation.cartanMatrix, hij]
  · simp only [tmul_mul_tmul, one_mul, mul_one, weight_E C hs i j, TensorProduct.smul_tmul']
    simp [cartanMatrix, Specs.LieNotes.Quantum.Presentation.cartanMatrix, hij']
  · exact (SerrePresentation.map_serrePolynomial includeLeft C.q (E C i) (E C j)).symm.trans
      ((congrArg includeLeft ((serre_relations C).pos i j hij)).trans (map_zero _))
  · calc
      _ = (kValue C i ^ 2 * kValue C j) ⊗ₜ[A] serrePolynomial C.q (E C i) (E C j) := by
        simp only [serrePolynomial, pow_two, tmul_mul_tmul, TensorProduct.tmul_add,
          TensorProduct.tmul_sub, TensorProduct.tmul_smul]
        rw [show kValue C i * kValue C j * kValue C i = kValue C i * kValue C i * kValue C j by
          rw [mul_assoc, ← hK, ← mul_assoc]]
        rw [show kValue C j * (kValue C i * kValue C i) = kValue C i * kValue C i * kValue C j by
          rw [← mul_assoc, ← hK, mul_assoc, ← hK, ← mul_assoc]]
      _ = 0 := by rw [(serre_relations C).pos i j hij, TensorProduct.tmul_zero]

private theorem image_serre (hs : HasCartanWeights C)
    (hω : InvertsCartan C) (hk : ∀ i, C.kappa (C.K i : T) = ↑((C.K i)⁻¹)) :
    SatisfiesSerre C.q (positiveImage C) (negativeImage C) := by
  refine ⟨image_serre_pos C hs, ?_⟩
  let φ := (Algebra.TensorProduct.comm A (U C) (U C)).toAlgHom.comp
    (map (omega hω) (omega hω))
  have hφ (i : Root) : φ (positiveImage C i) = negativeImage C i := by
    simp only [φ, positiveImage, negativeImage, kValue, AlgHom.comp_apply, map_add,
      map_tmul, omega_E, map_one, omega_cartan, hk, AlgEquiv.coe_toAlgHom,
      Algebra.TensorProduct.comm_tmul]
    exact add_comm _ _
  intro i j hij
  rw [← hφ i, ← hφ j]
  exact (SerrePresentation.map_serrePolynomial φ C.q _ _).symm.trans
    ((congrArg φ (image_serre_pos C hs i j hij)).trans (map_zero φ))

private def comulFromCartan (d : CartanMaps C) (hs : HasCartanWeights C)
    (hω : InvertsCartan C) (hk : ∀ i, C.kappa (C.K i : T) = ↑((C.K i)⁻¹)) :
    U C →ₐ[A] square A (U C) :=
  liftU C (cartanImage C d) (positiveImage C) (negativeImage C)
    (image_basic C d hs) (image_serre C hs hω hk)

set_option maxHeartbeats 1000000 in
private def dataFromCartan (d : CartanMaps C) (hs : HasCartanWeights C)
    (hω : InvertsCartan C) (hk : ∀ i, C.kappa (C.K i : T) = ↑((C.K i)⁻¹)) :
    Data C := by
  let Δ := comulFromCartan C d hs hω hk
  let ε := counitFromCartan C d.aug d.aug_D
  let a := cartan C
  let a₂ := map a a
  let a₃ := map a a₂
  have hΔ (x : T) : Δ (a x) = a₂ (d.delta x) :=
    liftU_cartan C _ _ _ (image_basic C d hs) (image_serre C hs hω hk) x
  have hε (x : T) : ε (a x) = d.aug x := counitFromCartan_cartan C _ _ x
  have hεE (i : Root) : ε (E C i) = 0 := counitFromCartan_E C _ _ i
  have hεF (i : Root) : ε (F C i) = 0 := counitFromCartan_F C _ _ i
  have hE (i : Root) : Δ (E C i) = positiveImage C i := liftU_E C _ _ _ (image_basic C d hs) (image_serre C hs hω hk) i
  have hF (i : Root) : Δ (F C i) = negativeImage C i := liftU_F C _ _ _ (image_basic C d hs) (image_serre C hs hω hk) i
  have hK (i : Root) : Δ (kValue C i) = kValue C i ⊗ₜ[A] kValue C i :=
    (hΔ _).trans (by rw [d.delta_K, map_tmul])
  have hKi (i : Root) : Δ (kInverse C i) = kInverse C i ⊗ₜ[A] kInverse C i :=
    map_inv_of_tmul Δ (K C i) (K C i) (K C i) (hK i)
  have hεK (i : Root) : ε (kValue C i) = 1 := (hε _).trans (d.aug_K i)
  have hεKi (i : Root) : ε (kInverse C i) = 1 := by
    have h := congrArg ε ((K C i).mul_inv)
    change ε (kValue C i * kInverse C i) = ε 1 at h
    simpa only [map_mul, map_one, hεK, one_mul] using h
  refine
    { comul := Δ
      counit := ε
      comul_E := hE
      comul_F := hF
      counit_E := hεE
      counit_F := hεF
      comul_K := hK
      counit_K := hεK
      coassoc := ?_
      left_counit := ?_
      right_counit := ?_ }
  · let lU := (Algebra.TensorProduct.assoc A A A (U C) (U C) (U C)).toAlgHom.comp
        (map Δ (AlgHom.id A (U C)))
    let lT := (Algebra.TensorProduct.assoc A A A T T T).toAlgHom.comp
        (map d.delta (AlgHom.id A T))
    let rU := map (AlgHom.id A (U C)) Δ
    let rT := map (AlgHom.id A T) d.delta
    have hl : lU.comp a₂ = a₃.comp lT := by
      apply Algebra.TensorProduct.ext'
      intro x y
      simp only [lU, lT, a₂, a₃, AlgHom.comp_apply, map_tmul, hΔ, AlgHom.id_apply]
      induction d.delta x using TensorProduct.inductionOn with
      | tmul b c => rfl
      | add p q hp hq => simp only [map_add, TensorProduct.add_tmul, hp, hq]
    have hr : rU.comp a₂ = a₃.comp rT := by
      apply Algebra.TensorProduct.ext'
      intro x y
      simp only [rU, rT, a₂, a₃, AlgHom.comp_apply, map_tmul, hΔ, AlgHom.id_apply]
    rw [← AlgHom.comp_assoc]
    apply hom_ext C
    · intro x
      change lU (Δ (a x)) = rU (Δ (a x))
      rw [hΔ]
      exact (DFunLike.congr_fun hl _).trans
        ((congrArg a₃ (DFunLike.congr_fun d.coassoc x)).trans (DFunLike.congr_fun hr _).symm)
    · intro i
      simp only [AlgHom.comp_apply, hE, positiveImage, map_add, map_tmul,
        AlgHom.id_apply, map_one, hK, TensorProduct.add_tmul,
        TensorProduct.tmul_add, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.assoc_tmul,
        Algebra.TensorProduct.one_def, add_assoc]
    · intro i
      simp only [AlgHom.comp_apply, hF, negativeImage, map_add, map_tmul,
        AlgHom.id_apply, map_one, hKi, TensorProduct.add_tmul,
        TensorProduct.tmul_add, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.assoc_tmul,
        Algebra.TensorProduct.one_def, add_assoc]
  · let lU := map ε (AlgHom.id A (U C))
    let lT := map d.aug (AlgHom.id A T)
    let b := map (AlgHom.id A A) a
    have hl : lU.comp a₂ = b.comp lT := by
      apply Algebra.TensorProduct.ext'
      intro x y
      simp only [lU, lT, a₂, b, AlgHom.comp_apply, map_tmul, hε, AlgHom.id_apply]
    change lU.comp Δ = _
    apply hom_ext C
    · intro x
      change lU (Δ (a x)) = 1 ⊗ₜ[A] a x
      rw [hΔ]
      exact (DFunLike.congr_fun hl _).trans (congrArg b (DFunLike.congr_fun d.left_counit x))
    · intro i
      simp only [lU, AlgHom.comp_apply, hE, positiveImage, map_add, map_tmul, hεK,
        AlgHom.id_apply, map_one, hεE, TensorProduct.zero_tmul,
        zero_add, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.lid_symm_apply]
    · intro i
      simp only [lU, AlgHom.comp_apply, hF, negativeImage, map_add, map_tmul,
        AlgHom.id_apply, map_one, hεF, TensorProduct.zero_tmul,
        zero_add, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.lid_symm_apply]
  · let rU := map (AlgHom.id A (U C)) ε
    let rT := map (AlgHom.id A T) d.aug
    let b := map a (AlgHom.id A A)
    have hr : rU.comp a₂ = b.comp rT := by
      apply Algebra.TensorProduct.ext'
      intro x y
      simp only [rU, rT, a₂, b, AlgHom.comp_apply, map_tmul, hε, AlgHom.id_apply]
    change rU.comp Δ = _
    apply hom_ext C
    · intro x
      change rU (Δ (a x)) = a x ⊗ₜ[A] 1
      rw [hΔ]
      exact (DFunLike.congr_fun hr _).trans (congrArg b (DFunLike.congr_fun d.right_counit x))
    · intro i
      simp only [rU, AlgHom.comp_apply, hE, positiveImage, map_add, map_tmul,
        AlgHom.id_apply, map_one, hεE, TensorProduct.tmul_zero,
        add_zero, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.rid_symm_apply]
    · intro i
      simp only [rU, AlgHom.comp_apply, hF, negativeImage, map_add, map_tmul, hεKi,
        AlgHom.id_apply, map_one, hεF, TensorProduct.tmul_zero,
        add_zero, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.rid_symm_apply]

private theorem dataFromCartan_comul_cartan (d : CartanMaps C) (hs : HasCartanWeights C)
    (hω : InvertsCartan C) (hk : ∀ i, C.kappa (C.K i : T) = ↑((C.K i)⁻¹)) (x : T) :
    (dataFromCartan C d hs hω hk).comul (cartan C x) = cartanImage C d x :=
  liftU_cartan C _ _ _ (image_basic C d hs) (image_serre C hs hω hk) x

private theorem dataFromCartan_counit_cartan (d : CartanMaps C) (hs : HasCartanWeights C)
    (hω : InvertsCartan C) (hk : ∀ i, C.kappa (C.K i : T) = ↑((C.K i)⁻¹)) (x : T) :
    (dataFromCartan C d hs hω hk).counit (cartan C x) = d.aug x :=
  counitFromCartan_cartan C d.aug d.aug_D x

end Descent


section Generic

open scoped TensorProduct
open Algebra.TensorProduct (map map_tmul tmul_mul_tmul)
open Specs.LieNotes.Quantum.Presentation
  (Lattice coordinate laurentUnit laurentScale laurentScale_single laurent_ext genericD)
open Specs.LieNotes.Quantum.Coproduct (Data GenericProp IndeterminateProp)
open LieNotes.Quantum.PresentationSymmetries (generic_invertsCartan)

variable {k : Type u} [Field k] [CharZero k]

private abbrev laurentMonomial (m : Lattice) : Laurent k :=
  AddMonoidAlgebra.single m 1

private def laurentDelta : Laurent k →ₐ[k] square k (Laurent k) :=
  AddMonoidAlgebra.lift k _ Lattice
    { toFun := fun m => laurentMonomial m.toAdd ⊗ₜ[k] laurentMonomial m.toAdd
      map_one' := by
        change laurentMonomial (0 : Lattice) ⊗ₜ[k] laurentMonomial 0 = 1
        rfl
      map_mul' := fun m n => by
        change laurentMonomial (m.toAdd + n.toAdd) ⊗ₜ[k] laurentMonomial (m.toAdd + n.toAdd) =
          (laurentMonomial m.toAdd ⊗ₜ[k] laurentMonomial m.toAdd) *
            (laurentMonomial n.toAdd ⊗ₜ[k] laurentMonomial n.toAdd)
        rw [tmul_mul_tmul]
        simp only [laurentMonomial, AddMonoidAlgebra.single_mul_single, mul_one] }

private def laurentAug : Laurent k →ₐ[k] k :=
  AddMonoidAlgebra.lift k k Lattice 1

omit [CharZero k] in
@[simp] private theorem laurentDelta_monomial (m : Lattice) :
    laurentDelta (laurentMonomial m : Laurent k) =
      laurentMonomial m ⊗ₜ[k] laurentMonomial m := by
  simp [laurentDelta, laurentMonomial]

omit [CharZero k] in
@[simp] private theorem laurentAug_monomial (m : Lattice) :
    laurentAug (laurentMonomial m : Laurent k) = 1 := by
  simp [laurentAug, laurentMonomial]

private def genericCartanMaps (q : kˣ) (hq : (q : k)^2 ≠ 1) :
    CartanMaps (generic q hq) where
  delta := laurentDelta
  aug := laurentAug
  shift_left i := by
    change (map (laurentScale q⁻¹ i) (AlgHom.id k (Laurent k))).comp laurentDelta =
      laurentDelta.comp (laurentScale q⁻¹ i)
    apply laurent_ext
    intro m
    simp only [AlgHom.comp_apply, laurentDelta_monomial, map_tmul, laurentScale_single,
      AlgHom.id_apply, map_smul, TensorProduct.smul_tmul']
  shift_right i := by
    change (map (AlgHom.id k (Laurent k)) (laurentScale q⁻¹ i)).comp laurentDelta =
      laurentDelta.comp (laurentScale q⁻¹ i)
    apply laurent_ext
    intro m
    simp only [AlgHom.comp_apply, laurentDelta_monomial, map_tmul, laurentScale_single,
      AlgHom.id_apply, map_smul, TensorProduct.tmul_smul]
  delta_K i := laurentDelta_monomial (coordinate i)
  aug_K i := laurentAug_monomial (coordinate i)
  delta_D i := by
    let a : Laurent k := laurentMonomial (coordinate i)
    let b : Laurent k := laurentMonomial (-coordinate i)
    let r : k := ((q : k) - ↑q⁻¹)⁻¹
    change laurentDelta (r • (a - b)) =
      (r • (a - b)) ⊗ₜ[k] b + a ⊗ₜ[k] (r • (a - b))
    simp only [a, b, map_smul, map_sub, laurentDelta_monomial,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.sub_tmul,
      TensorProduct.tmul_sub, smul_sub]
    abel
  aug_D i := by
    let r : k := ((q : k) - ↑q⁻¹)⁻¹
    change laurentAug (r • ((laurentMonomial (coordinate i) : Laurent k) -
      laurentMonomial (-coordinate i))) = 0
    simp only [map_smul, map_sub, laurentAug_monomial, sub_self, smul_zero]
  coassoc := by
    apply laurent_ext
    intro m
    simp only [AlgHom.comp_apply, laurentDelta_monomial, map_tmul,
      AlgHom.id_apply, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.assoc_tmul]
  left_counit := by
    apply laurent_ext
    intro m
    simp only [AlgHom.comp_apply, laurentDelta_monomial, map_tmul,
      AlgHom.id_apply, laurentAug_monomial, AlgEquiv.coe_toAlgHom,
      Algebra.TensorProduct.lid_symm_apply]
  right_counit := by
    apply laurent_ext
    intro m
    simp only [AlgHom.comp_apply, laurentDelta_monomial, map_tmul,
      AlgHom.id_apply, laurentAug_monomial, AlgEquiv.coe_toAlgHom,
      Algebra.TensorProduct.rid_symm_apply]

/-- The bialgebra maps for a parameter in a characteristic-zero field. -/
def genericData (q : kˣ) (hq : (q : k)^2 ≠ 1) : Data (generic q hq) :=
  dataFromCartan _ (genericCartanMaps q hq) (generic_scale q hq)
    (generic_invertsCartan q hq) (generic_kappa_K q hq)

theorem generic_coproduct : GenericProp := fun q hq => ⟨genericData q hq⟩

theorem indeterminate_coproduct : IndeterminateProp :=
  fun k => ⟨genericData (rationalQ k) (Specs.LieNotes.Quantum.Presentation.rationalQ_sq_ne k)⟩

end Generic

section FormalSeries

open Specs.LieNotes.Quantum.Presentation (exponentialUnit sinhDenominator)
open LieNotes.Quantum.Truncations (expH)

variable {S : Type*} [CommRing S] [Algebra ℚ S]

private theorem sinhRatio_zero : sinhRatio (0 : S) = 0 := by
  have h : dividedSinh (0 : S) = 0 := by
    ext n
    simp [Specs.LieNotes.Quantum.Presentation.dividedSinh]
  simp [Specs.LieNotes.Quantum.Presentation.sinhRatio, h]

private theorem exponentialUnit_inv (a : S) :
    (↑((exponentialUnit a)⁻¹) : PowerSeries S) = expH (-a) := by
  symm
  apply (exponentialUnit a).eq_inv_of_mul_eq_one_left
  rw [exponentialUnit_val, Truncations.expH_mul_neg]

/-- The Cartan identity holds before truncation. The common factor is a
power-series variable times a unit, so it can be cancelled here. -/
private theorem sinhRatio_add (a b : S) :
    sinhRatio (a + b) = sinhRatio a * expH (-b) + expH a * sinhRatio b := by
  let s := expH (1 : S) - expH (-1 : S)
  have h : s * sinhRatio (a + b) =
      s * (sinhRatio a * expH (-b) + expH a * sinhRatio b) := by
    have ha (x : S) : s * sinhRatio x = expH x - expH (-x) :=
      exponential_difference_mul_sinhRatio x
    rw [mul_add, ← mul_assoc s, mul_left_comm s, ha, ha, ha, neg_add,
      Truncations.expH_add, Truncations.expH_add]
    ring
  have htwo : IsUnit (2 : PowerSeries S) := by
    have h2 : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
    simpa only [map_ofNat] using h2.map (algebraMap ℚ (PowerSeries S))
  have hu : IsUnit ((2 : PowerSeries S) * dividedSinh (1 : S)) :=
    htwo.mul (sinhDenominator_val (S := S) ▸ (sinhDenominator S).isUnit)
  have hs : s = PowerSeries.X * ((2 : PowerSeries S) * dividedSinh (1 : S)) := by
    change expH (1 : S) - expH (-1 : S) = _
    rw [← two_X_mul_dividedSinh, mul_comm (2 : PowerSeries S) PowerSeries.X, mul_assoc]
  rw [hs] at h
  exact hu.mul_left_cancel (PowerSeries.X_mul_injective (by simpa only [← mul_assoc] using h))

end FormalSeries

section Truncated

open scoped TensorProduct
open Algebra.TensorProduct (map map_tmul tmul_mul_tmul includeLeft includeRight)
open Specs.LieNotes.Quantum.Presentation (exponentialUnit)
open Specs.LieNotes.Quantum.Coproduct (TruncatedData TruncatedProp H)
open LieNotes.Quantum.Truncations (A expH cartanTruncate)
open LieNotes.Quantum.PresentationSymmetries (truncated_invertsCartan truncated_kappa_K)

private def polynomialDelta (R : Type*) [CommRing R] :
    PolynomialCartan R →ₐ[R] square R (PolynomialCartan R) :=
  MvPolynomial.aeval fun i =>
    MvPolynomial.X i ⊗ₜ[R] 1 + 1 ⊗ₜ[R] MvPolynomial.X i

private def polynomialAug (R : Type*) [CommRing R] : PolynomialCartan R →ₐ[R] R :=
  MvPolynomial.aeval fun _ => 0

@[simp] private theorem polynomialDelta_X (R : Type*) [CommRing R] (i : Root) :
    polynomialDelta R (MvPolynomial.X i) =
      MvPolynomial.X i ⊗ₜ[R] 1 + 1 ⊗ₜ[R] MvPolynomial.X i :=
  MvPolynomial.aeval_X _ _

@[simp] private theorem polynomialAug_X (R : Type*) [CommRing R] (i : Root) :
    polynomialAug R (MvPolynomial.X i) = 0 :=
  MvPolynomial.aeval_X _ _

variable (k : Type u) [Field k] [CharZero k] (N : ℕ)

private def evalSeries {S B : Type*} [CommRing S] [CommRing B] [Algebra (A k N) B]
    (r : S →+* B) : PowerSeries S →+* B :=
  Truncations.evalTrunc N r (algebraMap (A k N) B (Truncations.h k N))
    (by rw [← map_pow, Truncations.h_pow, map_zero])

omit [CharZero k] in
private theorem map_cartanTruncation {S B : Type*} [CommRing S] [CommRing B] [Algebra (A k N) B]
    (r : S →+* B) (f : TruncatedCartan k N →ₐ[A k N] B)
    (g : PolynomialCartan k →+* S)
    (hg : f.toRingHom.comp (MvPolynomial.map (algebraMap k (A k N))) = r.comp g)
    (p : PowerSeries (PolynomialCartan k)) :
    f (cartanTruncate Root N p) = evalSeries k N r (p.map g) := by
  simp only [evalSeries, Truncations.evalTrunc_eq_sum, Truncations.cartanTruncate_eq_sum,
    map_sum, map_mul, map_pow, PowerSeries.coeff_map]
  apply Finset.sum_congr rfl
  intro n _
  rw [show f (MvPolynomial.C (Truncations.h k N)) =
    algebraMap (A k N) B (Truncations.h k N) from f.commutes _]
  exact congrArg (· * algebraMap (A k N) B (Truncations.h k N) ^ n)
    (DFunLike.congr_fun hg (PowerSeries.coeff n p))

private theorem truncatedK_exp (i : Root) :
    ((truncated k N).K i : TruncatedCartan k N) =
      cartanTruncate Root N (expH (MvPolynomial.X i : PolynomialCartan k)) :=
  congrArg (cartanTruncate Root N) (exponentialUnit_val (MvPolynomial.X i : PolynomialCartan k))

private theorem truncatedKinv_exp (i : Root) :
    (↑((truncated k N).K i)⁻¹ : TruncatedCartan k N) =
      cartanTruncate Root N (expH (-MvPolynomial.X i : PolynomialCartan k)) := by
  change (↑((Units.map (cartanTruncate (R := k) Root N).toMonoidHom
    (exponentialUnit (MvPolynomial.X i : PolynomialCartan k)))⁻¹) : TruncatedCartan k N) = _
  rw [← map_inv]
  exact congrArg (cartanTruncate Root N) (exponentialUnit_inv (MvPolynomial.X i : PolynomialCartan k))

set_option maxHeartbeats 900000 in
private theorem polynomialDelta_series (i : Root) :
    let C := truncated k N
    let δ := polynomialDelta (A k N)
    δ (C.K i : TruncatedCartan k N) = (C.K i : TruncatedCartan k N) ⊗ₜ[A k N] (C.K i : TruncatedCartan k N) ∧
      δ (C.D i) = C.D i ⊗ₜ[A k N] (↑((C.K i)⁻¹) : TruncatedCartan k N) +
        (C.K i : TruncatedCartan k N) ⊗ₜ[A k N] C.D i := by
  let R := A k N
  let T := TruncatedCartan k N
  let B := square R T
  -- Each of the left, right, and diagonal substitutions is evaluated
  -- in the same power-series ring on the two sets of Cartan variables.
  let S := MvPolynomial (Root ⊕ Root) k
  let xl (j : Root) : S := MvPolynomial.X (.inl j)
  let xr (j : Root) : S := MvPolynomial.X (.inr j)
  let l : T →ₐ[R] B := includeLeft
  let r : T →ₐ[R] B := includeRight
  let δ := polynomialDelta R
  let a := (algebraMap R B).comp (algebraMap k R)
  let w : Root ⊕ Root → B :=
    Sum.elim (fun j => l (MvPolynomial.X j)) (fun j => r (MvPolynomial.X j))
  let f : S →+* B := MvPolynomial.eval₂Hom a w
  let φ := evalSeries k N f
  have eval (s : Root → S) (g : T →ₐ[R] B)
      (hg : ∀ j, g (MvPolynomial.X j) = f (s j)) (p : PowerSeries (PolynomialCartan k)) :
      g (cartanTruncate Root N p) = φ (p.map (MvPolynomial.aeval s).toRingHom) := by
    apply map_cartanTruncation k N
    apply MvPolynomial.ringHom_ext
    · intro c
      change g (MvPolynomial.map (algebraMap k R) (MvPolynomial.C c)) =
        f (MvPolynomial.aeval s (MvPolynomial.C c))
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
      change g (algebraMap R T (algebraMap k R c)) = f (MvPolynomial.C c)
      exact (g.commutes _).trans (MvPolynomial.eval₂Hom_C a w c).symm
    · intro j
      change g (MvPolynomial.map (algebraMap k R) (MvPolynomial.X j)) =
        f (MvPolynomial.aeval s (MvPolynomial.X j))
      rw [MvPolynomial.map_X, MvPolynomial.aeval_X]
      exact hg j
  have hl (j : Root) : l (MvPolynomial.X j) = f (xl j) :=
    (MvPolynomial.eval₂Hom_X' a w (.inl j)).symm
  have hr (j : Root) : r (MvPolynomial.X j) = f (xr j) :=
    (MvPolynomial.eval₂Hom_X' a w (.inr j)).symm
  have hd (j : Root) : δ (MvPolynomial.X j) = f (xl j + xr j) := by
    rw [map_add, ← hl, ← hr]
    exact polynomialDelta_X R j
  let x : PolynomialCartan k := MvPolynomial.X i
  have evalExp (s : Root → S) (g : T →ₐ[R] B) (hg : ∀ j, g (MvPolynomial.X j) = f (s j)) :
      g (cartanTruncate Root N (expH x)) = φ (expH (s i)) :=
    (eval s g hg (expH x)).trans (congrArg φ
      ((Truncations.map_expH (MvPolynomial.aeval s).toRingHom x).trans
        (congrArg (fun a : S => expH a) (MvPolynomial.aeval_X s i))))
  have evalSinh (s : Root → S) (g : T →ₐ[R] B) (hg : ∀ j, g (MvPolynomial.X j) = f (s j)) :
      g (cartanTruncate Root N (sinhRatio x)) = φ (sinhRatio (s i)) :=
    (eval s g hg (sinhRatio x)).trans (congrArg φ
      ((map_sinhRatio (MvPolynomial.aeval s).toRingHom x).trans
        (congrArg (fun a : S => sinhRatio a) (MvPolynomial.aeval_X s i))))
  have eri : r (cartanTruncate Root N (expH (-x))) = φ (expH (-xr i)) :=
    (eval xr r hr (expH (-x))).trans (congrArg φ
      ((Truncations.map_expH (MvPolynomial.aeval xr).toRingHom (-x)).trans
        (congrArg (fun a : S => expH a)
          ((map_neg (MvPolynomial.aeval xr) x).trans
            (congrArg Neg.neg (MvPolynomial.aeval_X xr i))))))
  have el := evalExp xl l hl
  have er := evalExp xr r hr
  have ed := evalExp (fun j => xl j + xr j) δ hd
  have dl := evalSinh xl l hl
  have dr := evalSinh xr r hr
  have dd := evalSinh (fun j => xl j + xr j) δ hd
  have ht (a b : T) : l a * r b = a ⊗ₜ[R] b :=
    (tmul_mul_tmul (R := R) a 1 1 b).trans
      (congrArg₂ (TensorProduct.tmul R) (mul_one a) (one_mul b))
  constructor
  · rw [truncatedK_exp]
    change δ (cartanTruncate Root N (expH x)) = _ ⊗ₜ[R] _
    rw [ed, Truncations.expH_add, map_mul, ← el, ← er, ht]
  · rw [truncatedK_exp, truncatedKinv_exp]
    change δ (cartanTruncate Root N (sinhRatio x)) = _ ⊗ₜ[R] _ + _ ⊗ₜ[R] _
    rw [dd, sinhRatio_add, map_add, map_mul, map_mul, ← dl, ← dr, ← el, ← eri, ht, ht]
    rfl

private theorem polynomialAug_series (i : Root) :
    let C := truncated k N
    let ε := polynomialAug (A k N)
    ε (C.K i : TruncatedCartan k N) = 1 ∧ ε (C.D i) = 0 := by
  let R := A k N
  let ε := polynomialAug R
  let p := polynomialAug k
  have h : ε.toRingHom.comp (MvPolynomial.map (algebraMap k R)) =
      (algebraMap k R).comp p.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ε, p, polynomialAug]
    · intro j
      simp [ε, p]
  have eval := map_cartanTruncation k N (algebraMap k R) ε p.toRingHom h
  constructor
  · rw [truncatedK_exp, eval, Truncations.map_expH]
    change evalSeries k N (algebraMap k R) (expH (p (MvPolynomial.X i))) = 1
    rw [polynomialAug_X, Truncations.expH_zero, map_one]
  · change ε (cartanTruncate Root N (sinhRatio (MvPolynomial.X i : PolynomialCartan k))) = 0
    rw [eval, map_sinhRatio]
    change evalSeries k N (algebraMap k R) (sinhRatio (p (MvPolynomial.X i))) = 0
    rw [polynomialAug_X, sinhRatio_zero, map_zero]

private theorem truncated_tau_symm_X (i j : Root) :
    ((truncated k N).tau i).symm (MvPolynomial.X j) =
      MvPolynomial.X j - MvPolynomial.C (cartanMatrix j i : A k N) := by
  let τ := (truncated k N).tau i
  apply τ.injective
  rw [AlgEquiv.apply_symm_apply, map_sub, truncated_tau_H]
  rw [show τ (MvPolynomial.C (cartanMatrix j i : A k N)) =
    MvPolynomial.C (cartanMatrix j i : A k N) from τ.commutes _]
  exact (add_sub_cancel_right _ _).symm

private def truncatedCartanMaps : CartanMaps (truncated k N) where
  delta := polynomialDelta (A k N)
  aug := polynomialAug (A k N)
  shift_left i := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, polynomialDelta_X, map_add, map_tmul, AlgHom.id_apply,
      map_one, AlgEquiv.coe_toAlgHom, truncated_tau_symm_X, map_sub, TensorProduct.sub_tmul]
    rw [show polynomialDelta (A k N) (MvPolynomial.C (cartanMatrix j i : A k N)) =
        (MvPolynomial.C (cartanMatrix j i : A k N)) ⊗ₜ[A k N] 1 from
      (polynomialDelta (A k N)).commutes _]
    exact sub_add_eq_add_sub _ _ _
  shift_right i := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, polynomialDelta_X, map_add, map_tmul, AlgHom.id_apply,
      map_one, AlgEquiv.coe_toAlgHom, truncated_tau_symm_X, map_sub, TensorProduct.tmul_sub]
    rw [show polynomialDelta (A k N) (MvPolynomial.C (cartanMatrix j i : A k N)) =
        1 ⊗ₜ[A k N] (MvPolynomial.C (cartanMatrix j i : A k N)) from
      ((polynomialDelta (A k N)).commutes _).trans (Algebra.TensorProduct.algebraMap_apply' _)]
    abel
  delta_K i := (polynomialDelta_series k N i).1
  aug_K i := (polynomialAug_series k N i).1
  delta_D i := (polynomialDelta_series k N i).2
  aug_D i := (polynomialAug_series k N i).2
  coassoc := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, polynomialDelta_X, map_add, map_tmul,
      AlgHom.id_apply, map_one, TensorProduct.add_tmul, TensorProduct.tmul_add,
      AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.assoc_tmul, add_assoc, Algebra.TensorProduct.one_def]
  left_counit := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, polynomialDelta_X, polynomialAug_X, map_add, map_tmul,
      AlgHom.id_apply, map_one, TensorProduct.zero_tmul, zero_add,
      AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.lid_symm_apply]
  right_counit := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, polynomialDelta_X, polynomialAug_X, map_add, map_tmul,
      AlgHom.id_apply, map_one, TensorProduct.tmul_zero, add_zero,
      AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.rid_symm_apply]

/-- The bialgebra maps of the truncated formal presentation. -/
def truncatedData : TruncatedData k N where
  toData := dataFromCartan (truncated k N) (truncatedCartanMaps k N) (truncated_scale N)
    (truncated_invertsCartan k N) (truncated_kappa_K N)
  comul_H i := by
    change (dataFromCartan (truncated k N) (truncatedCartanMaps k N) (truncated_scale N)
      (truncated_invertsCartan k N) (truncated_kappa_K N)).comul
      (cartan (truncated k N) (MvPolynomial.X i)) = _
    refine (dataFromCartan_comul_cartan (truncated k N) (truncatedCartanMaps k N)
      (truncated_scale N) (truncated_invertsCartan k N) (truncated_kappa_K N) _).trans ?_
    simp only [cartanImage, truncatedCartanMaps, polynomialDelta_X, AlgHom.comp_apply,
      map_add, map_tmul, map_one, H]
  counit_H i := by
    change (dataFromCartan (truncated k N) (truncatedCartanMaps k N) (truncated_scale N)
      (truncated_invertsCartan k N) (truncated_kappa_K N)).counit
      (cartan (truncated k N) (MvPolynomial.X i)) = _
    exact (dataFromCartan_counit_cartan (truncated k N) (truncatedCartanMaps k N)
      (truncated_scale N) (truncated_invertsCartan k N) (truncated_kappa_K N) _).trans
      (polynomialAug_X _ _)

theorem truncated_coproduct : TruncatedProp := by
  intro k _ _ N _
  exact ⟨truncatedData k N⟩

end Truncated


section Reduction

open scoped TensorProduct
open Specs.LieNotes.Quantum.Coproduct (H K ReductionProp tensorReduce tensorReduce_tmul)
open LieNotes.Quantum.Truncations (A)

variable {k : Type u} [Field k] [CharZero k] {M N : ℕ}

private theorem truncated_ringHom_ext {B : Type*} [Ring B] {f g : Uₙ k N →+* B}
    (hs : ∀ a, f (algebraMap (A k N) (Uₙ k N) a) = g (algebraMap (A k N) (Uₙ k N) a))
    (hh : ∀ i, f (H k N i) = g (H k N i))
    (he : ∀ i, f (E (truncated k N) i) = g (E (truncated k N) i))
    (hf : ∀ i, f (F (truncated k N) i) = g (F (truncated k N) i)) : f = g := by
  apply ringHom_ext (truncated k N) hs _ he hf
  have ht : f.comp (cartan (truncated k N)).toRingHom =
      g.comp (cartan (truncated k N)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hmap := (cartan (truncated k N)).commutes a
      change f (cartan (truncated k N) (MvPolynomial.C a)) =
        g (cartan (truncated k N) (MvPolynomial.C a))
      rw [show cartan (truncated k N) (MvPolynomial.C a) =
        algebraMap (A k N) (Uₙ k N) a from hmap]
      exact hs a
    · exact hh
  exact DFunLike.congr_fun ht

private theorem tensorReduce_scalar (e : M ≤ N) (a : A k N) :
    tensorReduce e (algebraMap (A k N) (square (A k N) (Uₙ k N)) a) =
      algebraMap (A k M) (square (A k M) (Uₙ k M)) (Truncations.reduce e a) := by
  change tensorReduce e ((algebraMap (A k N) (Uₙ k N) a) ⊗ₜ[A k N] (1 : Uₙ k N)) =
    (algebraMap (A k M) (Uₙ k M) (Truncations.reduce e a)) ⊗ₜ[A k M] (1 : Uₙ k M)
  rw [tensorReduce_tmul, Presentation.reduce_scalar, map_one]

private theorem reduce_K_value (e : M ≤ N) (i : Root) :
    Presentation.reduce e (K (truncated k N) i : Uₙ k N) = (K (truncated k M) i : Uₙ k M) :=
  Presentation.reduce_K e i

private theorem reduce_K_inverse (e : M ≤ N) (i : Root) :
    Presentation.reduce e (↑((K (truncated k N) i)⁻¹) : Uₙ k N) =
      (↑((K (truncated k M) i)⁻¹) : Uₙ k M) := by
  apply (K (truncated k M) i).eq_inv_of_mul_eq_one_left
  rw [← reduce_K_value e i, ← map_mul, Units.mul_inv, map_one]

set_option maxHeartbeats 900000 in
theorem truncated_compatibility : ReductionProp := by
  intro k _ _ M N _ e dN dM
  constructor
  · apply truncated_ringHom_ext (k := k) (N := N)
    · intro a
      change tensorReduce e (dN.comul (algebraMap (A k N) (Uₙ k N) a)) =
        dM.comul (Presentation.reduce e (algebraMap (A k N) (Uₙ k N) a))
      rw [dN.comul.commutes, Presentation.reduce_scalar, dM.comul.commutes]
      exact tensorReduce_scalar e a
    · intro i
      change tensorReduce e (dN.comul (H k N i)) =
        dM.comul (Presentation.reduce e (H k N i))
      rw [dN.comul_H, show Presentation.reduce e (H k N i) = H k M i from
        Presentation.reduce_H e i, dM.comul_H]
      simp only [RingHom.map_add, tensorReduce_tmul, RingHom.map_one, H, Presentation.reduce_H]
    · intro i
      change tensorReduce e (dN.comul (E (truncated k N) i)) =
        dM.comul (Presentation.reduce e (E (truncated k N) i))
      rw [dN.comul_E, Presentation.reduce_E, dM.comul_E]
      simp only [RingHom.map_add, tensorReduce_tmul, RingHom.map_one, Presentation.reduce_E, reduce_K_value]
    · intro i
      change tensorReduce e (dN.comul (F (truncated k N) i)) =
        dM.comul (Presentation.reduce e (F (truncated k N) i))
      rw [dN.comul_F, Presentation.reduce_F, dM.comul_F]
      simp only [RingHom.map_add, tensorReduce_tmul, RingHom.map_one, Presentation.reduce_F, reduce_K_inverse]
  · apply truncated_ringHom_ext (k := k) (N := N)
    · intro a
      change Truncations.reduce e (dN.counit (algebraMap (A k N) (Uₙ k N) a)) =
        dM.counit (Presentation.reduce e (algebraMap (A k N) (Uₙ k N) a))
      rw [dN.counit.commutes, Presentation.reduce_scalar, dM.counit.commutes]
      rfl
    · intro i
      change Truncations.reduce e (dN.counit (H k N i)) =
        dM.counit (Presentation.reduce e (H k N i))
      rw [dN.counit_H, show Presentation.reduce e (H k N i) = H k M i from
        Presentation.reduce_H e i, dM.counit_H, map_zero]
    · intro i
      change Truncations.reduce e (dN.counit (E (truncated k N) i)) =
        dM.counit (Presentation.reduce e (E (truncated k N) i))
      rw [dN.counit_E, Presentation.reduce_E, dM.counit_E, map_zero]
    · intro i
      change Truncations.reduce e (dN.counit (F (truncated k N) i)) =
        dM.counit (Presentation.reduce e (F (truncated k N) i))
      rw [dN.counit_F, Presentation.reduce_F, dM.counit_F, map_zero]

end Reduction

end LieNotes.Quantum.Coproduct
