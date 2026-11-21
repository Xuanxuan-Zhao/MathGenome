import MathGenome.Internal.Specs.D07.Ch19.PrimitiveFermat
import Mathlib.NumberTheory.FLT.Polynomial

/-!
Primitive polynomial Fermat, K07.19.primitive_fermat.

Mathlib's `Polynomial.flt`, proved from polynomial abc, applies to a nonzero
coprime triple when the exponent is at least three and is nonzero in the
coefficient field. Characteristic zero supplies the latter condition.
Its three zero-degree conclusions give constant polynomials over F itself.
The additional two pairwise coprimality assumptions in the source are
retained in the independent statement, even though the library needs only
coprimality of the first two polynomials.
-/

universe u

namespace D07.Ch19.PrimitiveFermat

open Polynomial
open Specs.D07.Ch19.PrimitiveFermat

theorem primitive_fermat : PrimitiveFermat.{u} := by
  intro F _ _ n hn f g h hf hg hh hfg _ _ heq
  have hn0 : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  obtain ⟨hfd, hgd, hhd⟩ := Polynomial.flt hn hn0 hf hg hh hfg heq
  obtain ⟨a, ha⟩ := natDegree_eq_zero.mp hfd
  obtain ⟨b, hb⟩ := natDegree_eq_zero.mp hgd
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hhd
  exact ⟨a, b, c, ha.symm, hb.symm, hc.symm⟩

end D07.Ch19.PrimitiveFermat
