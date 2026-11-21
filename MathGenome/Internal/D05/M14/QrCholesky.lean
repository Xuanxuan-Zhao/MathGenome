import MathGenome.Internal.Specs.D05.M14.QrCholesky
import MathGenome.Internal.D05.M14.QrCholesky.Qr
import MathGenome.Internal.D05.M14.QrCholesky.Cholesky

/-! Reduced QR and Cholesky factorizations, K05.14.qr_cholesky.
Assemble the independently proved construction and uniqueness stages,
expressing the QR conclusion directly in terms of orthonormal columns. -/

namespace D05.M14.QrCholesky

theorem reduced_qr : Specs.D05.M14.QrCholesky.reduced_qr := by
  intro F _ m n A hA
  refine ⟨Qr.dimension_bound A hA, ?_⟩
  obtain ⟨p, hp, huniq⟩ := Qr.exists_unique_reduced_qr A hA
  refine ⟨p, ⟨hp.1, (Qr.orthonormal_columns_iff p.1).mpr hp.2.1, hp.2.2⟩, ?_⟩
  intro q hq
  exact huniq q ⟨hq.1, (Qr.orthonormal_columns_iff q.1).mp hq.2.1, hq.2.2⟩

theorem cholesky : Specs.D05.M14.QrCholesky.cholesky :=
  Cholesky.exists_unique_cholesky

end D05.M14.QrCholesky
