import C13Enumeration.Certificate
namespace C13.Enumeration
open Finset

/-- Composition is literal on every point and therefore on every block. -/
theorem transport_trans (e f : Equiv.Perm Point) (S : Family Point) :
    transport (e.trans f) S = transport f (transport e S) := by
  unfold transport
  rw [image_image]
  apply image_congr
  intro B hB
  change B.map (e.trans f).toEmbedding = (B.map e.toEmbedding).map f.toEmbedding
  rw [Finset.map_map]
  rfl

theorem transport_eq_iff (e : Equiv.Perm Point) (S T : Family Point) :
    transport e S = T ↔ S = transport e.symm T := by
  constructor
  · intro h
    rw [← h,transport_inverse]
  · intro h
    rw [h]
    simpa only [Equiv.symm_symm] using transport_inverse e.symm T

/-- A pair of certified source/target normalizers factors EVERY unrestricted
star isomorphism through the corresponding template-to-template isomorphism.
This is a statement about actual ambient permutations, including both anchors
and every isolated point; no support-only or construction-group assumption. -/
theorem factor_star_map (S T U W : Family Point)
    (a b e : Equiv.Perm Point) (ha : transport a S = U) (hb : transport b T = W)
    (he : transport e S = T) :
    transport ((a.symm.trans e).trans b) U = W := by
  rw [transport_trans,transport_trans,← ha,transport_inverse,he,hb]

theorem factor_star_map_reconstruct (a b e : Equiv.Perm Point) :
    (a.trans ((a.symm.trans e).trans b)).trans b.symm = e := by
  apply Equiv.ext
  intro x
  simp

/-- Exact pointwise maps suffice to recover the whole semantic pencil. -/
theorem emitPencil_congr (K : Family Point) (c q : Point)
    (f g : Point → Point) (h : ∀ x, f x = g x) :
    emitPencil K c q f = emitPencil K c q g := by
  have hf : f = g := funext h
  rw [hf]

/-- Target relabeling also preserves the literal inserted point label. -/
theorem transport_liftAt (e : Equiv.Perm Point) (q : Point) (S : Family Point) :
    transport e (liftAt q S) = liftAt (e q) (transport e S) := by
  unfold transport liftAt
  rw [image_image,image_image]
  apply image_congr
  intro B hB
  ext x
  simp

end C13.Enumeration
