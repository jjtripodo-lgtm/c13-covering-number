import C13Enumeration.CodeTransport
namespace C13.Enumeration
set_option Elab.async false

theorem emit_mem_completeDomain (catalog : Finset (Family Point)) (K L : Family Point)
    (hole c q : Point) (hK : K ∈ catalog) (e : Equiv.Perm Point)
    (he : e hole = q) (hc : e c = hole)
    (hs : transport e (link K c) = link L q) :
    emitPencil K c q e ∈ completeDomain catalog hole L hole q := by
  apply (mem_completeDomain_iff ..).mpr
  refine ⟨K,hK,e,he,C13.Raw.whole_star_of_punctured_star K L e c hole q hc hs,?_⟩
  rw [← C13.Raw.outside_pencil_from_center K e c hole q hc]
  simp only [emitPencil,mapFamily_equiv]
end C13.Enumeration
