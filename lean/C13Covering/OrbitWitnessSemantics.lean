import C13Covering.OrbitIndexing

namespace C13.OrbitPilot
open Finset
open SourceData

def indexedExtras (i : CompletionIndex) : Family Point :=
  {short0 ∪ choice0 i.1, short1 ∪ choice1 i.2.1, short2 ∪ choice2 i.2.2}

theorem transport_union (e : Equiv.Perm Point) (A B : Family Point) :
    transport e (A ∪ B) = transport e A ∪ transport e B := image_union A B

/-- Factor each literal image proof through a shared core-preservation proof.
All representative decomposition, bijectivity, omitted-point preservation and
three-block image hypotheses are explicit checked proof terms. -/
theorem coveredIndex_of_core_and_extras (i : CompletionIndex) (j : Fin 67)
    (e : Equiv.Perm Point) (extras : Family Point)
    (hrep : catalogRepresentative j = figure1Core ∪ extras)
    (hhole : e hole = hole)
    (hcore : transport e figure1Core = figure1Core)
    (hextras : transport e extras = indexedExtras i) : CoveredIndex i := by
  refine ⟨j,e,hhole,?_⟩
  rw [hrep,transport_union,hcore,hextras]
  rfl

end C13.OrbitPilot
