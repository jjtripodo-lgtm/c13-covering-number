import C13Covering.OrbitGenerators.Gen0
import C13Covering.OrbitGenerators.Gen1
import C13Covering.OrbitGenerators.Gen2
import C13Covering.OrbitGenerators.Gen3
import C13Covering.OrbitGenerators.Gen4
import C13Covering.OrbitGenerators.Gen5
import C13Covering.OrbitGenerators.Gen6
import Mathlib.Tactic.FinCases

namespace C13.OrbitPilot.Word
open C13.SourceData
set_option maxRecDepth 10000
set_option maxHeartbeats 0

abbrev Generator := Fin 7

def generator : Generator → Equiv.Perm Point := ![Generator0.permutation, Generator1.permutation, Generator2.permutation, Generator3.permutation, Generator4.permutation, Generator5.permutation, Generator6.permutation]

def step : Generator → CompletionIndex → CompletionIndex := ![Generator0.step, Generator1.step, Generator2.step, Generator3.step, Generator4.step, Generator5.step, Generator6.step]

theorem generator_hole (g : Generator) : generator g hole = hole := by
  fin_cases g
  · exact Generator0.hole_fixed
  · exact Generator1.hole_fixed
  · exact Generator2.hole_fixed
  · exact Generator3.hole_fixed
  · exact Generator4.hole_fixed
  · exact Generator5.hole_fixed
  · exact Generator6.hole_fixed

theorem generator_action (g : Generator) (i : CompletionIndex) :
    transport (generator g) (indexedCompletion i) = indexedCompletion (step g i) := by
  fin_cases g
  · exact Generator0.completion_action i
  · exact Generator1.completion_action i
  · exact Generator2.completion_action i
  · exact Generator3.completion_action i
  · exact Generator4.completion_action i
  · exact Generator5.completion_action i
  · exact Generator6.completion_action i

def wordPermutation : List Generator → Equiv.Perm Point
  | [] => Equiv.refl Point
  | g :: gs => (generator g).trans (wordPermutation gs)

def runWord : List Generator → CompletionIndex → CompletionIndex
  | [], i => i
  | g :: gs, i => runWord gs (step g i)

theorem word_hole (w : List Generator) : wordPermutation w hole = hole := by
  induction w with
  | nil => rfl
  | cons g gs ih =>
    change wordPermutation gs (generator g hole) = hole
    rw [generator_hole,ih]

theorem transport_identity (F : Family Point) : transport (Equiv.refl Point) F = F := by
  change F.image (Finset.map (Function.Embedding.refl Point)) = F
  calc
    _ = F.image id := Finset.image_congr (by intro B _; exact Finset.map_refl)
    _ = F := Finset.image_id

/-- A word in verified generators acts correctly on every raw completion.
The generation/census of the abstract group is deliberately irrelevant. -/
theorem word_action (w : List Generator) (i : CompletionIndex) :
    transport (wordPermutation w) (indexedCompletion i) = indexedCompletion (runWord w i) := by
  induction w generalizing i with
  | nil => exact transport_identity (indexedCompletion i)
  | cons g gs ih =>
    change transport ((generator g).trans (wordPermutation gs)) (indexedCompletion i) = _
    rw [← transport_trans,generator_action,ih]
    rfl

def representativeIndex : Fin 67 → CompletionIndex := ![(0,0,0), (0,0,1), (0,0,3), (0,0,5), (0,0,13), (0,0,16), (0,1,0), (0,3,0), (0,5,0), (0,14,0), (0,16,0), (0,22,0), (0,23,0), (0,27,0), (0,1,1), (0,1,2), (0,1,3), (0,1,5), (0,1,8), (0,1,11), (0,3,1), (0,5,1), (0,9,1), (0,11,1), (0,24,1), (0,3,3), (0,3,4), (0,3,5), (0,3,9), (0,3,10), (0,3,11), (0,3,14), (0,3,15), (0,3,16), (0,3,17), (0,3,22), (0,3,23), (0,3,25), (0,3,27), (0,5,3), (0,5,5), (0,5,6), (0,5,9), (0,5,11), (0,5,12), (0,5,14), (0,5,15), (0,5,16), (0,5,17), (0,5,22), (0,5,24), (3,3,3), (3,3,4), (3,3,10), (3,3,11), (3,4,5), (3,4,9), (3,4,10), (3,4,11), (3,4,14), (3,4,15), (3,4,17), (3,9,9), (3,9,11), (3,9,17), (3,11,15), (3,11,20)]

/-- Explicit small transition equality plus a checked representative identity
constructs the actual permutation witness needed by the source-coverage proof. -/
theorem covered_of_word (i : CompletionIndex) (j : Fin 67) (w : List Generator)
    (hrep : catalogRepresentative j = indexedCompletion (representativeIndex j))
    (hindex : runWord w (representativeIndex j) = i) : CoveredIndex i := by
  refine ⟨j,wordPermutation w,word_hole w,?_⟩
  rw [hrep,word_action,hindex]

end C13.OrbitPilot.Word
