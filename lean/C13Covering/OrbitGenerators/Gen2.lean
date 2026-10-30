import C13Covering.OrbitWitnessSemantics
namespace C13.OrbitPilot.Generator2
open C13.SourceData
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def permutation : Equiv.Perm Point where
  toFun := ![0,1,2,3,8,9,10,11,4,5,6,7,12]
  invFun := ![0,1,2,3,8,9,10,11,4,5,6,7,12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem hole_fixed : permutation hole = hole := by decide +kernel

theorem core_fixed : transport permutation figure1Core = figure1Core := by decide +kernel

def transition0 : Fin 28 → Fin 28 := ![22,23,24,3,9,14,18,25,26,4,10,15,19,27,5,11,16,20,6,12,17,21,0,1,2,7,8,13]

theorem block_action0 (a : Fin 28) :
    (short0 ∪ choice0 a).map permutation.toEmbedding =
      short0 ∪ choice0 (transition0 a) := by
  revert a
  decide +kernel

def transition1 : Fin 28 → Fin 28 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]

theorem block_action1 (a : Fin 28) :
    (short1 ∪ choice1 a).map permutation.toEmbedding =
      short2 ∪ choice2 (transition1 a) := by
  revert a
  decide +kernel

def transition2 : Fin 28 → Fin 28 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]

theorem block_action2 (a : Fin 28) :
    (short2 ∪ choice2 a).map permutation.toEmbedding =
      short1 ∪ choice1 (transition2 a) := by
  revert a
  decide +kernel

def step (i : CompletionIndex) : CompletionIndex := (transition0 i.1, transition2 i.2.2, transition1 i.2.1)

theorem completion_action (i : CompletionIndex) :
    transport permutation (indexedCompletion i) = indexedCompletion (step i) := by
  unfold indexedCompletion figure1Completion
  rw [transport_union,core_fixed]
  simp only [transport,image_insert,image_singleton,block_action0,block_action1,block_action2]
  dsimp only [step]
  all_goals
    ext B
    simp only [mem_union,mem_insert,mem_singleton,or_assoc,or_left_comm,or_comm]

end C13.OrbitPilot.Generator2
