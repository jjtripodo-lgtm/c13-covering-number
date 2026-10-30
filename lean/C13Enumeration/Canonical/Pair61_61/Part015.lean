import C13Enumeration.Canonical.Pair61_61.Part016
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound511 : ∀ f ∈ assignSearch step finish [] [] table511, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound510 : ∀ f ∈ assignSearch step finish [11] [3] table510, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table510 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound511

theorem bound509 : ∀ f ∈ assignSearch step finish [10,11] [3,10] table509, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,10] [10] table509 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound510

theorem bound508 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,10] table508, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,10] [9] table508 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound509

theorem bound507 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,8,9,10] table507, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,8,9,10] [8] table507 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound508

theorem bound506 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,3,8,9,10] table506, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,3,8,9,10] [0] table506 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound507

theorem bound505 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,8,9,10] table505, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,8,9,10] [1,9] table505 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound506
    · exact bound512

theorem bound504 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,8,9,10,11] table504, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [11] table504 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound505

theorem bound503 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,8,9,10,11] table503, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,8,9,10,11] [2] table503 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound504

theorem bound502 : ∀ f ∈ assignSearch step finish [] [] table502, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound501 : ∀ f ∈ assignSearch step finish [11] [6] table501, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [6] [6] table501 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound502

theorem bound500 : ∀ f ∈ assignSearch step finish [10,11] [2,6] table500, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,6] [2] table500 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound501

theorem bound499 : ∀ f ∈ assignSearch step finish [9,10,11] [2,6,9] table499, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,6,9] [9] table499 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound500

theorem bound498 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,6,8,9] table498, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,6,8,9] [8] table498 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound499

theorem bound497 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,6,8,9] table497, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,6,8,9] [0] table497 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound498

theorem bound496 : ∀ f ∈ assignSearch step finish [] [] table496, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound495 : ∀ f ∈ assignSearch step finish [11] [8] table495, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table495 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound496

theorem bound494 : ∀ f ∈ assignSearch step finish [10,11] [0,8] table494, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,8] [0] table494 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound495

theorem bound493 : ∀ f ∈ assignSearch step finish [9,10,11] [0,8,11] table493, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,8,11] [11] table493 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound494

theorem bound492 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,6,8,11] table492, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,6,8,11] [6] table492 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound493

theorem bound491 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,6,8,11] table491, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,6,8,11] [2] table491 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound492

theorem bound490 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,6,8,9,11] table490, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,6,8,9,11] [9,11] table490 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound491
    · exact bound497

theorem bound489 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,6,8,9,11] table489, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,6,8,9,11] [1] table489 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound490

theorem bound488 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,6,8,9,10,11] table488, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,6,8,9,10,11] [10] table488 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound489

theorem bound487 : ∀ f ∈ assignSearch step finish [] [] table487, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound486 : ∀ f ∈ assignSearch step finish [11] [0] table486, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table486 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound487

theorem bound485 : ∀ f ∈ assignSearch step finish [10,11] [0,8] table485, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,8] [8] table485 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound486

theorem bound484 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,8] table484, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,8] [1] table484 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound485

theorem bound483 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,8,10] table483, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,8,10] [10] table483 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound484

theorem bound482 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,8,10] table482, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,8,10] [3] table482 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound483

theorem bound481 : ∀ f ∈ assignSearch step finish [] [] table481, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound480 : ∀ f ∈ assignSearch step finish [11] [10] table480, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table480 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound481
end C13.Enumeration.Canonical.Pair61_61
