import C13Enumeration.Canonical.Pair61_61.Part015
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound479 : ∀ f ∈ assignSearch step finish [10,11] [3,10] table479, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,10] [3] table479 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound480

theorem bound478 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,10] table478, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,10] [9] table478 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound479

theorem bound477 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,3,9,10] table477, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,3,9,10] [0] table477 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound478

theorem bound476 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,3,8,9,10] table476, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,3,8,9,10] [8] table476 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound477

theorem bound475 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,8,9,10] table475, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,8,9,10] [1,9] table475 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound476
    · exact bound482

theorem bound474 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,8,9,10,11] table474, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [11] table474 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound475

theorem bound473 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,3,6,8,9,10,11] table473, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,3,6,8,9,10,11] [6] table473 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound474

theorem bound472 : ∀ f ∈ assignSearch step finish [] [] table472, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound471 : ∀ f ∈ assignSearch step finish [11] [2] table471, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table471 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound472

theorem bound470 : ∀ f ∈ assignSearch step finish [10,11] [2,6] table470, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,6] [6] table470 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound471

theorem bound469 : ∀ f ∈ assignSearch step finish [9,10,11] [1,2,6] table469, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,2,6] [1] table469 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound470

theorem bound468 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,6,10] table468, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,6,10] [10] table468 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound469

theorem bound467 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,3,6,10] table467, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,3,6,10] [3] table467 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound468

theorem bound466 : ∀ f ∈ assignSearch step finish [] [] table466, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound465 : ∀ f ∈ assignSearch step finish [11] [10] table465, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table465 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound466

theorem bound464 : ∀ f ∈ assignSearch step finish [10,11] [3,10] table464, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,10] [3] table464 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound465

theorem bound463 : ∀ f ∈ assignSearch step finish [9,10,11] [3,10,11] table463, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,10,11] [11] table463 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound464

theorem bound462 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,3,10,11] table462, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,3,10,11] [2] table462 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound463

theorem bound461 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,3,6,10,11] table461, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,3,6,10,11] [6] table461 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound462

theorem bound460 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,3,6,10,11] table460, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,3,6,10,11] [1,11] table460 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound461
    · exact bound467

theorem bound459 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [1,2,3,6,9,10,11] table459, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [1,2,3,6,9,10,11] [9] table459 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound460

theorem bound458 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [1,2,3,6,8,9,10,11] table458, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [1,2,3,6,8,9,10,11] [8] table458 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound459

theorem bound457 : ∀ f ∈ assignSearch step finish [1,2,3,6,7,8,9,10,11] [0,1,2,3,6,8,9,10,11] table457, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,6,7,8,9,10,11] [0,1,2,3,6,8,9,10,11] [0,2,3,6,8,10] table457 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound458
    · exact bound473
    · exact bound488
    · exact bound503
    · exact bound518
    · exact bound533

theorem bound456 : ∀ f ∈ assignSearch step finish [] [] table456, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound455 : ∀ f ∈ assignSearch step finish [11] [2] table455, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table455 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound456

theorem bound454 : ∀ f ∈ assignSearch step finish [10,11] [2,7] table454, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,7] [7] table454 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound455

theorem bound453 : ∀ f ∈ assignSearch step finish [9,10,11] [2,7,10] table453, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,7,10] [10] table453 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound454

theorem bound452 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,7,10] table452, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,7,10] [1] table452 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound453

theorem bound451 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,7,8,10] table451, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,7,8,10] [8] table451 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound452

theorem bound450 : ∀ f ∈ assignSearch step finish [] [] table450, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound449 : ∀ f ∈ assignSearch step finish [11] [1] table449, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table449 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound450

theorem bound448 : ∀ f ∈ assignSearch step finish [10,11] [1,8] table448, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,8] [8] table448 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound449
end C13.Enumeration.Canonical.Pair61_61
