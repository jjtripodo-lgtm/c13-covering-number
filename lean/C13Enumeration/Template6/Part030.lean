import C13Enumeration.Template6.Part031
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound495 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [4,5,7,8,9,11] table495, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [4,5,7,8,9,11] [7] table495 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound496

theorem bound494 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [2,4,5,7,8,9,11] table494, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [2,4,5,7,8,9,11] [2,8] table494 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound495
    · exact bound502

theorem bound493 : ∀ f ∈ assignSearch step finish [2,3,4,5,7,8,9,11] [1,2,4,5,7,8,9,11] table493, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,4,5,7,8,9,11] [1,2,4,5,7,8,9,11] [1,2,8,11] table493 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound494
    · exact bound509
    · exact bound524
    · exact bound539

theorem bound492 : ∀ f ∈ assignSearch step finish [] [] table492, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound491 : ∀ f ∈ assignSearch step finish [11] [8] table491, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table491 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound492

theorem bound490 : ∀ f ∈ assignSearch step finish [9,11] [3,8] table490, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [3,8] [3] table490 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound491

theorem bound489 : ∀ f ∈ assignSearch step finish [8,9,11] [1,3,8] table489, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,3,8] [1] table489 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound490

theorem bound488 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,3,4,8] table488, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,3,4,8] [4] table488 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound489

theorem bound487 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,3,4,5,8] table487, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,3,4,5,8] [5] table487 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound488

theorem bound486 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,3,4,5,7,8] table486, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,3,4,5,7,8] [7] table486 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound487

theorem bound485 : ∀ f ∈ assignSearch step finish [] [] table485, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound484 : ∀ f ∈ assignSearch step finish [11] [8] table484, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table484 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound485

theorem bound483 : ∀ f ∈ assignSearch step finish [9,11] [8,9] table483, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [8,9] [9] table483 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound484

theorem bound482 : ∀ f ∈ assignSearch step finish [8,9,11] [1,8,9] table482, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,8,9] [1] table482 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound483

theorem bound481 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,4,8,9] table481, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,4,8,9] [4] table481 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound482

theorem bound480 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,4,5,8,9] table480, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,4,5,8,9] [5] table480 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound481
end C13.Enumeration.Template6
