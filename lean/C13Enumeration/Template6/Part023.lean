import C13Enumeration.Template6.Part024
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound383 : ∀ f ∈ assignSearch step finish [8,9,11] [3,8,11] table383, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [3,8,11] [8] table383 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound384

theorem bound382 : ∀ f ∈ assignSearch step finish [7,8,9,11] [3,7,8,11] table382, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [3,7,8,11] [7] table382 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound383

theorem bound381 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [3,5,7,8,11] table381, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [3,5,7,8,11] [5] table381 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound382

theorem bound380 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [3,4,5,7,8,11] table380, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [3,4,5,7,8,11] [4] table380 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound381

theorem bound379 : ∀ f ∈ assignSearch step finish [] [] table379, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound378 : ∀ f ∈ assignSearch step finish [11] [11] table378, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table378 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound379

theorem bound377 : ∀ f ∈ assignSearch step finish [9,11] [9,11] table377, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [9,11] [9] table377 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound378

theorem bound376 : ∀ f ∈ assignSearch step finish [8,9,11] [8,9,11] table376, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [8,9,11] [8] table376 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound377

theorem bound375 : ∀ f ∈ assignSearch step finish [7,8,9,11] [7,8,9,11] table375, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [7,8,9,11] [7] table375 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound376

theorem bound374 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [5,7,8,9,11] table374, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [5,7,8,9,11] [5] table374 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound375

theorem bound373 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [4,5,7,8,9,11] table373, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [4,5,7,8,9,11] [4] table373 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound374

theorem bound372 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [3,4,5,7,8,9,11] table372, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [3,4,5,7,8,9,11] [3,9] table372 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound373
    · exact bound380

theorem bound371 : ∀ f ∈ assignSearch step finish [2,3,4,5,7,8,9,11] [2,3,4,5,7,8,9,11] table371, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,4,5,7,8,9,11] [2,3,4,5,7,8,9,11] [2,3,8,9] table371 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact bound372
    · exact bound387
    · exact bound402
    · exact bound417

theorem bound370 : ∀ f ∈ assignSearch step finish [1,2,3,4,5,7,8,9,11] [1,2,3,4,5,7,8,9,11] table370, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,4,5,7,8,9,11] [1,2,3,4,5,7,8,9,11] [1,2,3,8,9,11] table370 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound371
    · exact bound432
    · exact bound493
    · exact bound554
    · exact bound615
    · exact bound676

theorem bound369 : ∀ f ∈ assignSearch step finish [10,1,2,3,4,5,7,8,9,11] [0,1,2,3,4,5,7,8,9,11] table369, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [1,2,3,4,5,7,8,9,11] [0,1,2,3,4,5,7,8,9,11] [0] table369 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound370

theorem bound368 : ∀ f ∈ assignSearch step finish [] [] table368, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Template6
