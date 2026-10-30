import C13Enumeration.Template6.Part018
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound287 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,3,5,7] table287, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,3,5,7] [7] table287 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound288

theorem bound286 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,3,4,5,7] table286, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,3,4,5,7] [4] table286 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound287

theorem bound285 : ∀ f ∈ assignSearch step finish [] [] table285, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound284 : ∀ f ∈ assignSearch step finish [11] [3] table284, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table284 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound285

theorem bound283 : ∀ f ∈ assignSearch step finish [9,11] [3,11] table283, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [3,11] [11] table283 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound284

theorem bound282 : ∀ f ∈ assignSearch step finish [8,9,11] [2,3,11] table282, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,3,11] [2] table282 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound283

theorem bound281 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,3,5,11] table281, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,3,5,11] [5] table281 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound282

theorem bound280 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,3,5,7,11] table280, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,3,5,7,11] [7] table280 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound281

theorem bound279 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,3,4,5,7,11] table279, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,3,4,5,7,11] [4] table279 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound280

theorem bound278 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,3,4,5,7,11] table278, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,3,4,5,7,11] [1,11] table278 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound279
    · exact bound286

theorem bound277 : ∀ f ∈ assignSearch step finish [] [] table277, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound276 : ∀ f ∈ assignSearch step finish [11] [3] table276, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table276 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound277

theorem bound275 : ∀ f ∈ assignSearch step finish [9,11] [1,3] table275, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,3] [1] table275 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound276

theorem bound274 : ∀ f ∈ assignSearch step finish [8,9,11] [1,3,8] table274, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,3,8] [8] table274 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound275

theorem bound273 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,3,5,8] table273, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,3,5,8] [5] table273 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound274

theorem bound272 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,3,5,7,8] table272, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,3,5,7,8] [7] table272 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound273
end C13.Enumeration.Template6
