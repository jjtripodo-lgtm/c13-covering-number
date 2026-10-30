import C13Enumeration.Template6.Part021
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound335 : ∀ f ∈ assignSearch step finish [8,9,11] [1,2,9] table335, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,2,9] [9] table335 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound336

theorem bound334 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,2,7,9] table334, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,2,7,9] [7] table334 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound335

theorem bound333 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,2,4,7,9] table333, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,2,4,7,9] [4] table333 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound334

theorem bound332 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,2,4,5,7,9] table332, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,2,4,5,7,9] [5] table332 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound333

theorem bound331 : ∀ f ∈ assignSearch step finish [] [] table331, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound330 : ∀ f ∈ assignSearch step finish [11] [1] table330, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table330 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound331

theorem bound329 : ∀ f ∈ assignSearch step finish [9,11] [1,8] table329, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,8] [8] table329 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound330

theorem bound328 : ∀ f ∈ assignSearch step finish [8,9,11] [1,8,9] table328, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,8,9] [9] table328 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound329

theorem bound327 : ∀ f ∈ assignSearch step finish [7,8,9,11] [1,7,8,9] table327, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [1,7,8,9] [7] table327 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound328

theorem bound326 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [1,4,7,8,9] table326, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [1,4,7,8,9] [4] table326 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound327

theorem bound325 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,4,5,7,8,9] table325, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,4,5,7,8,9] [5] table325 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound326

theorem bound324 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,2,4,5,7,8,9] table324, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,2,4,5,7,8,9] [2,8] table324 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound325
    · exact bound332

theorem bound323 : ∀ f ∈ assignSearch step finish [] [] table323, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound322 : ∀ f ∈ assignSearch step finish [11] [1] table322, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table322 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound323

theorem bound321 : ∀ f ∈ assignSearch step finish [9,11] [1,3] table321, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [1,3] [3] table321 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound322

theorem bound320 : ∀ f ∈ assignSearch step finish [8,9,11] [1,3,8] table320, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [1,3,8] [8] table320 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound321
end C13.Enumeration.Template6
