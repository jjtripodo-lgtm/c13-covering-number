import C13Enumeration.Canonical.Pair61_61.Part011
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound351 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,6,7,8,9,10] table351, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,6,7,8,9,10] [8] table351 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound352

theorem bound350 : ∀ f ∈ assignSearch step finish [] [] table350, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound349 : ∀ f ∈ assignSearch step finish [11] [11] table349, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table349 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound350

theorem bound348 : ∀ f ∈ assignSearch step finish [10,11] [8,11] table348, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [8,11] [8] table348 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound349

theorem bound347 : ∀ f ∈ assignSearch step finish [9,10,11] [0,8,11] table347, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,8,11] [0] table347 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound348

theorem bound346 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,8,9,11] table346, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,8,9,11] [9] table346 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound347

theorem bound345 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,6,8,9,11] table345, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,6,8,9,11] [6] table345 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound346

theorem bound344 : ∀ f ∈ assignSearch step finish [] [] table344, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound343 : ∀ f ∈ assignSearch step finish [11] [9] table343, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table343 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound344

theorem bound342 : ∀ f ∈ assignSearch step finish [10,11] [6,9] table342, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,9] [6] table342 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound343

theorem bound341 : ∀ f ∈ assignSearch step finish [9,10,11] [2,6,9] table341, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,6,9] [2] table341 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound342

theorem bound340 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,6,9,11] table340, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,6,9,11] [11] table340 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound341

theorem bound339 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,6,8,9,11] table339, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,6,8,9,11] [8] table339 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound340

theorem bound338 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,6,8,9,11] table338, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,6,8,9,11] [0,2] table338 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound339
    · exact bound345

theorem bound337 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,6,8,9,11] table337, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,6,8,9,11] [1] table337 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound338

theorem bound336 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,6,7,8,9,11] table336, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,6,7,8,9,11] [7] table336 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound337

theorem bound335 : ∀ f ∈ assignSearch step finish [] [] table335, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound334 : ∀ f ∈ assignSearch step finish [11] [11] table334, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table334 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound335

theorem bound333 : ∀ f ∈ assignSearch step finish [10,11] [8,11] table333, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [8,11] [8] table333 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound334

theorem bound332 : ∀ f ∈ assignSearch step finish [9,10,11] [1,8,11] table332, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,8,11] [1] table332 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound333

theorem bound331 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,8,10,11] table331, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,8,10,11] [10] table331 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound332

theorem bound330 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,7,8,10,11] table330, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,7,8,10,11] [7] table330 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound331

theorem bound329 : ∀ f ∈ assignSearch step finish [] [] table329, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound328 : ∀ f ∈ assignSearch step finish [11] [10] table328, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table328 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound329

theorem bound327 : ∀ f ∈ assignSearch step finish [10,11] [7,10] table327, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [7,10] [7] table327 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound328

theorem bound326 : ∀ f ∈ assignSearch step finish [9,10,11] [2,7,10] table326, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,7,10] [2] table326 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound327

theorem bound325 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,7,10,11] table325, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,7,10,11] [11] table325 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound326

theorem bound324 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,7,8,10,11] table324, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,7,8,10,11] [8] table324 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound325

theorem bound323 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,7,8,10,11] table323, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,7,8,10,11] [1,2] table323 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound324
    · exact bound330

theorem bound322 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,7,8,10,11] table322, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,7,8,10,11] [0] table322 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound323

theorem bound321 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,6,7,8,10,11] table321, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,6,7,8,10,11] [6] table321 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound322

theorem bound320 : ∀ f ∈ assignSearch step finish [] [] table320, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Canonical.Pair61_61
