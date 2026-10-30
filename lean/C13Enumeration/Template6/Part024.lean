import C13Enumeration.Template6.Part025
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound399 : ∀ f ∈ assignSearch step finish [9,11] [2,11] table399, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,11] [2] table399 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound400

theorem bound398 : ∀ f ∈ assignSearch step finish [8,9,11] [2,9,11] table398, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,9,11] [9] table398 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound399

theorem bound397 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,7,9,11] table397, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,7,9,11] [7] table397 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound398

theorem bound396 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,4,7,9,11] table396, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,4,7,9,11] [4] table396 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound397

theorem bound395 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,4,5,7,9,11] table395, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,4,5,7,9,11] [5] table395 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound396

theorem bound394 : ∀ f ∈ assignSearch step finish [] [] table394, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound393 : ∀ f ∈ assignSearch step finish [11] [11] table393, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table393 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound394

theorem bound392 : ∀ f ∈ assignSearch step finish [9,11] [8,11] table392, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [8,11] [8] table392 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound393

theorem bound391 : ∀ f ∈ assignSearch step finish [8,9,11] [8,9,11] table391, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [8,9,11] [9] table391 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound392

theorem bound390 : ∀ f ∈ assignSearch step finish [7,8,9,11] [7,8,9,11] table390, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [7,8,9,11] [7] table390 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound391

theorem bound389 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [4,7,8,9,11] table389, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [4,7,8,9,11] [4] table389 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound390

theorem bound388 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [4,5,7,8,9,11] table388, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [4,5,7,8,9,11] [5] table388 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound389

theorem bound387 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [2,4,5,7,8,9,11] table387, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [2,4,5,7,8,9,11] [2,8] table387 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound388
    · exact bound395

theorem bound386 : ∀ f ∈ assignSearch step finish [] [] table386, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound385 : ∀ f ∈ assignSearch step finish [11] [11] table385, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table385 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound386

theorem bound384 : ∀ f ∈ assignSearch step finish [9,11] [3,11] table384, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [3,11] [3] table384 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound385
end C13.Enumeration.Template6
