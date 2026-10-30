import C13Enumeration.Canonical.Pair61_61.Part013
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound415 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,3,8,9,10] table415, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,3,8,9,10] [1] table415 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound416

theorem bound414 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,8,9,10] table414, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,8,9,10] [0,10] table414 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound415
    · exact bound421

theorem bound413 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,8,9,10,11] table413, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [11] table413 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound414

theorem bound412 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,8,9,10,11] table412, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,8,9,10,11] [2] table412 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound413

theorem bound411 : ∀ f ∈ assignSearch step finish [] [] table411, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound410 : ∀ f ∈ assignSearch step finish [11] [7] table410, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table410 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound411

theorem bound409 : ∀ f ∈ assignSearch step finish [10,11] [2,7] table409, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,7] [2] table409 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound410

theorem bound408 : ∀ f ∈ assignSearch step finish [9,10,11] [2,7,10] table408, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [2,7,10] [10] table408 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound409

theorem bound407 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,7,8,10] table407, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,7,8,10] [8] table407 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound408

theorem bound406 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,7,8,10] table406, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,7,8,10] [1] table406 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound407

theorem bound405 : ∀ f ∈ assignSearch step finish [] [] table405, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound404 : ∀ f ∈ assignSearch step finish [11] [8] table404, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table404 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound405

theorem bound403 : ∀ f ∈ assignSearch step finish [10,11] [1,8] table403, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,8] [1] table403 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound404

theorem bound402 : ∀ f ∈ assignSearch step finish [9,10,11] [1,8,11] table402, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,8,11] [11] table402 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound403

theorem bound401 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,7,8,11] table401, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,7,8,11] [7] table401 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound402

theorem bound400 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,7,8,11] table400, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,7,8,11] [2] table400 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound401

theorem bound399 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,7,8,10,11] table399, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,7,8,10,11] [10,11] table399 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound400
    · exact bound406

theorem bound398 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,7,8,10,11] table398, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,7,8,10,11] [0] table398 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound399

theorem bound397 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,7,8,9,10,11] table397, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,7,8,9,10,11] [9] table397 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound398

theorem bound396 : ∀ f ∈ assignSearch step finish [] [] table396, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound395 : ∀ f ∈ assignSearch step finish [11] [1] table395, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table395 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound396

theorem bound394 : ∀ f ∈ assignSearch step finish [10,11] [1,8] table394, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,8] [8] table394 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound395

theorem bound393 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,8] table393, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,8] [0] table393 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound394

theorem bound392 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,8,9] table392, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,8,9] [9] table392 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound393

theorem bound391 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,8,9] table391, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,8,9] [3] table391 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound392

theorem bound390 : ∀ f ∈ assignSearch step finish [] [] table390, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound389 : ∀ f ∈ assignSearch step finish [11] [9] table389, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table389 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound390

theorem bound388 : ∀ f ∈ assignSearch step finish [10,11] [3,9] table388, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,9] [3] table388 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound389

theorem bound387 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,10] table387, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,10] [10] table387 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound388

theorem bound386 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,3,9,10] table386, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,3,9,10] [1] table386 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound387

theorem bound385 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,3,8,9,10] table385, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,3,8,9,10] [8] table385 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound386

theorem bound384 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,3,8,9,10] table384, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,3,8,9,10] [0,10] table384 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound385
    · exact bound391
end C13.Enumeration.Canonical.Pair61_61
