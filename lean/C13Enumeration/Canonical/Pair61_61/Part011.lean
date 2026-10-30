import C13Enumeration.Canonical.Pair61_61.Part012
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound383 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,3,8,9,10,11] table383, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,3,8,9,10,11] [11] table383 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound384

theorem bound382 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,3,7,8,9,10,11] table382, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,3,7,8,9,10,11] [7] table382 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound383

theorem bound381 : ∀ f ∈ assignSearch step finish [] [] table381, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound380 : ∀ f ∈ assignSearch step finish [11] [2] table380, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [2] [2] table380 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound381

theorem bound379 : ∀ f ∈ assignSearch step finish [10,11] [2,7] table379, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,7] [7] table379 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound380

theorem bound378 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,7] table378, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,7] [0] table378 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound379

theorem bound377 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,7,9] table377, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,7,9] [9] table377 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound378

theorem bound376 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,7,9] table376, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,7,9] [3] table376 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound377

theorem bound375 : ∀ f ∈ assignSearch step finish [] [] table375, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound374 : ∀ f ∈ assignSearch step finish [11] [9] table374, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table374 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound375

theorem bound373 : ∀ f ∈ assignSearch step finish [10,11] [3,9] table373, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,9] [3] table373 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound374

theorem bound372 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,11] table372, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,11] [11] table372 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound373

theorem bound371 : ∀ f ∈ assignSearch step finish [8,9,10,11] [2,3,9,11] table371, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [2,3,9,11] [2] table371 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound372

theorem bound370 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,3,7,9,11] table370, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,3,7,9,11] [7] table370 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound371

theorem bound369 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,7,9,11] table369, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,7,9,11] [0,11] table369 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound370
    · exact bound376

theorem bound368 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,7,9,10,11] table368, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,7,9,10,11] [10] table368 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound369

theorem bound367 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,2,3,7,8,9,10,11] table367, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,2,3,7,8,9,10,11] [8] table367 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound368

theorem bound366 : ∀ f ∈ assignSearch step finish [1,2,3,6,7,8,9,10,11] [0,1,2,3,7,8,9,10,11] table366, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,6,7,8,9,10,11] [0,1,2,3,7,8,9,10,11] [1,2,3,7,8,9] table366 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound367
    · exact bound382
    · exact bound397
    · exact bound412
    · exact bound427
    · exact bound442

theorem bound365 : ∀ f ∈ assignSearch step finish [] [] table365, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound364 : ∀ f ∈ assignSearch step finish [11] [10] table364, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table364 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound365

theorem bound363 : ∀ f ∈ assignSearch step finish [10,11] [7,10] table363, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [7,10] [7] table363 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound364

theorem bound362 : ∀ f ∈ assignSearch step finish [9,10,11] [0,7,10] table362, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,7,10] [0] table362 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound363

theorem bound361 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,7,9,10] table361, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,7,9,10] [9] table361 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound362

theorem bound360 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,6,7,9,10] table360, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,6,7,9,10] [6] table360 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound361

theorem bound359 : ∀ f ∈ assignSearch step finish [] [] table359, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound358 : ∀ f ∈ assignSearch step finish [11] [9] table358, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table358 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound359

theorem bound357 : ∀ f ∈ assignSearch step finish [10,11] [6,9] table357, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [6,9] [6] table357 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound358

theorem bound356 : ∀ f ∈ assignSearch step finish [9,10,11] [1,6,9] table356, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,6,9] [1] table356 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound357

theorem bound355 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,6,9,10] table355, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,6,9,10] [10] table355 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound356

theorem bound354 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,6,7,9,10] table354, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,6,7,9,10] [7] table354 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound355

theorem bound353 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,6,7,9,10] table353, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,6,7,9,10] [0,1] table353 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound354
    · exact bound360

theorem bound352 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,6,7,9,10] table352, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,6,7,9,10] [2] table352 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound353
end C13.Enumeration.Canonical.Pair61_61
