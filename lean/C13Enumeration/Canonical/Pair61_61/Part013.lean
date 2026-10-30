import C13Enumeration.Canonical.Pair61_61.Part014
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound447 : ∀ f ∈ assignSearch step finish [9,10,11] [1,8,11] table447, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,8,11] [11] table447 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound448

theorem bound446 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,8,11] table446, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,8,11] [2] table446 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound447

theorem bound445 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [1,2,7,8,11] table445, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [1,2,7,8,11] [7] table445 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound446

theorem bound444 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [1,2,7,8,10,11] table444, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [1,2,7,8,10,11] [10,11] table444 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound445
    · exact bound451

theorem bound443 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,7,8,10,11] table443, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,7,8,10,11] [0] table443 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound444

theorem bound442 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,7,8,10,11] table442, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,7,8,10,11] [3] table442 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound443

theorem bound441 : ∀ f ∈ assignSearch step finish [] [] table441, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound440 : ∀ f ∈ assignSearch step finish [11] [7] table440, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [7] [7] table440 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound441

theorem bound439 : ∀ f ∈ assignSearch step finish [10,11] [2,7] table439, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [2,7] [2] table439 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound440

theorem bound438 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,7] table438, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,7] [0] table438 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound439

theorem bound437 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,3,7] table437, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,3,7] [3] table437 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound438

theorem bound436 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,7,9] table436, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,7,9] [9] table436 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound437

theorem bound435 : ∀ f ∈ assignSearch step finish [] [] table435, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound434 : ∀ f ∈ assignSearch step finish [11] [3] table434, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table434 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound435

theorem bound433 : ∀ f ∈ assignSearch step finish [10,11] [3,9] table433, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,9] [9] table433 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound434

theorem bound432 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,11] table432, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,11] [11] table432 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound433

theorem bound431 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,7,9,11] table431, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,7,9,11] [7] table431 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound432

theorem bound430 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [2,3,7,9,11] table430, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [2,3,7,9,11] [2] table430 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound431

theorem bound429 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,7,9,11] table429, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,7,9,11] [0,11] table429 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound430
    · exact bound436

theorem bound428 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,7,9,10,11] table428, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,7,9,10,11] [10] table428 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound429

theorem bound427 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,3,7,9,10,11] table427, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,3,7,9,10,11] [1] table427 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound428

theorem bound426 : ∀ f ∈ assignSearch step finish [] [] table426, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound425 : ∀ f ∈ assignSearch step finish [11] [8] table425, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table425 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound426

theorem bound424 : ∀ f ∈ assignSearch step finish [10,11] [1,8] table424, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,8] [1] table424 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound425

theorem bound423 : ∀ f ∈ assignSearch step finish [9,10,11] [0,1,8] table423, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,1,8] [0] table423 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound424

theorem bound422 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,1,3,8] table422, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,1,3,8] [3] table422 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound423

theorem bound421 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,3,8,9] table421, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,3,8,9] [9] table421 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound422

theorem bound420 : ∀ f ∈ assignSearch step finish [] [] table420, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound419 : ∀ f ∈ assignSearch step finish [11] [3] table419, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table419 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound420

theorem bound418 : ∀ f ∈ assignSearch step finish [10,11] [3,9] table418, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,9] [9] table418 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound419

theorem bound417 : ∀ f ∈ assignSearch step finish [9,10,11] [3,9,10] table417, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,9,10] [10] table417 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound418

theorem bound416 : ∀ f ∈ assignSearch step finish [8,9,10,11] [3,8,9,10] table416, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [3,8,9,10] [8] table416 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound417
end C13.Enumeration.Canonical.Pair61_61
