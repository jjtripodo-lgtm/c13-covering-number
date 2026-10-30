import C13Enumeration.Template6.Part027
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound431 : ∀ f ∈ assignSearch step finish [] [] table431, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound430 : ∀ f ∈ assignSearch step finish [11] [11] table430, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table430 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound431

theorem bound429 : ∀ f ∈ assignSearch step finish [9,11] [2,11] table429, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,11] [2] table429 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound430

theorem bound428 : ∀ f ∈ assignSearch step finish [8,9,11] [2,3,11] table428, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,3,11] [3] table428 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound429

theorem bound427 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,3,7,11] table427, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,3,7,11] [7] table427 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound428

theorem bound426 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,3,4,7,11] table426, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,3,4,7,11] [4] table426 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound427

theorem bound425 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,3,4,5,7,11] table425, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,3,4,5,7,11] [5] table425 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound426

theorem bound424 : ∀ f ∈ assignSearch step finish [] [] table424, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound423 : ∀ f ∈ assignSearch step finish [11] [11] table423, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table423 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound424

theorem bound422 : ∀ f ∈ assignSearch step finish [9,11] [8,11] table422, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [8,11] [8] table422 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound423

theorem bound421 : ∀ f ∈ assignSearch step finish [8,9,11] [3,8,11] table421, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [3,8,11] [3] table421 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound422

theorem bound420 : ∀ f ∈ assignSearch step finish [7,8,9,11] [3,7,8,11] table420, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [3,7,8,11] [7] table420 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound421

theorem bound419 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [3,4,7,8,11] table419, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [3,4,7,8,11] [4] table419 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound420

theorem bound418 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [3,4,5,7,8,11] table418, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [3,4,5,7,8,11] [5] table418 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound419

theorem bound417 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [2,3,4,5,7,8,11] table417, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [2,3,4,5,7,8,11] [2,8] table417 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound418
    · exact bound425

theorem bound416 : ∀ f ∈ assignSearch step finish [] [] table416, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Template6
