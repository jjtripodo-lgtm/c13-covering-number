import C13Enumeration.Template6.Part032
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound511 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [5,7,8,9,11] table511, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [5,7,8,9,11] [7] table511 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound512

theorem bound510 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [4,5,7,8,9,11] table510, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [4,5,7,8,9,11] [4] table510 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound511

theorem bound509 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,4,5,7,8,9,11] table509, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,4,5,7,8,9,11] [1,11] table509 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound510
    · exact bound517

theorem bound508 : ∀ f ∈ assignSearch step finish [] [] table508, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound507 : ∀ f ∈ assignSearch step finish [11] [9] table507, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table507 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound508

theorem bound506 : ∀ f ∈ assignSearch step finish [9,11] [2,9] table506, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,9] [2] table506 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound507

theorem bound505 : ∀ f ∈ assignSearch step finish [8,9,11] [2,9,11] table505, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,9,11] [11] table505 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound506

theorem bound504 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,5,9,11] table504, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,5,9,11] [5] table504 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound505

theorem bound503 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,4,5,9,11] table503, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,4,5,9,11] [4] table503 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound504

theorem bound502 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,4,5,7,9,11] table502, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,4,5,7,9,11] [7] table502 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound503

theorem bound501 : ∀ f ∈ assignSearch step finish [] [] table501, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound500 : ∀ f ∈ assignSearch step finish [11] [9] table500, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table500 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound501

theorem bound499 : ∀ f ∈ assignSearch step finish [9,11] [8,9] table499, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [8,9] [8] table499 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound500

theorem bound498 : ∀ f ∈ assignSearch step finish [8,9,11] [8,9,11] table498, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [8,9,11] [11] table498 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound499

theorem bound497 : ∀ f ∈ assignSearch step finish [7,8,9,11] [5,8,9,11] table497, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [5,8,9,11] [5] table497 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound498

theorem bound496 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [4,5,8,9,11] table496, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [4,5,8,9,11] [4] table496 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound497
end C13.Enumeration.Template6
