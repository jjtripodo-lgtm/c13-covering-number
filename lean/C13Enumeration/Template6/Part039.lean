import C13Enumeration.Template6.Part040
namespace C13.Enumeration.Template6
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound639 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [1,3,4,5,7,8] table639, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [1,3,4,5,7,8] [4] table639 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound640

theorem bound638 : ∀ f ∈ assignSearch step finish [] [] table638, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound637 : ∀ f ∈ assignSearch step finish [11] [3] table637, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table637 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound638

theorem bound636 : ∀ f ∈ assignSearch step finish [9,11] [3,11] table636, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [3,11] [11] table636 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound637

theorem bound635 : ∀ f ∈ assignSearch step finish [8,9,11] [3,8,11] table635, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [3,8,11] [8] table635 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound636

theorem bound634 : ∀ f ∈ assignSearch step finish [7,8,9,11] [3,5,8,11] table634, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [3,5,8,11] [5] table634 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound635

theorem bound633 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [3,5,7,8,11] table633, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [3,5,7,8,11] [7] table633 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound634

theorem bound632 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [3,4,5,7,8,11] table632, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [3,4,5,7,8,11] [4] table632 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound633

theorem bound631 : ∀ f ∈ assignSearch step finish [3,4,5,7,8,9,11] [1,3,4,5,7,8,11] table631, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [4,5,7,8,9,11] [1,3,4,5,7,8,11] [1,11] table631 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound632
    · exact bound639

theorem bound630 : ∀ f ∈ assignSearch step finish [] [] table630, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound629 : ∀ f ∈ assignSearch step finish [11] [3] table629, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [3] [3] table629 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound630

theorem bound628 : ∀ f ∈ assignSearch step finish [9,11] [2,3] table628, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [11] [2,3] [2] table628 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound629

theorem bound627 : ∀ f ∈ assignSearch step finish [8,9,11] [2,3,11] table627, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,11] [2,3,11] [11] table627 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound628

theorem bound626 : ∀ f ∈ assignSearch step finish [7,8,9,11] [2,3,5,11] table626, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,11] [2,3,5,11] [5] table626 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound627

theorem bound625 : ∀ f ∈ assignSearch step finish [5,7,8,9,11] [2,3,4,5,11] table625, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 5 [7,8,9,11] [2,3,4,5,11] [4] table625 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound626

theorem bound624 : ∀ f ∈ assignSearch step finish [4,5,7,8,9,11] [2,3,4,5,7,11] table624, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 4 [5,7,8,9,11] [2,3,4,5,7,11] [7] table624 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound625
end C13.Enumeration.Template6
