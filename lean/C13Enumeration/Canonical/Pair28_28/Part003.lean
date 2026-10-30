import C13Enumeration.Canonical.Pair28_28.Data
namespace C13.Enumeration.Canonical.Pair28_28
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound106 : ∀ f ∈ assignSearch step finish [] [] table106, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound105 : ∀ f ∈ assignSearch step finish [11] [9] table105, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table105 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound106

theorem bound104 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table104, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [10] table104 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound105

theorem bound103 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table103, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [11] table103 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound104

theorem bound102 : ∀ f ∈ assignSearch step finish [3,9,10,11] [1,9,10,11] table102, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [1,9,10,11] [1] table102 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound103

theorem bound101 : ∀ f ∈ assignSearch step finish [2,3,9,10,11] [1,2,9,10,11] table101, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,9,10,11] [1,2,9,10,11] [2] table101 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound102

theorem bound100 : ∀ f ∈ assignSearch step finish [1,2,3,9,10,11] [1,2,3,9,10,11] table100, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,9,10,11] [1,2,3,9,10,11] [3] table100 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound101

theorem bound99 : ∀ f ∈ assignSearch step finish [7,1,2,3,9,10,11] [1,2,3,5,9,10,11] table99, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [1,2,3,9,10,11] [1,2,3,5,9,10,11] [5] table99 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound100

theorem bound98 : ∀ f ∈ assignSearch step finish [] [] table98, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound97 : ∀ f ∈ assignSearch step finish [11] [10] table97, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table97 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound98

theorem bound96 : ∀ f ∈ assignSearch step finish [10,11] [9,10] table96, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,10] [9] table96 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound97
end C13.Enumeration.Canonical.Pair28_28
