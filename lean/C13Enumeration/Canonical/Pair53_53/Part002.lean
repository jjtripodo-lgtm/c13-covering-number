import C13Enumeration.Canonical.Pair53_53.Data
namespace C13.Enumeration.Canonical.Pair53_53
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound83 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [0,1,2,3,5,6,7] table83, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [0,1,2,3,5,6,7] [] table83 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound82 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [1,2,3,4,5,6,7] table82, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [1,2,3,4,5,6,7] [] table82 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound81 : ∀ f ∈ assignSearch step finish [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] table81, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] [0,4] table81 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound82
    · exact bound83

theorem bound80 : ∀ f ∈ assignSearch step finish [11,0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,9] table80, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,9] [9] table80 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound81

theorem bound79 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [0,1,2,3,5,6,7] table79, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [0,1,2,3,5,6,7] [] table79 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound78 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [1,2,3,4,5,6,7] table78, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [1,2,3,4,5,6,7] [] table78 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound77 : ∀ f ∈ assignSearch step finish [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] table77, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] [0,4] table77 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound78
    · exact bound79

theorem bound76 : ∀ f ∈ assignSearch step finish [11,0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,10] table76, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,10] [10] table76 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound77

theorem bound75 : ∀ f ∈ assignSearch step finish [10,11,0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,9,10] table75, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,9,10] [9,10] table75 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound76
    · exact bound80

theorem bound74 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [0,1,2,3,5,6,7] table74, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [0,1,2,3,5,6,7] [] table74 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound73 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [1,2,3,4,5,6,7] table73, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [1,2,3,4,5,6,7] [] table73 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound72 : ∀ f ∈ assignSearch step finish [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] table72, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] [0,4] table72 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound73
    · exact bound74

theorem bound71 : ∀ f ∈ assignSearch step finish [11,0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,9] table71, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,9] [9] table71 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound72

theorem bound70 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [0,1,2,3,5,6,7] table70, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [0,1,2,3,5,6,7] [] table70 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound69 : ∀ f ∈ assignSearch step finish [1,4,5,2,3,6,7] [1,2,3,4,5,6,7] table69, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [4,5,2,3,6,7] [1,2,3,4,5,6,7] [] table69 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound68 : ∀ f ∈ assignSearch step finish [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] table68, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7] [0,4] table68 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound69
    · exact bound70

theorem bound67 : ∀ f ∈ assignSearch step finish [11,0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,11] table67, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,11] [11] table67 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound68

theorem bound66 : ∀ f ∈ assignSearch step finish [10,11,0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,9,11] table66, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,0,1,4,5,2,3,6,7] [0,1,2,3,4,5,6,7,9,11] [9,11] table66 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound67
    · exact bound71

theorem bound65 : ∀ f ∈ assignSearch step finish [] [] table65, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound64 : ∀ f ∈ assignSearch step finish [7] [2] table64, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [] [2] [2] table64 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound65
end C13.Enumeration.Canonical.Pair53_53
