import C13Enumeration.Canonical.Pair28_28.Part003
namespace C13.Enumeration.Canonical.Pair28_28
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound95 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table95, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [11] table95 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound96

theorem bound94 : ∀ f ∈ assignSearch step finish [3,9,10,11] [2,9,10,11] table94, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [2,9,10,11] [2] table94 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound95

theorem bound93 : ∀ f ∈ assignSearch step finish [2,3,9,10,11] [1,2,9,10,11] table93, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,9,10,11] [1,2,9,10,11] [1] table93 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound94

theorem bound92 : ∀ f ∈ assignSearch step finish [1,2,3,9,10,11] [1,2,3,9,10,11] table92, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,9,10,11] [1,2,3,9,10,11] [3] table92 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound93

theorem bound91 : ∀ f ∈ assignSearch step finish [7,1,2,3,9,10,11] [1,2,3,6,9,10,11] table91, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [1,2,3,9,10,11] [1,2,3,6,9,10,11] [6] table91 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound92

theorem bound90 : ∀ f ∈ assignSearch step finish [6,7,1,2,3,9,10,11] [1,2,3,5,6,9,10,11] table90, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,1,2,3,9,10,11] [1,2,3,5,6,9,10,11] [5,6] table90 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound91
    · exact bound99

theorem bound89 : ∀ f ∈ assignSearch step finish [] [] table89, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound88 : ∀ f ∈ assignSearch step finish [11] [9] table88, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [9] [9] table88 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound89

theorem bound87 : ∀ f ∈ assignSearch step finish [10,11] [9,11] table87, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,11] [11] table87 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound88

theorem bound86 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table86, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [10] table86 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound87

theorem bound85 : ∀ f ∈ assignSearch step finish [3,9,10,11] [1,9,10,11] table85, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [1,9,10,11] [1] table85 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound86

theorem bound84 : ∀ f ∈ assignSearch step finish [2,3,9,10,11] [1,3,9,10,11] table84, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,9,10,11] [1,3,9,10,11] [3] table84 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound85

theorem bound83 : ∀ f ∈ assignSearch step finish [1,2,3,9,10,11] [1,2,3,9,10,11] table83, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,9,10,11] [1,2,3,9,10,11] [2] table83 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound84

theorem bound82 : ∀ f ∈ assignSearch step finish [7,1,2,3,9,10,11] [1,2,3,5,9,10,11] table82, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [1,2,3,9,10,11] [1,2,3,5,9,10,11] [5] table82 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound83

theorem bound81 : ∀ f ∈ assignSearch step finish [] [] table81, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound80 : ∀ f ∈ assignSearch step finish [11] [11] table80, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [11] [11] table80 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound81

theorem bound79 : ∀ f ∈ assignSearch step finish [10,11] [9,11] table79, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [9,11] [9] table79 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound80

theorem bound78 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table78, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [10] table78 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound79

theorem bound77 : ∀ f ∈ assignSearch step finish [3,9,10,11] [3,9,10,11] table77, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [3,9,10,11] [3] table77 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound78

theorem bound76 : ∀ f ∈ assignSearch step finish [2,3,9,10,11] [1,3,9,10,11] table76, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,9,10,11] [1,3,9,10,11] [1] table76 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound77

theorem bound75 : ∀ f ∈ assignSearch step finish [1,2,3,9,10,11] [1,2,3,9,10,11] table75, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,9,10,11] [1,2,3,9,10,11] [2] table75 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound76

theorem bound74 : ∀ f ∈ assignSearch step finish [7,1,2,3,9,10,11] [1,2,3,7,9,10,11] table74, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [1,2,3,9,10,11] [1,2,3,7,9,10,11] [7] table74 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound75

theorem bound73 : ∀ f ∈ assignSearch step finish [6,7,1,2,3,9,10,11] [1,2,3,5,7,9,10,11] table73, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,1,2,3,9,10,11] [1,2,3,5,7,9,10,11] [5,7] table73 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound74
    · exact bound82

theorem bound72 : ∀ f ∈ assignSearch step finish [] [] table72, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound71 : ∀ f ∈ assignSearch step finish [11] [10] table71, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table71 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound72

theorem bound70 : ∀ f ∈ assignSearch step finish [10,11] [10,11] table70, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [10,11] [11] table70 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound71

theorem bound69 : ∀ f ∈ assignSearch step finish [9,10,11] [9,10,11] table69, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [9,10,11] [9] table69 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound70

theorem bound68 : ∀ f ∈ assignSearch step finish [3,9,10,11] [2,9,10,11] table68, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [9,10,11] [2,9,10,11] [2] table68 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound69

theorem bound67 : ∀ f ∈ assignSearch step finish [2,3,9,10,11] [2,3,9,10,11] table67, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,9,10,11] [2,3,9,10,11] [3] table67 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound68

theorem bound66 : ∀ f ∈ assignSearch step finish [1,2,3,9,10,11] [1,2,3,9,10,11] table66, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 1 [2,3,9,10,11] [1,2,3,9,10,11] [1] table66 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound67

theorem bound65 : ∀ f ∈ assignSearch step finish [7,1,2,3,9,10,11] [1,2,3,6,9,10,11] table65, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [1,2,3,9,10,11] [1,2,3,6,9,10,11] [6] table65 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound66

theorem bound64 : ∀ f ∈ assignSearch step finish [] [] table64, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel
end C13.Enumeration.Canonical.Pair28_28
