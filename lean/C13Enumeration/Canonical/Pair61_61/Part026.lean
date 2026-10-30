import C13Enumeration.Canonical.Pair61_61.Part027
namespace C13.Enumeration.Canonical.Pair61_61
open C13.SourceData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem bound863 : ∀ f ∈ assignSearch step finish [9,10,11] [1,6,9] table863, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,6,9] [6] table863 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound864

theorem bound862 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,6,9,10] table862, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,6,9,10] [10] table862 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound863

theorem bound861 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,6,9,10] table861, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,6,9,10] [0] table861 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound862

theorem bound860 : ∀ f ∈ assignSearch step finish [] [] table860, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound859 : ∀ f ∈ assignSearch step finish [11] [10] table859, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [10] [10] table859 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound860

theorem bound858 : ∀ f ∈ assignSearch step finish [10,11] [0,10] table858, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,10] [0] table858 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound859

theorem bound857 : ∀ f ∈ assignSearch step finish [9,10,11] [0,7,10] table857, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,7,10] [7] table857 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound858

theorem bound856 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,7,9,10] table856, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,7,9,10] [9] table856 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound857

theorem bound855 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,1,7,9,10] table855, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,1,7,9,10] [1] table855 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound856

theorem bound854 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,1,6,7,9,10] table854, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,1,6,7,9,10] [6,7] table854 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound855
    · exact bound861

theorem bound853 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,1,2,6,7,9,10] table853, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,1,2,6,7,9,10] [2] table853 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound854

theorem bound852 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,1,2,6,7,8,9,10] table852, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,1,2,6,7,8,9,10] [8] table852 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound853

theorem bound851 : ∀ f ∈ assignSearch step finish [] [] table851, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound850 : ∀ f ∈ assignSearch step finish [11] [0] table850, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [0] [0] table850 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound851

theorem bound849 : ∀ f ∈ assignSearch step finish [10,11] [0,10] table849, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [0,10] [10] table849 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound850

theorem bound848 : ∀ f ∈ assignSearch step finish [9,10,11] [0,2,10] table848, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [0,2,10] [2] table848 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound849

theorem bound847 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,2,8,10] table847, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,2,8,10] [8] table847 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound848

theorem bound846 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,2,3,8,10] table846, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,2,3,8,10] [3] table846 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound847

theorem bound845 : ∀ f ∈ assignSearch step finish [] [] table845, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound844 : ∀ f ∈ assignSearch step finish [11] [8] table844, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [8] [8] table844 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound845

theorem bound843 : ∀ f ∈ assignSearch step finish [10,11] [3,8] table843, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [3,8] [3] table843 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound844

theorem bound842 : ∀ f ∈ assignSearch step finish [9,10,11] [3,6,8] table842, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [3,6,8] [6] table842 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound843

theorem bound841 : ∀ f ∈ assignSearch step finish [8,9,10,11] [0,3,6,8] table841, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [0,3,6,8] [0] table841 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound842

theorem bound840 : ∀ f ∈ assignSearch step finish [7,8,9,10,11] [0,3,6,8,10] table840, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 7 [8,9,10,11] [0,3,6,8,10] [10] table840 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound841

theorem bound839 : ∀ f ∈ assignSearch step finish [6,7,8,9,10,11] [0,2,3,6,8,10] table839, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 6 [7,8,9,10,11] [0,2,3,6,8,10] [2,6] table839 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound840
    · exact bound846

theorem bound838 : ∀ f ∈ assignSearch step finish [3,6,7,8,9,10,11] [0,2,3,6,7,8,10] table838, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 3 [6,7,8,9,10,11] [0,2,3,6,7,8,10] [7] table838 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound839

theorem bound837 : ∀ f ∈ assignSearch step finish [2,3,6,7,8,9,10,11] [0,2,3,6,7,8,9,10] table837, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 2 [3,6,7,8,9,10,11] [0,2,3,6,7,8,9,10] [9] table837 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound838

theorem bound836 : ∀ f ∈ assignSearch step finish [] [] table836, f ∈ maps := by
  apply list_all_maps_bound
  decide +kernel

theorem bound835 : ∀ f ∈ assignSearch step finish [11] [1] table835, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 11 [] [1] [1] table835 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound836

theorem bound834 : ∀ f ∈ assignSearch step finish [10,11] [1,9] table834, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11] [1,9] [9] table834 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound835

theorem bound833 : ∀ f ∈ assignSearch step finish [9,10,11] [1,2,9] table833, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [10,11] [1,2,9] [2] table833 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound834

theorem bound832 : ∀ f ∈ assignSearch step finish [8,9,10,11] [1,2,8,9] table832, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [9,10,11] [1,2,8,9] [8] table832 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound833
end C13.Enumeration.Canonical.Pair61_61
