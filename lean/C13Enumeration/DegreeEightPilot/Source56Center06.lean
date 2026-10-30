import C13Enumeration.DegreeEightPilot.Data
namespace C13.Enumeration.DegreeEightPilot.Source56Center06
open C13.SourceData C13.Checker.RawSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def valuesA : Array Nat := #[5,1,1,1,2,2,0,2,2,3,4,2,0,1,3,1,1,1,1,0,1,1,1,1,3,0,1,1,3,1,1,1,0,1,3,1,1,1,0,1,1,1,3,1,1,0,1,1,3,1,1,0,2,1,1,1,3,1,0,1,1,2,1,1,0,2,1,1,1,1,3,0,1,1,2,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,1,1,1,1,1,0,3,1,2,1,1,0,2,1,3,1,1,1,0,1,4,2,2,2,0,3,1,1,3,2,2,0,2,2,5,2,2,0,4,1,1,1,1,1,0,1,2,2,4,2,0,2,3,1,1,1,1,0,1,2,2,2,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def matrixA (a b : Point) : Nat := valuesA.getD (13*a.val+b.val) 0
theorem matrixA_checked : ∀ a b, matrixA a b = coDegree (link link56 6) a b := by decide +kernel

def maps : List (Point → Point) := []
def step := starStep (link link56 6) (link link01 4) matrixA matrix
def finish := crossMapFinish link56 link01 hole 6 4
def table0 : Point → Point := anchorTable hole hole 4
def table1 : Point → Point := put table0 0 0
def table2 : Point → Point := put table1 9 1
def table3 : Point → Point := put table2 8 2
def table4 : Point → Point := put table2 8 3
def table5 : Point → Point := put table0 0 1
def table6 : Point → Point := put table5 9 0
def table7 : Point → Point := put table6 8 2
def table8 : Point → Point := put table6 8 3

theorem bound8 : ∀ f ∈ assignSearch step finish [10,11,1,2,3,4,5,7] [2,5,6,7,8,9,10,11] table8, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,1,2,3,4,5,7] [2,5,6,7,8,9,10,11] [] table8 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound7 : ∀ f ∈ assignSearch step finish [10,11,1,2,3,4,5,7] [3,5,6,7,8,9,10,11] table7, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,1,2,3,4,5,7] [3,5,6,7,8,9,10,11] [] table7 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound6 : ∀ f ∈ assignSearch step finish [8,10,11,1,2,3,4,5,7] [2,3,5,6,7,8,9,10,11] table6, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [10,11,1,2,3,4,5,7] [2,3,5,6,7,8,9,10,11] [2,3] table6 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound7
    · exact bound8

theorem bound5 : ∀ f ∈ assignSearch step finish [9,8,10,11,1,2,3,4,5,7] [0,2,3,5,6,7,8,9,10,11] table5, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [8,10,11,1,2,3,4,5,7] [0,2,3,5,6,7,8,9,10,11] [0] table5 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound6

theorem bound4 : ∀ f ∈ assignSearch step finish [10,11,1,2,3,4,5,7] [2,5,6,7,8,9,10,11] table4, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,1,2,3,4,5,7] [2,5,6,7,8,9,10,11] [] table4 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound3 : ∀ f ∈ assignSearch step finish [10,11,1,2,3,4,5,7] [3,5,6,7,8,9,10,11] table3, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 10 [11,1,2,3,4,5,7] [3,5,6,7,8,9,10,11] [] table3 ?_ ?_
  · decide +kernel
  · intro y hy
    simp at hy

theorem bound2 : ∀ f ∈ assignSearch step finish [8,10,11,1,2,3,4,5,7] [2,3,5,6,7,8,9,10,11] table2, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 8 [10,11,1,2,3,4,5,7] [2,3,5,6,7,8,9,10,11] [2,3] table2 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound3
    · exact bound4

theorem bound1 : ∀ f ∈ assignSearch step finish [9,8,10,11,1,2,3,4,5,7] [1,2,3,5,6,7,8,9,10,11] table1, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 9 [8,10,11,1,2,3,4,5,7] [1,2,3,5,6,7,8,9,10,11] [1] table1 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl
    exact bound2

theorem bound0 : ∀ f ∈ assignSearch step finish [0,9,8,10,11,1,2,3,4,5,7] [0,1,2,3,5,6,7,8,9,10,11] table0, f ∈ maps := by
  refine assignSearch_map_bound_cons (R := fun f => f ∈ maps) step finish 0 [9,8,10,11,1,2,3,4,5,7] [0,1,2,3,5,6,7,8,9,10,11] [0,1] table0 ?_ ?_
  · decide +kernel
  · intro y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact bound1
    · exact bound5

theorem complete_maps (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (6 : Point) = hole)
    (hs : transport e (link link56 6) = link link01 4) : (e : Point → Point) ∈ maps := by
  exact cross_star_maps_complete link56 link01 hole 6 4 [0,9,8,10,11,1,2,3,4,5,7]
    (by decide +kernel) (by decide +kernel) matrixA matrix matrixA_checked matrix_checked maps bound0 e he hc hs

def pick : Fin maps.length → table.Index := fun i => Fin.elim0 (show Fin 0 from i)

theorem rows_checked : ∀ i : Fin maps.length,
    (codedDomain.pencil (table.row (pick i))).toFinset =
      (codedEmit RawClass9.CatalogCodes.codes56 6 4 (fun x => maps.get i ((Equiv.refl Point) x))).toFinset := by
  decide +kernel

theorem complete (e : Equiv.Perm Point) (he : e hole = 4) (hc : e (6 : Point) = hole)
    (hs : transport e (link link56 6) = link link01 4) :
    ∃ p ∈ codedDomain.supported.domain.2, RepresentsPencil p (emitPencil link56 6 4 e) := by
  exact mapsRepresented_of_code_checks codedDomain table RawClass9.CatalogCodes.codes56
    link56 RawClass9.CatalogCodes.checked56 6 4 (Equiv.refl Point) maps pick rows_checked
    e (complete_maps e he hc hs)
end C13.Enumeration.DegreeEightPilot.Source56Center06
