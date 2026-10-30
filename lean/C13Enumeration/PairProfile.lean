import C13Enumeration.CrossSearch
namespace C13.Enumeration
open Finset
set_option Elab.async false

/-- A finite profile contains every ambient point, including all zero-degree
columns. Multiset equality forgets labels but retains every incidence count. -/
def matrixVertexProfile (A : Point → Point → Nat) (a : Point) :
    Nat × Multiset (Nat × Nat) :=
  (A a a, (Finset.univ : Finset Point).val.map fun b => (A b b,A a b))

def matrixProfile (A : Point → Point → Nat) :
    Multiset (Nat × Multiset (Nat × Nat)) :=
  (Finset.univ : Finset Point).val.map (matrixVertexProfile A)

def starProfile (S : Family Point) : Multiset (Nat × Multiset (Nat × Nat)) :=
  matrixProfile (coDegree S)

theorem map_univ_multiset_equiv {α : Type*} (f : Point → α) (e : Equiv.Perm Point) :
    (Finset.univ : Finset Point).val.map (fun x => f (e x)) =
      (Finset.univ : Finset Point).val.map f := by
  have h : (Finset.univ : Finset Point).map e.toEmbedding = Finset.univ := by
    ext x
    simp
  have hv := congrArg Finset.val h
  change (Finset.univ : Finset Point).val.map (fun x => e x) =
    (Finset.univ : Finset Point).val at hv
  change (Finset.univ : Finset Point).val.map (f ∘ e) = _
  rw [← Multiset.map_map,hv]

theorem matrixVertexProfile_transport (S T : Family Point) (e : Equiv.Perm Point)
    (he : transport e S = T) (a : Point) :
    matrixVertexProfile (coDegree S) a = matrixVertexProfile (coDegree T) (e a) := by
  apply Prod.ext
  · exact coDegree_transport S T e he a a
  · change (Finset.univ : Finset Point).val.map (fun b => (coDegree S b b,coDegree S a b)) = _
    have hf : (fun b => (coDegree S b b,coDegree S a b)) =
        (fun b => (coDegree T (e b) (e b),coDegree T (e a) (e b))) := by
      funext b
      rw [coDegree_transport S T e he b b,coDegree_transport S T e he a b]
    rw [hf]
    exact map_univ_multiset_equiv (fun b => (coDegree T b b,coDegree T (e a) b)) e

theorem starProfile_transport (S T : Family Point) (e : Equiv.Perm Point)
    (he : transport e S = T) : starProfile S = starProfile T := by
  unfold starProfile matrixProfile
  have hf : matrixVertexProfile (coDegree S) =
      (fun a => matrixVertexProfile (coDegree T) (e a)) :=
    funext (matrixVertexProfile_transport S T e he)
  rw [hf]
  exact map_univ_multiset_equiv (matrixVertexProfile (coDegree T)) e

theorem matrixProfile_eq_starProfile (S : Family Point) (A : Point → Point → Nat)
    (hA : ∀ a b, A a b = coDegree S a b) : matrixProfile A = starProfile S := by
  have h : A = coDegree S := by funext a b; exact hA a b
  rw [h]
  rfl
end C13.Enumeration
