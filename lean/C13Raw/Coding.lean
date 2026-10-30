import C13Raw.BlockSupport
namespace C13.Checker.RawSupport

abbrev Code := BitVec 13
abbrev CodePencil := List Code

def decode (c : Code) : Block := (Finset.range 13).filter fun p => c.getLsbD p = true

def incident (c : Code) (p : Nat) : Bool := decide (p < 13) && c.getLsbD p

theorem mem_decode (c : Code) (p : Nat) : p ∈ decode c ↔ incident c p = true := by
  simp [decode, incident]

theorem decode_injective : Function.Injective decode := by
  intro a b hab
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  have h : a.getLsbD p = true ↔ b.getLsbD p = true := by
    simpa [decode, hp] using (Finset.ext_iff.mp hab p)
  cases ha : a.getLsbD p <;> cases hb : b.getLsbD p <;> simp_all

def decodePencil (p : CodePencil) : Pencil := p.map decode

def decodeDomain (d : Nat × List CodePencil) : Domain := (d.1,d.2.map decodePencil)

def decodeDomains (ds : List (Nat × List CodePencil)) : List Domain := ds.map decodeDomain

/-- Every raw pencil is built from indices into its explicit possible-block
alphabet. Its overapproximation proof follows from typing, not a producer claim. -/
structure CodedDomain where
  point : Nat
  alphabet : List Code
  rows : List (List (Fin alphabet.length))

def CodedDomain.pencil (d : CodedDomain) (r : List (Fin d.alphabet.length)) : CodePencil :=
  r.map fun i => d.alphabet[i]

def CodedDomain.codes (d : CodedDomain) : Nat × List CodePencil :=
  (d.point, d.rows.map d.pencil)

def CodedDomain.supported (d : CodedDomain) : SupportedDomain where
  domain := decodeDomain d.codes
  possible := d.alphabet.toFinset.image decode
  covers := by
    intro p hp b hb
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    exact Finset.mem_image.mpr ⟨d.alphabet[i],List.mem_toFinset.mpr (List.getElem_mem _),rfl⟩

def codedKeep (ds : List CodedDomain) (q : Nat) (p : CodePencil) : Bool :=
  ds.all fun d => if q = d.point then true else
    p.all fun c => !incident c d.point || d.alphabet.contains c

def codedStep (ds : List CodedDomain) : List (Nat × List CodePencil) :=
  ds.map fun d => (d.point, d.codes.2.filter (codedKeep ds d.point))


theorem decode_mem_image (s : Finset Code) (c : Code) :
    decode c ∈ s.image decode ↔ c ∈ s := by
  constructor
  · intro h
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp h
    simpa [decode_injective he] using hb
  · intro h
    exact Finset.mem_image.mpr ⟨c,h,rfl⟩

/-- Literal decoding connects the fast Boolean block test to physical support. -/
theorem codedKeep_eq_supportKeep (ds : List CodedDomain) (q : Nat) (p : CodePencil) :
    codedKeep ds q p = supportKeep (ds.map CodedDomain.supported) q (decodePencil p) := by
  unfold codedKeep supportKeep
  rw [List.all_map]
  apply congrArg (fun f : CodedDomain → Bool => ds.all f)
  funext d
  change (if q = d.point then true else p.all (fun c => !incident c d.point || d.alphabet.contains c)) =
    (if q = d.point then true else (p.map decode).all
      (fun b => decide (d.point ∈ b → b ∈ d.alphabet.toFinset.image decode)))
  by_cases hq : q = d.point
  · simp [hq]
  · simp only [hq, ↓reduceIte, List.all_map]
    apply congrArg (fun f : Code → Bool => p.all f)
    funext c
    apply Bool.eq_iff_iff.mpr
    cases hi : incident c d.point <;>
      simp [hi, mem_decode, decode_injective.eq_iff, List.mem_toFinset]

theorem supportStep_coded (ds : List CodedDomain) :
    supportStep (ds.map CodedDomain.supported) = decodeDomains (codedStep ds) := by
  unfold supportStep decodeDomains codedStep
  simp only [List.map_map]
  apply congrArg (fun f : CodedDomain → Domain => ds.map f)
  funext d
  apply Prod.ext
  · rfl
  · change ((d.codes.2).map decodePencil).filter
        (supportKeep (ds.map CodedDomain.supported) d.point) =
      ((d.codes.2).filter (codedKeep ds d.point)).map decodePencil
    rw [List.filter_map]
    apply congrArg (List.map decodePencil)
    apply congrArg (fun f : CodePencil → Bool => d.codes.2.filter f)
    funext p
    exact (codedKeep_eq_supportKeep ds d.point p).symm

/-- A concrete finite-coded certificate still concludes a theorem about the
original literal physical HasJoin relation. -/
theorem hasJoin_survives_coded {budget : Nat} {ds : List CodedDomain}
    (labels : ((domains (ds.map CodedDomain.supported)).map Prod.fst).Nodup)
    (h : HasJoin budget (domains (ds.map CodedDomain.supported)) []) :
    HasJoin budget (decodeDomains (codedStep ds)) [] := by
  rw [← supportStep_coded]
  exact hasJoin_survives_support labels h

def expandRows (alphabet : List Code) (rows : List (List (Fin alphabet.length))) : List CodePencil :=
  rows.map fun row => row.map fun i => alphabet[i]

def filterRows (ds : List CodedDomain) (q : Nat) (alphabet : List Code)
    (rows : List (List (Fin alphabet.length))) : List CodePencil :=
  (expandRows alphabet rows).filter (codedKeep ds q)

theorem filterRows_append (ds : List CodedDomain) (q : Nat) (alphabet : List Code)
    (a b : List (List (Fin alphabet.length))) :
    filterRows ds q alphabet (a ++ b) = filterRows ds q alphabet a ++ filterRows ds q alphabet b := by
  simp [filterRows, expandRows, List.map_append, List.filter_append]

@[simp] theorem filterRows_nil (ds : List CodedDomain) (q : Nat) (alphabet : List Code) :
    filterRows ds q alphabet [] = [] := rfl

@[simp] theorem decode_domains_eq (ds : List CodedDomain) :
    decodeDomains (ds.map CodedDomain.codes) = domains (ds.map CodedDomain.supported) := by
  simp [decodeDomains, domains, List.map_map, Function.comp_def, CodedDomain.supported]

theorem filterRows_flatten (ds : List CodedDomain) (q : Nat) (alphabet : List Code)
    (chunks : List (List (List (Fin alphabet.length)))) :
    filterRows ds q alphabet chunks.flatten = (chunks.map (filterRows ds q alphabet)).flatten := by
  induction chunks with
  | nil => rfl
  | cons c cs ih =>
    simpa only [List.flatten_cons, List.map_cons, filterRows_append] using
      congrArg (fun t => filterRows ds q alphabet c ++ t) ih

end C13.Checker.RawSupport
