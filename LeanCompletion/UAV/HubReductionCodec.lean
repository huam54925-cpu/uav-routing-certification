import LeanCompletion.UAV.HubGammaCodec

/-! EOF source and sparse-target formats. Shape checks are independent of the
three-partition promises. Counts are checked against actual decoded fields
before splitting any arrays. -/
namespace UAVProof.HubReductionCodec
open HubGammaCodec

structure Source where
  m : ℕ
  budget : ℕ
  items : List ℕ
  deriving DecidableEq, Repr

def SourceShape (s : Source) : Prop := s.items.length = 3 * s.m
instance (s : Source) : Decidable (SourceShape s) := inferInstanceAs (Decidable (_ = _))

def sourceFields (s : Source) : List ℕ := s.m :: s.budget :: s.items
def encodeSource (s : Source) : Bits := encodeAll (sourceFields s)

def sourceFromFields : List ℕ → Option Source
  | m :: b :: a => if a.length = 3*m then some ⟨m,b,a⟩ else none
  | _ => none

def decodeSource (x : Bits) : Option Source := decodeAll x >>= sourceFromFields

theorem sourceFromFields_iff (q : List ℕ) (s : Source) :
    sourceFromFields q = some s ↔ SourceShape s ∧ q = sourceFields s := by
  cases q with
  | nil => simp [sourceFromFields, sourceFields]
  | cons m q =>
    cases q with
    | nil => simp [sourceFromFields, sourceFields]
    | cons b a =>
      cases s
      by_cases ha : a.length = 3*m <;>
        simp [sourceFromFields, SourceShape, sourceFields, ha] <;> aesop

theorem decodeSource_eq_some_iff (x : Bits) (s : Source) :
    decodeSource x = some s ↔ SourceShape s ∧ x = encodeSource s := by
  simp only [decodeSource, Option.bind_eq_bind', Option.bind_eq_some_iff, sourceFromFields_iff,
    decodeAll_eq_some_iff, encodeSource]
  aesop

@[simp] theorem decodeSource_encode (s : Source) (h : SourceShape s) :
    decodeSource (encodeSource s) = some s :=
  (decodeSource_eq_some_iff _ _).2 ⟨h,rfl⟩

theorem encodeSource_injective : Function.Injective encodeSource := by
  intro s t h
  have := encodeAll_injective h
  cases s; cases t
  simpa [sourceFields] using this

structure Target where
  n : ℕ
  routes : ℕ
  budget : ℕ
  edges : List (ℕ × ℕ)
  demands : List ℕ
  costs : List ℕ
  deriving DecidableEq, Repr

def TargetWellFormed (t : Target) : Prop :=
  1 ≤ t.n ∧ t.edges.length = t.n-1 ∧ t.demands.length = t.n ∧
  t.costs.length = t.n ∧ ∀ i : Fin t.edges.length, (t.edges.get i).1 < i.val+1

instance (t : Target) : Decidable (TargetWellFormed t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def edgeFields (es : List (ℕ × ℕ)) : List ℕ := es.flatMap (fun p => [p.1,p.2])

def pairUp : List ℕ → List (ℕ × ℕ)
  | p :: h :: xs => (p,h) :: pairUp xs
  | _ => []

@[simp] theorem edgeFields_length (es : List (ℕ × ℕ)) :
    (edgeFields es).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons p es ih => simp [edgeFields]; omega

@[simp] theorem pairUp_edgeFields (es : List (ℕ × ℕ)) :
    pairUp (edgeFields es) = es := by
  induction es with
  | nil => rfl
  | cons p es ih => simpa [edgeFields, pairUp] using congrArg (p :: ·) ih

def targetFields (t : Target) : List ℕ :=
  t.n :: t.routes :: t.budget :: (edgeFields t.edges ++ t.demands ++ t.costs)

def encodeTarget (t : Target) : Bits := encodeAll (targetFields t)

def targetFromFields : List ℕ → Option Target
  | n :: m :: b :: q =>
    if 1 ≤ n ∧ q.length = 4*n-2 then
      let t := Target.mk n m b (pairUp (q.take (2*(n-1))))
        ((q.drop (2*(n-1))).take n) (q.drop (2*(n-1)+n))
      if TargetWellFormed t ∧ targetFields t = n::m::b::q then some t else none
    else none
  | _ => none

def decodeTarget (x : Bits) : Option Target := decodeAll x >>= targetFromFields

theorem targetFields_length (t : Target) (h : TargetWellFormed t) :
    (targetFields t).length = 4*t.n+1 := by
  simp only [targetFields, List.length_cons, List.length_append, edgeFields_length]
  rcases h with ⟨hn,he,hd,hc,_⟩
  omega

theorem targetFromFields_encode (t : Target) (h : TargetWellFormed t) :
    targetFromFields (targetFields t) = some t := by
  have hn := h.1
  have he := h.2.1
  have hd := h.2.2.1
  have hc := h.2.2.2.1
  have hq : (edgeFields t.edges ++ t.demands ++ t.costs).length = 4*t.n-2 := by
    simp only [List.length_append, edgeFields_length]; omega
  have he' : 2*(t.n-1) = (edgeFields t.edges).length := by simp [he]
  have hd' : t.n = t.demands.length := hd.symm
  have hre : Target.mk t.n t.routes t.budget t.edges t.demands t.costs = t := by cases t; rfl
  have hp : (edgeFields t.edges ++ t.demands ++ t.costs).take (2*(t.n-1)) =
      edgeFields t.edges := by rw [he', List.append_assoc]; simp
  have hdrop : (edgeFields t.edges ++ t.demands ++ t.costs).drop (2*(t.n-1)) =
      t.demands ++ t.costs := by rw [he', List.append_assoc]; simp
  have hcost : (edgeFields t.edges ++ t.demands ++ t.costs).drop (2*(t.n-1)+t.n) =
      t.costs := by rw [← List.drop_drop, hdrop, hd']; simp
  change targetFromFields (t.n :: t.routes :: t.budget ::
    (edgeFields t.edges ++ t.demands ++ t.costs)) = some t
  rw [targetFromFields, if_pos ⟨hn,hq⟩]
  dsimp only
  rw [hp, pairUp_edgeFields, hdrop, hcost]
  have htake : (t.demands ++ t.costs).take t.n = t.demands := by rw [hd']; simp
  rw [htake, hre, if_pos ⟨h,rfl⟩]

theorem targetFromFields_sound (q : List ℕ) (t : Target)
    (h : targetFromFields q = some t) : TargetWellFormed t ∧ q = targetFields t := by
  unfold targetFromFields at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  dsimp only at h
  split at h <;> try contradiction
  rename_i ht
  cases h
  exact ⟨ht.1,ht.2.symm⟩

theorem targetFromFields_iff (q : List ℕ) (t : Target) :
    targetFromFields q = some t ↔ TargetWellFormed t ∧ q = targetFields t := by
  exact ⟨targetFromFields_sound q t, fun ⟨h,hq⟩ => hq ▸ targetFromFields_encode t h⟩

theorem decodeTarget_eq_some_iff (x : Bits) (t : Target) :
    decodeTarget x = some t ↔ TargetWellFormed t ∧ x = encodeTarget t := by
  simp only [decodeTarget, Option.bind_eq_bind', Option.bind_eq_some_iff, targetFromFields_iff,
    decodeAll_eq_some_iff, encodeTarget]
  aesop

@[simp] theorem decodeTarget_encode (t : Target) (h : TargetWellFormed t) :
    decodeTarget (encodeTarget t) = some t :=
  (decodeTarget_eq_some_iff _ _).2 ⟨h,rfl⟩

theorem encodeTarget_injective (s t : Target)
    (hs : TargetWellFormed s) (ht : TargetWellFormed t)
    (h : encodeTarget s = encodeTarget t) : s = t := by
  have := congrArg decodeTarget h
  simpa [hs,ht] using this

theorem target_count_le_length (t : Target) (h : TargetWellFormed t) :
    4*t.n+1 ≤ (encodeTarget t).length := by
  rw [← targetFields_length t h]
  exact encodeAll_count_le _

theorem source_prefix_free (s t : Source) (hs : SourceShape s) (ht : SourceShape t)
    (r : Bits) (h : encodeSource s ++ r = encodeSource t) : s = t ∧ r = [] := by
  obtain ⟨hm,h1⟩ := encodeAll_prefix_head s.m t.m _ _ r h
  obtain ⟨hb,h2⟩ := encodeAll_prefix_head s.budget t.budget _ _ r h1
  have hc : s.items.length = t.items.length := by unfold SourceShape at *; omega
  obtain ⟨ha,hr⟩ := encodeAll_prefix_same_count _ _ r hc h2
  exact ⟨by cases s; cases t; simp_all, hr⟩

theorem target_prefix_free (s t : Target) (hs : TargetWellFormed s)
    (ht : TargetWellFormed t) (r : Bits)
    (h : encodeTarget s ++ r = encodeTarget t) : s = t ∧ r = [] := by
  obtain ⟨hn,_⟩ := encodeAll_prefix_head s.n t.n _ _ r h
  have hc : (targetFields s).length = (targetFields t).length := by
    rw [targetFields_length s hs, targetFields_length t ht, hn]
  obtain ⟨hf,hr⟩ := encodeAll_prefix_same_count _ _ r hc h
  exact ⟨encodeTarget_injective s t hs ht (congrArg encodeAll hf),hr⟩

theorem decodeSource_rejects_trailing (s : Source) (h : SourceShape s)
    (r : Bits) (hr : r ≠ []) : decodeSource (encodeSource s ++ r) = none := by
  cases hd : decodeSource (encodeSource s ++ r) with
  | none => rfl
  | some t =>
    obtain ⟨ht,he⟩ := (decodeSource_eq_some_iff _ _).1 hd
    exact (hr (source_prefix_free s t h ht r he).2).elim

theorem decodeTarget_rejects_trailing (t : Target) (h : TargetWellFormed t)
    (r : Bits) (hr : r ≠ []) : decodeTarget (encodeTarget t ++ r) = none := by
  cases hd : decodeTarget (encodeTarget t ++ r) with
  | none => rfl
  | some s =>
    obtain ⟨hs,he⟩ := (decodeTarget_eq_some_iff _ _).1 hd
    exact (hr (target_prefix_free t s h hs r he).2).elim

end UAVProof.HubReductionCodec
