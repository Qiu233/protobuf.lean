module

public import Std

@[expose] public section

@[always_inline]
def _root_.Array.eraseDupsBy {α} (r : α → α → Bool) (as : Array α) : Array α :=
  loop 0 as (Array.emptyWithCapacity as.size) -- TODO: is there a way to *shrink* capacity to size?
where
  @[specialize] loop : Nat → Array α → Array α → Array α := fun i as bs =>
    if h : as.size ≤ i then bs
    else
      let a := as[i]
      match bs.any (r a) with
      | true  => loop (i + 1) as bs
      | false => loop (i + 1) as (bs.push a)

@[specialize, always_inline]
def _root_.Array.eraseDups {α} [BEq α] (as : Array α) : Array α := as.eraseDupsBy (· == ·)

@[specialize, always_inline]
def _root_.Array.groupKeyed {α β} [BEq α] [Hashable α] (xs : Array (α × β))
    : Std.HashMap α (Array β) := runST fun σ => do
  let groups ← ST.mkRef (σ := σ) (∅ : Std.HashMap α (Array β))
  for (k, x) in xs do
    groups.modify fun groups => groups.alter k (some <| ·.getD #[] |>.push x)
  groups.get

@[always_inline]
def _root_.Array.hasDupsBy {α} (r : α → α → Bool) (as : Array α) : Bool := runST fun σ => do
  let bs ← ST.mkRef (σ := σ) #[]
  for a in as do
    if (← bs.get).any (r a) then return false
    bs.modify (fun bs => bs.push a)
  return true

@[always_inline]
def _root_.Array.hasDups {α} [BEq α] (as : Array α) : Bool := as.hasDupsBy (· == ·)

-- @[inline]
-- private def joinLines (xs : Array String) : String := String.intercalate "\n" xs.toList


-- @[specialize]
-- partial def _root_.Array.topoSort {α β} [BEq β] (key : α → β) (nodes : Array α)
--     (deps : α → Array α) : Option (Array α) := runST fun σ => do
--   let assocFindD (k : β) (xs : List (β × Nat)) (d : Nat) : Nat :=
--     (xs.lookup k).getD d
--   let assocFindDArray (k : β) (xs : List (β × Array α)) (d : Array α) : Array α :=
--     (xs.lookup k).getD d
--   let nodeSet : List (β × PUnit) :=
--     nodes.foldl (fun xs n => (key n, ()) :: xs) []
--   let indegRef ← ST.mkRef (σ := σ) (nodes.foldl (fun xs n => (key n, 0) :: xs) [])
--   let adjRef ← ST.mkRef (σ := σ) ([] : List (β × Array α))
--   for n in nodes do
--     for d in deps n do
--       if (nodeSet.lookup (key d)).isSome then
--         adjRef.modify fun adj =>
--           let ds := assocFindDArray (key d) adj #[]
--           (key d, ds.push n) :: adj
--         indegRef.modify fun indeg =>
--           let k := key n
--           let v := assocFindD k indeg 0
--           (k, v + 1) :: indeg
--   let queueRef ← ST.mkRef (σ := σ) (Array.emptyWithCapacity nodes.size)
--   for n in nodes do
--     let indeg ← indegRef.get
--     if assocFindD (key n) indeg 0 == 0 then
--       queueRef.modify (·.push n)
--   let outRef ← ST.mkRef (σ := σ) (Array.emptyWithCapacity nodes.size)
--   let idxRef ← ST.mkRef (σ := σ) 0
--   let rec @[specialize] loop : ST σ Unit := do
--     let idx ← idxRef.get
--     let q ← queueRef.get
--     if h : idx < q.size then
--       let n := q[idx]
--       idxRef.set (idx + 1)
--       outRef.modify (·.push n)
--       let adj := assocFindDArray (key n) (← adjRef.get) #[]
--       for m in adj do
--         let indeg ← indegRef.get
--         let k := key m
--         let v' := assocFindD k indeg 0 - 1
--         indegRef.set ((k, v') :: indeg)
--         if v' == 0 then
--           queueRef.modify (·.push m)
--       loop
--     else
--       pure ()
--   loop
--   let out ← outRef.get
--   if out.size == nodes.size then
--     return some out
--   else
--     return none

-- @[specialize]
-- partial def _root_.Array.topoSortSCC {α β} [Inhabited α] [BEq β] (key : α → β) (nodes : Array α)
--     (deps : α → Array α) : Array (Array α) := runST fun σ => do
--   let assocFindD (k : β) (xs : List (β × Array α)) (d : Array α) : Array α :=
--     (xs.lookup k).getD d
--   let nodeSet : List (β × PUnit) :=
--     nodes.foldl (fun xs n => (key n, ()) :: xs) []
--   let adjRef ← ST.mkRef (σ := σ) ([] : List (β × Array α))
--   let revAdjRef ← ST.mkRef (σ := σ) ([] : List (β × Array α))
--   for n in nodes do
--     for d in deps n do
--       if (nodeSet.lookup (key d)).isSome then
--         adjRef.modify fun adj =>
--           let ds := assocFindD (key n) adj #[]
--           (key n, ds.push d) :: adj
--         revAdjRef.modify fun adj =>
--           let ds := assocFindD (key d) adj #[]
--           (key d, ds.push n) :: adj
--   let visitedRef ← ST.mkRef (σ := σ) ([] : List (β × PUnit))
--   let orderRef ← ST.mkRef (σ := σ) (Array.emptyWithCapacity nodes.size)
--   let rec @[specialize] dfs1 (n : α) : ST σ Unit := do
--     let k := key n
--     let visited ← visitedRef.get
--     if (visited.lookup k).isSome then
--       pure ()
--     else
--       visitedRef.set ((k, ()) :: visited)
--       let adj := assocFindD k (← adjRef.get) #[]
--       for m in adj do
--         dfs1 m
--       orderRef.modify (·.push n)
--   for n in nodes do
--     dfs1 n
--   let visited2Ref ← ST.mkRef (σ := σ) ([] : List (β × PUnit))
--   let compsRef ← ST.mkRef (σ := σ) (Array.emptyWithCapacity nodes.size)
--   let rec @[specialize] dfs2 (n : α) : ST σ (Array α) := do
--     let k := key n
--     let visited2 ← visited2Ref.get
--     if (visited2.lookup k).isSome then
--       return #[]
--     else
--       visited2Ref.set ((k, ()) :: visited2)
--       let mut comp := #[n]
--       let adj := assocFindD k (← revAdjRef.get) #[]
--       for m in adj do
--         let xs ← dfs2 m
--         comp := comp ++ xs
--       return comp
--   let order ← orderRef.get
--   let idxRef ← ST.mkRef (σ := σ) order.size
--   let rec @[specialize] loop : ST σ Unit := do
--     let idx ← idxRef.get
--     if idx > 0 then
--       let idx' := idx - 1
--       idxRef.set idx'
--       let n := order[idx']!
--       let visited2 ← visited2Ref.get
--       if (visited2.lookup (key n)).isSome then
--         loop
--       else
--         let comp ← dfs2 n
--         compsRef.modify (·.push comp)
--         loop
--     else
--       pure ()
--   loop
--   compsRef.get

@[specialize]
partial def _root_.Array.topoSortSCCHash {α} [Inhabited α] [BEq α] [Hashable α] (nodes : Array α)
    (deps : Std.HashMap α (Array α)) : Array (Array α) := runST fun σ => do
  let nodeSet := nodes.foldl (fun m n => m.insert n ()) (∅ : Std.HashMap α PUnit)
  let adjRef ← ST.mkRef (σ := σ) (∅ : Std.HashMap α (Array α))
  let revAdjRef ← ST.mkRef (σ := σ) (∅ : Std.HashMap α (Array α))
  for n in nodes do
    for d in deps[n]?.getD #[] do
      if nodeSet.contains d then
        adjRef.modify fun adj => adj.alter n (some <| ·.getD #[] |>.push d)
        revAdjRef.modify fun adj => adj.alter d (some <| ·.getD #[] |>.push n)
  let visitedRef ← ST.mkRef (σ := σ) (∅ : Std.HashMap α PUnit)
  let orderRef ← ST.mkRef (σ := σ) (Array.emptyWithCapacity nodes.size)
  let rec dfs1 (n : α) : ST σ Unit := do
    if (← visitedRef.get).contains n then
      pure ()
    else
      visitedRef.modify (·.insert n ())
      let adj := (← adjRef.get)[n]?.getD #[]
      for m in adj do
        dfs1 m
      orderRef.modify (·.push n)
  for n in nodes do
    dfs1 n
  let visited2Ref ← ST.mkRef (σ := σ) (∅ : Std.HashMap α PUnit)
  let compsRef ← ST.mkRef (σ := σ) (Array.emptyWithCapacity nodes.size)
  let rec dfs2 (n : α) : ST σ (Array α) := do
    if (← visited2Ref.get).contains n then
      return #[]
    else
      visited2Ref.modify (·.insert n ())
      let mut comp := #[n]
      let adj := (← revAdjRef.get)[n]?.getD #[]
      for m in adj do
        let xs ← dfs2 m
        comp := comp ++ xs
      return comp
  let order ← orderRef.get
  let idxRef ← ST.mkRef (σ := σ) order.size
  let rec loop : ST σ Unit := do
    let idx ← idxRef.get
    if idx > 0 then
      let idx' := idx - 1
      idxRef.set idx'
      let n := order[idx']!
      if (← visited2Ref.get).contains n then
        loop
      else
        let comp ← dfs2 n
        compsRef.modify (·.push comp)
        loop
    else
      pure ()
  loop
  compsRef.get
