(*
 * OWL - OCaml Scientific and Engineering Computing
 * Copyright (c) 2016-2018 Liang Wang <liang.wang@cl.cam.ac.uk>
 *)


type 'a node = {
  id           : int;            (* unique identifier *)
  mutable name : string;         (* name of the node *)
  mutable prev : 'a node array;  (* parents of the node *)
  mutable next : 'a node array;  (* children of the node *)
  mutable attr : 'a;             (* indicate the validity *)
}

type order = BFS | DFS

type traversal = PreOrder | PostOrder

type dir = Ancestor | Descendant

module NodeHash = struct
  type t = E : 'a node -> t
  let equal (E x) (E y) = x == y
  let hash = function E x -> x.id
end

module NodeHashtbl = Hashtbl.Make(NodeHash)


let () = Random.self_init ()


let id x = x.id


let name x = x.name


let set_name x s = x.name <- s


let parents x = x.prev


let set_parents x parents = x.prev <- parents


let children x = x.next


let set_children x children = x.next <- children


let indegree x = Array.length x.prev


let outdegree x = Array.length x.next


let degree x = Array.(length x.prev + length x.next)


let attr x = x.attr


let set_attr x a = x.attr <- a


let hash x = NodeHash.E x


let node ?id ?(name="") ?(prev=[||]) ?(next=[||]) attr =
  let id = match id with
    | Some i -> i
    | None   -> Random.bits ()
  in
  { id; name; prev; next; attr }


let connect parents children =
  Array.iter (fun parent ->
    parent.next <- Array.append parent.next children;
    Array.iter (fun child ->
      child.prev <- Array.append child.prev parents
    ) children
  ) parents


let connect_descendants parents children =
  Array.iter (fun parent ->
    parent.next <- Array.append parent.next children
  ) parents


let connect_ancestors parents children =
  Array.iter (fun child ->
    child.prev <- Array.append child.prev parents
  ) children


let remove_node x =
  let f = fun y -> y == x in
  Array.iter (fun parent ->
    parent.next <- Owl_utils.Array.filter f parent.next
  ) x.prev;
  Array.iter (fun child ->
    child.prev <- Owl_utils.Array.filter f child.prev
  ) x.next


let remove_edge src dst =
  src.next <- Owl_utils.Array.filter (fun x -> x == dst) src.next;
  dst.prev <- Owl_utils.Array.filter (fun x -> x == src) dst.prev


let replace_child child_0 child_1 =
  Array.iter (fun parent ->
    let next = Array.map (fun v ->
      if v == child_0 then child_1 else v
    ) parent.next
    in
    parent.next <- next;
  ) child_0.prev


let replace_parent parent_0 parent_1 =
  Array.iter (fun child ->
    let prev = Array.map (fun v ->
      if v == parent_0 then parent_1 else v
    ) child.prev
    in
    child.prev <- prev;
  ) parent_0.next


(* depth-first search from [x]; [f : node -> unit] is applied to each node;
   [next node -> node array] returns the next set of nodes to iterate;
*)
let dfs_iter traversal f x next =
  let h = NodeHashtbl.create 512 in
  let rec _dfs_iter y =
    if not (NodeHashtbl.mem h (hash y)) then (
      NodeHashtbl.add h (hash y) None;
      update y;
    )
  and relax y =
    Array.iter (fun z -> _dfs_iter z) (next y)
  and update y = match traversal with
    | PreOrder -> f y; relax y
    | PostOrder -> relax y; f y
  in
  Array.iter _dfs_iter x


(* breadth-first search from [x]; [f : node -> unit] is applied to each node;
   [next node -> node array] returns the next set of nodes to iterate.
*)
let bfs_iter traversal f x next =
  match traversal with
  | PostOrder -> Owl_log.warn "PostOrder BFS not implemented. PreOrder is used."
  | PreOrder  -> ();
  let h = NodeHashtbl.create 512 in
  let q = Queue.create () in
  let relax y =
    Array.iter (fun z ->
      if not (NodeHashtbl.mem h (hash z)) then (
        NodeHashtbl.add h (hash z) None;
        Queue.push z q
      )
    ) (next y)
  in
  let update y = f y; relax y in

  Array.iter (fun y -> Queue.push y q) x;
  Array.iter (fun y -> NodeHashtbl.add h (hash y) None) x;
  while not (Queue.is_empty q) do
    let y = Queue.pop q in
    update y
  done


let iter_ancestors ?(order=DFS) ?(traversal=PreOrder) f x =
  match order with
  | BFS -> bfs_iter traversal f x parents
  | DFS -> dfs_iter traversal f x parents


let iter_descendants ?(order=DFS) ?(traversal=PreOrder) f x =
  match order with
  | BFS -> bfs_iter traversal f x children
  | DFS -> dfs_iter traversal f x children


let _iter ?(dir=Ancestor) ?order ?traversal f x =
  match dir with
  | Ancestor   -> iter_ancestors ?order ?traversal f x
  | Descendant -> iter_descendants ?order ?traversal f x


let filter_ancestors f x =
  let s = Owl_utils.Stack.make () in
  iter_ancestors (fun n -> if f n then Owl_utils.Stack.push s n) x;
  Owl_utils.Stack.to_array s


let filter_descendants f x =
  let s = Owl_utils.Stack.make () in
  iter_descendants (fun n -> if f n then Owl_utils.Stack.push s n) x;
  Owl_utils.Stack.to_array s


let fold_ancestors f a x =
  let a = ref a in
  iter_ancestors (fun b -> a := f !a b) x;
  !a


let fold_descendants f a x =
  let a = ref a in
  iter_descendants (fun b -> a := f !a b) x;
  !a


let iter_in_edges ?order f x =
  iter_ancestors ?order (fun dst ->
    Array.iter (fun src -> f src dst) dst.prev
  ) x


let iter_out_edges ?order f x =
  iter_descendants ?order (fun src ->
    Array.iter (fun dst -> f src dst) src.next
  ) x


let fold_in_edges f a x =
  let a = ref a in
  iter_in_edges (fun b c -> a := f !a b c) x;
  !a


let fold_out_edges f a x =
  let a = ref a in
  iter_out_edges (fun b c -> a := f !a b c) x;
  !a


(* TODO *)
let _map _f _x = None


(* TODO: optimise *)
let copy ?(dir=Ancestor) x =
  let _make_if_not_exists h n =
    if NodeHashtbl.mem h (hash n) then NodeHashtbl.find h (hash n)
    else (
      let n' = node ~id:n.id ~name:n.name ~prev:[||] ~next:[||] n.attr in
      NodeHashtbl.add h (hash n) n';
      n'
    )
  in
  let h = NodeHashtbl.create 128 in
  let _copy src dst =
    let src' = _make_if_not_exists h src in
    let dst' = _make_if_not_exists h dst in
    connect [|src'|] [|dst'|]
  in
  let _ = match dir with
    | Ancestor   -> iter_in_edges _copy x
    | Descendant -> iter_out_edges _copy x
  in
  Array.map (fun n -> NodeHashtbl.find h (hash n)) x


(* TODO *)
let _to_array = None

(* TODO *)
let _to_hashtbl = None


let num_ancestor x =
  let n = ref 0 in
  iter_ancestors (fun _ -> n := !n + 1) x;
  !n


let num_descendant x =
  let n = ref 0 in
  iter_descendants (fun _ -> n := !n + 1) x;
  !n


let length x = (num_ancestor x) + (num_descendant x) - (Array.length x)


let node_to_str x =
  Printf.sprintf "[ #%i %s in:%i out:%i ]" x.id x.name (indegree x) (outdegree x)


let pp_node formatter x =
  Format.open_box 0;
  Format.fprintf formatter "%s" (node_to_str x);
  Format.close_box ()


let to_string from_root x =
  let s = ref "" in
  let iter_fun = if from_root then iter_out_edges else iter_in_edges in
  iter_fun (fun u v -> s := Printf.sprintf "%s%i -> %i\n" !s u.id v.id) x;
  !s


let topo_sort nodes =
  let s = Owl_utils.Stack.make () in
  let f u = Owl_utils.Stack.push s u in
  iter_ancestors ~order:DFS ~traversal:PostOrder f nodes;
  Owl_utils_stack.to_array s


(* ends here *)
