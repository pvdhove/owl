(*
 * OWL - OCaml Scientific and Engineering Computing
 * Copyright (c) 2016-2018 Liang Wang <liang.wang@cl.cam.ac.uk>
 *)

open Owl_graph


(* Functor of making initialisor of a CPU-based engine. *)

module Make
  (Graph : Owl_computation_graph_sig.Sig)
  = struct

  open Graph.Optimiser.Operator.Symbol

  open Graph.Optimiser.Operator.Symbol.Shape.Type


  (* utility functions *)

  let is_broadcastable x =
    match get_operator x with
    | Pow             -> true
    | Atan2           -> true
    | Hypot           -> true
    | Min2            -> true
    | Max2            -> true
    | Add             -> true
    | Sub             -> true
    | Mul             -> true
    | Div             -> true
    | FMA             -> true
    | EltEqual        -> true
    | EltNotEqual     -> true
    | EltLess         -> true
    | EltGreater      -> true
    | EltLessEqual    -> true
    | EltGreaterEqual -> true
    | _               -> false


  (* written to be as safe as possible, but can probably set to true more
   * operations.
   * Careful: Broadcasting operations can not overwrite parents. *)
  let can_overwrite_parents x = match get_operator x with
    | Create _shape                                  -> false
    | Sequential _shape                              -> false
    | Uniform _shape                                 -> false
    | Gaussian _shape                                -> false
    | Bernoulli _shape                               -> false
    | GetSlice _slice                                -> false
    | Tile _repeats                                  -> false
    | Repeat _repeats                                -> false
    | Pad (_v, _padding)                             -> false
    | Concatenate _axis                              -> false
    | Map _f                                         -> false
    | Fold (_axis, _f)                               -> false
    | Scan (_axis, _f)                               -> false
    | OneHot _depth                                  -> false
    | Min _axis                                      -> false
    | Max _axis                                      -> false
    | Sum _axis                                      -> false
    | SumReduce _axis                                -> false
    | Pow                                            -> false (* Broadcasting *)
    | Atan2                                          -> false (* Broadcasting *)
    | Hypot                                          -> false (* Broadcasting *)
    | Min2                                           -> false (* Broadcasting *)
    | Max2                                           -> false (* Broadcasting *)
    | Add                                            -> false (* Broadcasting *)
    | Sub                                            -> false (* Broadcasting *)
    | Mul                                            -> false (* Broadcasting *)
    | Div                                            -> false (* Broadcasting *)
    | FMA                                            -> false (* Broadcasting *)
    | EltEqual                                       -> false (* Broadcasting *)
    | EltNotEqual                                    -> false (* Broadcasting *)
    | EltLess                                        -> false (* Broadcasting *)
    | EltGreater                                     -> false (* Broadcasting *)
    | EltLessEqual                                   -> false (* Broadcasting *)
    | EltGreaterEqual                                -> false (* Broadcasting *)
    | Conv1d (_padding, _stride)                     -> false
    | Conv2d (_padding, _stride)                     -> false
    | Conv3d (_padding, _stride)                     -> false
    | TransposeConv2d (_padding, _stride)            -> false
    | MaxPool1d (_padding, _kernel, _stride)         -> false
    | MaxPool2d (_padding, _kernel, _stride)         -> false
    | MaxPool3d (_padding, _kernel, _stride)         -> false
    | AvgPool1d (_padding, _kernel, _stride)         -> false
    | AvgPool2d (_padding, _kernel, _stride)         -> false
    | AvgPool3d (_padding, _kernel, _stride)         -> false
    | UpSampling2d _size                             -> false
    | Conv1dBackwardInput _stride                    -> false
    | Conv1dBackwardKernel _stride                   -> false
    | Conv2dBackwardInput _stride                    -> false
    | Conv2dBackwardKernel _stride                   -> false
    | Conv3dBackwardInput _stride                    -> false
    | Conv3dBackwardKernel _stride                   -> false
    | TransposeConv2dBackwardInput _stride           -> false
    | TransposeConv2dBackwardKernel _stride          -> false
    | MaxPool1dBackward (_padding, _kernel, _stride) -> false
    | MaxPool2dBackward (_padding, _kernel, _stride) -> false
    | MaxPool3dBackward (_padding, _kernel, _stride) -> false
    | AvgPool1dBackward (_padding, _kernel, _stride) -> false
    | AvgPool2dBackward (_padding, _kernel, _stride) -> false
    | AvgPool3dBackward (_padding, _kernel, _stride) -> false
    | UpSampling2dBackward _size                     -> false
    | Dot (_transa, _transb, _alpha, _beta)          -> false
    | Inv                                            -> false
    | Transpose _axis                                -> false
    | _                                              -> true


  (* return a partition of the parents in two arrays: the parents that the node
   * can safely overwrite and the others. *)
  let split_parents x =
    let par = Owl_utils.Array.unique (parents x) in
    if is_broadcastable x then
      let sx = node_shape x in
      Owl_utils.Array.filter (fun p -> node_shape p = sx) par,
      Owl_utils.Array.filter (fun p -> node_shape p <> sx) par
    else if can_overwrite_parents x then par, [||]
    else [||], par


  module IntMap = Map.Make(struct
                      type t = int
                      let compare : int -> int -> int = compare
                    end)


  (* core initialisation function *)
  let _init_terms nodes =
    (* hashtable associating to each node its number of references left to use *)
    let refs = Hashtbl.create 256 in
    (* hashtable associating a number of elements to the id of a reusable block *)
    let reusable = Hashtbl.create 256 in
    (* hashtable associating the id of a block to each node *)
    let node_to_block = Hashtbl.create 256 in
    (* hashtable associating to each block its size *)
    let block_to_size = Hashtbl.create 256 in
    (* hashtable associating to each node id the corresponding node *)
    let id_to_node = Hashtbl.create 256 in

    (* already has a block or is already associated to a block id during the
     * execution of the algorithm *)
    let is_initialised x =
      is_assigned x || Hashtbl.mem node_to_block (id x)
    in

    (* Notifies a node that it has been used by one of its children.
     * If no more children have to use the node, assumes that the memory of the
     * node can be reused by another node. *)
    let update_parent p =
      let id_p = id p in
      if not (is_assigned p) && Hashtbl.mem refs id_p then (
        let num = Hashtbl.find refs id_p in
        assert (num > 0);
        if num - 1 = 0 then (* can be reused *) (
          Hashtbl.remove refs id_p;
          let block_id = Hashtbl.find node_to_block id_p in
          let block_size = Hashtbl.find block_to_size block_id in
          Hashtbl.add reusable block_size block_id
        )
        else Hashtbl.replace refs id_p (num - 1)
      )
    in

    (* Heuristic: return the smallest block that is larger than numel.
     * If no such block exists, return the biggest one and make it bigger.
     * TODO: make it O(log). *)

    (* let best_block_to_reuse numel =
     *   if IntMap.is_empty !reusable then None
     *   else (
     *     let to_reuse = IntMap.find_first_opt (fun k -> k >= numel) !reusable in
     *     let to_reuse = match to_reuse with
     *       | Some x -> x
     *       | None   -> IntMap.max_binding !reusable
     *     in
     *     reusable := IntMap.remove (fst to_reuse) !reusable;
     *     Some (snd to_reuse)
     *   )
     * in *)
    let best_block_to_reuse numel =
      let factor = 10000 in
      let best = ref (-1) in
      (* find the current max size available *)
      Hashtbl.iter (fun s _ -> if s > !best then best := s) reusable;
      Hashtbl.iter (fun s _ -> if s < !best && s >= numel then best := s) reusable;
      (* Experimental heuristic: do not reuse memory if the number of
       * elements is too different *)
      if !best <= 1 || !best <= numel/factor || !best >= numel*factor then None
      else (
        let b_id = Hashtbl.find reusable !best in
        if !best < numel then (
          Hashtbl.replace block_to_size b_id numel
        );
        Hashtbl.remove reusable !best;
        Some b_id
      )
    in

    (* Links node [x] to a new block. *)
    let allocate_new x =
      let numel_x = node_numel x in
      let b_id = block_id () in
      Hashtbl.add node_to_block (id x) b_id;
      Hashtbl.add block_to_size b_id numel_x
    in

    (* Links the node [x] to the best reusable block if such a block exists.
     * Otherwise, links [x] to a new block. *)
    let allocate x =
      let numel_x = node_numel x in
      let block_id_to_reuse = best_block_to_reuse numel_x in
      match block_id_to_reuse with
      | Some b_id ->
         Hashtbl.add node_to_block (id x) b_id
      | None ->
         allocate_new x
    in

    (* assumes that the parents of an initialised node are always initialised. *)
    let rec init x =
      Owl_log.debug "init %s ..." (node_to_str x);

      if not (is_initialised x) then (
        Hashtbl.add id_to_node (id x) x;
        Array.iter init (parents x);
        let pre_par, post_par = split_parents x in
        Array.iter update_parent pre_par;
        if is_reusable x && node_numel x <> 1 then (
          Hashtbl.add refs (id x) (refnum x);
          allocate x
        )
        else (
          (* a node that cannot be reused cannot reuse either *)
          allocate_new x
        );
        Array.iter update_parent post_par;
      )
    in
    (* links all the nodes to a block id and all the blocks to a size *)
    Array.iter init nodes;

    (* Creates the blocks and initialises the relevant attributes of the nodes *)
    let id_to_block = Hashtbl.create 256 in
    Hashtbl.iter
      (fun x_id b_id ->
        let x = Hashtbl.find id_to_node x_id in
        if Hashtbl.mem id_to_block b_id then (
          let block = Hashtbl.find id_to_block b_id in
          add_node_to_block x block
        )
        else (
          let size = Hashtbl.find block_to_size b_id in
          let block = make_empty_block ~id:b_id size in
          Hashtbl.add id_to_block b_id block;
          add_node_to_block x block
        )
      ) node_to_block


  let init_stats nodes =
    let total_elt = ref 0
    and shared_elt = ref 0
    and non_shared_elt = ref 0 in
    let total_nodes = ref 0
    and reusable_nodes = ref 0
    and non_reusable_nodes = ref 0 in
    let blocks_seen = Hashtbl.create 256 in
    let reusable_blocks = ref 0
    and non_reusable_blocks = ref 0 in
    let alloc_reusable = ref 0
    and alloc_non_reusable = ref 0 in
    let update_stats x =
      let numel_x = node_numel x in
      total_elt := !total_elt + numel_x;
      total_nodes := !total_nodes + 1;
      if is_reusable x then (
        shared_elt := !shared_elt + numel_x;
        reusable_nodes := !reusable_nodes + 1
      )
      else (
        non_shared_elt := !non_shared_elt + numel_x;
        non_reusable_nodes := !non_reusable_nodes + 1;
      );

      let block_x = (get_block_exn x).(0) in
      let b_id = get_block_id x in
      if not (Hashtbl.mem blocks_seen b_id) then (
        Hashtbl.add blocks_seen b_id None;
        if is_reusable x then (
          reusable_blocks := !reusable_blocks + 1;
          alloc_reusable := !alloc_reusable + block_x.size;
        )
        else (
          non_reusable_blocks := !non_reusable_blocks + 1;
          alloc_non_reusable := !alloc_non_reusable + block_x.size;
        )
      )
    in
    Owl_graph.iter_ancestors update_stats nodes;

    let s =
      Printf.sprintf "*** INITIALISATION STATISTICS ***\n" ^
      Printf.sprintf "%d nodes, %d elements\n" !total_nodes !total_elt ^
      Printf.sprintf "%d reusable nodes, %d elements\n"
        !reusable_nodes !shared_elt ^
      Printf.sprintf "%d non-reusable nodes, %d elements\n"
        !non_reusable_nodes !non_shared_elt ^
      Printf.sprintf "%d shared blocks, %d allocated elements\n"
        !reusable_blocks !alloc_reusable ^
      Printf.sprintf "TOTAL ALLOCATED ELEMENTS: %d\n"
        (!alloc_reusable + !alloc_non_reusable) in
    Owl_log.info "%s" s
end


(* Make functor ends *)
