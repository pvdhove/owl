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

  open Graph.Optimiser.Operator.Symbol.Shape.Type.Device


  (* utility functions *)

  let make_value_from block dst =
    let dst_shp = node_shape dst in
    let dst_numel = node_numel dst in
    let src_val = value_to_arr (get_value_block block) in
    let dst_val = arr_to_value (A.reshape (A.sub_left src_val 0 dst_numel) dst_shp) in
    add_node_block block dst;
    set_block dst [| block |];
    (* TODO: ugly, clean this *)
    (attr dst).value <- [| dst_val |]


  let to_allocate x =
    match (get_operator x) with
    | Noop                                           -> false
    | Var                                            -> false
    | Const                                          -> false
    | Get _i                                         -> false
    | Min'                                           -> false
    | Max'                                           -> false
    | Sum'                                           -> false
    | L1norm'                                        -> false
    | L2norm'                                        -> false
    | L2NormSqr'                                     -> false
    | Trace                                          -> false
    | Scalar_Add                                     -> false
    | Scalar_Sub                                     -> false
    | Scalar_Mul                                     -> false
    | Scalar_Div                                     -> false
    | Scalar_Pow                                     -> false
    | Scalar_Atan2                                   -> false
    | Scalar_Abs                                     -> false
    | Scalar_Neg                                     -> false
    | Scalar_Sqr                                     -> false
    | Scalar_Sqrt                                    -> false
    | Scalar_Exp                                     -> false
    | Scalar_Log                                     -> false
    | Scalar_Log2                                    -> false
    | Scalar_Log10                                   -> false
    | Scalar_Signum                                  -> false
    | Scalar_Floor                                   -> false
    | Scalar_Ceil                                    -> false
    | Scalar_Round                                   -> false
    | Scalar_Sin                                     -> false
    | Scalar_Cos                                     -> false
    | Scalar_Tan                                     -> false
    | Scalar_Sinh                                    -> false
    | Scalar_Cosh                                    -> false
    | Scalar_Tanh                                    -> false
    | Scalar_Asin                                    -> false
    | Scalar_Acos                                    -> false
    | Scalar_Atan                                    -> false
    | Scalar_Asinh                                   -> false
    | Scalar_Acosh                                   -> false
    | Scalar_Atanh                                   -> false
    | Scalar_Relu                                    -> false
    | Scalar_Sigmoid                                 -> false
    | _                                              -> true

  (* written to be as safe as possible, but can probably set to true many more
   * functions.
   * Careful: Broadcasting operations can NEVER overwrite parents. *)
  let can_overwrite_parent x =
     match (get_operator x) with
     | Empty _shape                                   -> false
     | Zeros _shape                                   -> false
     | Ones _shape                                    -> false
     | Create _shape                                  -> false
     | Sequential _shape                              -> false
     | Uniform _shape                                 -> false
     | Gaussian _shape                                -> false
     | Bernoulli _shape                               -> false
     | Init (_shape, _f)                              -> false
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
     | AddScalar                                      -> false
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

  module IntMap = Map.Make(struct
                      type t = int
                      let compare : int -> int -> int = compare
                    end)

  (* TODO: add it in comp_symbol *)
  let block_id = ref 100000

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
    (* *)
    let id_to_node = Hashtbl.create 256 in

    let is_initialised x =
      is_assigned x || Hashtbl.mem node_to_block (id x)
    in

    let update_parent p =
      let id_p = id p in
      if not (is_assigned p) && Hashtbl.mem refs id_p then (
        let num = Hashtbl.find refs id_p in
        assert (num > 0);
        if num - 1 = 0 then (
          Hashtbl.remove refs id_p;
          let block_id = Hashtbl.find node_to_block id_p in
          let block_size = Hashtbl.find block_to_size block_id in
          Hashtbl.add reusable block_size block_id
        )
        else Hashtbl.replace refs id_p (num - 1)
      )
    in

    (* heuristic: return the smallest block that is larger than numel.
     * If no such block exists, return the biggest one and make it bigger. *)

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
      let best = ref (-1) in
      (* find the current max size available *)
      Hashtbl.iter (fun s _ -> if s > !best then best := s) reusable;
      Hashtbl.iter (fun s _ -> if s < !best && s >= numel then best := s) reusable;
      if !best <= 1 then None
      else (
        let b_id = Hashtbl.find reusable !best in
        Hashtbl.remove reusable !best;
        Some b_id
      )
    in
    (* let best_block_to_reuse numel =
     *   if Hashtbl.mem reusable numel then (
     *     let b_id = Hashtbl.find reusable numel in
     *     Hashtbl.remove reusable numel;
     *     Some b_id
     *   )
     *   else None
     * in *)

    let allocate_new x =
      let numel_x = node_numel x in
      block_id := !block_id + 1;
      Hashtbl.add node_to_block (id x) !block_id;
      Hashtbl.add block_to_size !block_id numel_x
    in

    let allocate x =
      let numel_x = node_numel x in
      let block_id_to_reuse = best_block_to_reuse numel_x in
      match block_id_to_reuse with
      | Some b_id ->
        (* Owl_log.info "for %s.\n" (node_to_str x); *)
         Hashtbl.add node_to_block (id x) b_id;
         let block_size = Hashtbl.find block_to_size b_id in
         if block_size < numel_x then
           Hashtbl.replace block_to_size b_id numel_x
      | None ->
         allocate_new x
    in

    let rec init x =
      Owl_log.debug "init %s ..." (node_to_str x);

      if not (is_initialised x) then (
        Hashtbl.add id_to_node (id x) x;
        Array.iter init (parents x);
        if to_allocate x then (
          (* a node that cannot be reused cannot reuse either *)
          if is_reusable x then (
            Hashtbl.add refs (id x) (refnum x);
            if can_overwrite_parent x then (
              Array.iter update_parent (Owl_utils.Array.unique (parents x));
              allocate x
            ) else (
              allocate x;
              Array.iter update_parent (Owl_utils.Array.unique (parents x))
            )
          )
          else (
            Array.iter update_parent (Owl_utils.Array.unique (parents x));
            allocate_new x
          )
        )
      )
    in
    Array.iter init nodes;

    let id_to_block = Hashtbl.create 256 in
    Hashtbl.iter
      (fun x_id b_id ->
        let x = Hashtbl.find id_to_node x_id in
        if Hashtbl.mem id_to_block b_id then (
          let block = Hashtbl.find id_to_block b_id in
          make_value_from block x
        )
        else (
          let size = Hashtbl.find block_to_size b_id in
          let block = make_empty_block ~id:b_id size in
          Hashtbl.add id_to_block b_id block;
          make_value_from block x
        )
      ) node_to_block

end


(* Make functor ends *)
