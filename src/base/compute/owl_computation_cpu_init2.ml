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

  let is_initialised x =
    if is_elt x then false
    else
      let x_val = get_value x in
      Array.length x_val > 0


  let make_value_from src dst =
    let dst_shp = node_shape dst in
    match src with
    | Some src -> (
      (* inherit memory from the src node *)
      (* if id dst = 3577 then (
       *   Owl_log.info "HEYYY! 3577 reused %s" (node_to_str src)
       * ); *)
      let src_val = value_to_arr (get_value src).(0) in
      let dst_val = arr_to_value (A.reshape src_val dst_shp) in
      set_value dst [| dst_val |];
      set_vnode dst [| src |]
    )
    | None     -> (
      (* allocate new memory for dst node *)
      let dst_val = arr_to_value (A.zeros dst_shp) in
      set_value dst [| dst_val |];
      set_vnode dst [| |]
    )


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

  (* core initialisation function *)

  let _init_terms nodes =
    (* TODO: only count nodes that are encountered during the traversal as
    refs *)
    (* hashtable associating to each node its number of unused references *)
    let refs = Hashtbl.create 256 in
    (* hashtable associating a number of elements to a reusable node *)
    let reusable = Hashtbl.create 256 in
    let numel x = Array.fold_left ( * ) 1 (node_shape x) in
    let update_parent p =
      if to_allocate p && get_reuse p then (
        let num = Hashtbl.find refs (id p) in
        assert (num > 0);
        Hashtbl.replace refs (id p) (num - 1);
        if num - 1 = 0 then
          let numel_p = numel p in
          Hashtbl.add reusable numel_p p
      )
    in
    let allocate x =
      let numel_x = numel x in
      if Hashtbl.mem reusable numel_x then (
        let to_reuse = Hashtbl.find reusable numel_x in
        (* Owl_log.info "reuse %s." (node_to_str to_reuse);
           Owl_log.info "for %s.\n" (node_to_str x); *)
        Hashtbl.remove reusable numel_x;
        make_value_from (Some to_reuse) x
      )
      else
        make_value_from None x
    in

    let rec init x =
      Owl_log.debug "init %s ..." (node_to_str x);

      if not (is_initialised x) then (
        (* Owl_log.info "hein %s" (node_to_str x); *)
        Array.iter init (parents x);

        if to_allocate x then (
          if get_reuse x then (
            Hashtbl.add refs (id x) (Array.length (children x))
          );
          if can_overwrite_parent x then (
            Array.iter update_parent (Owl_utils.Array.unique (parents x));
            allocate x
          ) else (
            allocate x;
            Array.iter update_parent (Owl_utils.Array.unique (parents x))
          )
        )
      )
    in
    Array.iter init nodes

end


(* Make functor ends *)
