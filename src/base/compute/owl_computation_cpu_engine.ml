(*
 * OWL - OCaml Scientific and Engineering Computing
 * Copyright (c) 2016-2018 Liang Wang <liang.wang@cl.cam.ac.uk>
 *)

open Owl_types


(* Functor of making a CPU-based engine to execute computation graphs. *)

module Make_Nested
  (Graph : Owl_computation_graph_sig.Sig)
  = struct

  module Graph = Graph

  open Graph.Optimiser.Operator.Symbol

  (* module aliases *)

  module CG_Init = Owl_computation_cpu_init2.Make (Graph)

  module CG_Eval = Owl_computation_cpu_eval.Make (Graph)


  (* core interface *)

  (* TODO: make sure the order of init/eval always stays the same *)
  let eval_gen nodes =
    (* let topo = Owl_graph.topo_sort nodes in *)
    (* Array.iter (fun s -> Owl_log.info "NODES: %s" (node_to_str s)) nodes; *)
    CG_Init._init_terms nodes;
    Array.iter CG_Eval._eval_term nodes


  let eval_elt xs = Array.map elt_to_node xs |> eval_gen


  let eval_arr xs = Array.map arr_to_node xs |> eval_gen


  let eval_graph graph =
    Graph.invalidate_rvs graph;
    (* let open Graph.Optimiser.Operator.Symbol.Shape.Type in
     * let open Device in
     * let open Owl_graph in
     * Owl_graph.iter_ancestors (fun x ->
     *     if id x = 3577 then
     *       let () = Owl_log.info "iter! %s" (node_to_str x) in
     *       let y = (attr x).value in
     *       if Array.length y > 0 then
     *         (\* Printf.printf "%f\n" (value_to_float y.(0)) *\)
     *         A.print ~max_col:8 (value_to_arr y.(0))
     *       else
     *         Printf.printf "NOT INITIALISED\n"
     *   )
     *   (Graph.get_outputs graph); *)
    Graph.get_outputs graph |> eval_gen


end


(* Functor of making CPU-based engine with unrolled module hierarchy *)

module Make
  (A : Ndarray_Mutable)
  = struct

  include
    Owl_computation_engine.Flatten (
      Make_Nested (
        Owl_computation_engine.Make_Graph (
          Owl_computation_cpu_device.Make (A)
        )
      )
    )

end


(* Make functor ends *)
