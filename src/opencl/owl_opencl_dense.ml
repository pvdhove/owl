(*
 * OWL - an OCaml numerical library for scientific computing
 * Copyright (c) 2016-2017 Liang Wang <liang.wang@cl.cam.ac.uk>
 *)

open Owl_dense_ndarray_s

open Owl_opencl_utils

open Owl_opencl_generated


type t =
  | F     of float
  | Arr   of arr
  | Trace of trace
and trace = {
  mutable op     : trace_op;
  mutable input  : trace array;
  mutable outval : t array;        (* output value, not Trace *)
  mutable outmem : cl_mem array;
  mutable events : cl_event array;
  mutable refnum : int;
}
and trace_op =
  | Noop
  | Add
  | Sub
  | Mul
  | Div
  | Sin


(* helper functions *)

let pack_input = function
  | Trace x -> (
      x.refnum <- x.refnum + 1;
      x
    )
  | x       -> {
      op      = Noop;
      input   = [| |];
      outval  = [|x|];
      outmem  = [| |];
      events  = [| |];
      refnum  = 1;
    }


let pack_op op input outval outmem =
Trace {
  op;
  input  = Array.map pack_input input;
  outval;
  outmem;
  events = [||];
  refnum = 0;
}


let unpack_arr = function
  | Arr x -> x
  | _     -> failwith "owl_opencl_dense:unpack_arr"


let unpack_trace = function
  | Trace x -> x
  | _       -> failwith "owl_opencl_dense:unpack_trace"


let get_input_event x =
  Array.fold_left (fun a i ->
      Array.append a i.events
  ) [||] x.input
  |> Array.to_list


(* math operator modules *)

module Noop = struct

  let eval context x =
    print_endline "@@@"; flush_all ();
    let ctx = Owl_opencl_kernels.(context.context) in
    match x.outval.(0) with
    | Arr y -> (
        let y' = Owl_opencl_base.Buffer.create ~flags:[Owl_opencl_generated.cl_MEM_USE_HOST_PTR] ctx y in
        x.outmem <- [|y'|]
      )
    | _ -> failwith "noop: not implemented yet"

end



module Sin = struct

  let run x = pack_op Sin [|x|] [||] [||]

  let mk_kernel program = Owl_opencl_base.Kernel.create program "owl_opencl_sin"

  let eval context x =
    print_endline "==="; flush_all ();
    let ctx = Owl_opencl_kernels.(context.context) in
    let cmdq = Owl_opencl_kernels.(context.command_queue) in
    let kernel = mk_kernel Owl_opencl_kernels.(context.program) in

    let input = x.input.(0) in
    let a_val = input.outval.(0) in
    let a_mem = input.outmem.(0) in
    let a_ptr = Ctypes.allocate Owl_opencl_generated.cl_mem a_mem in
    let _size = a_val |> unpack_arr |> numel in
    let wait_for = get_input_event x in

    let b_val, b_mem, b_ptr =
      match input.refnum = 1 with
      | true  -> a_val, a_mem, a_ptr
      | false -> (
          let b_val = zeros (a_val |> unpack_arr |> shape) in
          let b_mem = Owl_opencl_base.Buffer.create ~flags:[Owl_opencl_generated.cl_MEM_USE_HOST_PTR] ctx b_val in
          let b_ptr = Ctypes.allocate Owl_opencl_generated.cl_mem b_mem in
          Arr b_val, b_mem, b_ptr
        )
    in

    Owl_opencl_base.Kernel.set_arg kernel 0 sizeof_cl_mem a_ptr;
    Owl_opencl_base.Kernel.set_arg kernel 1 sizeof_cl_mem b_ptr;
    let event = Owl_opencl_base.Kernel.enqueue_ndrange ~wait_for cmdq kernel 1 [_size] in
    x.outval <- [|b_val|];
    x.outmem <- [|b_mem|];
    x.events <- [|event|]


end


(* graph related function *)

let eval x =
  let rec _eval x =
    Array.iter _eval x.input;
    if x.outmem = [||] then (
      match x.op with
      | Noop -> Noop.eval Owl_opencl_kernels.default x
      | Sin  -> Sin.eval Owl_opencl_kernels.default x
      | _    -> failwith "not implemented yet"
    )
    else (
          print_endline "stop"
    )
  in
  _eval (unpack_trace x);
  let cmdq = Owl_opencl_kernels.(default.command_queue) in
  Owl_opencl_base.CommandQueue.finish cmdq;
  x


(* ends here *)