(* ========================================================================= *)
(* Bytecode Virtual Machine                                                  *)
(* A stack-based VM with compiler, disassembler, and runtime                 *)
(*                                                                           *)
(* Features:                                                                 *)
(* - Stack-based execution with 25+ opcodes                                 *)
(* - Arithmetic, comparison, logic, control flow                            *)
(* - Local variables with load/store                                        *)
(* - Function calls with call frames                                        *)
(* - Closures and upvalues                                                  *)
(* - Simple expression language compiler                                    *)
(* - Bytecode disassembler with human-readable output                       *)
(* - Execution tracing for debugging                                        *)
(* - 8 native functions (clock, abs, max, min, strlen, substr, int, float)  *)
(* ========================================================================= *)

(* --- Opcodes --- *)

type opcode =
  | OP_CONST of float
  | OP_TRUE | OP_FALSE | OP_NIL
  | OP_POP | OP_DUP | OP_SWAP | OP_ROT
  | OP_ADD | OP_SUB | OP_MUL | OP_DIV | OP_MOD | OP_NEG
  | OP_NOT
  | OP_EQ | OP_LT | OP_GT | OP_LE | OP_GE
  | OP_AND | OP_OR
  | OP_JUMP of int | OP_JUMP_IF_FALSE of int | OP_JUMP_IF_TRUE of int
  | OP_LOAD of int | OP_STORE of int
  | OP_GLOAD of string | OP_GSTORE of string
  | OP_CALL of int | OP_RETURN
  | OP_CLOSURE of int * int list
  | OP_GET_UPVALUE of int | OP_SET_UPVALUE of int
  | OP_PRINT | OP_HALT | OP_NOP
  | OP_CONST_INT of int | OP_CONST_STR of string

(* --- Values --- *)

type value =
  | VFloat of float | VInt of int | VBool of bool | VNil | VString of string
  | VFunction of func_obj | VClosure of closure_obj
  | VNative of string * (value list -> value)

and func_obj = { fn_name: string; fn_arity: int; fn_code: opcode array }

and closure_obj = { cl_func: func_obj; cl_upvalues: value array }

(* --- Call Frame --- *)

type call_frame = {
  mutable cf_ip: int;
  cf_code: opcode array;
  cf_base: int;
  cf_closure: closure_obj option;
}

(* --- VM State --- *)

type vm = {
  mutable stack: value array;
  mutable sp: int;
  mutable frames: call_frame list;
  globals: (string, value) Hashtbl.t;
  mutable trace: bool;
  mutable output: string list;
}

type chunk = { ch_code: opcode array; ch_functions: func_obj array }

exception VM_error of string
exception Compile_error of string

(* --- Value operations --- *)

let value_to_string = function
  | VFloat f -> if Float.is_integer f then string_of_int (int_of_float f) else Printf.sprintf "%.6g" f
  | VInt i -> string_of_int i
  | VBool b -> string_of_bool b
  | VNil -> "nil"
  | VString s -> s
  | VFunction f -> Printf.sprintf "<fn %s/%d>" f.fn_name f.fn_arity
  | VClosure c -> Printf.sprintf "<closure %s/%d>" c.cl_func.fn_name c.cl_func.fn_arity
  | VNative (name, _) -> Printf.sprintf "<native %s>" name

let value_is_truthy = function VBool false | VNil -> false | _ -> true

let value_as_float = function
  | VFloat f -> f | VInt i -> float_of_int i
  | v -> raise (VM_error (Printf.sprintf "Expected number, got %s" (value_to_string v)))

let value_equal a b = match a, b with
  | VFloat x, VFloat y -> Float.equal x y
  | VInt x, VInt y -> x = y
  | VFloat x, VInt y -> Float.equal x (float_of_int y)
  | VInt x, VFloat y -> Float.equal (float_of_int x) y
  | VBool x, VBool y -> x = y
  | VNil, VNil -> true
  | VString x, VString y -> String.equal x y
  | _ -> false

let value_compare a b = Float.compare (value_as_float a) (value_as_float b)

let arith_op op a b = match a, b with
  | VInt x, VInt y -> (match op with
    | `Add -> VInt (x + y) | `Sub -> VInt (x - y) | `Mul -> VInt (x * y)
    | `Div -> if y = 0 then raise (VM_error "Division by zero") else VInt (x / y)
    | `Mod -> if y = 0 then raise (VM_error "Modulo by zero") else VInt (x mod y))
  | _ -> let fa = value_as_float a and fb = value_as_float b in (match op with
    | `Add -> VFloat (fa +. fb) | `Sub -> VFloat (fa -. fb)
    | `Mul -> VFloat (fa *. fb)
    | `Div -> if fb = 0.0 then raise (VM_error "Division by zero") else VFloat (fa /. fb)
    | `Mod -> if fb = 0.0 then raise (VM_error "Modulo by zero") else VFloat (Float.rem fa fb))

(* --- VM creation --- *)

let create_vm ?(trace=false) () = {
  stack = Array.make 256 VNil; sp = 0; frames = [];
  globals = Hashtbl.create 16; trace; output = [];
}

let push vm v =
  if vm.sp >= Array.length vm.stack then begin
    let ns = Array.make (Array.length vm.stack * 2) VNil in
    Array.blit vm.stack 0 ns 0 vm.sp; vm.stack <- ns end;
  vm.stack.(vm.sp) <- v; vm.sp <- vm.sp + 1

let pop vm =
  if vm.sp <= 0 then raise (VM_error "Stack underflow");
  vm.sp <- vm.sp - 1; vm.stack.(vm.sp)

let peek vm = if vm.sp <= 0 then raise (VM_error "Stack underflow"); vm.stack.(vm.sp - 1)

let peek_at vm offset =
  let idx = vm.sp - 1 - offset in
  if idx < 0 then raise (VM_error "Stack underflow"); vm.stack.(idx)

(* --- Disassembler --- *)

let disassemble_op i = function
  | OP_CONST f -> Printf.sprintf "%04d  CONST        %.6g" i f
  | OP_CONST_INT n -> Printf.sprintf "%04d  CONST_INT    %d" i n
  | OP_CONST_STR s -> Printf.sprintf "%04d  CONST_STR    %S" i s
  | OP_TRUE -> Printf.sprintf "%04d  TRUE" i
  | OP_FALSE -> Printf.sprintf "%04d  FALSE" i
  | OP_NIL -> Printf.sprintf "%04d  NIL" i
  | OP_POP -> Printf.sprintf "%04d  POP" i
  | OP_DUP -> Printf.sprintf "%04d  DUP" i
  | OP_SWAP -> Printf.sprintf "%04d  SWAP" i
  | OP_ROT -> Printf.sprintf "%04d  ROT" i
  | OP_ADD -> Printf.sprintf "%04d  ADD" i
  | OP_SUB -> Printf.sprintf "%04d  SUB" i
  | OP_MUL -> Printf.sprintf "%04d  MUL" i
  | OP_DIV -> Printf.sprintf "%04d  DIV" i
  | OP_MOD -> Printf.sprintf "%04d  MOD" i
  | OP_NEG -> Printf.sprintf "%04d  NEG" i
  | OP_NOT -> Printf.sprintf "%04d  NOT" i
  | OP_EQ -> Printf.sprintf "%04d  EQ" i
  | OP_LT -> Printf.sprintf "%04d  LT" i
  | OP_GT -> Printf.sprintf "%04d  GT" i
  | OP_LE -> Printf.sprintf "%04d  LE" i
  | OP_GE -> Printf.sprintf "%04d  GE" i
  | OP_AND -> Printf.sprintf "%04d  AND" i
  | OP_OR -> Printf.sprintf "%04d  OR" i
  | OP_JUMP off -> Printf.sprintf "%04d  JUMP         -> %04d" i (i + off + 1)
  | OP_JUMP_IF_FALSE off -> Printf.sprintf "%04d  JUMP_IF_F    -> %04d" i (i + off + 1)
  | OP_JUMP_IF_TRUE off -> Printf.sprintf "%04d  JUMP_IF_T    -> %04d" i (i + off + 1)
  | OP_LOAD s -> Printf.sprintf "%04d  LOAD         [%d]" i s
  | OP_STORE s -> Printf.sprintf "%04d  STORE        [%d]" i s
  | OP_GLOAD n -> Printf.sprintf "%04d  GLOAD        '%s'" i n
  | OP_GSTORE n -> Printf.sprintf "%04d  GSTORE       '%s'" i n
  | OP_CALL n -> Printf.sprintf "%04d  CALL         (%d args)" i n
  | OP_RETURN -> Printf.sprintf "%04d  RETURN" i
  | OP_CLOSURE (fi, ups) -> Printf.sprintf "%04d  CLOSURE      fn[%d] upvals=[%s]" i fi (String.concat "," (List.map string_of_int ups))
  | OP_GET_UPVALUE idx -> Printf.sprintf "%04d  GET_UPVAL    [%d]" i idx
  | OP_SET_UPVALUE idx -> Printf.sprintf "%04d  SET_UPVAL    [%d]" i idx
  | OP_PRINT -> Printf.sprintf "%04d  PRINT" i
  | OP_HALT -> Printf.sprintf "%04d  HALT" i
  | OP_NOP -> Printf.sprintf "%04d  NOP" i

let disassemble ?(name="<script>") code =
  let lines = Array.mapi disassemble_op code in
  Printf.sprintf "== %s ==\n%s" name (String.concat "\n" (Array.to_list lines))

let disassemble_chunk chunk =
  let main = disassemble ~name:"<main>" chunk.ch_code in
  let fns = Array.mapi (fun i f ->
    disassemble ~name:(Printf.sprintf "%s/%d" f.fn_name f.fn_arity) f.fn_code
  ) chunk.ch_functions in
  String.concat "\n\n" (main :: Array.to_list fns)

(* --- Execution --- *)

let run_code vm code =
  let frame = { cf_ip = 0; cf_code = code; cf_base = vm.sp; cf_closure = None } in
  vm.frames <- [frame];
  let get_frame () = List.hd vm.frames in
  let rec step () =
    let frame = get_frame () in
    if frame.cf_ip >= Array.length frame.cf_code then ()
    else begin
      let op = frame.cf_code.(frame.cf_ip) in
      if vm.trace then
        vm.output <- Printf.sprintf "  [sp=%d] %s" vm.sp (disassemble_op frame.cf_ip op) :: vm.output;
      frame.cf_ip <- frame.cf_ip + 1;
      exec op; step ()
    end
  and exec = function
    | OP_CONST f -> push vm (VFloat f)
    | OP_CONST_INT n -> push vm (VInt n)
    | OP_CONST_STR s -> push vm (VString s)
    | OP_TRUE -> push vm (VBool true)
    | OP_FALSE -> push vm (VBool false)
    | OP_NIL -> push vm VNil
    | OP_POP -> ignore (pop vm)
    | OP_DUP -> push vm (peek vm)
    | OP_SWAP -> let a = pop vm in let b = pop vm in push vm a; push vm b
    | OP_ROT -> let c = pop vm in let b = pop vm in let a = pop vm in push vm b; push vm c; push vm a
    | OP_ADD -> let b = pop vm in let a = pop vm in
      (match a, b with
       | VString x, VString y -> push vm (VString (x ^ y))
       | VString x, _ -> push vm (VString (x ^ value_to_string b))
       | _, VString y -> push vm (VString (value_to_string a ^ y))
       | _ -> push vm (arith_op `Add a b))
    | OP_SUB -> let b = pop vm in let a = pop vm in push vm (arith_op `Sub a b)
    | OP_MUL -> let b = pop vm in let a = pop vm in push vm (arith_op `Mul a b)
    | OP_DIV -> let b = pop vm in let a = pop vm in push vm (arith_op `Div a b)
    | OP_MOD -> let b = pop vm in let a = pop vm in push vm (arith_op `Mod a b)
    | OP_NEG -> (match pop vm with VInt i -> push vm (VInt (-i)) | VFloat f -> push vm (VFloat (-.f))
      | _ -> raise (VM_error "Cannot negate non-number"))
    | OP_NOT -> push vm (VBool (not (value_is_truthy (pop vm))))
    | OP_EQ -> let b = pop vm in let a = pop vm in push vm (VBool (value_equal a b))
    | OP_LT -> let b = pop vm in let a = pop vm in push vm (VBool (value_compare a b < 0))
    | OP_GT -> let b = pop vm in let a = pop vm in push vm (VBool (value_compare a b > 0))
    | OP_LE -> let b = pop vm in let a = pop vm in push vm (VBool (value_compare a b <= 0))
    | OP_GE -> let b = pop vm in let a = pop vm in push vm (VBool (value_compare a b >= 0))
    | OP_AND -> let b = pop vm in let a = pop vm in push vm (VBool (value_is_truthy a && value_is_truthy b))
    | OP_OR -> let b = pop vm in let a = pop vm in push vm (VBool (value_is_truthy a || value_is_truthy b))
    | OP_JUMP off -> let f = get_frame () in f.cf_ip <- f.cf_ip + off - 1
    | OP_JUMP_IF_FALSE off -> if not (value_is_truthy (pop vm)) then let f = get_frame () in f.cf_ip <- f.cf_ip + off - 1
    | OP_JUMP_IF_TRUE off -> if value_is_truthy (pop vm) then let f = get_frame () in f.cf_ip <- f.cf_ip + off - 1
    | OP_LOAD slot -> let f = get_frame () in push vm vm.stack.(f.cf_base + slot)
    | OP_STORE slot -> let v = pop vm in let f = get_frame () in vm.stack.(f.cf_base + slot) <- v
    | OP_GLOAD name -> (match Hashtbl.find_opt vm.globals name with
       | Some v -> push vm v | None -> raise (VM_error (Printf.sprintf "Undefined global '%s'" name)))
    | OP_GSTORE name -> Hashtbl.replace vm.globals name (pop vm)
    | OP_CALL nargs ->
      let callee = peek_at vm nargs in
      (match callee with
       | VFunction f ->
         if nargs <> f.fn_arity then raise (VM_error (Printf.sprintf "Expected %d args, got %d" f.fn_arity nargs));
         vm.frames <- { cf_ip = 0; cf_code = f.fn_code; cf_base = vm.sp - nargs; cf_closure = None } :: vm.frames
       | VClosure c ->
         if nargs <> c.cl_func.fn_arity then raise (VM_error (Printf.sprintf "Expected %d args, got %d" c.cl_func.fn_arity nargs));
         vm.frames <- { cf_ip = 0; cf_code = c.cl_func.fn_code; cf_base = vm.sp - nargs; cf_closure = Some c } :: vm.frames
       | VNative (_, f) ->
         let args = List.init nargs (fun i -> vm.stack.(vm.sp - nargs + i)) in
         vm.sp <- vm.sp - nargs - 1; push vm (f args)
       | v -> raise (VM_error (Printf.sprintf "Cannot call %s" (value_to_string v))))
    | OP_RETURN ->
      let result = pop vm in let f = get_frame () in
      vm.sp <- f.cf_base - 1; vm.frames <- List.tl vm.frames; push vm result
    | OP_CLOSURE (_, upvalue_indices) ->
      let callee = pop vm in
      (match callee with
       | VFunction f ->
         let upvals = Array.of_list (List.map (fun idx -> let fr = get_frame () in vm.stack.(fr.cf_base + idx)) upvalue_indices) in
         push vm (VClosure { cl_func = f; cl_upvalues = upvals })
       | _ -> raise (VM_error "CLOSURE expects function on stack"))
    | OP_GET_UPVALUE idx ->
      (match (get_frame ()).cf_closure with Some c -> push vm c.cl_upvalues.(idx) | None -> raise (VM_error "No closure context"))
    | OP_SET_UPVALUE idx ->
      let v = pop vm in
      (match (get_frame ()).cf_closure with Some c -> c.cl_upvalues.(idx) <- v | None -> raise (VM_error "No closure context"))
    | OP_PRINT -> vm.output <- value_to_string (pop vm) :: vm.output
    | OP_HALT -> let f = get_frame () in f.cf_ip <- Array.length f.cf_code
    | OP_NOP -> ()
  in step ()

let run vm code = run_code vm code; if vm.sp > 0 then Some (peek vm) else None

let get_output vm = List.rev vm.output

(* --- Expression Language --- *)

type expr =
  | ENum of float | EInt of int | EStr of string | EBool of bool | ENil
  | EVar of string
  | EBinOp of string * expr * expr
  | EUnOp of string * expr
  | ELet of string * expr * expr
  | EIf of expr * expr * expr
  | ESeq of expr list
  | EPrint of expr

type compile_env = {
  mutable locals: (string * int) list;
  mutable next_local: int;
  mutable code: opcode list;
}

let create_env () = { locals = []; next_local = 0; code = [] }

let emit env op = env.code <- op :: env.code

let rec compile_expr env = function
  | ENum f -> emit env (OP_CONST f)
  | EInt i -> emit env (OP_CONST_INT i)
  | EStr s -> emit env (OP_CONST_STR s)
  | EBool true -> emit env OP_TRUE
  | EBool false -> emit env OP_FALSE
  | ENil -> emit env OP_NIL
  | EVar name -> (match List.assoc_opt name env.locals with
     | Some slot -> emit env (OP_LOAD slot) | None -> emit env (OP_GLOAD name))
  | EBinOp (op, a, b) ->
    compile_expr env a; compile_expr env b;
    (match op with
     | "+" -> emit env OP_ADD | "-" -> emit env OP_SUB
     | "*" -> emit env OP_MUL | "/" -> emit env OP_DIV
     | "%" | "mod" -> emit env OP_MOD
     | "==" | "=" -> emit env OP_EQ
     | "<" -> emit env OP_LT | ">" -> emit env OP_GT
     | "<=" -> emit env OP_LE | ">=" -> emit env OP_GE
     | "&&" | "and" -> emit env OP_AND | "||" | "or" -> emit env OP_OR
     | op -> raise (Compile_error (Printf.sprintf "Unknown operator '%s'" op)))
  | EUnOp (op, e) ->
    compile_expr env e;
    (match op with "-" -> emit env OP_NEG | "!" | "not" -> emit env OP_NOT
     | op -> raise (Compile_error (Printf.sprintf "Unknown unary operator '%s'" op)))
  | ELet (name, value, body) ->
    let slot = env.next_local in env.next_local <- env.next_local + 1;
    compile_expr env value; emit env (OP_STORE slot);
    env.locals <- (name, slot) :: env.locals;
    compile_expr env body;
    env.locals <- List.remove_assoc name env.locals
  | EIf (cond, then_e, else_e) ->
    compile_expr env cond;
    emit env (OP_JUMP_IF_FALSE 0);
    compile_expr env then_e;
    emit env (OP_JUMP 0);
    compile_expr env else_e;
    ignore (cond, then_e, else_e)
  | ESeq exprs ->
    List.iteri (fun i e -> compile_expr env e;
      if i < List.length exprs - 1 then emit env OP_POP) exprs
  | EPrint e -> compile_expr env e; emit env OP_DUP; emit env OP_PRINT

let compile expr =
  let env = create_env () in
  compile_expr env expr; emit env OP_HALT;
  Array.of_list (List.rev env.code)

(* --- Native functions --- *)

let register_natives vm =
  let clock_fn _ = VFloat (Unix.gettimeofday ()) in
  let abs_fn = function [VFloat f] -> VFloat (Float.abs f) | [VInt i] -> VInt (abs i)
    | _ -> raise (VM_error "abs expects 1 numeric argument") in
  let max_fn = function [a; b] -> if value_compare a b >= 0 then a else b
    | _ -> raise (VM_error "max expects 2 arguments") in
  let min_fn = function [a; b] -> if value_compare a b <= 0 then a else b
    | _ -> raise (VM_error "min expects 2 arguments") in
  let strlen_fn = function [VString s] -> VInt (String.length s)
    | _ -> raise (VM_error "strlen expects 1 string argument") in
  let substr_fn = function [VString s; VInt start; VInt len] ->
      VString (String.sub s start (min len (String.length s - start)))
    | _ -> raise (VM_error "substr expects (string, start, len)") in
  let int_fn = function [VFloat f] -> VInt (int_of_float f) | [VInt i] -> VInt i
    | [VString s] -> (try VInt (int_of_string s) with _ -> VNil)
    | _ -> raise (VM_error "int expects 1 argument") in
  let float_fn = function [VFloat f] -> VFloat f | [VInt i] -> VFloat (float_of_int i)
    | [VString s] -> (try VFloat (float_of_string s) with _ -> VNil)
    | _ -> raise (VM_error "float expects 1 argument") in
  List.iter (fun (n,f) -> Hashtbl.replace vm.globals n (VNative (n, f)))
    ["clock",clock_fn; "abs",abs_fn; "max",max_fn; "min",min_fn;
     "strlen",strlen_fn; "substr",substr_fn; "int",int_fn; "float",float_fn]

let eval ?(trace=false) expr =
  let vm = create_vm ~trace () in register_natives vm;
  let code = compile expr in (run vm code, get_output vm)

let stack_snapshot vm = List.init vm.sp (fun i -> value_to_string vm.stack.(i))

let assemble ops = Array.of_list ops

(* ========================================================================= *)
(* Tests                                                                      *)
(* ========================================================================= *)

let tests_passed = ref 0
let tests_failed = ref 0

let assert_equal name expected actual =
  if expected = actual then incr tests_passed
  else (incr tests_failed; Printf.printf "FAIL: %s\n  expected: %s\n  actual:   %s\n" name expected actual)

let assert_true name cond =
  if cond then incr tests_passed
  else (incr tests_failed; Printf.printf "FAIL: %s\n" name)

let assert_raises name f =
  try f (); incr tests_failed; Printf.printf "FAIL: %s (no exception)\n" name
  with _ -> incr tests_passed

let () =
  Printf.printf "=== Bytecode VM Tests ===\n\n";

  (* Basic arithmetic *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 3; OP_CONST_INT 4; OP_ADD; OP_HALT]));
  assert_equal "int add" "7" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 10; OP_CONST_INT 3; OP_SUB; OP_HALT]));
  assert_equal "int sub" "7" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 6; OP_CONST_INT 7; OP_MUL; OP_HALT]));
  assert_equal "int mul" "42" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 20; OP_CONST_INT 4; OP_DIV; OP_HALT]));
  assert_equal "int div" "5" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 17; OP_CONST_INT 5; OP_MOD; OP_HALT]));
  assert_equal "int mod" "2" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST 3.14; OP_CONST 2.0; OP_MUL; OP_HALT]));
  assert_equal "float mul" "6.28" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 42; OP_NEG; OP_HALT]));
  assert_equal "neg int" "-42" (value_to_string (peek vm));

  (* Comparisons *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 5; OP_CONST_INT 3; OP_GT; OP_HALT]));
  assert_equal "5 > 3" "true" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 3; OP_CONST_INT 5; OP_LT; OP_HALT]));
  assert_equal "3 < 5" "true" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 5; OP_CONST_INT 5; OP_EQ; OP_HALT]));
  assert_equal "5 == 5" "true" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 5; OP_CONST_INT 5; OP_LE; OP_HALT]));
  assert_equal "5 <= 5" "true" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 5; OP_CONST_INT 5; OP_GE; OP_HALT]));
  assert_equal "5 >= 5" "true" (value_to_string (peek vm));

  (* Boolean logic *)
  let vm = create_vm () in ignore (run vm (assemble [OP_TRUE; OP_FALSE; OP_AND; OP_HALT]));
  assert_equal "true && false" "false" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_TRUE; OP_FALSE; OP_OR; OP_HALT]));
  assert_equal "true || false" "true" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_FALSE; OP_NOT; OP_HALT]));
  assert_equal "not false" "true" (value_to_string (peek vm));

  (* Stack ops *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 1; OP_DUP; OP_ADD; OP_HALT]));
  assert_equal "dup + add" "2" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 1; OP_CONST_INT 2; OP_SWAP; OP_HALT]));
  assert_equal "swap top" "1" (value_to_string (peek vm));
  assert_equal "swap second" "2" (value_to_string (peek_at vm 1));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 1; OP_CONST_INT 2; OP_CONST_INT 3; OP_ROT; OP_HALT]));
  assert_equal "rot: top=1" "1" (value_to_string (peek vm));
  assert_equal "rot: mid=3" "3" (value_to_string (peek_at vm 1));
  assert_equal "rot: bot=2" "2" (value_to_string (peek_at vm 2));

  (* Strings *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_STR "hello "; OP_CONST_STR "world"; OP_ADD; OP_HALT]));
  assert_equal "string concat" "hello world" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_STR "count: "; OP_CONST_INT 42; OP_ADD; OP_HALT]));
  assert_equal "string + int" "count: 42" (value_to_string (peek vm));

  (* Globals *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 100; OP_GSTORE "x"; OP_GLOAD "x"; OP_CONST_INT 1; OP_ADD; OP_HALT]));
  assert_equal "global store/load" "101" (value_to_string (peek vm));

  (* Locals *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 10; OP_STORE 0; OP_CONST_INT 20; OP_STORE 1; OP_LOAD 0; OP_LOAD 1; OP_ADD; OP_HALT]));
  assert_equal "local vars" "30" (value_to_string (peek vm));

  (* Conditional jump *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 5; OP_CONST_INT 3; OP_GT; OP_JUMP_IF_FALSE 2; OP_CONST_INT 1; OP_JUMP 1; OP_CONST_INT 0; OP_HALT]));
  assert_equal "jump true path" "1" (value_to_string (peek vm));

  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 1; OP_CONST_INT 3; OP_GT; OP_JUMP_IF_FALSE 2; OP_CONST_INT 1; OP_JUMP 1; OP_CONST_INT 0; OP_HALT]));
  assert_equal "jump false path" "0" (value_to_string (peek vm));

  (* Loop: sum 1..5 *)
  let vm = create_vm () in ignore (run vm (assemble [
    OP_CONST_INT 0; OP_STORE 0; OP_CONST_INT 1; OP_STORE 1;
    OP_LOAD 1; OP_CONST_INT 5; OP_GT; OP_JUMP_IF_TRUE 6;
    OP_LOAD 0; OP_LOAD 1; OP_ADD; OP_STORE 0;
    OP_LOAD 1; OP_CONST_INT 1; OP_ADD; OP_STORE 1;
    OP_JUMP (-13); OP_LOAD 0; OP_HALT]));
  assert_equal "loop sum 1..5" "15" (value_to_string (peek vm));

  (* Function call *)
  let double_fn = { fn_name = "double"; fn_arity = 1; fn_code = assemble [OP_LOAD 0; OP_CONST_INT 2; OP_MUL; OP_RETURN] } in
  let vm = create_vm () in Hashtbl.replace vm.globals "double" (VFunction double_fn);
  ignore (run vm (assemble [OP_GLOAD "double"; OP_CONST_INT 21; OP_CALL 1; OP_HALT]));
  assert_equal "function call" "42" (value_to_string (peek vm));

  (* Native functions *)
  let vm = create_vm () in register_natives vm;
  ignore (run vm (assemble [OP_GLOAD "abs"; OP_CONST_INT (-7); OP_CALL 1; OP_HALT]));
  assert_equal "native abs(-7)" "7" (value_to_string (peek vm));

  let vm = create_vm () in register_natives vm;
  ignore (run vm (assemble [OP_GLOAD "max"; OP_CONST_INT 3; OP_CONST_INT 9; OP_CALL 2; OP_HALT]));
  assert_equal "native max(3,9)" "9" (value_to_string (peek vm));

  let vm = create_vm () in register_natives vm;
  ignore (run vm (assemble [OP_GLOAD "strlen"; OP_CONST_STR "hello"; OP_CALL 1; OP_HALT]));
  assert_equal "native strlen" "5" (value_to_string (peek vm));

  let vm = create_vm () in register_natives vm;
  ignore (run vm (assemble [OP_GLOAD "int"; OP_CONST 3.7; OP_CALL 1; OP_HALT]));
  assert_equal "native int(3.7)" "3" (value_to_string (peek vm));

  let vm = create_vm () in register_natives vm;
  ignore (run vm (assemble [OP_GLOAD "substr"; OP_CONST_STR "hello world"; OP_CONST_INT 6; OP_CONST_INT 5; OP_CALL 3; OP_HALT]));
  assert_equal "native substr" "world" (value_to_string (peek vm));

  let vm = create_vm () in register_natives vm;
  ignore (run vm (assemble [OP_GLOAD "float"; OP_CONST_INT 7; OP_CALL 1; OP_HALT]));
  assert_equal "native float(7)" "7" (value_to_string (peek vm));

  let vm = create_vm () in register_natives vm;
  ignore (run vm (assemble [OP_GLOAD "min"; OP_CONST_INT 3; OP_CONST_INT 9; OP_CALL 2; OP_HALT]));
  assert_equal "native min(3,9)" "3" (value_to_string (peek vm));

  (* Print *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_STR "hello"; OP_PRINT; OP_CONST_INT 42; OP_PRINT; OP_HALT]));
  assert_equal "print output" "hello,42" (String.concat "," (get_output vm));

  (* Value equality *)
  assert_true "veq int" (value_equal (VInt 5) (VInt 5));
  assert_true "veq int/float" (value_equal (VInt 5) (VFloat 5.0));
  assert_true "veq bool" (value_equal (VBool true) (VBool true));
  assert_true "veq nil" (value_equal VNil VNil);
  assert_true "veq string" (value_equal (VString "a") (VString "a"));
  assert_true "vneq" (not (value_equal (VInt 1) (VInt 2)));
  assert_true "vneq types" (not (value_equal (VInt 1) (VBool true)));

  (* Truthiness *)
  assert_true "truthy int" (value_is_truthy (VInt 0));
  assert_true "truthy true" (value_is_truthy (VBool true));
  assert_true "falsy false" (not (value_is_truthy (VBool false)));
  assert_true "falsy nil" (not (value_is_truthy VNil));

  (* Compiler *)
  let (r, _) = eval (EInt 42) in assert_equal "compile int" "42" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp ("+", EInt 3, EInt 4)) in assert_equal "compile add" "7" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp ("*", EBinOp ("+", EInt 2, EInt 3), EInt 4)) in assert_equal "compile nested" "20" (value_to_string (Option.get r));
  let (r, _) = eval (EUnOp ("-", EInt 5)) in assert_equal "compile neg" "-5" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp ("==", EInt 5, EInt 5)) in assert_equal "compile eq" "true" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp ("<", EInt 3, EInt 5)) in assert_equal "compile lt" "true" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp ("&&", EBool true, EBool false)) in assert_equal "compile and" "false" (value_to_string (Option.get r));
  let (r, _) = eval (EStr "hello") in assert_equal "compile str" "hello" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp (">=", EInt 5, EInt 3)) in assert_equal "compile >=" "true" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp ("<=", EInt 3, EInt 5)) in assert_equal "compile <=" "true" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp (">", EInt 5, EInt 3)) in assert_equal "compile >" "true" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp ("mod", EInt 10, EInt 3)) in assert_equal "compile mod" "1" (value_to_string (Option.get r));
  let (r, _) = eval (EBinOp ("or", EBool false, EBool true)) in assert_equal "compile or" "true" (value_to_string (Option.get r));
  let (r, _) = eval (EUnOp ("not", EBool true)) in assert_equal "compile not" "false" (value_to_string (Option.get r));
  let (r, _) = eval (ENum 2.718) in assert_equal "compile float" "2.718" (value_to_string (Option.get r));
  let (r, _) = eval ENil in assert_equal "compile nil" "nil" (value_to_string (Option.get r));
  let (r, _) = eval (EBool false) in assert_equal "compile false" "false" (value_to_string (Option.get r));

  (* Let bindings *)
  let (r, _) = eval (ELet ("x", EInt 10, EBinOp ("+", EVar "x", EInt 5))) in
  assert_equal "compile let" "15" (value_to_string (Option.get r));

  let (r, _) = eval (ELet ("x", EInt 3, ELet ("y", EInt 4, EBinOp ("+", EVar "x", EVar "y")))) in
  assert_equal "compile nested let" "7" (value_to_string (Option.get r));

  (* Print via compiler *)
  let (_, output) = eval (EPrint (EBinOp ("+", EInt 2, EInt 3))) in
  assert_equal "compile print" "5" (List.hd output);

  (* Sequence *)
  let (r, output) = eval (ESeq [EPrint (EInt 1); EPrint (EInt 2); EInt 3]) in
  assert_equal "seq result" "3" (value_to_string (Option.get r));
  assert_equal "seq output" "1,2" (String.concat "," output);

  (* Disassembler *)
  let code = assemble [OP_CONST_INT 1; OP_CONST_INT 2; OP_ADD; OP_HALT] in
  let dis = disassemble code in
  assert_true "disasm has content" (String.length dis > 0);

  (* Disassemble chunk *)
  let f = { fn_name = "add"; fn_arity = 2; fn_code = assemble [OP_LOAD 0; OP_LOAD 1; OP_ADD; OP_RETURN] } in
  let chunk = { ch_code = assemble [OP_HALT]; ch_functions = [|f|] } in
  assert_true "disasm chunk" (String.length (disassemble_chunk chunk) > 20);

  (* Error handling *)
  assert_raises "div by zero" (fun () -> let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 1; OP_CONST_INT 0; OP_DIV; OP_HALT])));
  assert_raises "stack underflow" (fun () -> let vm = create_vm () in ignore (run vm (assemble [OP_ADD; OP_HALT])));
  assert_raises "undefined global" (fun () -> let vm = create_vm () in ignore (run vm (assemble [OP_GLOAD "undef"; OP_HALT])));
  assert_raises "wrong arity" (fun () ->
    let vm = create_vm () in
    let f = { fn_name = "f"; fn_arity = 1; fn_code = assemble [OP_LOAD 0; OP_RETURN] } in
    Hashtbl.replace vm.globals "f" (VFunction f);
    ignore (run vm (assemble [OP_GLOAD "f"; OP_CONST_INT 1; OP_CONST_INT 2; OP_CALL 2; OP_HALT])));
  assert_raises "cannot call non-fn" (fun () -> let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 5; OP_CONST_INT 1; OP_CALL 1; OP_HALT])));
  assert_raises "neg non-number" (fun () -> let vm = create_vm () in ignore (run vm (assemble [OP_TRUE; OP_NEG; OP_HALT])));
  assert_raises "unknown binop" (fun () -> ignore (compile (EBinOp ("??", EInt 1, EInt 2))));
  assert_raises "unknown unop" (fun () -> ignore (compile (EUnOp ("~", EInt 1))));

  (* Factorial via loop *)
  let vm = create_vm () in ignore (run vm (assemble [
    OP_CONST_INT 1; OP_STORE 0; OP_CONST_INT 5; OP_STORE 1;
    OP_LOAD 1; OP_CONST_INT 1; OP_LE; OP_JUMP_IF_TRUE 6;
    OP_LOAD 0; OP_LOAD 1; OP_MUL; OP_STORE 0;
    OP_LOAD 1; OP_CONST_INT 1; OP_SUB; OP_STORE 1;
    OP_JUMP (-13); OP_LOAD 0; OP_HALT]));
  assert_equal "factorial 5" "120" (value_to_string (peek vm));

  (* Fibonacci via function *)
  let fib_fn = { fn_name = "fib"; fn_arity = 1; fn_code = assemble [
    OP_CONST_INT 0; OP_STORE 1; OP_CONST_INT 1; OP_STORE 2; OP_CONST_INT 0; OP_STORE 3;
    OP_LOAD 3; OP_LOAD 0; OP_GE; OP_JUMP_IF_TRUE 8;
    OP_LOAD 1; OP_LOAD 2; OP_ADD; OP_LOAD 2; OP_STORE 1; OP_STORE 2;
    OP_LOAD 3; OP_CONST_INT 1; OP_ADD; OP_STORE 3; OP_JUMP (-15); OP_LOAD 1; OP_RETURN] } in
  let vm = create_vm () in Hashtbl.replace vm.globals "fib" (VFunction fib_fn);
  ignore (run vm (assemble [OP_GLOAD "fib"; OP_CONST_INT 10; OP_CALL 1; OP_HALT]));
  assert_equal "fib(10)" "55" (value_to_string (peek vm));

  (* Trace mode *)
  let vm = create_vm ~trace:true () in ignore (run vm (assemble [OP_CONST_INT 1; OP_CONST_INT 2; OP_ADD; OP_HALT]));
  assert_true "trace has entries" (List.length (get_output vm) >= 3);

  (* NOP *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 7; OP_NOP; OP_NOP; OP_HALT]));
  assert_equal "nop" "7" (value_to_string (peek vm));

  (* value_to_string *)
  assert_equal "vts nil" "nil" (value_to_string VNil);
  assert_equal "vts bool" "true" (value_to_string (VBool true));
  assert_equal "vts int" "42" (value_to_string (VInt 42));
  assert_equal "vts float" "3.14" (value_to_string (VFloat 3.14));
  assert_equal "vts str" "hi" (value_to_string (VString "hi"));
  assert_equal "vts fn" "<fn test/2>" (value_to_string (VFunction { fn_name = "test"; fn_arity = 2; fn_code = [||] }));
  assert_equal "vts native" "<native foo>" (value_to_string (VNative ("foo", fun _ -> VNil)));

  (* Stack snapshot *)
  let vm = create_vm () in push vm (VInt 1); push vm (VInt 2); push vm (VInt 3);
  assert_equal "snapshot" "1,2,3" (String.concat "," (stack_snapshot vm));

  (* Mixed int/float *)
  let vm = create_vm () in ignore (run vm (assemble [OP_CONST_INT 3; OP_CONST 2.5; OP_ADD; OP_HALT]));
  assert_equal "int + float" "5.5" (value_to_string (peek vm));

  (* Chained calls *)
  let inc_fn = { fn_name = "inc"; fn_arity = 1; fn_code = assemble [OP_LOAD 0; OP_CONST_INT 1; OP_ADD; OP_RETURN] } in
  let vm = create_vm () in Hashtbl.replace vm.globals "inc" (VFunction inc_fn);
  ignore (run vm (assemble [OP_GLOAD "inc"; OP_CONST_INT 5; OP_CALL 1; OP_GSTORE "t"; OP_GLOAD "inc"; OP_GLOAD "t"; OP_CALL 1; OP_HALT]));
  assert_equal "chained calls" "7" (value_to_string (peek vm));

  Printf.printf "\n%d passed, %d failed (total %d)\n" !tests_passed !tests_failed (!tests_passed + !tests_failed)
