section {* WebAssembly Core AST *}

theory Wasm_Ast imports Main "AFP/Native_Word/Uint8" begin

type_synonym --"immediate"
  i = nat
type_synonym --"static offset"
  off = nat
type_synonym --"alignment exponent"
  a = nat

--"primitive types"
typedecl i32
typedecl i64
typedecl f32
typedecl f64

--"memory"
type_synonym byte = uint8

typedef bytes = "UNIV :: (byte list) set" ..
setup_lifting type_definition_bytes
declare Quotient_bytes[transfer_rule]

lift_definition bytes_takefill :: "byte \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> bytes" is "(\<lambda>a n as. takefill (Abs_uint8 a) n as)" .
lift_definition bytes_replicate :: "nat \<Rightarrow> byte \<Rightarrow> bytes" is "(\<lambda>n b. replicate n (Abs_uint8 b))" .
definition msbyte :: "bytes \<Rightarrow> byte" where
  "msbyte bs = last (Rep_bytes bs)"

typedef mem = "UNIV :: (byte list) set" ..
setup_lifting type_definition_mem
declare Quotient_mem[transfer_rule]

lift_definition read_bytes :: "mem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bytes" is "(\<lambda>m n l. take l (drop n m))" .
lift_definition write_bytes :: "mem \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> mem" is "(\<lambda>m n bs. (take n m) @ bs @ (drop (n + length bs) m))" .
lift_definition mem_append :: "mem \<Rightarrow> bytes \<Rightarrow> mem" is append .

--"host"
typedecl host
typedecl host_state

datatype --"secrecy type"
  sec = Secret | Public

datatype --"trust type"
  trust = Trusted | Untrusted

datatype --"value types"
  t = T_i32 sec | T_i64 sec | T_f32 | T_f64

datatype --"packed types"
  tp = Tp_i8 | Tp_i16 | Tp_i32

datatype --"mutability"
  mut = T_immut | T_mut

record tg = --"global types"
  tg_mut :: mut
  tg_t :: t

datatype --"function types"
  tf = Tf "t list" "t list" ("_ '_> _" 60)

type_synonym --"function type with trust"
  tf_t = "trust \<times> tf"

(* TYPING *)
record t_context =
  trust_t :: trust
  types_t :: "tf_t list"
  func_t :: "tf_t list"
  global :: "tg list"
  table :: "nat option"
  memory :: "(nat \<times> sec) option"
  local :: "t list"
  label :: "(t list) list"
  return :: "(t list) option"

record s_context =
  s_inst :: "t_context list"
  s_funcs :: "tf_t list"
  s_tab  :: "nat list"
  s_mem  :: "(nat \<times> sec) list"
  s_globs :: "tg list"

datatype
  sx = S | U

datatype
  unop_i = Clz | Ctz | Popcnt

datatype
  unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt

datatype
  binop_i = Add | Sub | Mul | Div sx | Rem sx | And | Or | Xor | Shl | Shr sx | Rotl | Rotr

datatype
  binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign
  
datatype
  testop = Eqz
  
datatype
  relop_i = Eq | Ne | Lt sx | Gt sx | Le sx | Ge sx
  
datatype
  relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef
  
datatype
  cvtop = Convert | Reinterpret | Classify | Declassify

datatype --"values"
  v =
    ConstInt32 sec i32
    | ConstInt64 sec i64
    | ConstFloat32 f32
    | ConstFloat64 f64

datatype --"basic instructions"
  b_e =
    Unreachable
    | Nop
    | Drop
    | Select sec
    | Block tf "b_e list"
    | Loop tf "b_e list"
    | If tf "b_e list" "b_e list"
    | Br i
    | Br_if i
    | Br_table "i list" i
    | Return
    | Call i
    | Call_indirect i
    | Get_local i
    | Set_local i
    | Tee_local i
    | Get_global i
    | Set_global i
    | Load t "(tp \<times> sx) option" a off
    | Store t "tp option" a off
    | Current_memory
    | Grow_memory
    | EConst v ("C _" 60)
    | Unop_i t unop_i
    | Unop_f t unop_f
    | Binop_i t binop_i
    | Binop_f t binop_f
    | Testop t testop
    | Relop_i t relop_i
    | Relop_f t relop_f
    | Cvtop t cvtop t "sx option"

datatype cl = --"function closures"
  Func_native i tf_t "t list" "b_e list"
| Func_host tf_t host

record inst = --"instances"
  types :: "tf_t list"
  funcs :: "i list"
  tab :: "i option"
  mem :: "i option"
  globs :: "i list"

type_synonym tabinst = "(cl option) list"

record global =
  g_mut :: mut
  g_val :: v

record s = --"store"
  inst :: "inst list"
  funcs :: "cl list"
  tab :: "tabinst list"
  mem :: "(mem \<times> sec) list"
  globs :: "global list"

datatype e = --"administrative instruction"
  Basic b_e ("$_" 60)
  | Trap
  | Callcl cl
  | Label nat "e list" "e list"
  | Local nat i "v list" "e list"

datatype Lholed =
    --"L0 = v* [<hole>] e*"
    LBase "e list" "e list"
    --"L(i+1) = v* (label n {e* } Li) e*"
  | LRec "e list" nat "e list" Lholed "e list"

datatype action =
  Unop_i32_action unop_i
| Unop_i64_action unop_i
| Unop_f32_action unop_f f32
| Unop_f64_action unop_f f64
| Binop_i32_Some_action binop_i i32 i32
| Binop_i32_None_action binop_i i32 i32
| Binop_i64_Some_action binop_i i64 i64
| Binop_i64_None_action binop_i i64 i64
| Binop_f32_Some_action binop_f f32 f32
| Binop_f32_None_action binop_f f32 f32
| Binop_f64_Some_action binop_f f64 f64
| Binop_f64_None_action binop_f f64 f64
| Testop_i32_action testop
| Testop_i64_action testop
| Relop_i32_action relop_i
| Relop_i64_action relop_i
| Relop_f32_action relop_f f32 f32
| Relop_f64_action relop_f f64 f64
| Convert_Some_action t t v
| Convert_None_action t t v
| Reinterpret_action
| Classify_action
| Declassify_action
| Unreachable_action
| Nop_action
| Drop_action
| Select_action sec i32
| Block_action
| Loop_action
| If_false_action i32
| If_true_action i32
| Label_const_action
| Label_trap_action
| Br_action
| Br_if_false_action i32
| Br_if_true_action i32
| Br_table_action i32
| Br_table_length_action i32
| Local_const_action
| Local_trap_action
| Return_action
| Tee_local_action
| Trap_action
| Call_action
| Call_indirect_Some_action i32
| Call_indirect_None_action i32
| Callcl_native_action nat
| Callcl_host_Some_action s "v list" s "v list" trust tf host host_state
| Callcl_host_None_action s "v list" trust tf host host_state
| Get_local_action
| Set_local_action
| Get_global_action
| Set_global_action
| Load_Some_action t nat a off
| Load_None_action t nat a off
| Load_packed_Some_action tp sx nat a off
| Load_packed_None_action tp sx nat a off
| Store_Some_action t nat a off
| Store_None_action t nat a off
| Store_packed_Some_action t tp nat a off
| Store_packed_None_action t tp nat a off
| Current_memory_action nat
| Grow_memory_Some_action nat nat
| Grow_memory_None_action nat nat
| Label_action
| Local_action

end
