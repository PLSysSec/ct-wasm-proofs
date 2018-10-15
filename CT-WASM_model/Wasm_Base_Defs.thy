section {* WebAssembly Base Definitions *}

theory Wasm_Base_Defs imports Wasm_Ast Wasm_Type_Abs begin

instantiation i32 :: wasm_int begin instance .. end
instantiation i64 :: wasm_int begin instance .. end
instantiation f32 :: wasm_float begin instance .. end
instantiation f64 :: wasm_float begin instance .. end

consts
  (* inter-type conversions *)
  (* float to i32 *)
  ui32_trunc_f32 :: "f32 \<Rightarrow> i32 option"
  si32_trunc_f32 :: "f32 \<Rightarrow> i32 option"
  ui32_trunc_f64 :: "f64 \<Rightarrow> i32 option"
  si32_trunc_f64 :: "f64 \<Rightarrow> i32 option"
  (* float to i64 *)
  ui64_trunc_f32 :: "f32 \<Rightarrow> i64 option"
  si64_trunc_f32 :: "f32 \<Rightarrow> i64 option"
  ui64_trunc_f64 :: "f64 \<Rightarrow> i64 option"
  si64_trunc_f64 :: "f64 \<Rightarrow> i64 option"
  (* int to f32 *)
  f32_convert_ui32 :: "i32 \<Rightarrow> f32"
  f32_convert_si32 :: "i32 \<Rightarrow> f32"
  f32_convert_ui64 :: "i64 \<Rightarrow> f32"
  f32_convert_si64 :: "i64 \<Rightarrow> f32"
  (* int to f64 *)
  f64_convert_ui32 :: "i32 \<Rightarrow> f64"
  f64_convert_si32 :: "i32 \<Rightarrow> f64"
  f64_convert_ui64 :: "i64 \<Rightarrow> f64"
  f64_convert_si64 :: "i64 \<Rightarrow> f64"
  (* intra-{int/float} conversions *)
  wasm_wrap :: "i64 \<Rightarrow> i32"
  wasm_extend_u :: "i32 \<Rightarrow> i64"
  wasm_extend_s :: "i32 \<Rightarrow> i64"
  wasm_demote :: "f64 \<Rightarrow> f32"
  wasm_promote :: "f32 \<Rightarrow> f64"
  (* boolean encoding *)
  serialise_i32 :: "i32 \<Rightarrow> bytes"
  serialise_i64 :: "i64 \<Rightarrow> bytes"
  serialise_f32 :: "f32 \<Rightarrow> bytes"
  serialise_f64 :: "f64 \<Rightarrow> bytes"
  wasm_bool :: "bool \<Rightarrow> i32"
  int32_minus_one :: i32

  (* memory *)
definition mem_size :: "mem \<Rightarrow> nat" where
  "mem_size m = length (Rep_mem m)"

definition mem_grow :: "mem \<Rightarrow> nat \<Rightarrow> mem" where
  "mem_grow m n = mem_append m (bytes_replicate (n * 64000) 0)"

definition load :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> nat \<Rightarrow> bytes option" where
  "load m n off l = (if (mem_size m \<ge> (n+off+l))
                       then Some (read_bytes m (n+off) l)
                       else None)"

definition sign_extend :: "sx \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> bytes" where
  "sign_extend sx l bytes = (let msb = msb (msbyte bytes) in
                          let byte = (case sx of U \<Rightarrow> 0 | S \<Rightarrow> if msb then -1 else 0) in
                          bytes_takefill byte l bytes)"

definition load_packed :: "sx \<Rightarrow> mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bytes option" where
  "load_packed sx m n off lp l = map_option (sign_extend sx l) (load m n off lp)"

definition store :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> bytes \<Rightarrow> nat \<Rightarrow> mem option" where
  "store m n off bs l = (if (mem_size m \<ge> (n+off+l))
                          then Some (write_bytes m (n+off) (bytes_takefill 0 l bs))
                          else None)"

definition store_packed :: "mem \<Rightarrow> nat \<Rightarrow> off \<Rightarrow> bytes \<Rightarrow> nat \<Rightarrow> mem option" where
  "store_packed = store"

consts
  wasm_deserialise :: "bytes \<Rightarrow> t \<Rightarrow> v"
  (* host *)
  host_apply :: "s \<Rightarrow> tf \<Rightarrow> host \<Rightarrow> v list \<Rightarrow> host_state \<Rightarrow> (s \<times> v list) option"

definition typeof :: " v \<Rightarrow> t" where
  "typeof v = (case v of
                 ConstInt32 sec _ \<Rightarrow> (T_i32 sec)
               | ConstInt64 sec _ \<Rightarrow> (T_i64 sec)
               | ConstFloat32 _ \<Rightarrow> T_f32
               | ConstFloat64 _ \<Rightarrow> T_f64)"

definition trust_compat :: "trust \<Rightarrow> trust \<Rightarrow> bool" where
  "trust_compat tr tr' = (tr = Trusted \<or> (tr = Untrusted \<and> tr' = Untrusted))"

definition classify_t :: "t \<Rightarrow> t" where
  "classify_t t = (case t of
                     T_i32 _ \<Rightarrow> T_i32 Secret
                   | T_i64 _ \<Rightarrow> T_i64 Secret
                   | T_f32 \<Rightarrow> T_f32
                   | T_f64 \<Rightarrow> T_f64)"

definition classify :: "v \<Rightarrow> v" where
  "classify v = (case v of
                   ConstInt32 sec c \<Rightarrow> ConstInt32 Secret c
                 | ConstInt64 sec c \<Rightarrow> ConstInt64 Secret c
                 | ConstFloat32 c \<Rightarrow> ConstFloat32 c
                 | ConstFloat64 c \<Rightarrow> ConstFloat64 c)"

definition declassify_t :: "t \<Rightarrow> t" where
  "declassify_t t = (case t of
                     T_i32 _ \<Rightarrow> T_i32 Public
                   | T_i64 _ \<Rightarrow> T_i64 Public
                   | T_f32 \<Rightarrow> T_f32
                   | T_f64 \<Rightarrow> T_f64)"

definition declassify :: "v \<Rightarrow> v" where
  "declassify v = (case v of
                   ConstInt32 sec c \<Rightarrow> ConstInt32 Public c
                 | ConstInt64 sec c \<Rightarrow> ConstInt64 Public c
                 | ConstFloat32 c \<Rightarrow> ConstFloat32 c
                 | ConstFloat64 c \<Rightarrow> ConstFloat64 c)"

definition option_projl :: "('a \<times> 'b) option \<Rightarrow> 'a option" where
  "option_projl x = map_option fst x"

definition option_projr :: "('a \<times> 'b) option \<Rightarrow> 'b option" where
  "option_projr x = map_option snd x"

definition t_length :: "t \<Rightarrow> nat" where
 "t_length t = (case t of
                  T_i32 _ \<Rightarrow> 4
                | T_i64 _ \<Rightarrow> 8
                | T_f32 \<Rightarrow> 4
                | T_f64 \<Rightarrow> 8)"

definition tp_length :: "tp \<Rightarrow> nat" where
 "tp_length tp = (case tp of
                 Tp_i8 \<Rightarrow> 1
               | Tp_i16 \<Rightarrow> 2
               | Tp_i32 \<Rightarrow> 4)"

definition t_sec :: "t \<Rightarrow> sec" where
 "t_sec t = (case t of
               T_i32 sec \<Rightarrow> sec
             | T_i64 sec \<Rightarrow> sec
             | T_f32 \<Rightarrow> Public
             | T_f64 \<Rightarrow> Public)"

abbreviation is_public_t :: "t \<Rightarrow> bool" where
  "is_public_t t \<equiv> ((t_sec t) = Public)"

abbreviation is_secret_t :: "t \<Rightarrow> bool" where
  "is_secret_t t \<equiv> ((t_sec t) = Secret)"

definition is_int_t :: "t \<Rightarrow> bool" where
 "is_int_t t = (case t of
                  T_i32 _ \<Rightarrow> True
                | T_i64 _ \<Rightarrow> True
                | T_f32 \<Rightarrow> False
                | T_f64 \<Rightarrow> False)"

definition is_float_t :: "t \<Rightarrow> bool" where
 "is_float_t t = (case t of
                    T_i32 _ \<Rightarrow> False
                  | T_i64 _ \<Rightarrow> False
                  | T_f32 \<Rightarrow> True
                  | T_f64 \<Rightarrow> True)"

definition is_mut :: "tg \<Rightarrow> bool" where
  "is_mut tg = (tg_mut tg = T_mut)"

definition safe_binop_i :: "binop_i \<Rightarrow> bool" where
  "safe_binop_i bop =
     (case bop of
        Div _ \<Rightarrow> False
      | Rem _ \<Rightarrow> False
      | _ \<Rightarrow> True)"

definition app_unop_i :: "unop_i \<Rightarrow> 'i::wasm_int \<Rightarrow> 'i::wasm_int" where
  "app_unop_i iop c =
     (case iop of
     Ctz \<Rightarrow> int_ctz c
   | Clz \<Rightarrow> int_clz c
   | Popcnt \<Rightarrow> int_popcnt c)"

definition app_unop_f :: "unop_f \<Rightarrow> 'f::wasm_float \<Rightarrow> 'f::wasm_float" where
  "app_unop_f fop c =
                 (case fop of
                    Neg \<Rightarrow> float_neg c
                  | Abs \<Rightarrow> float_abs c
                  | Ceil \<Rightarrow> float_ceil c
                  | Floor \<Rightarrow> float_floor c
                  | Trunc \<Rightarrow> float_trunc c
                  | Nearest \<Rightarrow> float_nearest c
                  | Sqrt \<Rightarrow> float_sqrt c)"

definition app_binop_i :: "binop_i \<Rightarrow> 'i::wasm_int \<Rightarrow> 'i::wasm_int \<Rightarrow> ('i::wasm_int) option" where
  "app_binop_i iop c1 c2 = (case iop of
                              Add \<Rightarrow> Some (int_add c1 c2)
                            | Sub \<Rightarrow> Some (int_sub c1 c2)
                            | Mul \<Rightarrow> Some (int_mul c1 c2)
                            | Div U \<Rightarrow> int_div_u c1 c2
                            | Div S \<Rightarrow> int_div_s c1 c2
                            | Rem U \<Rightarrow> int_rem_u c1 c2
                            | Rem S \<Rightarrow> int_rem_s c1 c2
                            | And \<Rightarrow> Some (int_and c1 c2)
                            | Or \<Rightarrow> Some (int_or c1 c2)
                            | Xor \<Rightarrow> Some (int_xor c1 c2)
                            | Shl \<Rightarrow> Some (int_shl c1 c2)
                            | Shr U \<Rightarrow> Some (int_shr_u c1 c2)
                            | Shr S \<Rightarrow> Some (int_shr_s c1 c2)
                            | Rotl \<Rightarrow> Some (int_rotl c1 c2)
                            | Rotr \<Rightarrow> Some (int_rotr c1 c2))"

definition app_binop_f :: "binop_f \<Rightarrow> 'f::wasm_float \<Rightarrow> 'f::wasm_float \<Rightarrow> ('f::wasm_float) option" where
  "app_binop_f fop c1 c2 = (case fop of
                              Addf \<Rightarrow> Some (float_add c1 c2)
                            | Subf \<Rightarrow> Some (float_sub c1 c2)
                            | Mulf \<Rightarrow> Some (float_mul c1 c2)
                            | Divf \<Rightarrow> Some (float_div c1 c2)
                            | Min \<Rightarrow> Some (float_min c1 c2)
                            | Max \<Rightarrow> Some (float_max c1 c2)
                            | Copysign \<Rightarrow> Some (float_copysign c1 c2))"

definition app_testop_i :: "testop \<Rightarrow> 'i::wasm_int \<Rightarrow> bool" where
  "app_testop_i testop c = (case testop of Eqz \<Rightarrow> int_eqz c)"

definition app_relop_i :: "relop_i \<Rightarrow> 'i::wasm_int \<Rightarrow> 'i::wasm_int \<Rightarrow> bool" where
  "app_relop_i rop c1 c2 = (case rop of
                              Eq \<Rightarrow> int_eq c1 c2
                            | Ne \<Rightarrow> int_ne c1 c2
                            | Lt U \<Rightarrow> int_lt_u c1 c2
                            | Lt S \<Rightarrow> int_lt_s c1 c2
                            | Gt U \<Rightarrow> int_gt_u c1 c2
                            | Gt S \<Rightarrow> int_gt_s c1 c2
                            | Le U \<Rightarrow> int_le_u c1 c2
                            | Le S \<Rightarrow> int_le_s c1 c2
                            | Ge U \<Rightarrow> int_ge_u c1 c2
                            | Ge S \<Rightarrow> int_ge_s c1 c2)"

definition app_relop_f :: "relop_f \<Rightarrow> 'f::wasm_float \<Rightarrow> 'f::wasm_float \<Rightarrow> bool" where
  "app_relop_f rop c1 c2 = (case rop of
                              Eqf \<Rightarrow> float_eq c1 c2
                            | Nef \<Rightarrow> float_ne c1 c2
                            | Ltf \<Rightarrow> float_lt c1 c2
                            | Gtf \<Rightarrow> float_gt c1 c2
                            | Lef \<Rightarrow> float_le c1 c2
                            | Gef \<Rightarrow> float_ge c1 c2)" 

definition types_agree :: "t \<Rightarrow> v \<Rightarrow> bool" where
  "types_agree t v = (typeof v = t)"

definition types_agree_insecure :: "t \<Rightarrow> v \<Rightarrow> bool" where
  "types_agree_insecure t v = (let v_t = typeof v in
                               is_int_t v_t = is_int_t t \<and> t_length v_t = t_length t)"

definition cl_type :: "cl \<Rightarrow> tf_t" where
  "cl_type cl = (case cl of Func_native _ tf _ _ \<Rightarrow> tf | Func_host tf _ \<Rightarrow> tf)"

definition rglob_is_mut :: "global \<Rightarrow> bool" where
  "rglob_is_mut g = (g_mut g = T_mut)"

definition stypes :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tf_t" where
  "stypes s i j = ((types ((inst s)!i))!j)"
  
definition sfunc_ind :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sfunc_ind s i j = ((inst.funcs ((inst s)!i))!j)"

definition sfunc :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cl" where
  "sfunc s i j = (funcs s)!(sfunc_ind s i j)"

definition sglob_ind :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sglob_ind s i j = ((inst.globs ((inst s)!i))!j)"
  
definition sglob :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> global" where
  "sglob s i j = (globs s)!(sglob_ind s i j)"

definition sglob_val :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> v" where
  "sglob_val s i j = g_val (sglob s i j)"

definition smem_ind :: "s \<Rightarrow> nat \<Rightarrow> nat option" where
  "smem_ind s i = (inst.mem ((inst s)!i))"

definition stab_s :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cl option" where
  "stab_s s i j = (let stabinst = ((tab s)!i) in  (if (length (stabinst) > j) then (stabinst!j) else None))"

definition stab :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cl option" where
  "stab s i j = (case (inst.tab ((inst s)!i)) of Some k => stab_s s k j | None => None)"

definition supdate_glob_s :: "s \<Rightarrow> nat \<Rightarrow> v \<Rightarrow> s" where
  "supdate_glob_s s k v = s\<lparr>globs := (globs s)[k:=((globs s)!k)\<lparr>g_val := v\<rparr>]\<rparr>"

definition supdate_glob :: "s \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> v \<Rightarrow> s" where
  "supdate_glob s i j v = (let k = sglob_ind s i j in supdate_glob_s s k v)"

definition is_const :: "e \<Rightarrow> bool" where
  "is_const e = (case e of Basic (C _) \<Rightarrow> True | _ \<Rightarrow> False)"
    
definition const_list :: "e list \<Rightarrow> bool" where
  "const_list xs = list_all is_const xs"

inductive store_extension :: "s \<Rightarrow> s \<Rightarrow> bool" where
"\<lbrakk>insts = insts'; fs = fs'; tclss = tclss'; list_all2 (\<lambda>(bs,sec) (bs',sec'). mem_size bs \<le> mem_size bs' \<and> sec = sec') bss bss'; gs = gs'\<rbrakk> \<Longrightarrow>
  store_extension \<lparr>s.inst = insts, s.funcs = fs, s.tab = tclss, s.mem = bss, s.globs = gs\<rparr>
                    \<lparr>s.inst = insts', s.funcs = fs', s.tab = tclss', s.mem = bss', s.globs = gs'\<rparr>"

abbreviation to_e_list :: "b_e list \<Rightarrow> e list" ("$* _" 60) where
  "to_e_list b_es \<equiv> map Basic b_es"

abbreviation v_to_e_list :: "v list \<Rightarrow> e list" ("$$* _" 60) where
  "v_to_e_list ves \<equiv> map (\<lambda>v. $C v) ves"

  (* Lfilled depth thing-to-fill fill-with result *)
inductive Lfilled :: "nat \<Rightarrow> Lholed \<Rightarrow> e list \<Rightarrow> e list \<Rightarrow> bool" where
  (* "Lfill (LBase vs es') es = vs @ es @ es'" *)
  L0:"\<lbrakk>const_list vs; lholed = (LBase vs es')\<rbrakk> \<Longrightarrow> Lfilled 0 lholed es (vs @ es @ es')"
  (* "Lfill (LRec vs ts es' l es'') es = vs @ [Label ts es' (Lfill l es)] @ es''" *)
| LN:"\<lbrakk>const_list vs; lholed = (LRec vs n es' l es''); Lfilled k l es lfilledk\<rbrakk> \<Longrightarrow> Lfilled (k+1) lholed es (vs @ [Label n es' lfilledk] @ es'')"

  (* Lfilled depth thing-to-fill fill-with result *)
inductive Lfilled_exact :: "nat \<Rightarrow> Lholed \<Rightarrow> e list \<Rightarrow> e list \<Rightarrow> bool" where
  (* "Lfill (LBase vs es') es = vs @ es @ es'" *)
  L0:"\<lbrakk>lholed = (LBase [] [])\<rbrakk> \<Longrightarrow> Lfilled_exact 0 lholed es es"
  (* "Lfill (LRec vs ts es' l es'') es = vs @ [Label ts es' (Lfill l es)] @ es''" *)
| LN:"\<lbrakk>const_list vs; lholed = (LRec vs n es' l es''); Lfilled_exact k l es lfilledk\<rbrakk> \<Longrightarrow> Lfilled_exact (k+1) lholed es (vs @ [Label n es' lfilledk] @ es'')"

definition load_store_t_bounds :: "a \<Rightarrow> tp option \<Rightarrow> t \<Rightarrow> bool" where
  "load_store_t_bounds a tp t = (case tp of
                                   None \<Rightarrow> 2^a \<le> t_length t
                                 | Some tp \<Rightarrow> 2^a \<le> tp_length tp \<and> tp_length tp < t_length t \<and>  is_int_t t)"

definition memory_public_agree :: "(mem \<times> sec) \<Rightarrow> (mem \<times> sec) \<Rightarrow> bool" where
  "memory_public_agree x y = (x = y \<or> (mem_size (fst x) = mem_size (fst y) \<and> (snd x = Secret) \<and> (snd y = Secret)))"

abbreviation memories_public_agree :: "(mem \<times> sec) list \<Rightarrow> (mem \<times> sec) list \<Rightarrow> bool" where
  "memories_public_agree xs ys \<equiv> list_all2 memory_public_agree xs ys"

definition public_agree :: "v \<Rightarrow> v \<Rightarrow> bool" where
  "public_agree x y = (y = x \<or> ((typeof y) = (typeof x) \<and> is_secret_t (typeof x)))"

abbreviation publics_agree :: "v list \<Rightarrow> v list \<Rightarrow> bool" where
  "publics_agree xs ys \<equiv> list_all2 public_agree xs ys"

definition global_public_agree :: "global \<Rightarrow> global \<Rightarrow> bool" where
  "global_public_agree x y = (g_mut x = g_mut y \<and> public_agree (g_val x) (g_val y))"

abbreviation globals_public_agree :: "global list \<Rightarrow> global list \<Rightarrow> bool" where
  "globals_public_agree xs ys \<equiv> list_all2 global_public_agree xs ys"

definition store_public_agree :: "s \<Rightarrow> s \<Rightarrow> bool" where
  "store_public_agree s s' = (inst s = inst s' \<and>
                        funcs s = funcs s' \<and>
                        tab s = tab s' \<and>
                        memories_public_agree (mem s) (mem s') \<and>
                        globals_public_agree (globs s) (globs s'))"

inductive expr_public_agree :: "e \<Rightarrow> e \<Rightarrow> bool" where
  "expr_public_agree e e"
| "\<lbrakk>public_agree v v'\<rbrakk> \<Longrightarrow>
     expr_public_agree ($C v) ($C v')"
| "\<lbrakk>list_all2 expr_public_agree ($* bes) ($* bes')\<rbrakk> \<Longrightarrow>
     expr_public_agree ($Block tf bes) ($Block tf bes')"
| "\<lbrakk>list_all2 expr_public_agree ($* bes) ($* bes')\<rbrakk> \<Longrightarrow>
     expr_public_agree ($Loop tf bes) ($Loop tf bes')"
| "\<lbrakk>list_all2 expr_public_agree ($* bes1) ($* bes1'); list_all2 expr_public_agree ($* bes2) ($* bes2')\<rbrakk> \<Longrightarrow>
     expr_public_agree ($If tf bes1 bes2) ($If tf bes1' bes2')"
| "\<lbrakk>list_all2 expr_public_agree les les'; list_all2 expr_public_agree es es'\<rbrakk> \<Longrightarrow>
     expr_public_agree (Label n les es) (Label n les' es')"
| "\<lbrakk>publics_agree vs vs'; list_all2 expr_public_agree es es'\<rbrakk> \<Longrightarrow>
     expr_public_agree (Local n i vs es) (Local n i vs' es')"

abbreviation exprs_public_agree :: "e list \<Rightarrow> e list \<Rightarrow> bool" where
  "exprs_public_agree es es' \<equiv> list_all2 expr_public_agree es es'"

inductive lholed_public_agree :: " Lholed \<Rightarrow> Lholed \<Rightarrow> bool" where
  "\<lbrakk>exprs_public_agree ves ves'; exprs_public_agree es es'\<rbrakk> \<Longrightarrow> lholed_public_agree (LBase ves es) (LBase ves' es')"
| "\<lbrakk>lholed_public_agree LN LN'; exprs_public_agree ves ves'; exprs_public_agree les les'; exprs_public_agree es es'\<rbrakk> \<Longrightarrow>
     lholed_public_agree (LRec ves n les LN es) (LRec ves' n les' LN' es')"


definition cvt_i32 :: "sx option \<Rightarrow> v \<Rightarrow> i32 option" where
  "cvt_i32 sx v = (case v of
                   ConstInt32 _ c \<Rightarrow> None
                 | ConstInt64 _ c \<Rightarrow> Some (wasm_wrap c)
                 | ConstFloat32 c \<Rightarrow> (case sx of
                                        Some U \<Rightarrow> ui32_trunc_f32 c
                                      | Some S \<Rightarrow> si32_trunc_f32 c
                                      | None \<Rightarrow> None)
                 | ConstFloat64 c \<Rightarrow> (case sx of
                                        Some U \<Rightarrow> ui32_trunc_f64 c
                                      | Some S \<Rightarrow> si32_trunc_f64 c
                                      | None \<Rightarrow> None))"

definition cvt_i64 :: "sx option \<Rightarrow> v \<Rightarrow> i64 option" where
  "cvt_i64 sx v = (case v of
                   ConstInt32 _ c \<Rightarrow> (case sx of
                                        Some U \<Rightarrow> Some (wasm_extend_u c)
                                      | Some S \<Rightarrow> Some (wasm_extend_s c)
                                      | None \<Rightarrow> None)
                 | ConstInt64 _ c \<Rightarrow> None
                 | ConstFloat32 c \<Rightarrow> (case sx of
                                        Some U \<Rightarrow> ui64_trunc_f32 c
                                      | Some S \<Rightarrow> si64_trunc_f32 c
                                      | None \<Rightarrow> None)
                 | ConstFloat64 c \<Rightarrow> (case sx of
                                        Some U \<Rightarrow> ui64_trunc_f64 c
                                      | Some S \<Rightarrow> si64_trunc_f64 c
                                      | None \<Rightarrow> None))"

definition cvt_f32 :: "sx option \<Rightarrow> v \<Rightarrow> f32 option" where
  "cvt_f32 sx v = (case v of
                   ConstInt32 _ c \<Rightarrow> (case sx of
                                      Some U \<Rightarrow> Some (f32_convert_ui32 c)
                                    | Some S \<Rightarrow> Some (f32_convert_si32 c)
                                    | _ \<Rightarrow> None)
                 | ConstInt64 _ c \<Rightarrow> (case sx of
                                      Some U \<Rightarrow> Some (f32_convert_ui64 c)
                                    | Some S \<Rightarrow> Some (f32_convert_si64 c)
                                    | _ \<Rightarrow> None)
                 | ConstFloat32 c \<Rightarrow> None
                 | ConstFloat64 c \<Rightarrow> Some (wasm_demote c))"

definition cvt_f64 :: "sx option \<Rightarrow> v \<Rightarrow> f64 option" where
  "cvt_f64 sx v = (case v of
                   ConstInt32 _ c \<Rightarrow> (case sx of
                                      Some U \<Rightarrow> Some (f64_convert_ui32 c)
                                    | Some S \<Rightarrow> Some (f64_convert_si32 c)
                                    | _ \<Rightarrow> None)
                 | ConstInt64 _ c \<Rightarrow> (case sx of
                                      Some U \<Rightarrow> Some (f64_convert_ui64 c)
                                    | Some S \<Rightarrow> Some (f64_convert_si64 c)
                                    | _ \<Rightarrow> None)
                 | ConstFloat32 c \<Rightarrow> Some (wasm_promote c)
                 | ConstFloat64 c \<Rightarrow> None)"

definition cvt :: "t \<Rightarrow> sx option \<Rightarrow> v \<Rightarrow> v option" where
  "cvt t sx v = (case t of
                 (T_i32 sec) \<Rightarrow> (case (cvt_i32 sx v) of Some c \<Rightarrow> Some (ConstInt32 sec c) | None \<Rightarrow> None)
               | (T_i64 sec) \<Rightarrow> (case (cvt_i64 sx v) of Some c \<Rightarrow> Some (ConstInt64 sec c) | None \<Rightarrow> None)
               | T_f32 \<Rightarrow> (case (cvt_f32 sx v) of Some c \<Rightarrow> Some (ConstFloat32 c) | None \<Rightarrow> None)
               | T_f64 \<Rightarrow> (case (cvt_f64 sx v) of Some c \<Rightarrow> Some (ConstFloat64 c) | None \<Rightarrow> None))"

definition bits :: "v \<Rightarrow> bytes" where
  "bits v = (case v of
               ConstInt32 _ c \<Rightarrow> (serialise_i32 c)
             | ConstInt64 _ c \<Rightarrow> (serialise_i64 c)
             | ConstFloat32 c \<Rightarrow> (serialise_f32 c)
             | ConstFloat64 c \<Rightarrow> (serialise_f64 c))"

definition bitzero :: "t \<Rightarrow> v" where
  "bitzero t = (case t of
                (T_i32 sec) \<Rightarrow> ConstInt32 sec 0
              | (T_i64 sec) \<Rightarrow> ConstInt64 sec 0
              | T_f32 \<Rightarrow> ConstFloat32 0
              | T_f64 \<Rightarrow> ConstFloat64 0)"

definition n_zeros :: "t list \<Rightarrow> v list" where
  "n_zeros ts = (map (\<lambda>t. bitzero t) ts)"

lemma is_int_t_exists:
  assumes "is_int_t t"
  shows "\<exists>sec. t = (T_i32 sec) \<or> t = (T_i64 sec)"
  using assms
  by (cases t) (auto simp add: is_int_t_def)

lemma is_float_t_exists:
  assumes "is_float_t t"
  shows "\<exists>sec. t = T_f32 \<or> t = T_f64"
  using assms
  by (cases t) (auto simp add: is_float_t_def)


lemma int_float_disjoint: "is_int_t t = -(is_float_t t)"
  by simp (metis is_float_t_def is_int_t_def t.exhaust t.simps(15-18))

lemma types_agree_imp_types_agree_insecure:
  assumes "types_agree t v"
  shows "types_agree_insecure t v"
  using assms
  unfolding types_agree_def types_agree_insecure_def
  by simp

lemma stab_unfold:
  assumes "stab s i j = Some cl"
  shows "\<exists>k. inst.tab ((inst s)!i) = Some k \<and> length ((tab s)!k) > j \<and>((tab s)!k)!j = Some cl"
proof -
  obtain k where have_k:"(inst.tab ((inst s)!i)) = Some k"
    using assms
    unfolding stab_def
    by fastforce
  hence s_o:"stab s i j = stab_s s k j"
    using assms
    unfolding stab_def
    by simp
  then obtain stabinst where stabinst_def:"stabinst = ((tab s)!k)"
    by blast
  hence "stab_s s k j = (stabinst!j) \<and> (length stabinst > j)"
    using assms s_o
    unfolding stab_s_def
    by (cases "(length stabinst > j)", auto)
  thus ?thesis
    using have_k stabinst_def assms s_o
    by auto
qed

lemma inj_basic: "inj Basic"
  by (meson e.inject(1) injI)

lemma inj_basic_econst: "inj (\<lambda>v. $C v)"
  by (simp add: inj_def)

lemma to_e_list_1:"[$ a] = $* [a]"
  by simp

lemma to_e_list_2:"[$ a, $ b] = $* [a, b]"
  by simp

lemma to_e_list_3:"[$ a, $ b, $ c] = $* [a, b, c]"
  by simp

lemma v_exists_b_e:"\<exists>ves. ($$*vs) = ($*ves)"
proof (induction vs)
  case (Cons a vs)
  thus ?case
  by (metis list.simps(9))
qed auto

lemma Lfilled_exact_imp_Lfilled:
  assumes "Lfilled_exact n lholed es LI"
  shows "Lfilled n lholed es LI"
  using assms
proof (induction rule: Lfilled_exact.induct)
  case (L0 lholed es)
  thus ?case
    using const_list_def Lfilled.intros(1)
    by fastforce
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma Lfilled_exact_app_imp_exists_Lfilled:
  assumes "const_list ves"
          "Lfilled_exact n lholed (ves@es) LI"
  shows "\<exists>lholed'. Lfilled n lholed' es LI"
  using assms(2,1)
proof (induction "(ves@es)" LI rule: Lfilled_exact.induct)
  case (L0 lholed)
  show ?case
    using Lfilled.intros(1)[OF L0(2), of _ "[]"]
    by fastforce
next
  case (LN vs lholed n es' l es'' k lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma Lfilled_imp_exists_Lfilled_exact:
  assumes "Lfilled n lholed es LI"
  shows "\<exists>lholed' ves es_c. const_list ves \<and> Lfilled_exact n lholed' (ves@es@es_c) LI"
  using assms Lfilled_exact.intros
  by (induction rule: Lfilled.induct) fastforce+

lemma n_zeros_typeof:
  "n_zeros ts = vs \<Longrightarrow> (ts = map typeof vs)"
proof (induction ts arbitrary: vs)
  case Nil
  thus ?case
    unfolding n_zeros_def
    by simp
next
  case (Cons t ts)
  obtain vs' where "n_zeros ts = vs'"
    using n_zeros_def
    by blast
  moreover
  have "typeof (bitzero t) = t"
    unfolding typeof_def bitzero_def
    by (cases t, simp_all)
  ultimately
  show ?case
    using Cons
    unfolding n_zeros_def
    by auto
qed

end