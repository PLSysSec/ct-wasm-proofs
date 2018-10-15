theory Wasm_Checker_Printing imports "../Wasm_Checker" "HOL-Library.Code_Target_Nat" begin 

definition "typing = b_e_type_checker"

code_printing
  type_constructor i32 \<rightharpoonup> (OCaml) "I32.t"
| type_constructor i64 \<rightharpoonup> (OCaml) "I64.t"
| type_constructor f32 \<rightharpoonup> (OCaml) "F32.t"
| type_constructor f64 \<rightharpoonup> (OCaml) "F64.t"

export_code open typing in OCaml file "Wasm_Extracted/checker.ml"

end
