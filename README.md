# ct-wasm-proofs

The CT-WASM Isabelle model may be found in CT-WASM_model.

Lemmas/definitions mentioned in paper, in order of appearance:

preservation - Wasm_Soundness.thy @ line 5
equivp_config_indistinguishable - Wasm_Secret_Aux.thy @ line 1029
config_indistinguishable_imp_config_typing - Wasm_Secret_Aux.thy @ line 891
equivp_action_indistinguishable - Wasm_Secret.thy @ line 106
config_indistinguishable_imp_reduce - Wasm_Secret.thy @ line 2165
config_bisimulation - Wasm_Secret.thy @ line 2195
config_bisimilar - Wasm_Secret.thy @ line 2201
typed_indistinguishable_pairs - Wasm_Secret.thy @ line 2339
config_bisimulation_typed_indistinguishable_pairs - Wasm_Secret.thy @ line 2388
config_indistinguishable_imp_config_bisimilar - Wasm_Secret.thy @ line 2411
config_indistinguishable_trace_noninterference - Wasm_Secret.thy @ line 2430
config_is_trace - Wasm_Constant_Time.thy @ line 14
config_trace_set - Wasm_Constant_Time.thy @ line 18
observation - Wasm_Constant_Time.thy @ line 10
config_obs_set - Wasm_Constant_Time.thy @ line 216
config_untrusted_equiv - Wasm_Secret_Aux.thy @ line 1034
part_equivp_config_untrusted_equiv - Wasm_Secret_Aux.thy @ line 1110
config_untrusted_quot - Wasm_Secret_Aux.thy @ line 1119
config_untrusted_quot_config_typing - Wasm_Secret_Aux.thy @ line 1220
config_untrusted_quot_obs_set - Wasm_Constant_Time.thy @ line 218
constant_time - Wasm_Constant_Time.thy @ line 244
config_untrusted_constant_time - Wasm_Constant_Time.thy @ line 247
config_untrusted_quot_constant_time - Wasm_Constant_Time.thy @ line 254
config_untrusted_quot_constant_time_trivial - Wasm_Constant_Time.thy @ line 274

To run the proofs end-to-end, Isabelle2017 is required:
https://isabelle.in.tum.de/website-Isabelle2017/index.html

We provide a ROOT file to run all proofs and generate a summary document.
With Isabelle downloaded, run the following command in the CT-WASM_model
folder.
<path/to/isabelle> build -D ./

In the archive linked above, the Isabelle command line tool can be found in the
bin subdirectory. This build will take a very long time due to the need to
bootstrap the full Isabelle environment on the first execution.

Note that existing ROOT files from previous installations of Isabelle2017 may
interfere with the build. These may have to be deleted from the .isabelle
folder that will have been left somewhere in the home directory.

All documents will appear in CT-WASM_model/output.

The executable type checker will appear in
CT-WASM_model/Wasm_Printing/Wasm_Extracted/checker.ml

For convenience, we supply a pre-built type checker, session graph, and summary
document in the prebuilt folder.
