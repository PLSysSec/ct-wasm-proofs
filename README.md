# CT-Wasm Proofs

This repository contains the CT-Wasm model and mechanized proofs of soundness
and security.

The CT-WASM Isabelle model may be found in [CT-WASM_model](./CT-WASM_model).

#### Lemmas/definitions mentioned in paper, in order of appearance:

- [`preservation`](./CT-WASM_model/Wasm_Soundness.thy#L5)
- [`equivp_config_indistinguishable`](./CT-WASM_model/Wasm_Secret_Aux.thy#L1029)
- [`config_indistinguishable_imp_config_typing`](./CT-WASM_model/Wasm_Secret_Aux.thy#L891)
- [`equivp_action_indistinguishable`](./CT-WASM_model/Wasm_Secret.thy#L106)
- [`config_indistinguishable_imp_reduce`](./CT-WASM_model/Wasm_Secret.thy#L2165)
- [`config_bisimulation`](./CT-WASM_model/Wasm_Secret.thy#L2195)
- [`config_bisimilar`](./CT-WASM_model/Wasm_Secret.thy#L2201)
- [`typed_indistinguishable_pairs`](./CT-WASM_model/Wasm_Secret.thy#L2339)
- [`config_bisimulation_typed_indistinguishable_pairs`](./CT-WASM_model/Wasm_Secret.thy#L2388)
- [`config_indistinguishable_imp_config_bisimilar`](./CT-WASM_model/Wasm_Secret.thy#L2411)
- [`config_indistinguishable_trace_noninterference`](./CT-WASM_model/Wasm_Secret.thy#L2430)
- [`config_is_trace`](./CT-WASM_model/Wasm_Constant_Time.thy#L14)
- [`config_trace_set`](./CT-WASM_model/Wasm_Constant_Time.thy#L18)
- [`observation`](./CT-WASM_model/Wasm_Constant_Time.thy#L10)
- [`config_obs_set`](./CT-WASM_model/Wasm_Constant_Time.thy#L216)
- [`config_untrusted_equiv`](./CT-WASM_model/Wasm_Secret_Aux.thy#L1034)
- [`part_equivp_config_untrusted_equiv`](./CT-WASM_model/Wasm_Secret_Aux.thy#L1110)
- [`config_untrusted_quot`](./CT-WASM_model/Wasm_Secret_Aux.thy#L1119)
- [`config_untrusted_quot_config_typing`](./CT-WASM_model/Wasm_Secret_Aux.thy#L1220)
- [`config_untrusted_quot_obs_set`](./CT-WASM_model/Wasm_Constant_Time.thy#L218)
- [`constant_time`](./CT-WASM_model/Wasm_Constant_Time.thy#L244)
- [`config_untrusted_constant_time`](./CT-WASM_model/Wasm_Constant_Time.thy#L247)
- [`config_untrusted_quot_constant_time`](./CT-WASM_model/Wasm_Constant_Time.thy#L254)
- [`config_untrusted_quot_constant_time_trivial`](./CT-WASM_model/Wasm_Constant_Time.thy#L274)


#### Running the proofs

To run the proofs end-to-end, Isabelle2017 is required; you can download an archive from:
https://isabelle.in.tum.de/website-Isabelle2017/index.html

We provide a ROOT file to run all proofs and generate a summary document.

With Isabelle downloaded, run:

```bash
git clone git@github.com:PLSysSec/ct-wasm-proofs.git
cd ct-wasm-proofs/CT-WASM_model
<.../bin/isabelle> build -D ./
```

> Note: the `isabelle` binary you want to use if you downloaded Isabelle from the
> above link lives in the `bin` directory. (The binary that lives in the top-level
> directory is for the IDE and NOT what you want.)

> Note: This build will take a very long time due to the need to bootstrap the
> full Isabelle environment on the first execution. 
>
> Moreover, note that existing ROOT files from previous installations of
> Isabelle2017 may interfere with the build. These may have to be deleted from
> the `.isabelle` folder that will have been left somewhere in the home
> directory.

Running the above commands will produce:

- Summary documents in the `CT-WASM_model/output` directory.
- Executable type checker `CT-WASM_model/Wasm_Printing/Wasm_Extracted/checker.ml`

For convenience, we supply a pre-built type checker, session graph, and summary
document in the [prebuilt folder](./prebuilt).
