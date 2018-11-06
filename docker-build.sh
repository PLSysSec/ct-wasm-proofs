docker run -ti --init -u `id -u`:`id -g` -v `pwd`/CT-WASM_model/:/home/isabelle/CT-WASM_model jmrenner/isabelle2017 build -D ./CT-WASM_model
