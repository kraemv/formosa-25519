# Dockerfile description

The Dockerfile in this folder prepares an environment for building and checking the implementations from this repository.

## How to build the docker image and check/compile the available implementations
```
$ git clone https://github.com/formosa-crypto/formosa-25519.git
$ cd formosa-25519/
$ git submodule init && git submodule update
$ docker build -t formosa-25519:latest -f scripts/docker/Dockerfile .
$ docker run -it formosa-25519 bash
$ cd src/
$ make -j$(nproc)
```

The last command, `make`, can take up to 5 minutes to execute (depending on the machine, and if 8 cores are available).
It does the following (search for the `all` rule in `src/Makefile` for more details):

* `make distclean`: cleans everything
* `make check-safety`: runs the safety checker on the implementations
* `make check-sct`: checks if implementations are speculative constant-time
* `make extract-to-easycrypt`: extracts Jasmin code to EasyCrypt and populates the `proof/` folder
* `make lib25519.a`: compiles the Jasmin code into assembly; then object files and packs everything into lib25519.a
* `make libx25519.h`: builds the header file
* `make reporter`: prints the current status (below, the expected output for this step)
* `make err`: returns an error if there was any error in the previous steps

The expected output for `make reporter`, which is executed during `make all` is the following:
```
Safety checking status: 
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/mulx/.ci/jade_scalarmult_curve25519_amd64_mulx.safety.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/mulx/.ci/jade_scalarmult_curve25519_amd64_mulx_base.safety.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref4/.ci/jade_scalarmult_curve25519_amd64_ref4.safety.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref4/.ci/jade_scalarmult_curve25519_amd64_ref4_base.safety.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref5/.ci/jade_scalarmult_curve25519_amd64_ref5.safety.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref5/.ci/jade_scalarmult_curve25519_amd64_ref5_base.safety.log

Speculative constant-time status: 
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/mulx/.ci/jade_scalarmult_curve25519_amd64_mulx.sct.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/mulx/.ci/jade_scalarmult_curve25519_amd64_mulx_base.sct.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref4/.ci/jade_scalarmult_curve25519_amd64_ref4.sct.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref4/.ci/jade_scalarmult_curve25519_amd64_ref4_base.sct.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref5/.ci/jade_scalarmult_curve25519_amd64_ref5.sct.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref5/.ci/jade_scalarmult_curve25519_amd64_ref5_base.sct.log

Extraction to EasyCrypt status: 
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/mulx/.ci/scalarmult_s.ec.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref4/.ci/scalarmult_s.ec.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref5/.ci/scalarmult_s.ec.log

Compilation status (*.jazz -> *.s): 
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/mulx/.ci/scalarmult.s.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref4/.ci/scalarmult.s.log
OK, 0, formosa-25519/src/crypto_scalarmult/curve25519/amd64/ref5/.ci/scalarmult.s.log
```

Which means:

* `Safety checking status`: all implementations pass the safety-checking step. You can find the output of the safety checker (what the safety checker prints to the terminal) with `find . -name *.safety` after running `make`. The you can open and inspect these files with, for instance, `less`: `formosa-25519/src$ less ./crypto_scalarmult/curve25519/amd64/mulx/jade_scalarmult_curve25519_amd64_mulx.safety`

* `Speculative constant-time status`: all implementations pass the speculative constant-time type checking. To find the files containing the output of this verification step: `find . -name *.sct`

* `Extraction to EasyCrypt status`: all implementations were successfully extracted from Jasmin to EasyCrypt. As a note, `easycrypt` is not used during this step, so the files were not checked in `easycrypt` #TODO support make check in proof and update this README.md; open issue

* `Compilation status (*.jazz -> *.s)`: all implementations were successfully compiled to assembly. Assembly files be found with: `find . -name *.s`


