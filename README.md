# Faster Bootstrapping for CKKS with Less Modulus Consumption
This repository is a proof of concept of *Level-Conserved Rescaling* technique for CKKS bootstrapping.
Codes are based on [Lattigo v2.4.0](https://github.com/tuneinsight/lattigo/tree/v2.4.0) with the following modifications:

- Modified Level-Conserved CKKS Parameters
  In `ckks/bootstrapping/bootstrap_params.go`, the `LevelConservedCKKSParameters` and `LevelConservedParameters` are for level-conserved rescaling.
  1. `CoeffsToSlotsParameters.BSGSRatio` is set to large to avoid BSGS algorithm during coefficient-to-slot procedure. 
  2. The very last modulus of `Q []uint64` in `LevelConservedCKKSParameters` is commented out, as the level-conserved rescaling requires one-less moduli for coeffs-to-slots. Additionally, another modulus is inserted right after the moduli for slots-to-coeffs.
  3. The last modulus in `CoeffsToSlotsParameters.ScalingFactor [][]Float64` is replaced with the penultimate one, for that such modulus is applied twice as level is conserved.
- Implementations for Level-Conserved Rescaling
- Implementations for Aggregated Key-Swiching
- Tests
  In `ckks/bootstrapping/bootstrap_test.go`, a function named `TestRescaling` is added.

# Run Tests
Change directory to `ckks/bootstrapping`, and run
```sh
$ go test -v -run TestRescaling
```

Till now, `paramSet` in `TestRescaling` at `ckks/bootstrapping/bootstrap_test.go` can be set to 0 to 2, as the experiments did in our paper.
We recommend to run with the `flagLongTest` to be `false` in that test file, for faster evaluation. 

Running tests will store key-swithcing keys at the current directory, which can be reused to run the same test multiple times.

  
