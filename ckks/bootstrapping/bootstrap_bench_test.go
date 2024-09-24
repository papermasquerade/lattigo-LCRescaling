package bootstrapping

import (
	"errors"
	"fmt"
	"math"
	"os"
	"testing"
	"time"

	"github.com/ldsec/lattigo/v2/ckks"
	"github.com/ldsec/lattigo/v2/rlwe"
)

func BenchmarkBSGS(b *testing.B) {
	paramSet := 0
	ckksParams := DefaultCKKSParameters[paramSet]
	bootstrapParams := DefaultParameters[paramSet]

	// if !*flagLongTest {
	// 	ckksParams.LogN = 13
	// 	ckksParams.LogSlots = 12
	// }
	//
	params, err := ckks.NewParametersFromLiteral(ckksParams)
	if err != nil {
		panic(err)
	}

	kgen := ckks.NewKeyGenerator(params)
	sk := kgen.GenSecretKeySparse(bootstrapParams.H)
	rlk := kgen.GenRelinearizationKey(sk, 2)

	rotations := bootstrapParams.RotationsForBootstrapping(params.LogN(), params.LogSlots())
	rotkeys := kgen.GenRotationKeysForRotations(rotations, true, sk)

	btp, err := NewBootstrapper(params, bootstrapParams, rlwe.EvaluationKey{Rlk: rlk, Rtks: rotkeys})
	if err != nil {
		panic(err)
	}
	bootstrappingScale := math.Exp2(math.Round(math.Log2(btp.params.QiFloat64(0) / btp.evalModPoly.MessageRatio())))
	ct := ckks.NewCiphertext(params, 1, 0, bootstrappingScale)
	ct = btp.modUpFromQ0(ct)

	in := ct.CopyNew()
	out := ct.CopyNew()
	for ii, plainVector := range btp.ctsMatrices.Matrices() {
		scale := in.Scale
		b.Run(ParamsToString(params, fmt.Sprintf("BSGSCoeffToSlot-%d/", ii)), func(b *testing.B) {
			for i := 0; i < b.N; i++ {

				btp.LinearTransform(in, plainVector, []*ckks.Ciphertext{out})
				t := time.Now()
				if err := btp.Rescale(out, scale, out); err != nil {
					panic(err)
				}
				fmt.Println("Rescaling Time:", time.Since(t))
			}
		})

		in = out.CopyNew()
	}
}

func BenchmarkLCBootstrap(b *testing.B) {
	paramSet := 0
	ckksParams := LevelConservedCKKSParameters[paramSet]
	bootstrapParams := LevelConservedParameters[paramSet]
	mixed := false
	// strategy_one := false

	// if !*flagLongTest {
	// 	ckksParams.LogN = 13
	// 	ckksParams.LogSlots = 12
	// }
	//
	params, err := ckks.NewParametersFromLiteral(ckksParams)
	if err != nil {
		panic(err)
	}

	// prefix := "param1/"
	prefix := fmt.Sprintf("param%d/", paramSet+1)
	sk_filename := prefix + "sk"
	rlk_filename := prefix + "rlk"
	rtk_filename := prefix + "rtk"
	aux_filename := prefix + "auxksk"

	// =================== Key Generation =====================
	kgen := ckks.NewKeyGenerator(params)
	sk := kgen.GenSecretKeySparse(bootstrapParams.H)
	if _, err := os.Stat(sk_filename); !errors.Is(err, os.ErrNotExist) {
		fmt.Println("unmarshall sk")
		sk_data, err := os.ReadFile(sk_filename)
		if err != nil {
			panic(err)
		}

		sk.UnmarshalBinary(sk_data)
	} else {
		sk_data, err := sk.MarshalBinary()
		if err != nil {
			panic(err)
		}

		err = os.WriteFile(sk_filename, sk_data, 0644)
		if err != nil {
			panic(err)
		}
	}

	rlk := kgen.GenRelinearizationKey(sk, 2)
	if _, err := os.Stat(rlk_filename); !errors.Is(err, os.ErrNotExist) {
		fmt.Println("unmarshall rlk")
		rlk_data, err := os.ReadFile(rlk_filename)
		if err != nil {
			panic(err)
		}

		rlk.UnmarshalBinary(rlk_data)
	} else {
		rlk_data, err := rlk.MarshalBinary()
		if err != nil {
			panic(err)
		}

		err = os.WriteFile(rlk_filename, rlk_data, 0644)
		if err != nil {
			panic(err)
		}
	}

	rotations := bootstrapParams.RotationsForBootstrapping(params.LogN(), params.LogSlots())
	var rotkeys *rlwe.RotationKeySet = &rlwe.RotationKeySet{}
	if _, err := os.Stat(rtk_filename); !errors.Is(err, os.ErrNotExist) {
		fmt.Println("unmarshall rtk")
		rtk_data, err := os.ReadFile(rtk_filename)
		if err != nil {
			panic(err)
		}

		rotkeys.UnmarshalBinary(rtk_data)
	} else {
		rotkeys = kgen.GenRotationKeysForRotations(rotations, true, sk)
		rtk_data, err := rotkeys.MarshalBinary()
		if err != nil {
			panic(err)
		}

		err = os.WriteFile(rtk_filename, rtk_data, 0644)
		if err != nil {
			panic(err)
		}
	}

	btp, err := NewBootstrapper(params, bootstrapParams, rlwe.EvaluationKey{Rlk: rlk, Rtks: rotkeys})
	if err != nil {
		panic(err)
	}
	matRotKeys := make([]*rlwe.RotationKeySet, 0)
	matrices := btp.ctsMatrices.Matrices()

	for i := range matrices {
		filename := rtk_filename + fmt.Sprintf("%d", i)
		if _, err := os.Stat(filename); !errors.Is(err, os.ErrNotExist) {
			var matrtk *rlwe.RotationKeySet = &rlwe.RotationKeySet{}
			matrtk_data, err := os.ReadFile(filename)
			if err != nil {
				panic(err)
			}
			if i == 0 {
			} else {
				matrtk.UnmarshalBinary(matrtk_data)
			}
			matRotKeys = append(matRotKeys, matrtk)
		} else {

			btp.InitialMatRotKeys()
			btp.MergeCTSMatRotKeys(matrices[i:i+1], kgen, sk, rotations, []bool{i == 0})
			matRotKeys = append(matRotKeys, btp.MatRotKeys(0))
			matrtk_data, err := btp.MatRotKeys(0).MarshalBinary()
			if err != nil {
				panic(err)
			}
			if i == 0 {
				os.Create(filename)
			} else {
				err = os.WriteFile(filename, matrtk_data, 0644)
			}
			if err != nil {
				panic(err)
			}

			if i == 0 {
				btp.MarshallLevelFreeAuxCt(aux_filename)
			}
		}
	}
	btp.InitialMatRotKeys()
	for _, matrtk := range matRotKeys {
		btp.AppendNewMatRowKeys(matrtk)
	}
	btp.UnmarshallLevelFreeAuxCt(aux_filename)

	// lvlFree := make([]bool, len(btp.ctsMatrices.Matrices()))
	// lvlFree[0] = true
	// btp.MergeCTSMatRotKeys(btp.ctsMatrices.Matrices(), kgen, sk, rotations, lvlFree)

	bootstrappingScale := math.Exp2(math.Round(math.Log2(btp.params.QiFloat64(0) / btp.evalModPoly.MessageRatio())))

	b.Run(ParamsToString(params, "LevelConserved"), func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			b.StopTimer()
			ct := ckks.NewCiphertext(params, 1, 0, bootstrappingScale)
			b.StartTimer()

			ctL := btp.modUpFromQ0(ct)

			b.StopTimer()
			ctReal := ckks.NewCiphertext(btp.params, 1, btp.ctsMatrices.LevelStart, 0)
			ctImag := ckks.NewCiphertext(btp.params, 1, btp.ctsMatrices.LevelStart, 0)
			b.StartTimer()
			if mixed {

			} else {

				btp.CoeffsToSlotsPrecomputed(ctL, btp.ctsMatrices, ctReal, ctImag)
			}

			ctReal = btp.EvalModNew(ctReal, btp.evalModPoly)
			ctReal.Scale = btp.params.DefaultScale()
			ctImag = btp.EvalModNew(ctImag, btp.evalModPoly)
			ctImag.Scale = btp.params.DefaultScale()

			btp.SlotsToCoeffsNew(ctReal, ctImag, btp.stcMatrices)
		}
	})

}
func BenchmarkLevelConserved(b *testing.B) {
	paramSet := 2
	ckksParams := LevelConservedCKKSParameters[paramSet]
	bootstrapParams := LevelConservedParameters[paramSet]
	strategy_one := false

	// if !*flagLongTest {
	// 	ckksParams.LogN = 13
	// 	ckksParams.LogSlots = 12
	// }
	//
	params, err := ckks.NewParametersFromLiteral(ckksParams)
	if err != nil {
		panic(err)
	}

	// prefix := "param1/"
	prefix := fmt.Sprintf("param%d/", paramSet+1)
	sk_filename := prefix + "sk"
	rlk_filename := prefix + "rlk"
	rtk_filename := prefix + "rtk"
	aux_filename := prefix + "auxksk"

	// =================== Key Generation =====================
	kgen := ckks.NewKeyGenerator(params)
	sk := kgen.GenSecretKeySparse(bootstrapParams.H)
	if _, err := os.Stat(sk_filename); !errors.Is(err, os.ErrNotExist) {
		fmt.Println("unmarshall sk")
		sk_data, err := os.ReadFile(sk_filename)
		if err != nil {
			panic(err)
		}

		sk.UnmarshalBinary(sk_data)
	} else {
		sk_data, err := sk.MarshalBinary()
		if err != nil {
			panic(err)
		}

		err = os.WriteFile(sk_filename, sk_data, 0644)
		if err != nil {
			panic(err)
		}
	}

	rlk := kgen.GenRelinearizationKey(sk, 2)
	if _, err := os.Stat(rlk_filename); !errors.Is(err, os.ErrNotExist) {
		fmt.Println("unmarshall rlk")
		rlk_data, err := os.ReadFile(rlk_filename)
		if err != nil {
			panic(err)
		}

		rlk.UnmarshalBinary(rlk_data)
	} else {
		rlk_data, err := rlk.MarshalBinary()
		if err != nil {
			panic(err)
		}

		err = os.WriteFile(rlk_filename, rlk_data, 0644)
		if err != nil {
			panic(err)
		}
	}

	rotations := bootstrapParams.RotationsForBootstrapping(params.LogN(), params.LogSlots())
	var rotkeys *rlwe.RotationKeySet = &rlwe.RotationKeySet{}
	if _, err := os.Stat(rtk_filename); !errors.Is(err, os.ErrNotExist) {
		fmt.Println("unmarshall rtk")
		rtk_data, err := os.ReadFile(rtk_filename)
		if err != nil {
			panic(err)
		}

		rotkeys.UnmarshalBinary(rtk_data)
	} else {
		rotkeys = kgen.GenRotationKeysForRotations(rotations, true, sk)
		rtk_data, err := rotkeys.MarshalBinary()
		if err != nil {
			panic(err)
		}

		err = os.WriteFile(rtk_filename, rtk_data, 0644)
		if err != nil {
			panic(err)
		}
	}

	btp, err := NewBootstrapper(params, bootstrapParams, rlwe.EvaluationKey{Rlk: rlk, Rtks: rotkeys})
	if err != nil {
		panic(err)
	}
	matRotKeys := make([]*rlwe.RotationKeySet, 0)
	matrices := btp.ctsMatrices.Matrices()

	for i := range matrices {
		filename := rtk_filename + fmt.Sprintf("%d", i)
		if _, err := os.Stat(filename); !errors.Is(err, os.ErrNotExist) {
			var matrtk *rlwe.RotationKeySet = &rlwe.RotationKeySet{}
			matrtk_data, err := os.ReadFile(filename)
			if err != nil {
				panic(err)
			}
			if i == 0 {
			} else {
				matrtk.UnmarshalBinary(matrtk_data)
			}
			matRotKeys = append(matRotKeys, matrtk)
		} else {

			btp.InitialMatRotKeys()
			btp.MergeCTSMatRotKeys(matrices[i:i+1], kgen, sk, rotations, []bool{i == 0})
			matRotKeys = append(matRotKeys, btp.MatRotKeys(0))
			matrtk_data, err := btp.MatRotKeys(0).MarshalBinary()
			if err != nil {
				panic(err)
			}
			if i == 0 {
				os.Create(filename)
			} else {
				err = os.WriteFile(filename, matrtk_data, 0644)
			}
			if err != nil {
				panic(err)
			}

			if i == 0 {
				btp.MarshallLevelFreeAuxCt(aux_filename)
			}
		}
	}
	btp.InitialMatRotKeys()
	for _, matrtk := range matRotKeys {
		btp.AppendNewMatRowKeys(matrtk)
	}
	btp.UnmarshallLevelFreeAuxCt(aux_filename)

	// lvlFree := make([]bool, len(btp.ctsMatrices.Matrices()))
	// lvlFree[0] = true
	// btp.MergeCTSMatRotKeys(btp.ctsMatrices.Matrices(), kgen, sk, rotations, lvlFree)

	bootstrappingScale := math.Exp2(math.Round(math.Log2(btp.params.QiFloat64(0) / btp.evalModPoly.MessageRatio())))
	ct := ckks.NewCiphertext(params, 1, 0, bootstrappingScale)
	ct = btp.modUpFromQ0(ct)

	in := ct.CopyNew()
	out := ct.CopyNew()
	for ii, plainVector := range btp.ctsMatrices.Matrices()[:] {
		scale := in.Scale
		b.Run(ParamsToString(params, fmt.Sprintf("LevelConserved-%d/", ii)), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				if ii == 0 {
					// fmt.Println("Level Free Modulus Performed")
					btp.Evaluator.LinearTransformWithPrecomputedMatRotKeys(
						in,
						plainVector,
						nil,
						[]*ckks.Ciphertext{out}, true)

				} else {
					if strategy_one {
						btp.LinearTransform(in, plainVector, []*ckks.Ciphertext{out})
					} else {
						btp.Evaluator.LinearTransformWithPrecomputedMatRotKeys(
							in,
							plainVector,
							btp.MatRotKeys(ii),
							[]*ckks.Ciphertext{out}, false)
					}
					t := time.Now()
					if err := btp.Rescale(out, scale, out); err != nil {
						panic(err)
					}
					fmt.Println("Rescaling time:", time.Since(t))
				}
			}
		})

		in = out.CopyNew()
	}
	// values := make([]complex128, 1<<params.LogSlots())
	// for i := range values {
	// 	values[i] = utils.RandComplex128(-1, 1)
	// }
	//
	// plaintext := ckks.NewPlaintext(params, 0, params.DefaultScale())
	// encoder.Encode(values, plaintext, params.LogSlots())
	// ciphertexts := encryptor.EncryptNew(plaintext)
	//
	// var ctL, ctL1, ctLfree, ct0 *ckks.Ciphertext
	//
	// ct0 = ciphertexts.CopyNew()
	// for ct0.Level() > 1 {
	// 	btp.DropLevel(ct0, 1)
	// }
	// if ct0.Level() == 1 {
	// 	btp.SetScale(ct0, btp.q0OverMessageRatio)
	// 	for ct0.Level() != 0 {
	// 		btp.DropLevel(ct0, 1)
	// 	}
	// } else {
	// 	if btp.q0OverMessageRatio < ct0.Scale {
	// 		panic("...")
	// 	}
	// 	btp.ScaleUp(ct0, math.Round(btp.q0OverMessageRatio/ct0.Scale), ct0)
	// }
	//
	// ctL = ct0.CopyNew()
	// ctL = btp.modUpFromQ0(ctL)
	//
	// ctL1 = ctL.CopyNew()
	// btp.MultByConst(ctL1, btp.params.RingQ().Modulus[ctL1.Level()], ctL1)
	// minScale := ctL1.Scale
	// ctL1.Scale *= float64(btp.params.RingQ().Modulus[ctL1.Level()])
	// if err := btp.Rescale(ctL1, minScale, ctL1); err != nil {
	// 	panic(err)
	// }

	// ctLfree = ctL1.CopyNew()
	// ctLfree = btp.modUpFromQl1(ctLfree)
	// for u := range ctLfree.Value {
	// 	params.RingQ().ModupFromQLMinus1(ctLfree.Value[u], btp.params.MaxLevel(), btp.params.N())
	// }

	// var ctReal, ctImag *ckks.Ciphertext
	// ctReal = ckks.NewCiphertext(btp.params, 1, btp.ctsMatrices.LevelStart, 0)
	// ctImag = ckks.NewCiphertext(btp.params, 1, btp.ctsMatrices.LevelStart, 0)
	// btp.CoeffsToSlotsPrecomputed(ctL, btp.ctsMatrices, ctReal, ctImag)
}

func BenchmarkBootstrapp(b *testing.B) {

	var err error
	var btp *Bootstrapper

	paramSet := 0

	ckksParams := DefaultCKKSParameters[paramSet]
	btpParams := DefaultParameters[paramSet]

	params, err := ckks.NewParametersFromLiteral(ckksParams)
	if err != nil {
		panic(err)
	}

	kgen := ckks.NewKeyGenerator(params)
	sk := kgen.GenSecretKeySparse(btpParams.H)
	rlk := kgen.GenRelinearizationKey(sk, 2)

	rotations := btpParams.RotationsForBootstrapping(params.LogN(), params.LogSlots())
	rotkeys := kgen.GenRotationKeysForRotations(rotations, true, sk)

	if btp, err = NewBootstrapper(params, btpParams, rlwe.EvaluationKey{Rlk: rlk, Rtks: rotkeys}); err != nil {
		panic(err)
	}

	b.Run(ParamsToString(params, "Bootstrapp/"), func(b *testing.B) {
		for i := 0; i < b.N; i++ {

			bootstrappingScale := math.Exp2(math.Round(math.Log2(btp.params.QiFloat64(0) / btp.evalModPoly.MessageRatio())))

			b.StopTimer()
			ct := ckks.NewCiphertext(params, 1, 0, bootstrappingScale)
			b.StartTimer()

			var t time.Time
			var ct0, ct1 *ckks.Ciphertext

			// ModUp ct_{Q_0} -> ct_{Q_L}
			t = time.Now()
			ct = btp.modUpFromQ0(ct)
			b.Log("After ModUp  :", time.Since(t), ct.Level(), ct.Scale)

			//SubSum X -> (N/dslots) * Y^dslots
			t = time.Now()
			btp.Trace(ct, btp.params.LogSlots(), btp.params.LogN()-1, ct)
			b.Log("After SubSum :", time.Since(t), ct.Level(), ct.Scale)

			// Part 1 : Coeffs to slots
			t = time.Now()
			ct0, ct1 = btp.CoeffsToSlotsNew(ct, btp.ctsMatrices)
			b.Log("After CtS    :", time.Since(t), ct0.Level(), ct0.Scale)

			// Part 2 : SineEval
			t = time.Now()
			ct0 = btp.EvalModNew(ct0, btp.evalModPoly)
			ct0.Scale = btp.params.DefaultScale()

			if ct1 != nil {
				ct1 = btp.EvalModNew(ct1, btp.evalModPoly)
				ct1.Scale = btp.params.DefaultScale()
			}
			b.Log("After Sine   :", time.Since(t), ct0.Level(), ct0.Scale)

			// Part 3 : Slots to coeffs
			t = time.Now()
			ct0 = btp.SlotsToCoeffsNew(ct0, ct1, btp.stcMatrices)
			ct0.Scale = math.Exp2(math.Round(math.Log2(ct0.Scale)))
			b.Log("After StC    :", time.Since(t), ct0.Level(), ct0.Scale)
		}
	})
}
