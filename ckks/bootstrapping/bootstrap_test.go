package bootstrapping

import (
	"errors"
	"flag"
	"fmt"
	"math"
	"os"
	"runtime"

	"testing"

	"github.com/ldsec/lattigo/v2/ckks"
	"github.com/ldsec/lattigo/v2/rlwe"
	"github.com/ldsec/lattigo/v2/utils"
	"github.com/stretchr/testify/assert"
)

var p = fmt.Println
var flagLongTest = flag.Bool("long", false, "run the long test suite (all parameters + secure bootstrapping). Overrides -short and requires -timeout=0.")
var testBootstrapping = flag.Bool("test-bootstrapping", true, "run the bootstrapping tests (memory intensive)")
var printPrecisionStats = flag.Bool("print-precision", true, "print precision stats")

func ParamsToString(params ckks.Parameters, opname string) string {
	return fmt.Sprintf("%slogN=%d/LogSlots=%d/logQP=%d/levels=%d/a=%d/b=%d",
		opname,
		params.LogN(),
		params.LogSlots(),
		params.LogQP(),
		params.MaxLevel()+1,
		params.PCount(),
		params.Beta())
}

func TestBootstrapParametersMarshalling(t *testing.T) {
	bootstrapParams := DefaultParameters[0]
	data, err := bootstrapParams.MarshalBinary()
	assert.Nil(t, err)

	bootstrapParamsNew := new(Parameters)
	if err := bootstrapParamsNew.UnmarshalBinary(data); err != nil {
		assert.Nil(t, err)
	}
	assert.Equal(t, bootstrapParams, *bootstrapParamsNew)
}

func TestRescaling(t *testing.T) {
	paramSet := 0
	ckksParams := LevelConservedCKKSParameters[paramSet]
	bootstrapParams := LevelConservedParameters[paramSet]
	// ckksParams := DefaultCKKSParameters[paramSet]
	// bootstrapParams := DefaultParameters[paramSet]

	prefix := fmt.Sprintf("param%d/", paramSet+1)
	if !*flagLongTest {
		ckksParams.LogN = 13
		ckksParams.LogSlots = 12
		prefix = fmt.Sprintf("param%d-short/", paramSet+1)
	}
	if err := os.MkdirAll(prefix, os.ModePerm); err != nil {
		panic(err)
	}

	params, err := ckks.NewParametersFromLiteral(ckksParams)
	if err != nil {
		panic(err)
	}

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

	/// Generated sk is tenary and in ntt domain

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

	encoder := ckks.NewEncoder(params)
	encryptor := ckks.NewEncryptor(params, sk)
	decryptor := ckks.NewDecryptor(params, sk)
	// the total coefftoslots and slotstocoeffs rotations
	rotations := bootstrapParams.RotationsForBootstrapping(params.LogN(), params.LogSlots())
	fmt.Println("generate rotation keys")

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

	fmt.Println("merge rotation with matrices")

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
				// btp.UnmarshallLevelFreeAuxCt(aux_filename)
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
			err = os.WriteFile(filename, matrtk_data, 0644)
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

	// btp.MatRotKeys()
	values := make([]complex128, 1<<params.LogSlots())
	for test_i := 0; test_i < 1; test_i++ {
		for i := range values {
			values[i] = utils.RandComplex128(-1, 1)
		}

		plaintext := ckks.NewPlaintext(params, 0, params.DefaultScale())
		encoder.Encode(values, plaintext, params.LogSlots())
		fmt.Println("default scale:", params.DefaultScale())
		ciphertexts := encryptor.EncryptNew(plaintext)
		var ctL, ctL1, ctLfree, ct0 *ckks.Ciphertext

		ct0 = ciphertexts.CopyNew()
		for ct0.Level() > 1 {
			btp.DropLevel(ct0, 1)
		}
		if ct0.Level() == 1 {
			btp.SetScale(ct0, btp.q0OverMessageRatio)
			for ct0.Level() != 0 {
				btp.DropLevel(ct0, 1)
			}
		} else {
			if btp.q0OverMessageRatio < ct0.Scale {
				panic("...")
			}
			btp.ScaleUp(ct0, math.Round(btp.q0OverMessageRatio/ct0.Scale), ct0)
		}

		fmt.Println(" ================== ModUp ================")
		ctL = ct0.CopyNew()
		ctL = btp.modUpFromQ0(ctL)
		fmt.Println("ct level:", ctL.Level())

		fmt.Println(" ================== Rescaling ============")
		ctL1 = ctL.CopyNew()
		fmt.Println("ct scale:", ctL1.Scale)
		btp.MultByConst(ctL1, btp.params.RingQ().Modulus[ctL1.Level()], ctL1)
		minScale := ctL1.Scale
		ctL1.Scale *= float64(btp.params.RingQ().Modulus[ctL1.Level()])
		if err := btp.Rescale(ctL1, minScale, ctL1); err != nil {
			panic(err)
		}

		fmt.Println(" ================= Re-ModUP ===============")
		ctLfree = ctL1.CopyNew()
		// ctLfree = btp.modUpFromQl1(ctLfree)
		for u := range ctLfree.Value {
			params.RingQ().ModupFromQLMinus1(ctLfree.Value[u], btp.params.MaxLevel(), btp.params.N())
		}

		fmt.Println("after level-free rescaling level:", ctLfree.Level())
		ptL := decryptor.DecryptNew(ctL)
		valuesL := encoder.Decode(ptL, params.LogSlots())

		verifyTestVectors(params, encoder, decryptor, valuesL, ctLfree, params.LogSlots(), 0, t)
		fmt.Println(" ================ Coefficients to Slots =========")
		/// expand this function
		// ctReal, ctImag := btp.CoeffsToSlotsNew(ctL, btp.ctsMatrices)
		var ctReal, ctImag *ckks.Ciphertext
		ctReal = ckks.NewCiphertext(btp.params, 1, btp.ctsMatrices.LevelStart, 0)
		ctImag = ckks.NewCiphertext(btp.params, 1, btp.ctsMatrices.LevelStart, 0)
		btp.CoeffsToSlotsPrecomputed(ctL, btp.ctsMatrices, ctReal, ctImag)

		fmt.Println(" =============== Eval Mod ====================")
		fmt.Println("Level before eval mod:", ctReal.Level(), ctImag.Level())
		ctReal = btp.EvalModNew(ctReal, btp.evalModPoly)
		ctReal.Scale = btp.params.DefaultScale()

		ctImag = btp.EvalModNew(ctImag, btp.evalModPoly)
		ctImag.Scale = btp.params.DefaultScale()
		fmt.Println("Level after eval mod:", ctReal.Level(), ctImag.Level())
		fmt.Println(" =============== Slots to Coeffs ==============")
		ctOut := btp.SlotsToCoeffsNew(ctReal, ctImag, btp.stcMatrices)
		verifyTestVectors(params, encoder, decryptor, values, ctOut, params.LogSlots(), 0, t)
	}
}

func TestBootstrap(t *testing.T) {

	if runtime.GOARCH == "wasm" {
		t.Skip("skipping bootstrapping tests for GOARCH=wasm")
	}

	if !*testBootstrapping {
		t.Skip("skipping bootstrapping tests (add -test-bootstrapping to run the bootstrapping tests)")
	}

	paramSet := 3

	ckksParams := DefaultCKKSParameters[paramSet]
	bootstrapParams := DefaultParameters[paramSet]

	// Insecure params for fast testing only
	// if !*flagLongTest {
	// 	ckksParams.LogN = 13
	// 	ckksParams.LogSlots = 12
	// }

	params, err := ckks.NewParametersFromLiteral(ckksParams)
	// almost all literal, but polyQ, polyP computed for supporting computation with NTT
	if err != nil {
		panic(err)
	}

	for _, testSet := range []func(params ckks.Parameters, btpParams Parameters, t *testing.T){
		testbootstrap,
	} {
		testSet(params, bootstrapParams, t)
		runtime.GC()
	}

	return
	// This is for repacking
	ckksParams.LogSlots--

	params, err = ckks.NewParametersFromLiteral(ckksParams)
	if err != nil {
		panic(err)
	}

	for _, testSet := range []func(params ckks.Parameters, btpParams Parameters, t *testing.T){
		testbootstrap,
	} {
		testSet(params, bootstrapParams, t)
		runtime.GC()
	}
}

func memUsage(m1, m2 *runtime.MemStats) {
	p("Alloc(MB): ", (m2.Alloc-m1.Alloc)/1024.0/1024.0,
		"TotalAlloc(MB): ", (m2.TotalAlloc-m1.TotalAlloc)/1024.0/1024.0,
		"HeapAlloc(MB):", (m2.HeapAlloc-m1.HeapAlloc)/1024.0/1024.0)
}

func testbootstrap(params ckks.Parameters, btpParams Parameters, t *testing.T) {

	t.Run(ParamsToString(params, "Bootstrapping/FullCircuit/"), func(t *testing.T) {

		kgen := ckks.NewKeyGenerator(params)
		sk := kgen.GenSecretKeySparse(btpParams.H)
		rlk := kgen.GenRelinearizationKey(sk, 2)
		encoder := ckks.NewEncoder(params)
		encryptor := ckks.NewEncryptor(params, sk)
		decryptor := ckks.NewDecryptor(params, sk)
		var m1, m2 runtime.MemStats

		// the total coefftoslots and slotstocoeffs rotations
		rotations := btpParams.RotationsForBootstrapping(params.LogN(), params.LogSlots())
		fmt.Println("rotations:", len(rotations))
		runtime.ReadMemStats(&m1)
		rotkeys := kgen.GenRotationKeysForRotations(rotations, true, sk)
		runtime.ReadMemStats(&m2)
		memUsage(&m1, &m2)

		btp, err := NewBootstrapper(params, btpParams, rlwe.EvaluationKey{Rlk: rlk, Rtks: rotkeys})
		if err != nil {
			panic(err)
		}
		// till now, no BSGS detected

		values := make([]complex128, 1<<params.LogSlots())
		for i := range values {
			values[i] = utils.RandComplex128(-1, 1)
		}

		values[0] = complex(0.9238795325112867, 0.3826834323650898)
		values[1] = complex(0.9238795325112867, 0.3826834323650898)
		if 1<<params.LogSlots() > 2 {
			values[2] = complex(0.9238795325112867, 0.3826834323650898)
			values[3] = complex(0.9238795325112867, 0.3826834323650898)
		}

		plaintext := ckks.NewPlaintext(params, 0, params.DefaultScale())
		fmt.Println("default scale:", params.DefaultScale())

		encoder.Encode(values, plaintext, params.LogSlots())

		ciphertexts := make([]*ckks.Ciphertext, 1)
		bootstrappers := make([]*Bootstrapper, 1)
		for i := range ciphertexts {
			ciphertexts[i] = encryptor.EncryptNew(plaintext)
			if i == 0 {
				bootstrappers[i] = btp
			} else {
				bootstrappers[i] = bootstrappers[0].ShallowCopy()
			}
		}

		// var wg sync.WaitGroup
		// wg.Add(1)
		for i := range ciphertexts {
			// go func(index int) {
			ciphertexts[i] = bootstrappers[i].Bootstrapp(ciphertexts[i])
			//btp.SetScale(ciphertexts[index], params.Scale())
			// wg.Done()
			// }(i)
		}
		// wg.Wait()

		for i := range ciphertexts {
			verifyTestVectors(params, encoder, decryptor, values, ciphertexts[i], params.LogSlots(), 0, t)
		}
	})
}

func verifyTestVectors(params ckks.Parameters, encoder ckks.Encoder, decryptor ckks.Decryptor, valuesWant []complex128, element interface{}, logSlots int, bound float64, t *testing.T) bool {
	precStats := ckks.GetPrecisionStats(params, encoder, decryptor, valuesWant, element, logSlots, bound)
	if *printPrecisionStats {
		t.Log(precStats.String())
	}

	return precStats.MeanPrecision.Real < 0
}
