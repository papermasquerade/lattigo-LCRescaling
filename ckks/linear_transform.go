package ckks

import (
	"fmt"
	// "math"
	"runtime"
	"time"

	"github.com/ldsec/lattigo/v2/ring"
	"github.com/ldsec/lattigo/v2/rlwe"
	"github.com/ldsec/lattigo/v2/utils"
)

// Trace maps X -> sum((-1)^i * X^{i*n+1}) for 0 <= i < N
// For log(n) = logSlotStart and log(N/2) = logSlotsEnd
// Monomial X^k vanishes if k is not divisible by (N/n), else it is multiplied by (N/n).
// Ciphertext is pre-multiplied by (N/n)^-1 to remove the (N/n) factor.
// Examples of full Trace for [0 + 1X + 2X^2 + 3X^3 + 4X^4 + 5X^5 + 6X^6 + 7X^7]
//
// 1)	   [1 + 2X + 3X^2 + 4X^3 + 5X^4 + 6X^5 + 7X^6 + 8X^7]
//   - [1 - 6X - 3X^2 + 8X^3 + 5X^4 + 2X^5 - 7X^6 - 4X^7]  {X-> X^(i * 5^1)}
//     = [2 - 4X + 0X^2 +12X^3 +10X^4 + 8X^5 - 0X^6 + 4X^7]
//
// 2)      [2 - 4X + 0X^2 +12X^3 +10X^4 + 8X^5 - 0X^6 + 4X^7]
//   - [2 + 4X + 0X^2 -12X^3 +10X^4 - 8X^5 + 0X^6 - 4X^7]  {X-> X^(i * 5^2)}
//     = [4 + 0X + 0X^2 - 0X^3 +20X^4 + 0X^5 + 0X^6 - 0X^7]
//
// 3)      [4 + 0X + 0X^2 - 0X^3 +20X^4 + 0X^5 + 0X^6 - 0X^7]
//   - [4 + 4X + 0X^2 - 0X^3 -20X^4 + 0X^5 + 0X^6 - 0X^7]  {X-> X^(i * -1)}
//     = [8 + 0X + 0X^2 - 0X^3 + 0X^4 + 0X^5 + 0X^6 - 0X^7]
func (eval *evaluator) Trace(ctIn *Ciphertext, logSlotsStart, logSlotsEnd int, ctOut *Ciphertext) {

	levelQ := utils.MinInt(ctIn.Level(), ctOut.Level())

	ctOut.Value[0].Coeffs = ctOut.Value[0].Coeffs[:levelQ+1]
	ctOut.Value[1].Coeffs = ctOut.Value[1].Coeffs[:levelQ+1]

	n := 1 << (logSlotsEnd - logSlotsStart)

	if n > 1 {

		ringQ := eval.params.RingQ()

		// pre-multiplication by (N/n)^-1
		for i := 0; i < levelQ+1; i++ {
			Q := ringQ.Modulus[i]
			bredParams := ringQ.BredParams[i]
			mredparams := ringQ.MredParams[i]
			invN := ring.ModExp(uint64(n), Q-2, Q)
			invN = ring.MForm(invN, Q, bredParams)

			ring.MulScalarMontgomeryVec(ctIn.Value[0].Coeffs[i], ctOut.Value[0].Coeffs[i], invN, Q, mredparams)
			ring.MulScalarMontgomeryVec(ctIn.Value[1].Coeffs[i], ctOut.Value[1].Coeffs[i], invN, Q, mredparams)
		}

		for i := logSlotsStart; i < logSlotsEnd; i++ {
			eval.permuteNTT(ctOut, eval.params.GaloisElementForColumnRotationBy(1<<i), eval.ctxpool)
			ctPool := &Ciphertext{Ciphertext: eval.ctxpool.Ciphertext, Scale: ctOut.Scale}
			ctPool.Value = ctPool.Value[:2]
			eval.Add(ctOut, ctPool, ctOut)
		}
	} else {
		if ctIn != ctOut {
			ctOut.Copy(ctIn)
		}
	}
}

// TraceNew maps X -> sum((-1)^i * X^{i*n+1}) for 0 <= i < N and returns the result on a new ciphertext.
// For log(n) = logSlotStart and log(N/2) = logSlotsEnd
func (eval *evaluator) TraceNew(ctIn *Ciphertext, logSlotsStart, logSlotsEnd int) (ctOut *Ciphertext) {
	ctOut = NewCiphertext(eval.params, 1, ctIn.Level(), ctIn.Scale)
	eval.Trace(ctIn, logSlotsStart, logSlotsEnd, ctOut)
	return
}

// RotateHoistedNew takes an input Ciphertext and a list of rotations and returns a map of Ciphertext, where each element of the map is the input Ciphertext
// rotation by one element of the list. It is much faster than sequential calls to Rotate.
func (eval *evaluator) RotateHoistedNew(ctIn *Ciphertext, rotations []int) (ctOut map[int]*Ciphertext) {
	ctOut = make(map[int]*Ciphertext)
	for _, i := range rotations {
		ctOut[i] = NewCiphertext(eval.params, 1, ctIn.Level(), ctIn.Scale)
	}
	eval.RotateHoisted(ctIn, rotations, ctOut)
	return
}

// RotateHoisted takes an input Ciphertext and a list of rotations and populates a map of pre-allocated Ciphertexts,
// where each element of the map is the input Ciphertext rotation by one element of the list.
// It is much faster than sequential calls to Rotate.
func (eval *evaluator) RotateHoisted(ctIn *Ciphertext, rotations []int, ctOut map[int]*Ciphertext) {
	levelQ := ctIn.Level()
	eval.DecomposeNTT(levelQ, eval.params.PCount()-1, eval.params.PCount(), ctIn.Value[1], eval.PoolDecompQP)
	for _, i := range rotations {
		ctOut[i].Value[0].Coeffs = ctOut[i].Value[0].Coeffs[:levelQ+1]
		ctOut[i].Value[1].Coeffs = ctOut[i].Value[1].Coeffs[:levelQ+1]
		if i == 0 {
			ctOut[i].Copy(ctIn)
		} else {
			eval.PermuteNTTHoisted(levelQ, ctIn.Value[0], ctIn.Value[1], eval.PoolDecompQP, i, ctOut[i].Value[0], ctOut[i].Value[1])
		}
	}
}

// LinearTransform is a type for linear transformations on ciphertexts.
// It stores a plaintext matrix diagonalized in diagonal form and
// can be evaluated on a ciphertext by using the evaluator.LinearTransform method.
type LinearTransform struct {
	LogSlots int                 // Log of the number of slots of the plaintext (needed to compute the appropriate rotation keys)
	N1       int                 // N1 is the number of inner loops of the baby-step giant-step algorithm used in the evaluation (if N1 == 0, BSGS is not used).
	Level    int                 // Level is the level at which the matrix is encoded (can be circuit dependent)
	Scale    float64             // Scale is the scale at which the matrix is encoded (can be circuit dependent)
	Vec      map[int]rlwe.PolyQP // Vec is the matrix, in diagonal form, where each entry of vec is an indexed non-zero diagonal.
}

// NewLinearTransform allocates a new LinearTransform with zero plaintexts at the specified level.
// If BSGSRatio == 0, the LinearTransform is set to not use the BSGS approach.
// Method will panic if BSGSRatio < 0.
func NewLinearTransform(params Parameters, nonZeroDiags []int, level, logSlots int, BSGSRatio float64) LinearTransform {
	vec := make(map[int]rlwe.PolyQP)
	slots := 1 << logSlots
	levelQ := level
	levelP := params.PCount() - 1
	var N1 int
	if BSGSRatio == 0 {
		// fmt.Println("non BSGS")
		N1 = 0
		for _, i := range nonZeroDiags {
			idx := i
			if idx < 0 {
				idx += slots
			}
			vec[idx] = params.RingQP().NewPolyLvl(levelQ, levelP)
		}
	} else if BSGSRatio > 0 {
		// fmt.Println("in BSGS")
		N1 = FindBestBSGSSplit(nonZeroDiags, slots, BSGSRatio)
		index, _, _ := BsgsIndex(nonZeroDiags, slots, N1)
		for j := range index {
			for _, i := range index[j] {
				vec[j+i] = params.RingQP().NewPolyLvl(levelQ, levelP)
			}
		}
	} else {
		panic("BSGS ratio cannot be negative")
	}

	return LinearTransform{LogSlots: logSlots, N1: N1, Level: level, Vec: vec}
}

// Rotations returns the list of rotations needed for the evaluation
// of the linear transform.
func (LT *LinearTransform) Rotations() (rotations []int) {
	slots := 1 << LT.LogSlots

	rotIndex := make(map[int]bool)

	var index int

	N1 := LT.N1

	if LT.N1 == 0 {

		for j := range LT.Vec {
			rotIndex[j] = true
		}

	} else {

		for j := range LT.Vec {

			index = ((j / N1) * N1) & (slots - 1)
			rotIndex[index] = true

			index = j & (N1 - 1)
			rotIndex[index] = true
		}
	}

	rotations = make([]int, len(rotIndex))
	var i int
	for j := range rotIndex {
		rotations[i] = j
		i++
	}

	return rotations
}

// Encode encodes on a pre-allocated LinearTransform the linear transforms' matrix in diagonal form `value`.
// values.(type) can be either map[int][]complex128 or map[int][]float64.
// User must ensure that 1 <= len([]complex128\[]float64) <= 2^logSlots < 2^logN.
// It can then be evaluated on a ciphertext using evaluator.LinearTransform.
// Evaluation will use the naive approach (single hoisting and no baby-step giant-step).
// Faster if there is only a few non-zero diagonals but uses more keys.
func (LT *LinearTransform) Encode(encoder Encoder, value interface{}, scale float64) {

	enc, ok := encoder.(*encoderComplex128)
	if !ok {
		panic("encoder should be an encoderComplex128")
	}

	dMat := interfaceMapToMapOfInterface(value)
	slots := 1 << LT.LogSlots
	N1 := LT.N1

	if N1 == 0 {
		for i := range dMat {
			idx := i
			if idx < 0 {
				idx += slots
			}

			if _, ok := LT.Vec[idx]; !ok {
				panic("error encoding on LinearTransform: input does not match the same non-zero diagonals")
			}

			enc.embed(dMat[i], LT.LogSlots, scale, LT.Vec[idx])
			enc.switchToNTTDomain(LT.LogSlots, true, LT.Vec[idx])
		}
	} else {
		index, _, _ := BsgsIndex(value, slots, N1)

		for j := range index {
			for _, i := range index[j] {
				// manages inputs that have rotation between 0 and slots-1 or between -slots/2 and slots/2-1
				v, ok := dMat[j+i]
				if !ok {
					v = dMat[j+i-slots]
				}

				if _, ok := LT.Vec[j+i]; !ok {
					panic("error encoding on LinearTransform BSGS: input does not match the same non-zero diagonals")
				}

				enc.embed(utils.RotateSlice(v, -j), LT.LogSlots, scale, LT.Vec[j+i])
				enc.switchToNTTDomain(LT.LogSlots, true, LT.Vec[j+i])
			}
		}
	}

	LT.Scale = scale
}

// GenLinearTransform allocates and encode a new LinearTransform struct from the linear transforms' matrix in diagonal form `value`.
// values.(type) can be either map[int][]complex128 or map[int][]float64.
// User must ensure that 1 <= len([]complex128\[]float64) <= 2^logSlots < 2^logN.
// It can then be evaluated on a ciphertext using evaluator.LinearTransform.
// Evaluation will use the naive approach (single hoisting and no baby-step giant-step).
// Faster if there is only a few non-zero diagonals but uses more keys.
func GenLinearTransform(encoder Encoder, value interface{}, level int, scale float64, logslots int) LinearTransform {

	enc, ok := encoder.(*encoderComplex128)
	if !ok {
		panic("encoder should be an encoderComplex128")
	}

	params := enc.params
	dMat := interfaceMapToMapOfInterface(value)
	vec := make(map[int]rlwe.PolyQP)
	slots := 1 << logslots
	levelQ := level
	levelP := params.PCount() - 1
	for i := range dMat {

		idx := i
		if idx < 0 {
			idx += slots
		}
		vec[idx] = params.RingQP().NewPolyLvl(levelQ, levelP)
		enc.embed(dMat[i], logslots, scale, vec[idx])
		enc.switchToNTTDomain(logslots, true, vec[idx])
	}

	return LinearTransform{LogSlots: logslots, N1: 0, Vec: vec, Level: level, Scale: scale}
}

// GenLinearTransformBSGS allocates and encodes a new LinearTransform struct from the linear transforms' matrix in diagonal form `value` for evaluation with a baby-step giant-step approach.
// values.(type) can be either map[int][]complex128 or map[int][]float64.
// User must ensure that 1 <= len([]complex128\[]float64) <= 2^logSlots < 2^logN.
// LinearTransform types can be be evaluated on a ciphertext using evaluator.LinearTransform.
// Evaluation will use the optimized approach (double hoisting and baby-step giant-step).
// Faster if there is more than a few non-zero diagonals.
// BSGSRatio is the maximum ratio between the inner and outer loop of the baby-step giant-step algorithm used in evaluator.LinearTransform.
// Optimal BSGSRatio value is between 4 and 16 depending on the sparsity of the matrix.
func GenLinearTransformBSGS(encoder Encoder, value interface{}, level int, scale, BSGSRatio float64, logSlots int) (LT LinearTransform) {

	enc, ok := encoder.(*encoderComplex128)
	if !ok {
		panic("encoder should be an encoderComplex128")
	}

	params := enc.params

	slots := 1 << logSlots

	// N1*N2 = N
	N1 := FindBestBSGSSplit(value, slots, BSGSRatio)

	index, _, _ := BsgsIndex(value, slots, N1)

	vec := make(map[int]rlwe.PolyQP)

	dMat := interfaceMapToMapOfInterface(value)
	levelQ := level
	levelP := params.PCount() - 1
	for j := range index {

		for _, i := range index[j] {

			// manages inputs that have rotation between 0 and slots-1 or between -slots/2 and slots/2-1
			v, ok := dMat[j+i]
			if !ok {
				v = dMat[j+i-slots]
			}
			vec[j+i] = params.RingQP().NewPolyLvl(levelQ, levelP)
			enc.embed(utils.RotateSlice(v, -j), logSlots, scale, vec[j+i])
			enc.switchToNTTDomain(logSlots, true, vec[j+i])
		}
	}

	return LinearTransform{LogSlots: logSlots, N1: N1, Vec: vec, Level: level, Scale: scale}
}

// BsgsIndex returns the index map and needed rotation for the BSGS matrix-vector multiplication algorithm.
// (el : matrix interface) -> (N1 : int) -> (index : (N1 : int) -> (N2 : List int)) times (rotN1 : List of index of N1) times (rotN1 : List of index of N2)
// i.e. For a vector [ .... ]
// split it into a matrix
// [ [...], [ ... ], ... , [...]]
// such that the shape is N1 times N2, and for each rotation, assign its n1xn2 and collect
func BsgsIndex(el interface{}, slots, N1 int) (index map[int][]int, rotN1, rotN2 []int) {
	index = make(map[int][]int)
	rotN1Map := make(map[int]bool)
	rotN2Map := make(map[int]bool)
	var nonZeroDiags []int
	switch element := el.(type) {
	case map[int][]complex128:
		nonZeroDiags = make([]int, len(element))
		var i int
		for key := range element {
			nonZeroDiags[i] = key
			i++
		}
	case map[int][]float64:
		nonZeroDiags = make([]int, len(element))
		var i int
		for key := range element {
			nonZeroDiags[i] = key
			i++
		}
	case map[int]bool:
		nonZeroDiags = make([]int, len(element))
		var i int
		for key := range element {
			nonZeroDiags[i] = key
			i++
		}
	case map[int]rlwe.PolyQP:
		nonZeroDiags = make([]int, len(element))
		var i int
		for key := range element {
			nonZeroDiags[i] = key
			i++
		}
	case []int:
		nonZeroDiags = element
	}

	for _, rot := range nonZeroDiags {
		rot &= (slots - 1)
		idxN1 := ((rot / N1) * N1) & (slots - 1)
		idxN2 := rot & (N1 - 1)
		if index[idxN1] == nil {
			index[idxN1] = []int{idxN2}
		} else {
			index[idxN1] = append(index[idxN1], idxN2)
		}
		rotN1Map[idxN1] = true
		rotN2Map[idxN2] = true
	}

	rotN1 = []int{}
	for i := range rotN1Map {
		rotN1 = append(rotN1, i)
	}

	rotN2 = []int{}
	for i := range rotN2Map {
		rotN2 = append(rotN2, i)
	}

	return
}

func interfaceMapToMapOfInterface(m interface{}) map[int]interface{} {
	d := make(map[int]interface{})
	switch el := m.(type) {
	case map[int][]complex128:
		for i := range el {
			d[i] = el[i]
		}
	case map[int][]float64:
		for i := range el {
			d[i] = el[i]
		}
	default:
		panic("invalid input, must be map[int][]complex128 or map[int][]float64")
	}
	return d
}

// FindBestBSGSSplit finds the best N1*N2 = N for the baby-step giant-step algorithm for matrix multiplication.
// maxN is the number of slots that is used in a ring
func FindBestBSGSSplit(diagMatrix interface{}, maxN int, maxRatio float64) (minN int) {

	for N1 := 1; N1 < maxN; N1 <<= 1 {

		_, rotN1, rotN2 := BsgsIndex(diagMatrix, maxN, N1)

		nbN1, nbN2 := len(rotN1)-1, len(rotN2)-1

		// fmt.Println("nbN1:", nbN1, "nbN2:", nbN2)
		if float64(nbN2)/float64(nbN1) == maxRatio {
			return N1
		}

		if float64(nbN2)/float64(nbN1) > maxRatio {
			return N1 / 2
		}
	}

	return maxN
	// return 1
}

// LinearTransformNew evaluates a linear transform on the ciphertext and returns the result on a new ciphertext.
// The linearTransform can either be an (ordered) list of PtDiagMatrix or a single PtDiagMatrix.
// In either case a list of ciphertext is returned (the second case returning a list of
// containing a single ciphertext. A PtDiagMatrix is a diagonalized plaintext matrix constructed with an Encoder using
// the method encoder.EncodeDiagMatrixAtLvl(*).
func (eval *evaluator) LinearTransformNew(ctIn *Ciphertext, linearTransform interface{}) (ctOut []*Ciphertext) {

	switch LTs := linearTransform.(type) {
	case []LinearTransform:
		ctOut = make([]*Ciphertext, len(LTs))

		var maxLevel int
		for _, LT := range LTs {
			maxLevel = utils.MaxInt(maxLevel, LT.Level)
		}

		minLevel := utils.MinInt(maxLevel, ctIn.Level())

		eval.DecomposeNTT(minLevel, eval.params.PCount()-1, eval.params.PCount(), ctIn.Value[1], eval.PoolDecompQP)

		for i, LT := range LTs {
			ctOut[i] = NewCiphertext(eval.params, 1, minLevel, ctIn.Scale)

			if LT.N1 == 0 {
				eval.MultiplyByDiagMatrix(ctIn, LT, eval.PoolDecompQP, ctOut[i])
			} else {
				eval.MultiplyByDiagMatrixBSGS(ctIn, LT, eval.PoolDecompQP, ctOut[i])
			}
		}

	case LinearTransform:

		minLevel := utils.MinInt(LTs.Level, ctIn.Level())
		eval.DecomposeNTT(minLevel, eval.params.PCount()-1, eval.params.PCount(), ctIn.Value[1], eval.PoolDecompQP)

		ctOut = []*Ciphertext{NewCiphertext(eval.params, 1, minLevel, ctIn.Scale)}

		if LTs.N1 == 0 {
			eval.MultiplyByDiagMatrix(ctIn, LTs, eval.PoolDecompQP, ctOut[0])
		} else {
			eval.MultiplyByDiagMatrixBSGS(ctIn, LTs, eval.PoolDecompQP, ctOut[0])
		}
	}
	return
}

// LinearTransformNew evaluates a linear transform on the pre-allocated ciphertexts.
// The linearTransform can either be an (ordered) list of PtDiagMatrix or a single PtDiagMatrix.
// In either case a list of ciphertext is returned (the second case returning a list of
// containing a single ciphertext. A PtDiagMatrix is a diagonalized plaintext matrix constructed with an Encoder using
// the method encoder.EncodeDiagMatrixAtLvl(*).
func (eval *evaluator) LinearTransform(ctIn *Ciphertext, linearTransform interface{}, ctOut []*Ciphertext) {

	switch LTs := linearTransform.(type) {
	case []LinearTransform:
		var maxLevel int
		for _, LT := range LTs {
			maxLevel = utils.MaxInt(maxLevel, LT.Level)
		}

		minLevel := utils.MinInt(maxLevel, ctIn.Level())

		eval.DecomposeNTT(minLevel, eval.params.PCount()-1, eval.params.PCount(), ctIn.Value[1], eval.PoolDecompQP)

		for i, LT := range LTs {
			if LT.N1 == 0 {
				eval.MultiplyByDiagMatrix(ctIn, LT, eval.PoolDecompQP, ctOut[i])
			} else {
				eval.MultiplyByDiagMatrixBSGS(ctIn, LT, eval.PoolDecompQP, ctOut[i])
			}
		}

	case LinearTransform:
		minLevel := utils.MinInt(LTs.Level, ctIn.Level())
		eval.DecomposeNTT(minLevel, eval.params.PCount()-1, eval.params.PCount(), ctIn.Value[1], eval.PoolDecompQP)
		// idx, _, _ := BsgsIndex(LTs.Vec, 1<<LTs.LogSlots, LTs.N1)
		// fmt.Println("LTs.N1:", LTs.N1, " --> idx", idx)
		if LTs.N1 == 0 {
			eval.MultiplyByDiagMatrix(ctIn, LTs, eval.PoolDecompQP, ctOut[0])
		} else {
			// if len(idx) == 1 {
			// eval.MultiplyByDiagMatrix(ctIn, LTs, eval.PoolDecompQP, ctOut[0])
			// eval.MultiplyByDiagMatrixPrecomputed(ctIn, LTs, eval.PoolDecompQP, ctOut[0])
			// } else {
			eval.MultiplyByDiagMatrixBSGS(ctIn, LTs, eval.PoolDecompQP, ctOut[0])
			// }
		}
	}
}

func (eval *evaluator) LinearTransformWithPrecomputedMatRotKeys(ctIn *Ciphertext, linearTransform interface{}, key *rlwe.RotationKeySet, ctOut []*Ciphertext, levelFree bool) {

	switch LTs := linearTransform.(type) {
	case []LinearTransform:
		var maxLevel int
		for _, LT := range LTs {
			maxLevel = utils.MaxInt(maxLevel, LT.Level)
		}

		minLevel := utils.MinInt(maxLevel, ctIn.Level())

		eval.DecomposeNTT(minLevel, eval.params.PCount()-1, eval.params.PCount(), ctIn.Value[1], eval.PoolDecompQP)

		for i, LT := range LTs {
			if LT.N1 == 0 {
				eval.MultiplyByDiagMatrix(ctIn, LT, eval.PoolDecompQP, ctOut[i])
			} else {
				eval.MultiplyByDiagMatrixBSGS(ctIn, LT, eval.PoolDecompQP, ctOut[i])
			}
		}

	case LinearTransform:
		minLevel := utils.MinInt(LTs.Level, ctIn.Level())
		// fmt.Println("lvl c1:", ctIn.Level())
		// fmt.Println("Value c1:")
		// eval.RingQ().PrintHeadNTT(ctIn.Value[1], 3)
		eval.DecomposeNTT(minLevel, eval.params.PCount()-1, eval.params.PCount(), ctIn.Value[1], eval.PoolDecompQP)
		idx, _, _ := BsgsIndex(LTs.Vec, 1<<LTs.LogSlots, LTs.N1)
		// fmt.Println("LTs.N1:", LTs.N1, " --> idx", idx)
		if LTs.N1 == 0 {
			eval.MultiplyByDiagMatrix(ctIn, LTs, eval.PoolDecompQP, ctOut[0])
		} else {
			if len(idx) == 1 {
				// eval.MultiplyByDiagMatrix(ctIn, LTs, eval.PoolDecompQP, ctOut[0])
				eval.MultiplyByDiagMatrixPrecomputed(ctIn, LTs, key, eval.PoolDecompQP, ctOut[0], levelFree)
			} else {
				eval.MultiplyByDiagMatrixBSGS(ctIn, LTs, eval.PoolDecompQP, ctOut[0])
			}
		}
	}
}

// Average returns the average of vectors of batchSize elements.
// The operation assumes that ctIn encrypts SlotCount/'batchSize' sub-vectors of size 'batchSize'.
// It then replaces all values of those sub-vectors by the component-wise average between all the sub-vectors.
// Example for batchSize=4 and slots=8: [{a, b, c, d}, {e, f, g, h}] -> [0.5*{a+e, b+f, c+g, d+h}, 0.5*{a+e, b+f, c+g, d+h}]
// Operation requires log2(SlotCout/'batchSize') rotations.
// Required rotation keys can be generated with 'RotationsForInnerSumLog(batchSize, SlotCount/batchSize)”
func (eval *evaluator) Average(ctIn *Ciphertext, logBatchSize int, ctOut *Ciphertext) {

	if logBatchSize > eval.params.LogSlots() {
		panic("batchSize must be smaller or equal to the number of slots")
	}

	ringQ := eval.params.RingQ()

	level := utils.MinInt(ctIn.Level(), ctOut.Level())

	n := eval.params.Slots() / (1 << logBatchSize)

	// pre-multiplication by n^-1
	for i := 0; i < level+1; i++ {
		Q := ringQ.Modulus[i]
		bredParams := ringQ.BredParams[i]
		mredparams := ringQ.MredParams[i]
		invN := ring.ModExp(uint64(n), Q-2, Q)
		invN = ring.MForm(invN, Q, bredParams)

		ring.MulScalarMontgomeryVec(ctIn.Value[0].Coeffs[i], ctOut.Value[0].Coeffs[i], invN, Q, mredparams)
		ring.MulScalarMontgomeryVec(ctIn.Value[1].Coeffs[i], ctOut.Value[1].Coeffs[i], invN, Q, mredparams)
	}

	eval.InnerSumLog(ctOut, 1<<logBatchSize, n, ctOut)
}

// InnerSumLog applies an optimized inner sum on the ciphertext (log2(n) + HW(n) rotations with double hoisting).
// The operation assumes that `ctIn` encrypts SlotCount/`batchSize` sub-vectors of size `batchSize` which it adds together (in parallel) by groups of `n`.
// It outputs in ctOut a ciphertext for which the "leftmost" sub-vector of each group is equal to the sum of the group.
// This method is faster than InnerSum when the number of rotations is large and uses log2(n) + HW(n) instead of 'n' keys.
func (eval *evaluator) InnerSumLog(ctIn *Ciphertext, batchSize, n int, ctOut *Ciphertext) {

	ringQ := eval.params.RingQ()
	ringP := eval.params.RingP()
	ringQP := rlwe.RingQP{RingQ: ringQ, RingP: ringP}

	levelQ := ctIn.Level()
	levelP := len(ringP.Modulus) - 1

	ctOut.Value[0].Coeffs = ctOut.Value[0].Coeffs[:levelQ+1]
	ctOut.Value[1].Coeffs = ctOut.Value[1].Coeffs[:levelQ+1]

	if n == 1 {
		if ctIn != ctOut {
			ring.CopyValuesLvl(levelQ, ctIn.Value[0], ctOut.Value[0])
			ring.CopyValuesLvl(levelQ, ctIn.Value[1], ctOut.Value[1])
		}
	} else {

		// Memory pool for ctIn = ctIn + rot(ctIn, 2^i) in Q
		tmpc0 := eval.poolQMul[0] // unused memory pool from evaluator
		tmpc1 := eval.poolQMul[1] // unused memory pool from evaluator

		tmpc1.IsNTT = true

		c0OutQP := eval.Pool[2]
		c1OutQP := eval.Pool[3]
		c0QP := eval.Pool[4]
		c1QP := eval.Pool[5]

		state := false
		copy := true
		// Binary reading of the input n
		for i, j := 0, n; j > 0; i, j = i+1, j>>1 {

			// Starts by decomposing the input ciphertext
			if i == 0 {
				// If first iteration, then copies directly from the input ciphertext that hasn't been rotated
				eval.DecomposeNTT(levelQ, levelP, levelP+1, ctIn.Value[1], eval.PoolDecompQP)
			} else {
				// Else copies from the rotated input ciphertext
				eval.DecomposeNTT(levelQ, levelP, levelP+1, tmpc1, eval.PoolDecompQP)
			}

			// If the binary reading scans a 1
			if j&1 == 1 {

				k := n - (n & ((2 << i) - 1))
				k *= batchSize

				// If the rotation is not zero
				if k != 0 {

					// Rotate((tmpc0, tmpc1), k)
					if i == 0 {
						eval.PermuteNTTHoistedNoModDown(levelQ, ctIn.Value[0], eval.PoolDecompQP, k, c0QP.Q, c1QP.Q, c0QP.P, c1QP.P)
					} else {
						eval.PermuteNTTHoistedNoModDown(levelQ, tmpc0, eval.PoolDecompQP, k, c0QP.Q, c1QP.Q, c0QP.P, c1QP.P)
					}

					// ctOut += Rotate((tmpc0, tmpc1), k)
					if copy {
						ringQP.CopyValuesLvl(levelQ, levelP, c0QP, c0OutQP)
						ringQP.CopyValuesLvl(levelQ, levelP, c1QP, c1OutQP)
						copy = false
					} else {
						ringQP.AddLvl(levelQ, levelP, c0OutQP, c0QP, c0OutQP)
						ringQP.AddLvl(levelQ, levelP, c1OutQP, c1QP, c1OutQP)
					}
				} else {

					state = true

					// if n is not a power of two
					if n&(n-1) != 0 {
						eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c0OutQP.Q, c0OutQP.P, c0OutQP.Q) // Division by P
						eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c1OutQP.Q, c1OutQP.P, c1OutQP.Q) // Division by P

						// ctOut += (tmpc0, tmpc1)
						ringQ.AddLvl(levelQ, c0OutQP.Q, tmpc0, ctOut.Value[0])
						ringQ.AddLvl(levelQ, c1OutQP.Q, tmpc1, ctOut.Value[1])

					} else {
						ring.CopyValuesLvl(levelQ, tmpc0, ctOut.Value[0])
						ring.CopyValuesLvl(levelQ, tmpc1, ctOut.Value[1])
						ctOut.Value[0].IsNTT = true
						ctOut.Value[1].IsNTT = true
					}
				}
			}

			if !state {
				if i == 0 {
					eval.PermuteNTTHoisted(levelQ, ctIn.Value[0], ctIn.Value[1], eval.PoolDecompQP, (1<<i)*batchSize, tmpc0, tmpc1)
					ringQ.AddLvl(levelQ, tmpc0, ctIn.Value[0], tmpc0)
					ringQ.AddLvl(levelQ, tmpc1, ctIn.Value[1], tmpc1)
				} else {
					// (tmpc0, tmpc1) = Rotate((tmpc0, tmpc1), 2^i)
					eval.PermuteNTTHoisted(levelQ, tmpc0, tmpc1, eval.PoolDecompQP, (1<<i)*batchSize, c0QP.Q, c1QP.Q)
					ringQ.AddLvl(levelQ, tmpc0, c0QP.Q, tmpc0)
					ringQ.AddLvl(levelQ, tmpc1, c1QP.Q, tmpc1)
				}
			}
		}
	}
}

// InnerSum applies an naive inner sum on the ciphertext (n rotations with single hoisting).
// The operation assumes that `ctIn` encrypts SlotCount/`batchSize` sub-vectors of size `batchSize` which it adds together (in parallel) by groups of `n`.
// It outputs in ctOut a ciphertext for which the "leftmost" sub-vector of each group is equal to the sum of the group.
// This method is faster than InnerSumLog when the number of rotations is small but uses 'n' keys instead of log(n) + HW(n).
func (eval *evaluator) InnerSum(ctIn *Ciphertext, batchSize, n int, ctOut *Ciphertext) {

	ringQ := eval.params.RingQ()
	ringP := eval.params.RingP()
	ringQP := rlwe.RingQP{RingQ: ringQ, RingP: ringP}

	levelQ := ctIn.Level()
	levelP := len(ringP.Modulus) - 1

	QiOverF := eval.params.QiOverflowMargin(levelQ) >> 1
	PiOverF := eval.params.PiOverflowMargin(levelP) >> 1

	ctOut.Value[0].Coeffs = ctOut.Value[0].Coeffs[:levelQ+1]
	ctOut.Value[1].Coeffs = ctOut.Value[1].Coeffs[:levelQ+1]

	// If sum with only the first element, then returns the input
	if n == 1 {

		// If the input-output points differ, copies on the output
		if ctIn != ctOut {
			ring.CopyValuesLvl(levelQ, ctIn.Value[0], ctOut.Value[0])
			ring.CopyValuesLvl(levelQ, ctIn.Value[1], ctOut.Value[1])
		}
		// If sum on at least two elements
	} else {

		// List of n-2 rotations
		rotations := []int{}
		for i := 1; i < n; i++ {
			rotations = append(rotations, i*batchSize)
		}

		// Memory pool
		tmp0QP := eval.Pool[1]
		tmp1QP := eval.Pool[2]

		// Basis decomposition
		eval.DecomposeNTT(levelQ, levelP, levelP+1, ctIn.Value[1], eval.PoolDecompQP)

		// Pre-rotates all [1, ..., n-1] rotations
		// Hoisted rotation without division by P
		ctInRotQP := eval.RotateHoistedNoModDownNew(levelQ, rotations, ctIn.Value[0], eval.PoolDecompQP)

		// P*c0 -> tmp0QP.Q
		ringQ.MulScalarBigintLvl(levelQ, ctIn.Value[0], ringP.ModulusBigint, tmp0QP.Q)

		// Adds phi_k(P*c0) on each of the vecRotQ
		// Does not need to add on the vecRotP because mod P === 0
		var reduce int
		// Sums elements [2, ..., n-1]
		for i := 1; i < n; i++ {

			j := i * batchSize

			if i == 1 {
				ringQP.CopyValuesLvl(levelQ, levelP, ctInRotQP[j][0], tmp0QP)
				ringQP.CopyValuesLvl(levelQ, levelP, ctInRotQP[j][1], tmp1QP)
			} else {
				ringQP.AddNoModLvl(levelQ, levelP, tmp0QP, ctInRotQP[j][0], tmp0QP)
				ringQP.AddNoModLvl(levelQ, levelP, tmp1QP, ctInRotQP[j][1], tmp1QP)
			}

			if reduce%QiOverF == QiOverF-1 {
				ringQ.ReduceLvl(levelQ, tmp0QP.Q, tmp0QP.Q)
				ringQ.ReduceLvl(levelQ, tmp1QP.Q, tmp1QP.Q)
			}

			if reduce%PiOverF == PiOverF-1 {
				ringP.ReduceLvl(levelP, tmp0QP.P, tmp0QP.P)
				ringP.ReduceLvl(levelP, tmp1QP.P, tmp1QP.P)
			}

			reduce++
		}

		if reduce%QiOverF != 0 {
			ringQ.ReduceLvl(levelQ, tmp0QP.Q, tmp0QP.Q)
			ringQ.ReduceLvl(levelQ, tmp1QP.Q, tmp1QP.Q)
		}

		if reduce%PiOverF != 0 {
			ringP.ReduceLvl(levelP, tmp0QP.P, tmp0QP.P)
			ringP.ReduceLvl(levelP, tmp1QP.P, tmp1QP.P)
		}

		// Division by P of sum(elements [2, ..., n-1] )
		eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, tmp0QP.Q, tmp0QP.P, tmp0QP.Q) // sum_{i=1, n-1}(phi(d0))/P
		eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, tmp1QP.Q, tmp1QP.P, tmp1QP.Q) // sum_{i=1, n-1}(phi(d1))/P

		// Adds element[1] (which did not require rotation)
		ringQ.AddLvl(levelQ, ctIn.Value[0], tmp0QP.Q, ctOut.Value[0]) // sum_{i=1, n-1}(phi(d0))/P + ct0
		ringQ.AddLvl(levelQ, ctIn.Value[1], tmp1QP.Q, ctOut.Value[1]) // sum_{i=1, n-1}(phi(d1))/P + ct1
	}
}

// ReplicateLog applies an optimized replication on the ciphertext (log2(n) + HW(n) rotations with double hoisting).
// It acts as the inverse of a inner sum (summing elements from left to right).
// The replication is parameterized by the size of the sub-vectors to replicate "batchSize" and
// the number of time "n" they need to be replicated.
// To ensure correctness, a gap of zero values of size batchSize * (n-1) must exist between
// two consecutive sub-vectors to replicate.
// This method is faster than Replicate when the number of rotations is large and uses log2(n) + HW(n) instead of 'n'.
func (eval *evaluator) ReplicateLog(ctIn *Ciphertext, batchSize, n int, ctOut *Ciphertext) {
	eval.InnerSumLog(ctIn, -batchSize, n, ctOut)
}

// Replicate applies naive replication on the ciphertext (n rotations with single hoisting).
// It acts as the inverse of a inner sum (summing elements from left to right).
// The replication is parameterized by the size of the sub-vectors to replicate "batchSize" and
// the number of time "n" they need to be replicated.
// To ensure correctness, a gap of zero values of size batchSize * (n-1) must exist between
// two consecutive sub-vectors to replicate.
// This method is faster than ReplicateLog when the number of rotations is small but uses 'n' keys instead of log2(n) + HW(n).
func (eval *evaluator) Replicate(ctIn *Ciphertext, batchSize, n int, ctOut *Ciphertext) {
	eval.InnerSum(ctIn, -batchSize, n, ctOut)
}

// MultiplyByDiagMatrix multiplies the ciphertext "ctIn" by the plaintext matrix "matrix" and returns the result on the ciphertext
// "ctOut". Memory pools for the decomposed ciphertext PoolDecompQ, PoolDecompP must be provided, those are list of poly of ringQ and ringP
// respectively, each of size params.Beta().
// The naive approach is used (single hoisting and no baby-step giant-step), which is faster than MultiplyByDiagMatrixBSGS
// for matrix of only a few non-zero diagonals but uses more keys.
func (eval *evaluator) MultiplyByDiagMatrix(ctIn *Ciphertext, matrix LinearTransform, PoolDecompQP []rlwe.PolyQP, ctOut *Ciphertext) {

	ringQ := eval.params.RingQ()
	ringP := eval.params.RingP()
	ringQP := rlwe.RingQP{RingQ: ringQ, RingP: ringP}

	levelQ := utils.MinInt(ctOut.Level(), utils.MinInt(ctIn.Level(), matrix.Level))
	levelP := len(ringP.Modulus) - 1

	ctOut.Value[0].Coeffs = ctOut.Value[0].Coeffs[:levelQ+1]
	ctOut.Value[1].Coeffs = ctOut.Value[1].Coeffs[:levelQ+1]

	QiOverF := eval.params.QiOverflowMargin(levelQ)
	PiOverF := eval.params.PiOverflowMargin(levelP)

	c0OutQP := rlwe.PolyQP{Q: ctOut.Value[0], P: eval.Pool[5].Q}
	c1OutQP := rlwe.PolyQP{Q: ctOut.Value[1], P: eval.Pool[5].P}

	ct0TimesP := eval.Pool[0].Q // ct0 * P mod Q
	tmp0QP := eval.Pool[1]
	tmp1QP := eval.Pool[2]
	ksRes0QP := eval.Pool[3]
	ksRes1QP := eval.Pool[4]

	ring.CopyValuesLvl(levelQ, ctIn.Value[0], eval.ctxpool.Value[0])
	ring.CopyValuesLvl(levelQ, ctIn.Value[1], eval.ctxpool.Value[1])
	ctInTmp0, ctInTmp1 := eval.ctxpool.Value[0], eval.ctxpool.Value[1]

	ringQ.MulScalarBigintLvl(levelQ, ctInTmp0, ringP.ModulusBigint, ct0TimesP) // P*c0

	var state bool
	var cnt int
	for k := range matrix.Vec {

		k &= int((ringQ.NthRoot >> 2) - 1)

		if k == 0 {
			state = true
		} else {

			galEl := eval.params.GaloisElementForColumnRotationBy(k)

			rtk, generated := eval.rtks.Keys[galEl]
			if !generated {
				panic("switching key not available")
			}

			index := eval.permuteNTTIndex[galEl]

			eval.KeyswitchHoistedNoModDown(levelQ, PoolDecompQP, rtk, ksRes0QP.Q, ksRes1QP.Q, ksRes0QP.P, ksRes1QP.P)
			ringQ.AddLvl(levelQ, ksRes0QP.Q, ct0TimesP, ksRes0QP.Q)
			ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, ksRes0QP, index, tmp0QP)
			ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, ksRes1QP, index, tmp1QP)

			if cnt == 0 {
				// keyswitch(c1_Q) = (d0_QP, d1_QP)
				ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, matrix.Vec[k], tmp0QP, c0OutQP)
				ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, matrix.Vec[k], tmp1QP, c1OutQP)
			} else {
				// keyswitch(c1_Q) = (d0_QP, d1_QP)
				ringQP.MulCoeffsMontgomeryAndAddLvl(levelQ, levelP, matrix.Vec[k], tmp0QP, c0OutQP)
				ringQP.MulCoeffsMontgomeryAndAddLvl(levelQ, levelP, matrix.Vec[k], tmp1QP, c1OutQP)
			}

			if cnt%QiOverF == QiOverF-1 {
				ringQ.ReduceLvl(levelQ, c0OutQP.Q, c0OutQP.Q)
				ringQ.ReduceLvl(levelQ, c1OutQP.Q, c1OutQP.Q)
			}

			if cnt%PiOverF == PiOverF-1 {
				ringP.ReduceLvl(levelP, c0OutQP.P, c0OutQP.P)
				ringP.ReduceLvl(levelP, c1OutQP.P, c1OutQP.P)
			}

			cnt++
		}
	}

	if cnt%QiOverF == 0 {
		ringQ.ReduceLvl(levelQ, c0OutQP.Q, c0OutQP.Q)
		ringQ.ReduceLvl(levelQ, c1OutQP.Q, c1OutQP.Q)
	}

	if cnt%PiOverF == 0 {
		ringP.ReduceLvl(levelP, c0OutQP.P, c0OutQP.P)
		ringP.ReduceLvl(levelP, c1OutQP.P, c1OutQP.P)
	}

	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c0OutQP.Q, c0OutQP.P, c0OutQP.Q) // sum(phi(c0 * P + d0_QP))/P
	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c1OutQP.Q, c1OutQP.P, c1OutQP.Q) // sum(phi(d1_QP))/P

	if state { // Rotation by zero
		ringQ.MulCoeffsMontgomeryAndAddLvl(levelQ, matrix.Vec[0].Q, ctInTmp0, c0OutQP.Q) // ctOut += c0_Q * plaintext
		ringQ.MulCoeffsMontgomeryAndAddLvl(levelQ, matrix.Vec[0].Q, ctInTmp1, c1OutQP.Q) // ctOut += c1_Q * plaintext
	}

	ctOut.Scale = matrix.Scale * ctIn.Scale
}

// MultiplyByDiagMatrixBSGS multiplies the ciphertext "ctIn" by the plaintext matrix "matrix" and returns the result on the ciphertext
// "ctOut". Memory pools for the decomposed ciphertext PoolDecompQ, PoolDecompP must be provided, those are list of poly of ringQ and ringP
// respectively, each of size params.Beta().
// The BSGS approach is used (double hoisting with baby-step giant-step), which is faster than MultiplyByDiagMatrix
// for matrix with more than a few non-zero diagonals and uses much less keys.
func (eval *evaluator) MultiplyByDiagMatrixBSGS(ctIn *Ciphertext, matrix LinearTransform, PoolDecompQP []rlwe.PolyQP, ctOut *Ciphertext) {

	ringQ := eval.params.RingQ()
	ringP := eval.params.RingP()
	ringQP := rlwe.RingQP{RingQ: ringQ, RingP: ringP}

	levelQ := utils.MinInt(ctOut.Level(), utils.MinInt(ctIn.Level(), matrix.Level))
	levelP := len(ringP.Modulus) - 1

	ctOut.Value[0].Coeffs = ctOut.Value[0].Coeffs[:levelQ+1]
	ctOut.Value[1].Coeffs = ctOut.Value[1].Coeffs[:levelQ+1]

	QiOverF := eval.params.QiOverflowMargin(levelQ) >> 1
	PiOverF := eval.params.PiOverflowMargin(levelP) >> 1

	// Computes the N2 rotations indexes of the non-zero rows of the diagonalized DFT matrix for the baby-step giang-step algorithm

	index, _, rotN2 := BsgsIndex(matrix.Vec, 1<<matrix.LogSlots, matrix.N1)
	// fmt.Println(index)
	// fmt.Println(len(index))
	// for i := range index {
	// 	fmt.Println(len(index[i]))
	// }
	// fmt.Println(" ------ ")
	// fmt.Println(rotN1, len(rotN1))
	// fmt.Println(rotN2, len(rotN2))

	ring.CopyValuesLvl(levelQ, ctIn.Value[0], eval.ctxpool.Value[0])
	ring.CopyValuesLvl(levelQ, ctIn.Value[1], eval.ctxpool.Value[1])
	ctInTmp0, ctInTmp1 := eval.ctxpool.Value[0], eval.ctxpool.Value[1]

	// Pre-rotates ciphertext for the baby-step giant-step algorithm, does not divide by P yet
	var t time.Time
	t = time.Now()
	ctInRotQP := eval.RotateHoistedNoModDownNew(levelQ, rotN2, ctInTmp0, eval.PoolDecompQP)

	// Accumulator inner loop
	tmp0QP := eval.Pool[1]
	tmp1QP := eval.Pool[2]

	// Accumulator outer loop
	c0QP := eval.Pool[3]
	c1QP := eval.Pool[4]

	// Result in QP
	c0OutQP := rlwe.PolyQP{Q: ctOut.Value[0], P: eval.Pool[5].Q}
	c1OutQP := rlwe.PolyQP{Q: ctOut.Value[1], P: eval.Pool[5].P}

	ringQ.MulScalarBigintLvl(levelQ, ctInTmp0, ringP.ModulusBigint, ctInTmp0) // P*c0
	ringQ.MulScalarBigintLvl(levelQ, ctInTmp1, ringP.ModulusBigint, ctInTmp1) // P*c1

	// OUTER LOOP
	var cnt0 int
	count := 0
	for j := range index {
		// INNER LOOP
		var cnt1 int
		// fmt.Println("j:", j, "n1:", len(index[j]))
		for _, i := range index[j] {
			count++

			if i == 0 {
				if cnt1 == 0 {
					ringQ.MulCoeffsMontgomeryConstantLvl(levelQ, matrix.Vec[j].Q, ctInTmp0, tmp0QP.Q)
					ringQ.MulCoeffsMontgomeryConstantLvl(levelQ, matrix.Vec[j].Q, ctInTmp1, tmp1QP.Q)
					tmp0QP.P.Zero()
					tmp1QP.P.Zero()
				} else {
					ringQ.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, matrix.Vec[j].Q, ctInTmp0, tmp0QP.Q)
					ringQ.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, matrix.Vec[j].Q, ctInTmp1, tmp1QP.Q)
				}
			} else {
				if cnt1 == 0 {
					ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, matrix.Vec[j+i], ctInRotQP[i][0], tmp0QP)
					ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, matrix.Vec[j+i], ctInRotQP[i][1], tmp1QP)
				} else {
					ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, matrix.Vec[j+i], ctInRotQP[i][0], tmp0QP)
					ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, matrix.Vec[j+i], ctInRotQP[i][1], tmp1QP)
				}
			}

			if cnt1%QiOverF == QiOverF-1 {
				ringQ.ReduceLvl(levelQ, tmp0QP.Q, tmp0QP.Q)
				ringQ.ReduceLvl(levelQ, tmp1QP.Q, tmp1QP.Q)
			}

			if cnt1%PiOverF == PiOverF-1 {
				ringP.ReduceLvl(levelP, tmp0QP.P, tmp0QP.P)
				ringP.ReduceLvl(levelP, tmp1QP.P, tmp1QP.P)
			}

			cnt1++
		}

		if cnt1%QiOverF != 0 {
			ringQ.ReduceLvl(levelQ, tmp0QP.Q, tmp0QP.Q)
			ringQ.ReduceLvl(levelQ, tmp1QP.Q, tmp1QP.Q)
		}

		if cnt1%PiOverF != 0 {
			ringP.ReduceLvl(levelP, tmp0QP.P, tmp0QP.P)
			ringP.ReduceLvl(levelP, tmp1QP.P, tmp1QP.P)
		}

		// If j != 0, then rotates ((tmp0QP.Q, tmp0QP.P), (tmp1QP.Q, tmp1QP.P)) by N1*j and adds the result on ((c0QP.Q, c0QP.P), (c1QP.Q, c1QP.P))
		if j != 0 {

			// Hoisting of the ModDown of sum(sum(phi(d1) * plaintext))
			eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, tmp1QP.Q, tmp1QP.P, tmp1QP.Q) // c1 * plaintext + sum(phi(d1) * plaintext) + phi(c1) * plaintext mod Q

			galEl := eval.params.GaloisElementForColumnRotationBy(j)

			rtk, generated := eval.rtks.Keys[galEl]
			if !generated {
				panic("switching key not available")
			}

			rotIndex := eval.permuteNTTIndex[galEl]

			tmp1QP.Q.IsNTT = true
			eval.SwitchKeysInPlaceNoModDown(levelQ, tmp1QP.Q, rtk, c0QP.Q, c0QP.P, c1QP.Q, c1QP.P) // Switchkey(P*phi(tmpRes_1)) = (d0, d1) in base QP
			ringQP.AddLvl(levelQ, levelP, c0QP, tmp0QP, c0QP)

			// Outer loop rotations
			if cnt0 == 0 {
				ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, c0QP, rotIndex, c0OutQP)
				ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, c1QP, rotIndex, c1OutQP)
			} else {
				ringQP.PermuteNTTWithIndexAndAddNoModLvl(levelQ, levelP, c0QP, rotIndex, c0OutQP)
				ringQP.PermuteNTTWithIndexAndAddNoModLvl(levelQ, levelP, c1QP, rotIndex, c1OutQP)
			}

			// Else directly adds on ((c0QP.Q, c0QP.P), (c1QP.Q, c1QP.P))
		} else {
			if cnt0 == 0 {
				ringQP.CopyValuesLvl(levelQ, levelP, tmp0QP, c0OutQP)
				ringQP.CopyValuesLvl(levelQ, levelP, tmp1QP, c1OutQP)
			} else {
				ringQP.AddNoModLvl(levelQ, levelP, c0OutQP, tmp0QP, c0OutQP)
				ringQP.AddNoModLvl(levelQ, levelP, c1OutQP, tmp1QP, c1OutQP)
			}
		}

		if cnt0%QiOverF == QiOverF-1 {
			ringQ.ReduceLvl(levelQ, ctOut.Value[0], ctOut.Value[0])
			ringQ.ReduceLvl(levelQ, ctOut.Value[1], ctOut.Value[1])
		}

		if cnt0%PiOverF == PiOverF-1 {
			ringP.ReduceLvl(levelP, c0OutQP.P, c0OutQP.P)
			ringP.ReduceLvl(levelP, c1OutQP.P, c1OutQP.P)
		}

		cnt0++
	}

	// fmt.Println("count:", float32(count)/float32(len(index)))

	if cnt0%QiOverF != 0 {
		ringQ.ReduceLvl(levelQ, ctOut.Value[0], ctOut.Value[0])
		ringQ.ReduceLvl(levelQ, ctOut.Value[1], ctOut.Value[1])
	}

	if cnt0%PiOverF != 0 {
		ringP.ReduceLvl(levelP, c0OutQP.P, c0OutQP.P)
		ringP.ReduceLvl(levelP, c1OutQP.P, c1OutQP.P)
	}

	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, ctOut.Value[0], c0OutQP.P, ctOut.Value[0]) // sum(phi(c0 * P + d0_QP))/P
	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, ctOut.Value[1], c1OutQP.P, ctOut.Value[1]) // sum(phi(d1_QP))/P

	ctOut.Scale = matrix.Scale * ctIn.Scale

	ctInRotQP = nil

	fmt.Println("Real Time: ", time.Since(t))
	runtime.GC()

}

func (eval *evaluator) MultiplyByDiagMatrixPrecomputed(ctIn *Ciphertext, matrix LinearTransform, matRotKey *rlwe.RotationKeySet, PoolDecompQP []rlwe.PolyQP, ctOut *Ciphertext, levelFree bool) {

	// fmt.Println("ctlevel:", ctIn.Level(), "matrixlevel:", matrix.Level, "outlevel:", ctOut.Level(), "matrix scale:", matrix.Scale)
	ringQ := eval.params.RingQ()
	ringP := eval.params.RingP()
	ringQP := rlwe.RingQP{RingQ: ringQ, RingP: ringP}

	levelQ := utils.MinInt(ctOut.Level(), utils.MinInt(ctIn.Level(), matrix.Level))
	levelP := len(ringP.Modulus) - 1

	ctOut.Value[0].Coeffs = ctOut.Value[0].Coeffs[:levelQ+1]
	ctOut.Value[1].Coeffs = ctOut.Value[1].Coeffs[:levelQ+1]

	QiOverF := eval.params.QiOverflowMargin(levelQ) / 2
	PiOverF := eval.params.PiOverflowMargin(levelP) / 2

	c0OutQP := rlwe.PolyQP{Q: ctOut.Value[0], P: eval.Pool[5].Q}
	c1OutQP := rlwe.PolyQP{Q: ctOut.Value[1], P: eval.Pool[5].P}

	ct0TimesP := eval.Pool[0].Q // ct0 * P mod Q
	tmp0QP := eval.Pool[1]
	tmp1QP := eval.Pool[2]
	ksRes0QP := eval.Pool[3]
	ksRes1QP := eval.Pool[4]

	ring.CopyValuesLvl(levelQ, ctIn.Value[0], eval.ctxpool.Value[0])
	ring.CopyValuesLvl(levelQ, ctIn.Value[1], eval.ctxpool.Value[1])
	ctInTmp0, ctInTmp1 := eval.ctxpool.Value[0], eval.ctxpool.Value[1]

	c0TimesM := ringQ.NewPoly()
	t := time.Now()
	/// No Need P * c0, as we do not need it in the rotation step
	//
	/// Sum of Matrix multiplies c0, r = SUM_k permute(k, c0) * M_k
	ringQ.MulScalarBigintLvl(levelQ, ctInTmp0, ringP.ModulusBigint, ct0TimesP) // P*c0
	// c0TimesMQP := c0OutQP.CopyNew()

	var cnt int = 0
	for k := range matrix.Vec {
		// permute(k, c0) * M_k
		// Note that M_k is prepermuted
		k &= int((ringQ.NthRoot >> 2) - 1)
		if k == 0 {
			// continue
			// tmp0QP.Q.Copy(ctInTmp0)
			// continue
			if cnt == 0 {
				ringQ.MulCoeffsMontgomery(matrix.Vec[k].Q, ctInTmp0, c0TimesM)
			} else {
				ringQ.MulCoeffsMontgomeryAndAddNoMod(matrix.Vec[k].Q, ctInTmp0, c0TimesM)
			}

		} else {
			galEl := eval.params.GaloisElementForColumnRotationBy(k)
			index := eval.permuteNTTIndex[galEl]

			ringQ.PermuteNTTWithIndexLvl(levelQ, ctInTmp0, index, tmp0QP.Q)

			if cnt == 0 {
				ringQ.MulCoeffsMontgomery(matrix.Vec[k].Q, tmp0QP.Q, c0TimesM)
			} else {
				ringQ.MulCoeffsMontgomeryAndAddNoMod(matrix.Vec[k].Q, tmp0QP.Q, c0TimesM)
			}

		}

		if cnt%QiOverF == QiOverF-1 {
			ringQ.ReduceLvl(levelQ, c0TimesM, c0TimesM)
		}

		cnt++
	}
	if cnt != 0 {
		ringQ.ReduceLvl(levelQ, c0TimesM, c0TimesM)
	}

	// fmt.Println("mul ct0:", time.Since(t))
	// rtkMultiplyByDiagMatrix := eval.PremultiplyByRotatedDiagMatrix(matrix)

	var state bool
	cnt = 0
	for k := range matrix.Vec {

		k &= int((ringQ.NthRoot >> 2) - 1)

		if k == 0 {
			state = true
		} else {

			galEl := eval.params.GaloisElementForColumnRotationBy(k)

			// rtk, generated := eval.rtks.Keys[galEl]
			// if !generated {
			// 	panic("switching key not available")
			// }

			index := eval.permuteNTTIndex[galEl]
			// rtk := rtkMultiplyByDiagMatrix[k]

			if levelFree {
				// fmt.Println("decompose vs non-decompose")

				// eval.KeyswitchHoistedNoModDown(levelQ, PoolDecompQP, rtk, ksRes0QP.Q, ksRes1QP.Q, ksRes0QP.P, ksRes1QP.P)
				// ringQP.PrintHeadNTT(ksRes0QP, 3)

				eval.KeyswitchHoistedNoModDownDivFirst(levelQ, PoolDecompQP, nil,
					eval.levelFreeAuxCt[galEl], ksRes0QP.Q, ksRes1QP.Q, ksRes0QP.P, ksRes1QP.P)
				// ringQP.PrintHeadNTT(ksRes0QP, 3)
				// ringQP.PrintHeadNTT(ksRes1QP, 3)

			} else {
				rtk, generated := matRotKey.Keys[galEl]
				if !generated {
					panic("switching key not available")
				}

				eval.KeyswitchHoistedNoModDown(levelQ, PoolDecompQP, rtk, ksRes0QP.Q, ksRes1QP.Q, ksRes0QP.P, ksRes1QP.P)
			}

			// ringQ.AddLvl(levelQ, ksRes0QP.Q, ct0TimesP, ksRes0QP.Q)
			if cnt == 0 {
				// ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, ksRes0QP, index, tmp0QP)
				// ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, ksRes1QP, index, tmp1QP)
				ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, ksRes0QP, index, c0OutQP)
				ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, ksRes1QP, index, c1OutQP)

			} else {
				ringQP.PermuteNTTWithIndexAndAddNoModLvl(levelQ, levelP, ksRes0QP, index, c0OutQP)
				ringQP.PermuteNTTWithIndexAndAddNoModLvl(levelQ, levelP, ksRes1QP, index, c1OutQP)

			}
			//
			// if false {
			// 	fmt.Println(k, ":")
			// 	fmt.Println("ksres0")
			// 	// ringQP.RingQ.MulScalarBigint(tmp0QP.Q, ring.NewUint(ringP.Modulus[levelP]), ksRes0QP.Q)
			// 	ringQP.PrintHeadNTT(ksRes0QP, 3)
			// 	fmt.Println("ksres1")
			// 	// ringQP.RingQ.MulScalarBigint(tmp1QP.Q, ring.NewUint(ringP.Modulus[levelP]), ksRes1QP.Q)
			// 	ringQP.PrintHeadNTT(ksRes1QP, 3)
			// }
			//
			if false {
				if cnt == 0 {
					// keyswitch(c1_Q) = (d0_QP, d1_QP)
					// ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, matrix.Vec[k], tmp0QP, c0OutQP)
					// ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, matrix.Vec[k], tmp1QP, c1OutQP)

					ring.CopyValuesLvl(levelQ, tmp0QP.Q, c0OutQP.Q)
					ring.CopyValuesLvl(levelP, tmp0QP.P, c0OutQP.P)
					ring.CopyValuesLvl(levelQ, tmp1QP.Q, c1OutQP.Q)
					ring.CopyValuesLvl(levelP, tmp1QP.P, c1OutQP.P)
					// ringQ.ReduceLvl(levelQ, c0OutQP.Q, c0OutQP.Q)
					// ringQ.ReduceLvl(levelQ, c1OutQP.Q, c1OutQP.Q)
					// ringP.ReduceLvl(levelP, c0OutQP.P, c0OutQP.P)
					// ringP.ReduceLvl(levelP, c1OutQP.P, c1OutQP.P)

				} else {
					// keyswitch(c1_Q) = (d0_QP, d1_QP)
					// ringQP.MulCoeffsMontgomeryAndAddLvl(levelQ, levelP, matrix.Vec[k], tmp0QP, c0OutQP)
					// ringQP.MulCoeffsMontgomeryAndAddLvl(levelQ, levelP, matrix.Vec[k], tmp1QP, c1OutQP)
					ringQP.AddNoModLvl(levelQ, levelP, tmp0QP, c0OutQP, c0OutQP)
					ringQP.AddNoModLvl(levelQ, levelP, tmp1QP, c1OutQP, c1OutQP)
				}
			}

			if QiOverF == 0 || cnt%QiOverF == QiOverF-1 {
				ringQ.ReduceLvl(levelQ, c0OutQP.Q, c0OutQP.Q)
				ringQ.ReduceLvl(levelQ, c1OutQP.Q, c1OutQP.Q)
			}

			if PiOverF == 0 || cnt%PiOverF == PiOverF-1 {
				ringP.ReduceLvl(levelP, c0OutQP.P, c0OutQP.P)
				ringP.ReduceLvl(levelP, c1OutQP.P, c1OutQP.P)
			}

			cnt++
		}
	}

	if cnt%QiOverF != 0 {

		ringQ.ReduceLvl(levelQ, ctOut.Value[0], ctOut.Value[0])
		ringQ.ReduceLvl(levelQ, ctOut.Value[1], ctOut.Value[1])
	}

	if cnt%PiOverF != 0 {
		ringP.ReduceLvl(levelP, c0OutQP.P, c0OutQP.P)
		ringP.ReduceLvl(levelP, c1OutQP.P, c1OutQP.P)
	}

	// ringQ.MulScalarBigintLvl(levelQ, c0TimesMQP.Q, ringP.ModulusBigint, c0TimesMQP.Q) // P*c0
	// ringQP.AddLvl(levelQ, levelP, c0TimesMQP, c0OutQP, c0OutQP)
	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c0OutQP.Q, c0OutQP.P, c0OutQP.Q) // sum(phi(c0 * P + d0_QP))/P
	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c1OutQP.Q, c1OutQP.P, c1OutQP.Q) // sum(phi(d1_QP))/P

	// Add accumulated c0 to final result
	if levelFree {
		// t2 := time.Now()
		level := ctOut.Level()

		// ringQ.InvNTTSingleLazy(level, c0TimesM.Coeffs[level], eval.poolQMul[0].Coeffs[level])
		// perform normal levelfree rescaling on ct0
		ringQ.DivRoundByLastModulusNTTLvl(level, c0TimesM, eval.poolQMul[0], c0TimesM)
		// ringQ.DivRoundByLastModulusLvl(level, c0TimesM, c0TimesM)
		c0TimesM.Coeffs = c0TimesM.Coeffs[:level]
		ringQ.ModupFromQLMinus1(c0TimesM, level, eval.params.N())
		// ringQ.ModupFromQLMinus1NoNTT(c0TimesM, level, eval.params.N())

		// div q_L
		// ringQ.DivRoundByLastModulusManyNTTLvl(level, 1, c0OutQP.Q, eval.poolQMul[0], c0OutQP.Q)
		// ringQ.DivRoundByLastModulusManyNTTLvl(level, 1, c1OutQP.Q, eval.poolQMul[0], c1OutQP.Q)
		// ringQ.ModupFromQLMinus1(c0OutQP.Q, levelQ, eval.params.N())
		// ringQ.ModupFromQLMinus1(c1OutQP.Q, levelQ, eval.params.N())

		if state { // Rotation by zero
			// ringQ.MulCoeffsMontgomeryLvl(levelQ, matrix.Vec[0].Q, ctInTmp0, ctInTmp0) // ctOut += c0_Q * plaintext
			ringQ.MulCoeffsMontgomeryLvl(levelQ, matrix.Vec[0].Q, ctInTmp1, ctInTmp1) // ctOut += c1_Q * plaintext

			// ringQ.InvNTTSingleLazy(level, ctInTmp1.Coeffs[level], eval.poolQMul[0].Coeffs[level])
			ringQ.DivRoundByLastModulusNTTLvl(level, ctInTmp1, eval.poolQMul[0], ctInTmp1)
			// ringQ.DivRoundByLastModulusLvl(level, ctInTmp1, ctInTmp1)

			ctInTmp1.Coeffs = ctInTmp1.Coeffs[:level]
			// ctInTmp0.Coeffs = ctInTmp0.Coeffs[:level]

			// ringQ.ModupFromQLMinus1NoNTT(ctInTmp1, level, eval.params.N())
			ringQ.ModupFromQLMinus1(ctInTmp1, level, eval.params.N())
			// ringQ.ModupFromQLMinus1(ctInTmp0, level, eval.params.N())

			ringQ.AddLvl(level, ctInTmp1, c1OutQP.Q, c1OutQP.Q)
			// ringQ.AddLvl(level, ctInTmp0, c0OutQP.Q, c0OutQP.Q)
		}

		ringQ.AddLvl(levelQ, c0TimesM, c0OutQP.Q, c0OutQP.Q)
		// ringQ.NTTLvl(levelQ, c0OutQP.Q, c0OutQP.Q)
		// ringQ.NTTLvl(levelQ, c1OutQP.Q, c1OutQP.Q)

		// Rescaling
		// c0OutQP.Q.Coeffs = c0OutQP.Q.Coeffs[:level]
		// c1OutQP.Q.Coeffs = c1OutQP.Q.Coeffs[:level]
		//
		// fmt.Println(ctOut.Level(), levelQ)
		ctOut.Scale = matrix.Scale * ctIn.Scale / (float64(ringQ.Modulus[levelQ]))

		// fmt.Println(
		// 	"matrix.Scale:", math.Log2(matrix.Scale),
		// 	"ctIn.scale:", math.Log2(ctIn.Scale),
		// 	"pk:", math.Log2(float64(ringP.Modulus[levelP])),
		// 	"qL:", math.Log2(float64(ringQ.Modulus[levelQ])),
		// 	"ctOut.Scale:", math.Log2(ctOut.Scale),
		// )

		// ctOut.Scale = matrix.Scale * ctIn.Scale / (0x1000000002a0001 - 3141632)
		// ctOut.Scale = matrix.Scale * ctIn.Scale / (float64(ringP.Modulus[levelP])) * 32

		// fmt.Println("first level:", time.Since(t2))
	} else {
		ringQ.MulScalarBigint(c0OutQP.Q, ring.NewUint(ringQ.Modulus[levelQ]), c0OutQP.Q)
		ringQ.MulScalarBigint(c1OutQP.Q, ring.NewUint(ringQ.Modulus[levelQ]), c1OutQP.Q)

		if state { // Rotation by zero
			// ringQ.MulCoeffsMontgomeryAndAddLvl(levelQ, matrix.Vec[0].Q, ctInTmp0, c0OutQP.Q) // ctOut += c0_Q * plaintext
			ringQ.MulCoeffsMontgomeryAndAddLvl(levelQ, matrix.Vec[0].Q, ctInTmp1, c1OutQP.Q) // ctOut += c1_Q * plaintext
		}

		ringQ.AddLvl(levelQ, c0TimesM, c0OutQP.Q, c0OutQP.Q)
		// c0OutQP.Q.Coeffs = c0OutQP.Q.Coeffs[:levelQ]
		// c1OutQP.Q.Coeffs = c1OutQP.Q.Coeffs[:levelQ]
		// ctOut.Scale = matrix.Scale * ctIn.Scale / (float64(ringQ.Modulus[levelQ]))
		ctOut.Scale = matrix.Scale * ctIn.Scale
	}

	fmt.Println("Real time: ", time.Since(t))

}

func (eval *evaluator) PremultiplyByRotatedDiagMatrix(matrix LinearTransform) map[int]*rlwe.SwitchingKey {
	ringQ := eval.params.RingQ()
	ringP := eval.params.RingP()
	ringQP := rlwe.RingQP{RingQ: ringQ, RingP: ringP}

	// levelQ := utils.MinInt(ctOut.Level(), utils.MinInt(ctIn.Level(), matrix.Level))
	levelQ := matrix.Level
	levelP := len(ringP.Modulus) - 1

	weighted_ksk := make(map[int]*rlwe.SwitchingKey)
	for k := range matrix.Vec {
		k &= int((ringQ.NthRoot >> 2) - 1)

		if k == 0 {
			continue
		}

		galEl := eval.params.GaloisElementForColumnRotationBy(k)
		negGalEl := eval.params.GaloisElementForColumnRotationBy(-k)

		rtk, generated := eval.rtks.Keys[galEl]
		if !generated {
			panic("switching key not available")
		}

		index := eval.permuteNTTIndex[negGalEl]

		rerotated_mat := ringQP.NewPoly()

		ringQP.PermuteNTTWithIndexLvl(
			levelQ,
			levelP,
			matrix.Vec[k],
			index,
			rerotated_mat)

		weighted_key := rtk.CopyNew()
		for key_idx := range weighted_key.Value {
			ringQP.MulCoeffsMontgomeryLvl(
				levelQ, levelP,
				rerotated_mat,
				weighted_key.Value[key_idx][0],
				weighted_key.Value[key_idx][0])
			ringQP.MulCoeffsMontgomeryLvl(
				levelQ, levelP,
				rerotated_mat,
				weighted_key.Value[key_idx][1],
				weighted_key.Value[key_idx][1])
		}

		weighted_ksk[k] = weighted_key
	}

	return weighted_ksk
}
