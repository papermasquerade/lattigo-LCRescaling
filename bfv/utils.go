package bfv

import (
	"fmt"
	"github.com/ldsec/lattigo/v2/ring"
	"math"
	"math/big"
)

// DecryptAndPrintError decrypts a ciphertext and prints the log2 of the error.
func DecryptAndPrintError(ptWant *Plaintext, cthave *Ciphertext, ringQ *ring.Ring, decryptor Decryptor) {
	ringQ.Sub(cthave.Value[0], ptWant.Value, cthave.Value[0])
	plaintext := decryptor.DecryptNew(cthave)
	bigintCoeffs := make([]*big.Int, ringQ.N)
	ringQ.PolyToBigint(plaintext.Value, bigintCoeffs)
	center(bigintCoeffs, ringQ.ModulusBigint)
	stdErr, minErr, maxErr := errorStats(bigintCoeffs)
	fmt.Printf("STD : %f - Min : %f - Max : %f\n", math.Log2(stdErr), math.Log2(minErr), math.Log2(maxErr))
}

func errorStats(vec []*big.Int) (float64, float64, float64) {

	vecfloat := make([]*big.Float, len(vec))
	minErr := new(big.Float).SetFloat64(0)
	maxErr := new(big.Float).SetFloat64(0)
	tmp := new(big.Float)
	minErr.SetInt(vec[0])
	minErr.Abs(minErr)
	for i := range vec {
		vecfloat[i] = new(big.Float)
		vecfloat[i].SetInt(vec[i])

		tmp.Abs(vecfloat[i])

		if minErr.Cmp(tmp) == 1 {
			minErr.Set(tmp)
		}

		if maxErr.Cmp(tmp) == -1 {
			maxErr.Set(tmp)
		}
	}

	n := new(big.Float).SetFloat64(float64(len(vec)))

	mean := new(big.Float).SetFloat64(0)

	for _, c := range vecfloat {
		mean.Add(mean, c)
	}

	mean.Quo(mean, n)

	err := new(big.Float).SetFloat64(0)
	for _, c := range vecfloat {
		tmp.Sub(c, mean)
		tmp.Mul(tmp, tmp)
		err.Add(err, tmp)
	}

	err.Quo(err, n)
	err.Sqrt(err)

	x, _ := err.Float64()
	y, _ := minErr.Float64()
	z, _ := maxErr.Float64()

	return x, y, z

}

func center(coeffs []*big.Int, Q *big.Int) {
	qHalf := new(big.Int)
	qHalf.Set(Q)
	qHalf.Rsh(qHalf, 1)
	var sign int
	for i := range coeffs {
		coeffs[i].Mod(coeffs[i], Q)
		sign = coeffs[i].Cmp(qHalf)
		if sign == 1 || sign == 0 {
			coeffs[i].Sub(coeffs[i], Q)
		}
	}
}
