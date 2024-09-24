package bootstrapping

import (
	"fmt"
	"math"

	"github.com/ldsec/lattigo/v2/ckks"
	"github.com/ldsec/lattigo/v2/ring"
)

var _ = fmt.Println

// Bootstrapp re-encrypt a ciphertext at lvl Q0 to a ciphertext at MaxLevel-k where k is the depth of the bootstrapping circuit.
// If the input ciphertext level is zero, the input scale must be an exact power of two smaller or equal to round(Q0/2^{10}).
// If the input ciphertext is at level one or more, the input scale does not need to be an exact power of two as one level
// can be used to do a scale matching.
func (btp *Bootstrapper) Bootstrapp(ctIn *ckks.Ciphertext) (ctOut *ckks.Ciphertext) {

	ctOut = ctIn.CopyNew()

	// Drops the level to 1
	for ctOut.Level() > 1 {
		btp.DropLevel(ctOut, 1)
	}

	// Brings the ciphertext scale to Q0/MessageRatio
	if ctOut.Level() == 1 {

		// If one level is available, then uses it to match the scale
		btp.SetScale(ctOut, btp.q0OverMessageRatio)

		// Then drops to level 0
		for ctOut.Level() != 0 {
			btp.DropLevel(ctOut, 1)
		}

	} else {

		// Does an integer constant mult by round((Q0/Delta_m)/ctscle)
		if btp.q0OverMessageRatio < ctOut.Scale {
			panic("ciphetext scale > q/||m||)")
		}

		btp.ScaleUp(ctOut, math.Round(btp.q0OverMessageRatio/ctOut.Scale), ctOut)
	}

	// Step 1 : Extend the basis from q to Q
	ctOut = btp.modUpFromQ0(ctOut)

	// Brings the ciphertext scale to EvalMod-ScalingFactor/(Q0/scale) if Q0 < EvalMod-ScalingFactor.
	// Does it after modUp to avoid plaintext overflow as the scaling used during EvalMod can be larger than Q0.
	// Doing this at this stage helps mitigate the additive error of the next steps.
	if (btp.evalModPoly.ScalingFactor()/btp.evalModPoly.MessageRatio())/ctOut.Scale > 1 {
		btp.ScaleUp(ctOut, math.Round((btp.evalModPoly.ScalingFactor()/btp.evalModPoly.MessageRatio())/ctOut.Scale), ctOut)
	}

	//SubSum X -> (N/dslots) * Y^dslots
	btp.Trace(ctOut, btp.params.LogSlots(), btp.params.LogN()-1, ctOut)

	// Step 2 : CoeffsToSlots (Homomorphic encoding)
	ctReal, ctImag := btp.CoeffsToSlotsNew(ctOut, btp.ctsMatrices)

	// Step 3 : EvalMod (Homomorphic modular reduction)
	// ctReal = Ecd(real)
	// ctImag = Ecd(imag)
	// If n < N/2 then ctReal = Ecd(real|imag)
	ctReal = btp.EvalModNew(ctReal, btp.evalModPoly)
	ctReal.Scale = btp.params.DefaultScale()

	if ctImag != nil {
		ctImag = btp.EvalModNew(ctImag, btp.evalModPoly)
		ctImag.Scale = btp.params.DefaultScale()
	}

	// Step 4 : SlotsToCoeffs (Homomorphic decoding)
	ctOut = btp.SlotsToCoeffsNew(ctReal, ctImag, btp.stcMatrices)

	return
}

// func mulMod(a, b, q uint64) (r uint64) {
//
// }

// modup in NTT domain
func (btp *Bootstrapper) modUpFromQl1(ct *ckks.Ciphertext) *ckks.Ciphertext {
	ringQ := btp.params.RingQ()
	for i := range ct.Value {
		ringQ.InvNTTLvl(ct.Level(), ct.Value[i], ct.Value[i])
	}

	nowLevel := ct.Level()
	// assign zero polynomials
	for u := range ct.Value {
		ct.Value[u].Coeffs = append(ct.Value[u].Coeffs, make([][]uint64, btp.params.MaxLevel()-nowLevel)...)
		for i := nowLevel + 1; i < btp.params.MaxLevel()+1; i++ {
			ct.Value[u].Coeffs[i] = make([]uint64, btp.params.N())
		}
	}

	bredparams := ringQ.BredParams
	l := len(ringQ.Modulus) - 1
	ql := ringQ.Modulus[l]
	bredql := ring.BRedParams(ql)

	var QL1 uint64 = 1
	for _, qi := range ringQ.Modulus[:l] {
		QL1 = ring.BRed(QL1, qi, ql, bredql)
	}

	// u for indexing polynomial
	for u := range ct.Value {
		// coefi for indexing coefficienct of polynomials
		for coefi := 0; coefi < btp.params.N(); coefi++ {
			var rL uint64 = 0
			var z float64 = 0
			// i for indexing RNS basis, i.e. levels
			for i := 0; i < l; i++ {
				var invQi uint64 = 1       // in Z_q0
				var prodQiModQL uint64 = 1 // in Z_ql

				qi := ringQ.Modulus[i]
				for j, qj := range ringQ.Modulus {
					if i == j || j == l {
						continue
					}
					// prod_(j eq.not i) q_j mod q_i
					invQi = ring.BRed(invQi, qj, qi, bredparams[i])

					// prod_(j eq.not i) q_j mod q_L
					prodQiModQL = ring.BRed(prodQiModQL, qj, ql, bredql)
				}
				invQi = ring.ModInv(invQi, qi)
				invQi = ring.BRed(invQi, ct.Value[u].Coeffs[i][coefi], qi, bredparams[i])

				if invQi > (qi >> 1) {
					z -= float64(qi-invQi) / float64(qi)
					rL += ql - ring.BRed(prodQiModQL, qi-invQi, ql, bredql)
				} else {
					z += float64(invQi) / float64(qi)
					rL += ring.BRed(prodQiModQL, invQi, ql, bredql)
				}

				rL = ring.BRedAdd(rL, ql, bredql)
			}

			z = math.Round(z)
			if z < 0 {
				rL += ring.BRed(QL1, uint64(-z), ql, bredql)
			} else {
				rL += ql - ring.BRed(QL1, uint64(z), ql, bredql)
			}
			ct.Value[u].Coeffs[l][coefi] = ring.BRedAdd(rL, ql, bredql)
		}
	}

	for i := range ct.Value {
		ringQ.NTTLvl(ct.Level(), ct.Value[i], ct.Value[i])
	}
	return ct
}

func (btp *Bootstrapper) modUpFromQ0(ct *ckks.Ciphertext) *ckks.Ciphertext {

	ringQ := btp.params.RingQ()

	for i := range ct.Value {
		ringQ.InvNTTLvl(ct.Level(), ct.Value[i], ct.Value[i])
	}

	// Extend the ciphertext with zero polynomials.
	for u := range ct.Value {
		ct.Value[u].Coeffs = append(ct.Value[u].Coeffs, make([][]uint64, btp.params.MaxLevel())...)
		for i := 1; i < btp.params.MaxLevel()+1; i++ {
			ct.Value[u].Coeffs[i] = make([]uint64, btp.params.N())
		}
	}

	//Centers the values around Q0 and extends the basis from Q0 to QL
	Q := ringQ.Modulus[0]
	bredparams := ringQ.BredParams

	var coeff, qi uint64
	for u := range ct.Value {

		for j := 0; j < btp.params.N(); j++ {

			coeff = ct.Value[u].Coeffs[0][j]

			for i := 1; i < btp.params.MaxLevel()+1; i++ {

				qi = ringQ.Modulus[i]

				if coeff > (Q >> 1) {
					ct.Value[u].Coeffs[i][j] = qi - ring.BRedAdd(Q-coeff, qi, bredparams[i])
				} else {
					ct.Value[u].Coeffs[i][j] = ring.BRedAdd(coeff, qi, bredparams[i])
				}
			}
		}
	}

	for i := range ct.Value {
		ringQ.NTTLvl(ct.Level(), ct.Value[i], ct.Value[i])
	}

	return ct
}
