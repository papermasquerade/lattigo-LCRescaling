package rlwe

import (
	"fmt"
	"math"
	// "math/big"

	"github.com/ldsec/lattigo/v2/ring"
)

var _ = fmt.Println

// KeySwitcher is a struct for RLWE key-switching.
type KeySwitcher struct {
	*Parameters
	*keySwitcherBuffer
	Baseconverter *ring.FastBasisExtender
	Decomposer    *ring.Decomposer
}

type keySwitcherBuffer struct {
	// PoolQ[0]/PoolP[0] : on the fly decomp(c2)
	// PoolQ[1-5]/PoolP[1-5] : available
	Pool         [6]PolyQP
	PoolInvNTT   *ring.Poly
	PoolDecompQP []PolyQP // Memory pool for the basis extension in hoisting
}

func newKeySwitcherBuffer(params Parameters) *keySwitcherBuffer {

	buff := new(keySwitcherBuffer)
	beta := params.Beta()
	ringQP := params.RingQP()

	buff.Pool = [6]PolyQP{ringQP.NewPoly(), ringQP.NewPoly(), ringQP.NewPoly(), ringQP.NewPoly(), ringQP.NewPoly(), ringQP.NewPoly()}

	buff.PoolInvNTT = params.RingQ().NewPoly()

	buff.PoolDecompQP = make([]PolyQP, beta)
	for i := 0; i < beta; i++ {
		buff.PoolDecompQP[i] = ringQP.NewPoly()
	}

	return buff
}

// NewKeySwitcher creates a new KeySwitcher.
func NewKeySwitcher(params Parameters) *KeySwitcher {
	ks := new(KeySwitcher)
	ks.Parameters = &params
	ks.Baseconverter = ring.NewFastBasisExtender(params.RingQ(), params.RingP())
	ks.Decomposer = ring.NewDecomposer(params.RingQ(), params.RingP())
	ks.keySwitcherBuffer = newKeySwitcherBuffer(params)
	return ks
}

// ShallowCopy creates a copy of a KeySwitcher, only reallocating the memory pool.
func (ks *KeySwitcher) ShallowCopy() *KeySwitcher {
	return &KeySwitcher{
		Parameters:        ks.Parameters,
		Decomposer:        ks.Decomposer,
		keySwitcherBuffer: newKeySwitcherBuffer(*ks.Parameters),
		Baseconverter:     ks.Baseconverter.ShallowCopy(),
	}
}

// SwitchKeysInPlace applies the general key-switching procedure of the form [c0 + cx*evakey[0], c1 + cx*evakey[1]]
// Will return the result in the same NTT domain as the input cx.
func (ks *KeySwitcher) SwitchKeysInPlace(levelQ int, cx *ring.Poly, evakey *SwitchingKey, p0, p1 *ring.Poly) {
	ks.SwitchKeysInPlaceNoModDown(levelQ, cx, evakey, p0, ks.Pool[1].P, p1, ks.Pool[2].P)

	levelP := len(evakey.Value[0][0].P.Coeffs) - 1

	if cx.IsNTT {
		ks.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, p0, ks.Pool[1].P, p0)
		ks.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, p1, ks.Pool[2].P, p1)
	} else {

		ks.ringQ.InvNTTLazyLvl(levelQ, p0, p0)
		ks.ringQ.InvNTTLazyLvl(levelQ, p1, p1)
		ks.ringP.InvNTTLazyLvl(levelP, ks.Pool[1].P, ks.Pool[1].P)
		ks.ringP.InvNTTLazyLvl(levelP, ks.Pool[2].P, ks.Pool[2].P)

		ks.Baseconverter.ModDownQPtoQ(levelQ, levelP, p0, ks.Pool[1].P, p0)
		ks.Baseconverter.ModDownQPtoQ(levelQ, levelP, p1, ks.Pool[2].P, p1)
	}
}

// DecomposeNTT applies the full RNS basis decomposition for all q_alpha_i on c2.
// Expects the IsNTT flag of c2 to correctly reflect the domain of c2.
// PoolDecompQ and PoolDecompQ are vectors of polynomials (mod Q and mod P) that store the
// special RNS decomposition of c2 (in the NTT domain)
func (ks *KeySwitcher) DecomposeNTT(levelQ, levelP, alpha int, c2 *ring.Poly, PoolDecomp []PolyQP) {

	ringQ := ks.RingQ()
	var polyNTT, polyInvNTT *ring.Poly

	if c2.IsNTT {
		polyNTT = c2
		polyInvNTT = ks.PoolInvNTT
		ringQ.InvNTTLvl(levelQ, polyNTT, polyInvNTT)
	} else {
		polyNTT = ks.PoolInvNTT
		polyInvNTT = c2
		ringQ.NTTLvl(levelQ, polyInvNTT, polyNTT)
	}

	beta := int(math.Ceil(float64(levelQ+1) / float64(levelP+1)))

	for i := 0; i < beta; i++ {
		ks.DecomposeSingleNTT(levelQ, levelP, alpha, i, polyNTT, polyInvNTT, PoolDecomp[i].Q, PoolDecomp[i].P)
	}
}

// DecomposeSingleNTT takes the input polynomial c2 (c2NTT and c2InvNTT, respectively in the NTT and out of the NTT domain)
// modulo q_alpha_beta, and returns the result on c2QiQ are c2QiP the receiver polynomials
// respectively mod Q and mod P (in the NTT domain)
func (ks *KeySwitcher) DecomposeSingleNTT(levelQ, levelP, alpha, beta int, c2NTT, c2InvNTT, c2QiQ, c2QiP *ring.Poly) {

	ringQ := ks.RingQ()
	ringP := ks.RingP()
	ks.Decomposer.DecomposeAndSplit(levelQ, levelP, alpha, beta, c2InvNTT, c2QiQ, c2QiP)
	p0idxst := beta * (levelP + 1)
	p0idxed := p0idxst + 1

	// c2_qi = cx mod qi mod qi
	for x := 0; x < levelQ+1; x++ {
		if p0idxst <= x && x < p0idxed {
			copy(c2QiQ.Coeffs[x], c2NTT.Coeffs[x])
		} else {
			ringQ.NTTSingleLazy(x, c2QiQ.Coeffs[x], c2QiQ.Coeffs[x])
			// ringQ.NTTSingle(x, c2QiQ.Coeffs[x], c2QiQ.Coeffs[x])
		}
		// ringQ.NTTSingle(x, c2QiQ.Coeffs[x], c2QiQ.Coeffs[x])
	}

	// c2QiP = c2 mod qi mod pj
	ringP.NTTLazyLvl(levelP, c2QiP, c2QiP)
	// ringP.NTTLvl(levelP, c2QiP, c2QiP)

}

// SwitchKeysInPlaceNoModDown applies the key-switch to the polynomial cx :
//
// pool2 = dot(decomp(cx) * evakey[0]) mod QP (encrypted input is multiplied by P factor)
// pool3 = dot(decomp(cx) * evakey[1]) mod QP (encrypted input is multiplied by P factor)
//
// Expects the flag IsNTT of cx to correctly reflect the domain of cx.
func (ks *KeySwitcher) SwitchKeysInPlaceNoModDown(levelQ int, cx *ring.Poly, evakey *SwitchingKey, c0Q, c0P, c1Q, c1P *ring.Poly) {

	var reduce int

	ringQ := ks.RingQ()
	ringP := ks.RingP()
	ringQP := ks.RingQP()

	c2QP := ks.Pool[0]

	var cxNTT, cxInvNTT *ring.Poly
	if cx.IsNTT {
		cxNTT = cx
		cxInvNTT = ks.PoolInvNTT
		ringQ.InvNTTLvl(levelQ, cxNTT, cxInvNTT)
	} else {
		cxNTT = ks.PoolInvNTT
		cxInvNTT = cx
		ringQ.NTTLvl(levelQ, cxInvNTT, cxNTT)
	}

	c0QP := PolyQP{c0Q, c0P}
	c1QP := PolyQP{c1Q, c1P}

	reduce = 0

	alpha := len(evakey.Value[0][0].P.Coeffs)
	levelP := alpha - 1
	beta := int(math.Ceil(float64(levelQ+1) / float64(levelP+1)))

	QiOverF := ks.Parameters.QiOverflowMargin(levelQ) >> 1
	PiOverF := ks.Parameters.PiOverflowMargin(levelP) >> 1

	// Key switching with CRT decomposition for the Qi
	for i := 0; i < beta; i++ {

		ks.DecomposeSingleNTT(levelQ, levelP, alpha, i, cxNTT, cxInvNTT, c2QP.Q, c2QP.P)

		if i == 0 {
			ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, evakey.Value[i][0], c2QP, c0QP)
			ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, evakey.Value[i][1], c2QP, c1QP)
		} else {
			ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, evakey.Value[i][0], c2QP, c0QP)
			ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, evakey.Value[i][1], c2QP, c1QP)
		}

		if reduce%QiOverF == QiOverF-1 {
			ringQ.ReduceLvl(levelQ, c0QP.Q, c0QP.Q)
			ringQ.ReduceLvl(levelQ, c1QP.Q, c1QP.Q)
		}

		if reduce%PiOverF == PiOverF-1 {
			ringP.ReduceLvl(levelP, c0QP.P, c0QP.P)
			ringP.ReduceLvl(levelP, c1QP.P, c1QP.P)
		}

		reduce++
	}

	if reduce%QiOverF != 0 {
		ringQ.ReduceLvl(levelQ, c0QP.Q, c0QP.Q)
		ringQ.ReduceLvl(levelQ, c1QP.Q, c1QP.Q)
	}

	if reduce%PiOverF != 0 {
		ringP.ReduceLvl(levelP, c0QP.P, c0QP.P)
		ringP.ReduceLvl(levelP, c1QP.P, c1QP.P)
	}
}

// KeyswitchHoisted applies the key-switch to the decomposed polynomial c2 mod QP (PoolDecompQ and PoolDecompP)
// and divides the result by P, reducing the basis from QP to Q.
//
// pool2 = dot(PoolDecompQ||PoolDecompP * evakey[0]) mod Q
// pool3 = dot(PoolDecompQ||PoolDecompP * evakey[1]) mod Q
func (ks *KeySwitcher) KeyswitchHoisted(levelQ int, PoolDecompQP []PolyQP, evakey *SwitchingKey, c0Q, c1Q, c0P, c1P *ring.Poly) {

	ks.KeyswitchHoistedNoModDown(levelQ, PoolDecompQP, evakey, c0Q, c1Q, c0P, c1P)

	levelP := len(evakey.Value[0][0].P.Coeffs) - 1

	// Computes c0Q = c0Q/c0P and c1Q = c1Q/c1P
	ks.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c0Q, c0P, c0Q)
	ks.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c1Q, c1P, c1Q)
}

// KeyswitchHoistedNoModDown applies the key-switch to the decomposed polynomial c2 mod QP (PoolDecompQ and PoolDecompP)
//
// pool2 = dot(PoolDecompQ||PoolDecompP * evakey[0]) mod QP
// pool3 = dot(PoolDecompQ||PoolDecompP * evakey[1]) mod QP
func (ks *KeySwitcher) KeyswitchHoistedNoModDown(levelQ int, PoolDecompQP []PolyQP, evakey *SwitchingKey, c0Q, c1Q, c0P, c1P *ring.Poly) {

	ringQ := ks.RingQ()
	ringP := ks.RingP()
	ringQP := ks.RingQP()

	c0QP := PolyQP{c0Q, c0P}
	c1QP := PolyQP{c1Q, c1P}

	alpha := len(evakey.Value[0][0].P.Coeffs)
	levelP := alpha - 1
	beta := int(math.Ceil(float64(levelQ+1) / float64(alpha)))

	QiOverF := ks.Parameters.QiOverflowMargin(levelQ) >> 1
	PiOverF := ks.Parameters.PiOverflowMargin(levelP) >> 1

	// Key switching with CRT decomposition for the Qi
	var reduce int
	for i := 0; i < beta; i++ {

		if i == 0 {
			ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, evakey.Value[i][0], PoolDecompQP[i], c0QP)
			ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, evakey.Value[i][1], PoolDecompQP[i], c1QP)
		} else {
			ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, evakey.Value[i][0], PoolDecompQP[i], c0QP)
			ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, evakey.Value[i][1], PoolDecompQP[i], c1QP)
		}

		if reduce%QiOverF == QiOverF-1 {
			ringQ.ReduceLvl(levelQ, c0QP.Q, c0QP.Q)
			ringQ.ReduceLvl(levelQ, c1QP.Q, c1QP.Q)
		}

		if reduce%PiOverF == PiOverF-1 {
			ringP.ReduceLvl(levelP, c0QP.P, c0QP.P)
			ringP.ReduceLvl(levelP, c1QP.P, c1QP.P)
		}

		reduce++
	}

	if reduce%QiOverF != 0 {
		ringQ.ReduceLvl(levelQ, c0QP.Q, c0QP.Q)
		ringQ.ReduceLvl(levelQ, c1QP.Q, c1QP.Q)
	}

	if reduce%PiOverF != 0 {
		ringP.ReduceLvl(levelP, c0QP.P, c0QP.P)
		ringP.ReduceLvl(levelP, c1QP.P, c1QP.P)
	}
}

func (ks *KeySwitcher) KeyswitchHoistedNoModDownDivFirst(levelQ int, PoolDecompQP []PolyQP, evakey *SwitchingKey, ksAux []PolyQP, c0Q, c1Q, c0P, c1P *ring.Poly) {

	ringQ := ks.RingQ()
	ringP := ks.RingP()
	ringQP := ks.RingQP()

	// N := ks.Parameters.N()
	// r, err := ring.NewRing(N, append(ringQ.Modulus, ringP.Modulus...))
	// if err != nil {
	// 	panic(err)
	// }

	c0QP := PolyQP{c0Q, c0P}
	c1QP := PolyQP{c1Q, c1P}

	alpha := len(ringP.Modulus)
	// alpha := len(evakey.Value[0][0].P.Coeffs)
	levelP := alpha - 1

	// ringQP.InvMFormLvl(levelQ, levelP, ksAux[0], ksAux[0])
	// ringQP.InvMFormLvl(levelQ, levelP, ksAux[1], ksAux[1])
	ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, PoolDecompQP[0], ksAux[0], c0QP)
	ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, PoolDecompQP[0], ksAux[1], c1QP)

	ringQ.ReduceLvl(levelQ, c0QP.Q, c0QP.Q)
	ringQ.ReduceLvl(levelQ, c1QP.Q, c1QP.Q)

	ringP.ReduceLvl(levelP, c0QP.P, c0QP.P)
	ringP.ReduceLvl(levelP, c1QP.P, c1QP.P)
	// fmt.Println(" ============= c0QP & c1QP ===============")
	// ringQP.PrintHeadNTT(ksAux[0], 3)
	// ringQP.PrintHeadNTT(c0QP, 3)
	// ringQP.PrintHeadNTT(c1QP, 3)
	return

	// beta := int(math.Ceil(float64(levelQ+1) / float64(alpha)))
	//
	// QiOverF := ks.Parameters.QiOverflowMargin(levelQ) >> 1
	// PiOverF := ks.Parameters.PiOverflowMargin(levelP) >> 1
	//
	// var reduce int
	// // sum c1_beta * qstar * qtilde in ZZ_QP
	// // Should be in montgomery domain?
	// bigPQ := big.NewInt(1)
	// for _, modulus := range r.Modulus {
	// 	bigPQ.Mul(bigPQ, ring.NewUint(modulus))
	// }
	// kQP := ringQP.NewPoly()
	//
	// bigP := big.NewInt(1)
	// for _, modulus := range ringP.Modulus {
	// 	bigP.Mul(bigP, ring.NewUint(modulus))
	// }
	//
	// tmp := big.NewInt(0)
	// Q := big.NewInt(1)
	// for _, qi := range ringQ.Modulus {
	// 	Q.Mul(Q, ring.NewUint(qi))
	// }
	//
	// tmpBigs := make([]*big.Int, ringQ.N)
	// for i := range tmpBigs {
	// 	tmpBigs[i] = big.NewInt(0)
	// }
	//
	// halfQ := big.NewInt(1)
	// halfQ.Rsh(Q, 1)
	//
	// poolQP := PolyQP{ringQP.RingQ.NewPoly(), ringQP.RingP.NewPoly()}
	// poolQP.P.Zero()
	// poolQP.Q.Zero()
	//
	// sumDj := big.NewInt(0)
	// for i := 0; i < beta; i++ {
	// 	Dj := big.NewInt(1)
	// 	for j := 0; j < alpha; j++ {
	//
	// 		index := i*alpha + j
	//
	// 		// It handles the case where nb pj does not divide nb qi
	// 		if index >= levelQ+1 {
	// 			break
	// 		}
	//
	// 		qi := ringQ.Modulus[index]
	// 		//
	// 		// // qstar mod P
	// 		// ringQP.RingP.MulScalarLvl(levelP, Dbeta.P, qi, Dbeta.P)
	//
	// 		// qstar * qinv mod PQ
	// 		// for w := 0; w < ringQ.N; w++ {
	// 		// 	Dbeta.Q.Coeffs[index][w] = 1
	// 		// }
	// 		Dj.Mul(Dj, ring.NewUint(qi))
	// 	}
	// 	halfDj := big.NewInt(0)
	// 	halfDj.Rsh(Dj, 1)
	//
	// 	DjHat := big.NewInt(1)
	// 	DjHat.Div(Q, Dj)
	// 	tmp.ModInverse(DjHat, Dj)
	//
	// 	// centered
	// 	// if tmp.Cmp(halfDj) >= 0 {
	// 	// 	tmp.Sub(tmp, Dj)
	// 	// }
	//
	// 	// DjHatInvDjHat := big.NewInt(0)
	// 	// DjHatInvDjHat.Mul(DjHat, tmp)
	// 	// sumDj.Add(sumDj, DjHatInvDjHat)
	// 	// fmt.Println("sum Dj:", sumDj)
	// 	// tmp.Div(sumDj, Q)
	// 	// fmt.Println("sum Dj / Q", tmp)
	// 	//
	// 	// ringQ.PolyToBigintCenteredLvl(levelQ, Dbeta.Q, Dbigs)
	// 	//
	// 	// for w := 0; w < ringQ.N; w++ {
	// 	// 	for j, pi := range ringP.Modulus {
	// 	// 		tmp.Mod(Dbigs[w], ring.NewUint(pi))
	// 	// 		Dbeta.P.Coeffs[j][w] = tmp.Uint64()
	// 	// 	}
	// 	// }
	// 	//
	// 	// fmt.Println(i, " KSUm:", KSumBigs[:3])
	// 	// fmt.Println("q delta:")
	// 	// ringQP.PrintHead()
	//
	// 	// ringQP.NTTLvl(levelQ, levelP, Dbeta, Dbeta)
	// 	// ringQP.InvNTTLvl(levelQ, levelP, PoolDecompQP[i], PoolDecompQP[i])
	//
	// 	// ringQP.MFormLvl(levelQ, levelP, Dbeta, Dbeta)
	//
	// 	// fmt.Println("check dbete.Q vs dbeta")
	// 	// ringQ.PrintHeadNTT(Dbeta.Q, 3)
	// 	// ringQP.PrintHeadNTT(Dbeta, 3)
	// 	// fmt.Println("q delta:")
	// 	// ringQP.PrintHeadNTT(Dbeta, 1)
	// 	// fmt.Println("PQ")
	// 	// fmt.Println(bigPQ)
	//
	// 	// c[i] * qstar * qinv mod PQ
	// 	// if i == 0 {
	// 	// 	// ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, Dbeta, PoolDecompQP[i], kQP)
	// 	//
	// 	// 	ringQP.AddLvl(levelQ, levelP, kQP, Dbeta, kQP)
	// 	// 	// ringQ.MulCoeffsLvl(levelQ, Dbeta.Q, PoolDecompQP[i].Q, kQP.Q)
	// 	// 	// ringP.MulCoeffsLvl(levelP, Dbeta.P, PoolDecompQP[i].P, kQP.P)
	// 	// } else {
	// 	// 	// ringQP.MulCoeffsMontgomeryAndAddLvl(levelQ, levelP, Dbeta, PoolDecompQP[i], kQP)
	// 	//
	// 	// 	// ringQP.AddLvl(levelQ, levelP, kQP, Dbeta, kQP)
	// 	// 	// ringQ.MulCoeffsAndAddLvl(levelQ, Dbeta.Q, PoolDecompQP[i].Q, kQP.Q)
	// 	// 	// ringP.MulCoeffsAndAddLvl(levelP, Dbeta.P, PoolDecompQP[i].P, kQP.P)
	// 	// }
	// 	//
	// 	// ringQP.NTTLvl(levelQ, levelP, PoolDecompQP[i], PoolDecompQP[i])
	// 	// if reduce%QiOverF == QiOverF-1 {
	// 	// 	ringQ.ReduceLvl(levelQ, kQP.Q, kQP.Q)
	// 	// }
	// 	//
	// 	// if reduce%PiOverF == PiOverF-1 {
	// 	// 	ringP.ReduceLvl(levelP, kQP.P, kQP.P)
	// 	// }
	//
	// 	// reduce++
	// 	// fmt.Println(i, ":")
	// 	// ringQP.PrintHeadApplyFunc(kQP, 3, func(x *big.Int) *big.Int {
	// 	// 	x.Div(x, Q)
	// 	// 	return x
	// 	// })
	// 	// ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, kQP, PoolDecompQP[0], poolQP)
	// 	// ringQP.PrintHeadNTTApplyFunc(poolQP, 3, func(x *big.Int) *big.Int {
	// 	// 	x.Div(x, Q)
	// 	// 	return x
	// 	// })
	// 	//
	// 	// ringQP.InvNTTLvl(levelQ, levelP, PoolDecompQP[i], poolQP)
	// 	// ringQP.PolyToBigintCenteredLvl(poolQP, tmpBigs)
	// 	// fmt.Println("oo norm of c", ring.InfNorm(tmpBigs))
	//
	// 	// ringQP.InvNTTLvl(levelQ, levelP, Dbeta, poolQP)
	// 	// ringQP.PolyToBigintCenteredLvl(poolQP, tmpBigs)
	// 	// fmt.Println("oo norm of Dbeta", ring.InfNorm(tmpBigs))
	// 	//
	// 	// ringQP.NTTLvl(levelQ, levelP, kQP, kQP)
	//
	// }
	//
	// if reduce%QiOverF != 0 {
	// 	ringQ.ReduceLvl(levelQ, kQP.Q, kQP.Q)
	// }
	//
	// if reduce%PiOverF != 0 {
	// 	ringP.ReduceLvl(levelP, kQP.P, kQP.P)
	// }
	//
	// // ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, PoolDecompQP[0], kQP, kQP)
	// // ringQP.PrintHeadNTTApplyFunc(kQP, 3, func(x *big.Int) *big.Int {
	// // 	x.Div(x, Q)
	// // 	return x
	// // })
	// //
	// // ringQP.InvMFormLvl(levelQ, levelP, kQP, poolQP)
	// // ringQP.PrintHeadNTTApplyFunc(poolQP, 3, func(x *big.Int) *big.Int {
	// // 	x.Div(x, Q)
	// // 	return x
	// // })
	//
	// fmt.Println("P")
	// fmt.Println(bigP)
	// fmt.Println("PQ")
	// fmt.Println(bigPQ)
	//
	// // ringQP.InvMFormLvl(levelQ, levelP, PoolDecompQP[0], PoolDecompQP[0])
	// // ringQP.InvNTTLvl(levelQ, levelP, PoolDecompQP[0], PoolDecompQP[0])
	// // for j := 0; j < N; j++ {
	// // 	for i := range ringQ.Modulus {
	// // 		decompC0QP.Coeffs[i][j] = PoolDecompQP[0].Q.Coeffs[i][j]
	// // 	}
	// // 	for i := range ringP.Modulus {
	// // 		decompC0QP.Coeffs[i+len(ringQ.Modulus)][j] = PoolDecompQP[0].P.Coeffs[i][j]
	// // 	}
	// // }
	//
	// // ringQP.NTTLvl(levelQ, levelP, PoolDecompQP[0], PoolDecompQP[0])
	// // ringQP.MFormLvl(levelQ, levelP, PoolDecompQP[0], PoolDecompQP[0])
	//
	// fmt.Print("c0 mod q_delta_3")
	// ringQP.PrintHeadNTT(PoolDecompQP[1], 3)
	//
	// // kRing := r.NewPoly()
	// // for j := 0; j < N; j++ {
	// // 	for i := range ringQ.Modulus {
	// // 		kRing.Coeffs[i][j] = kQP.Q.Coeffs[i][j]
	// // 	}
	// // 	for i := range ringP.Modulus {
	// // 		kRing.Coeffs[i+len(ringQ.Modulus)][j] = kQP.P.Coeffs[i][j]
	// // 	}
	// // }
	// //
	// kbigs := make([]*big.Int, N)
	// for i := range kbigs {
	// 	kbigs[i] = big.NewInt(0)
	// }
	//
	// ringQP.InvNTTLvl(levelQ, levelP, PoolDecompQP[0], poolQP)
	// ringQP.PolyToBigintCenteredLvl(poolQP, kbigs)
	// for i := range kbigs {
	// 	kbigs[i].Mul(kbigs[i], sumDj)
	// }
	//
	// // r.PolyToBigintCenteredLvl(kRing.Level(), kRing, kbigs)
	// for i := 0; i < N; i++ {
	// 	tmp.Mod(kbigs[i], Q)
	// 	if tmp.Cmp(halfQ) >= 0 {
	// 		tmp.Sub(tmp, Q)
	// 	}
	//
	// 	// sum ci * qstar * qtilde / Q
	// 	kbigs[i].Sub(kbigs[i], tmp)
	// 	kbigs[i].Div(kbigs[i], Q)
	// 	for j, pqj := range r.Modulus {
	// 		tmp.Mod(kbigs[i], ring.NewUint(pqj))
	// 		if j <= levelQ {
	// 			kQP.Q.Coeffs[j][i] = tmp.Uint64()
	// 		} else {
	// 			kQP.P.Coeffs[j-levelQ-1][i] = tmp.Uint64()
	// 		}
	// 	}
	// }
	//
	// fmt.Println("k:")
	// fmt.Println(kbigs[:5])
	// // fmt.Println(KSumBigs[:10])
	//
	// ringQP.NTTLvl(levelQ, levelP, kQP, kQP)
	// ringQP.MFormLvl(levelQ, levelP, kQP, kQP) // should add this?
	// c0QP.P.Zero()
	// c0QP.Q.Zero()
	// c1QP.Q.Zero()
	// c1QP.P.Zero()
	//
	// // ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, ksAux[0], kQP, c0QP)
	// // ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, ksAux[1], kQP, c1QP)
	// reduce = 1
	// // Key switching with CRT decomposition for the Qi
	// for i := 0; i < beta; i++ {
	//
	// 	// fmt.Println(evakey.Value[i][1].Q.Coeffs[1][:5])
	// 	// if i == 0 {
	// 	// 	ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, evakey.Value[i][0], PoolDecompQP[i], c0QP)
	// 	// 	ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, evakey.Value[i][1], PoolDecompQP[i], c1QP)
	// 	// } else {
	// 	ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, evakey.Value[i][0], PoolDecompQP[i], c0QP)
	// 	ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, evakey.Value[i][1], PoolDecompQP[i], c1QP)
	// 	// }
	//
	// 	if reduce%QiOverF == QiOverF-1 {
	// 		ringQ.ReduceLvl(levelQ, c0QP.Q, c0QP.Q)
	// 		ringQ.ReduceLvl(levelQ, c1QP.Q, c1QP.Q)
	// 	}
	//
	// 	if reduce%PiOverF == PiOverF-1 {
	// 		ringP.ReduceLvl(levelP, c0QP.P, c0QP.P)
	// 		ringP.ReduceLvl(levelP, c1QP.P, c1QP.P)
	// 	}
	//
	// 	reduce++
	// }
	//
	// if reduce%QiOverF != 0 {
	// 	ringQ.ReduceLvl(levelQ, c0QP.Q, c0QP.Q)
	// 	ringQ.ReduceLvl(levelQ, c1QP.Q, c1QP.Q)
	// }
	//
	// if reduce%PiOverF != 0 {
	// 	ringP.ReduceLvl(levelP, c0QP.P, c0QP.P)
	// 	ringP.ReduceLvl(levelP, c1QP.P, c1QP.P)
	// }
}
