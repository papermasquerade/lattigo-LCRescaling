package rlwe

import (
	"fmt"
	"math"
	"math/big"

	"github.com/ldsec/lattigo/v2/ring"
	"github.com/ldsec/lattigo/v2/utils"
)

var _ = fmt.Println

// KeyGenerator is an interface implementing the methods of the KeyGenerator.
type KeyGenerator interface {
	GenSecretKey() (sk *SecretKey)
	GenSecretKeyGaussian() (sk *SecretKey)
	GenSecretKeyWithDistrib(p float64) (sk *SecretKey)
	GenSecretKeySparse(hw int) (sk *SecretKey)
	GenPublicKey(sk *SecretKey) (pk *PublicKey)
	GenKeyPair() (sk *SecretKey, pk *PublicKey)
	GenKeyPairSparse(hw int) (sk *SecretKey, pk *PublicKey)
	GenRelinearizationKey(sk *SecretKey, maxDegree int) (evk *RelinearizationKey)
	GenSwitchingKey(skInput, skOutput *SecretKey) (newevakey *SwitchingKey)
	GenSwitchingKeyForGalois(galEl uint64, sk *SecretKey) (swk *SwitchingKey)
	GenRotationKeys(galEls []uint64, sk *SecretKey) (rks *RotationKeySet)
	GenSwitchingKeyForRotationBy(k int, sk *SecretKey) (swk *SwitchingKey)
	GenRotationKeysForRotations(ks []int, inclueSwapRows bool, sk *SecretKey) (rks *RotationKeySet)
	GenRotationKeysForRotationsApplyFunc(ks []int, inclueSwapRows bool, sk *SecretKey, matrix map[uint64]PolyQP, cts map[uint64][]PolyQP, levelQ int) (rks *RotationKeySet)
	GenSwitchingKeyForRowRotation(sk *SecretKey) (swk *SwitchingKey)
	GenRotationKeysForInnerSum(sk *SecretKey) (rks *RotationKeySet)
	GenSwitchingKeysForRingSwap(skCKKS, skCI *SecretKey) (swkStdToConjugateInvariant, swkConjugateInvariantToStd *SwitchingKey)
	GenCorrectionPartForRotationKey(skIn *ring.Poly, skOut PolyQP, matrix PolyQP) (ct0 PolyQP, ct1 PolyQP)
}

// KeyGenerator is a structure that stores the elements required to create new keys,
// as well as a small memory pool for intermediate values.
type keyGenerator struct {
	params           Parameters
	poolQ            *ring.Poly
	poolQP           PolyQP
	gaussianSamplerQ *ring.GaussianSampler
	uniformSamplerQ  *ring.UniformSampler
	uniformSamplerP  *ring.UniformSampler
}

// NewKeyGenerator creates a new KeyGenerator, from which the secret and public keys, as well as the evaluation,
// rotation and switching keys can be generated.
func NewKeyGenerator(params Parameters) KeyGenerator {

	prng, err := utils.NewPRNG()
	if err != nil {
		panic(err)
	}

	return &keyGenerator{
		params:           params,
		poolQ:            params.RingQ().NewPoly(),
		poolQP:           params.RingQP().NewPoly(),
		gaussianSamplerQ: ring.NewGaussianSampler(prng, params.RingQ(), params.Sigma(), int(6*params.Sigma())),
		uniformSamplerQ:  ring.NewUniformSampler(prng, params.RingQ()),
		uniformSamplerP:  ring.NewUniformSampler(prng, params.RingP()),
	}
}

// GenSecretKey generates a new SecretKey with the distribution [1/3, 1/3, 1/3].
func (keygen *keyGenerator) GenSecretKey() (sk *SecretKey) {
	return keygen.GenSecretKeyWithDistrib(1.0 / 3)
}

// GenSecretKey generates a new SecretKey with the error distribution.
func (keygen *keyGenerator) GenSecretKeyGaussian() (sk *SecretKey) {
	return keygen.genSecretKeyFromSampler(keygen.gaussianSamplerQ)
}

// GenSecretKeyWithDistrib generates a new SecretKey with the distribution [(p-1)/2, p, (p-1)/2].
func (keygen *keyGenerator) GenSecretKeyWithDistrib(p float64) (sk *SecretKey) {
	prng, err := utils.NewPRNG()
	if err != nil {
		panic(err)
	}
	ternarySamplerMontgomery := ring.NewTernarySampler(prng, keygen.params.RingQ(), p, false)
	return keygen.genSecretKeyFromSampler(ternarySamplerMontgomery)
}

// GenSecretKeySparse generates a new SecretKey with exactly hw non-zero coefficients.
// The key's coefficients are tenery and key is in NTT domain
func (keygen *keyGenerator) GenSecretKeySparse(hw int) (sk *SecretKey) {
	prng, err := utils.NewPRNG()
	if err != nil {
		panic(err)
	}
	ternarySamplerMontgomery := ring.NewTernarySamplerSparse(prng, keygen.params.RingQ(), hw, false)
	return keygen.genSecretKeyFromSampler(ternarySamplerMontgomery)
}

// GenPublicKey generates a new public key from the provided SecretKey.
func (keygen *keyGenerator) GenPublicKey(sk *SecretKey) (pk *PublicKey) {

	pk = new(PublicKey)
	ringQP := keygen.params.RingQP()
	levelQ, levelP := keygen.params.QCount()-1, keygen.params.PCount()-1

	//pk[0] = [-as + e]
	//pk[1] = [a]
	pk = NewPublicKey(keygen.params)
	keygen.gaussianSamplerQ.Read(pk.Value[0].Q)
	ringQP.ExtendBasisSmallNormAndCenter(pk.Value[0].Q, levelP, nil, pk.Value[0].P)
	ringQP.NTTLvl(levelQ, levelP, pk.Value[0], pk.Value[0])

	keygen.uniformSamplerQ.Read(pk.Value[1].Q)
	keygen.uniformSamplerP.Read(pk.Value[1].P)

	ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, sk.Value, pk.Value[1], pk.Value[0])
	return pk
}

// GenKeyPair generates a new SecretKey with distribution [1/3, 1/3, 1/3] and a corresponding public key.
func (keygen *keyGenerator) GenKeyPair() (sk *SecretKey, pk *PublicKey) {
	sk = keygen.GenSecretKey()
	return sk, keygen.GenPublicKey(sk)
}

// GenKeyPairSparse generates a new SecretKey with exactly hw non zero coefficients [1/2, 0, 1/2].
func (keygen *keyGenerator) GenKeyPairSparse(hw int) (sk *SecretKey, pk *PublicKey) {
	sk = keygen.GenSecretKeySparse(hw)
	return sk, keygen.GenPublicKey(sk)
}

// GenRelinKey generates a new EvaluationKey that will be used to relinearize Ciphertexts during multiplication.
func (keygen *keyGenerator) GenRelinearizationKey(sk *SecretKey, maxDegree int) (evk *RelinearizationKey) {

	if keygen.params.PCount() == 0 {
		panic("modulus P is empty")
	}

	levelQ := keygen.params.QCount() - 1
	levelP := keygen.params.PCount() - 1

	evk = new(RelinearizationKey)
	evk.Keys = make([]*SwitchingKey, maxDegree)
	for i := range evk.Keys {
		evk.Keys[i] = NewSwitchingKey(keygen.params, levelQ, levelP)
	}

	keygen.poolQP.Q.CopyValues(sk.Value.Q)
	ringQ := keygen.params.RingQ()
	for i := 0; i < maxDegree; i++ {
		ringQ.MulCoeffsMontgomery(keygen.poolQP.Q, sk.Value.Q, keygen.poolQP.Q)
		keygen.genSwitchingKey(keygen.poolQP.Q, sk.Value, evk.Keys[i])
	}

	return
}

// GenRotationKeys generates a RotationKeySet from a list of galois element corresponding to the desired rotations
// See also GenRotationKeysForRotations.
func (keygen *keyGenerator) GenRotationKeys(galEls []uint64, sk *SecretKey) (rks *RotationKeySet) {
	rks = NewRotationKeySet(keygen.params, galEls)
	for _, galEl := range galEls {
		keygen.genrotKey(sk.Value, keygen.params.InverseGaloisElement(galEl), rks.Keys[galEl])
	}
	return rks
}

func (keygen *keyGenerator) GenSwitchingKeyForRotationBy(k int, sk *SecretKey) (swk *SwitchingKey) {
	swk = NewSwitchingKey(keygen.params, keygen.params.QCount()-1, keygen.params.PCount()-1)
	galElInv := keygen.params.GaloisElementForColumnRotationBy(-int(k))
	keygen.genrotKey(sk.Value, galElInv, swk)
	return
}

// GenRotationKeysForRotations generates a RotationKeySet supporting left rotations by k positions for all k in ks.
// Negative k is equivalent to a right rotation by k positions
// If includeConjugate is true, the resulting set contains the conjugation key.
func (keygen *keyGenerator) GenRotationKeysForRotations(ks []int, includeConjugate bool, sk *SecretKey) (rks *RotationKeySet) {
	galEls := make([]uint64, len(ks), len(ks)+1)
	for i, k := range ks {
		galEls[i] = keygen.params.GaloisElementForColumnRotationBy(k)
	}
	if includeConjugate {
		galEls = append(galEls, keygen.params.GaloisElementForRowRotation())
	}
	return keygen.GenRotationKeys(galEls, sk)
}

// multiply the matrix to rotation key, matrix should **NOT** be permuted
func (keygen *keyGenerator) GenRotationKeysForRotationsApplyFunc(
	ks []int,
	includeConjugate bool,
	sk *SecretKey,
	matrix map[uint64]PolyQP,
	// pool *ring.Poly,
	cts map[uint64][]PolyQP, levelQ int) (rks *RotationKeySet) {

	galEls := make([]uint64, len(ks), len(ks)+1)
	// for i, k := range ks {
	// 	galEls[i] = keygen.params.GaloisElementForColumnRotationBy(k)
	// }
	for i := range matrix {
		galEls = append(galEls, i)
	}

	if includeConjugate {
		galEls = append(galEls, keygen.params.GaloisElementForRowRotation())
	}
	rks = NewRotationKeySet(keygen.params, galEls)
	// for i := range matrix {
	// 	galEls = append(galEls, i)
	// }
	// rks = NewRotationKeySet(keygen.params, galEls)
	ringQ := keygen.params.RingQ()
	ringP := keygen.params.RingP()
	levelP := len(ringP.Modulus) - 1
	ringQP := RingQP{RingQ: ringQ, RingP: ringP}
	// r, err := ring.NewRing(keygen.params.N(), append(ringQ.Modulus, ringP.Modulus...))
	// if err != nil {
	// 	panic(err)
	// }

	// fmt.Println("mat keygen")
	// for _, galEl := range galEls {
	// 	vec, hasValue := matrix[galEl]
	// 	if hasValue {
	for galEl := range matrix {
		vec := matrix[galEl]
		// levelQ := len(rks.Keys[galEl].Value[0][0].Q.Coeffs) - 1
		// levelQ := vec.Q.Level()
		// fmt.Println("levelQ:", levelQ)

		// multiply the key switch key with the message vector
		hook := func(in PolyQP, out PolyQP) {
			// ringQ.MulCoeffsMontgomeryLvl(levelQ, vec.Q, in.Q, out.Q)
			// P * s * M
			ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, vec, in, out)
		}

		postHook := func(in PolyQP, out PolyQP) {
			// P * s * M / q_L

			ringQP.InvMFormLvl(levelQ, levelP, in, out)
			ringQP.InvNTTLvl(levelQ, levelP, out, out)

			N := keygen.params.N()
			moduli := append(ringQP.RingP.Modulus, ringQP.RingQ.Modulus...)
			r, _ := ring.NewRing(N, moduli)
			poly := r.NewPoly()
			poly.Coeffs = make([][]uint64, len(moduli))
			for i := range out.P.Coeffs {
				poly.Coeffs[i] = make([]uint64, 0)
				poly.Coeffs[i] = append(poly.Coeffs[i], out.P.Coeffs[i]...)
			}
			for i := range out.Q.Coeffs {
				poly.Coeffs[i+len(out.P.Coeffs)] = make([]uint64, 0)
				poly.Coeffs[i+len(out.P.Coeffs)] = append(poly.Coeffs[i+len(out.P.Coeffs)], out.Q.Coeffs[i]...)
			}

			//
			// level := poly.Level()
			// r.PolyToBigintCenteredLvl(level, poly, outQP)
			outQP := make([]*big.Int, N)
			for i := range outQP {
				outQP[i] = big.NewInt(0)
			}

			// r.PolyToBigint(poly, outQP)
			// r.PolyToBigintCenteredLvl(level, poly, outQP)
			r.PolyToBigintDirectly(poly, outQP)
			bigqL := big.NewInt(int64(ringQ.Modulus[levelQ]))
			tmp := big.NewInt(0)
			modMul := big.NewInt(1)
			for _, modulus := range ringQ.Modulus {
				modMul.Mul(modMul, big.NewInt(int64(modulus)))
			}
			negModMul := big.NewInt(-1)
			negModMul.Mul(negModMul, modMul)

			halfMod := big.NewInt(0)
			halfMod.Rsh(bigqL, 1)
			// zero := big.NewInt(0)
			P := big.NewInt(1)
			for _, modulus := range ringP.Modulus {
				P = P.Mul(P, ring.NewUint(modulus))
			}

			// k := big.NewInt(0)
			for i := range outQP {

				tmpp := ring.NewUint(0)
				tmpp.Mod(outQP[i], bigqL)
				if tmpp.Cmp(halfMod) == 1 {
					outQP[i].Add(outQP[i], bigqL)
				}

				outQP[i].Div(outQP[i], bigqL)
				for pi := range poly.Coeffs {
					if pi <= levelP {
						tmp.Mod(outQP[i], big.NewInt(int64(ringP.Modulus[pi])))
					} else {
						tmp.Mod(outQP[i], big.NewInt(int64(ringQ.Modulus[pi-levelP-1])))
					}
					poly.Coeffs[pi][i] = tmp.Uint64()
					// if pi == level {
					// poly.Coeffs[pi][i] = 0
					// }
				}
			}

			for i := range out.P.Coeffs {
				for j := range out.P.Coeffs[i] {
					out.P.Coeffs[i][j] = poly.Coeffs[i][j]
				}
			}

			for i := range out.Q.Coeffs {
				for j := range out.Q.Coeffs[i] {
					out.Q.Coeffs[i][j] = poly.Coeffs[i+len(out.P.Coeffs)][j]
				}
			}

			// ringQ.ModupFromQLMinus1(out.Q, levelQ, keygen.params.N())
			ringQP.NTTLvl(levelQ, levelP, out, out)
			ringQP.MFormLvl(levelQ, levelP, out, out)
		}

		keygen.genrotKeyApplyFunc(sk.Value, keygen.params.InverseGaloisElement(galEl), rks.Keys[galEl], hook, postHook)
		if cts != nil {
			cti0, cti1 := keygen.GenCorrectionPartForRotationKey(sk.Value.Q, keygen.poolQP, vec)
			cts[galEl] = []PolyQP{cti0, cti1}
		} else {
		}

		// }
		//   else {
		// 	keygen.genrotKey(sk.Value, keygen.params.InverseGaloisElement(galEl), rks.Keys[galEl])
		// }
	}

	// for i := range rks.Keys {
	// 	fmt.Println(rks.Keys[i].Value[0][0].Q.Level(), " + ", rks.Keys[i].Value[0][0].P.Level())
	// }
	return rks
}

func (keygen *keyGenerator) GenSwitchingKeyForRowRotation(sk *SecretKey) (swk *SwitchingKey) {
	swk = NewSwitchingKey(keygen.params, keygen.params.QCount()-1, keygen.params.PCount()-1)
	keygen.genrotKey(sk.Value, keygen.params.GaloisElementForRowRotation(), swk)
	return
}

func (keygen *keyGenerator) GenSwitchingKeyForGalois(galoisEl uint64, sk *SecretKey) (swk *SwitchingKey) {
	swk = NewSwitchingKey(keygen.params, keygen.params.QCount()-1, keygen.params.PCount()-1)
	keygen.genrotKey(sk.Value, keygen.params.InverseGaloisElement(galoisEl), swk)
	return
}

// GenRotationKeysForInnerSum generates a RotationKeySet supporting the InnerSum operation of the Evaluator
func (keygen *keyGenerator) GenRotationKeysForInnerSum(sk *SecretKey) (rks *RotationKeySet) {
	return keygen.GenRotationKeys(keygen.params.GaloisElementsForRowInnerSum(), sk)
}

// generate roation key: sk -> rot(galEl, sk)
func (keygen *keyGenerator) genrotKey(sk PolyQP, galEl uint64, swk *SwitchingKey) {

	skIn := sk
	skOut := keygen.poolQP
	ringQ := keygen.params.RingQ()

	index := ringQ.PermuteNTTIndex(galEl)
	ringQ.PermuteNTTWithIndexLvl(keygen.params.QCount()-1, skIn.Q, index, skOut.Q)
	ringQ.PermuteNTTWithIndexLvl(keygen.params.PCount()-1, skIn.P, index, skOut.P)

	keygen.genSwitchingKey(skIn.Q, skOut, swk)
}

func (keygen *keyGenerator) genrotKeyApplyFunc(sk PolyQP, galEl uint64, swk *SwitchingKey, preHook func(PolyQP, PolyQP), postHook func(PolyQP, PolyQP)) {

	skIn := sk
	skOut := keygen.poolQP
	ringQ := keygen.params.RingQ()

	index := ringQ.PermuteNTTIndex(galEl)
	ringQ.PermuteNTTWithIndexLvl(keygen.params.QCount()-1, skIn.Q, index, skOut.Q)
	ringQ.PermuteNTTWithIndexLvl(keygen.params.PCount()-1, skIn.P, index, skOut.P)

	keygen.genSwitchingKeyApplyFunc(skIn.Q, skOut, swk, preHook, postHook)
}

// GenSwitchingKeysForRingSwap generates the necessary switching keys to switch from a standard ring to to a conjugate invariant ring and vice-versa.
func (keygen *keyGenerator) GenSwitchingKeysForRingSwap(skStd, skConjugateInvariant *SecretKey) (swkStdToConjugateInvariant, swkConjugateInvariantToStd *SwitchingKey) {

	skCIMappedToStandard := &SecretKey{Value: keygen.poolQP}
	keygen.params.RingQ().UnfoldConjugateInvariantToStandard(skConjugateInvariant.Value.Q.Level(), skConjugateInvariant.Value.Q, skCIMappedToStandard.Value.Q)
	keygen.params.RingQ().UnfoldConjugateInvariantToStandard(skConjugateInvariant.Value.P.Level(), skConjugateInvariant.Value.P, skCIMappedToStandard.Value.P)

	swkConjugateInvariantToStd = keygen.GenSwitchingKey(skCIMappedToStandard, skStd)
	swkStdToConjugateInvariant = keygen.GenSwitchingKey(skStd, skCIMappedToStandard)
	return
}

// GenSwitchingKey generates a new key-switching key, that will re-encrypt a Ciphertext encrypted under the input key into the output key.
// If the ringDegree(skOutput) > ringDegree(skInput),  generates [-a*SkOut + w*P*skIn_{Y^{N/n}} + e, a] in X^{N}.
// If the ringDegree(skOutput) < ringDegree(skInput),  generates [-a*skOut_{Y^{N/n}} + w*P*skIn + e_{N}, a_{N}] in X^{N}.
// Else generates [-a*skOut + w*P*skIn + e, a] in X^{N}.
// The output switching key is always given in max(N, n) and in the moduli of the output switching key.
// When key-switching a ciphertext from Y^{N/n} to X^{N}, the ciphertext must first be mapped to X^{N}
// using SwitchCiphertextRingDegreeNTT(ctSmallDim, nil, ctLargeDim).
// When key-switching a ciphertext from X^{N} to Y^{N/n}, the output of the key-switch is in still X^{N} and
// must be mapped Y^{N/n} using SwitchCiphertextRingDegreeNTT(ctLargeDim, ringQLargeDim, ctSmallDim).
func (keygen *keyGenerator) GenSwitchingKey(skInput, skOutput *SecretKey) (swk *SwitchingKey) {

	if keygen.params.PCount() == 0 {
		panic("Cannot GenSwitchingKey: modulus P is empty")
	}

	swk = NewSwitchingKey(keygen.params, skOutput.Value.Q.Level(), skOutput.Value.P.Level())

	if len(skInput.Value.Q.Coeffs[0]) > len(skOutput.Value.Q.Coeffs[0]) { // N -> n
		ring.MapSmallDimensionToLargerDimensionNTT(skOutput.Value.Q, keygen.poolQP.Q)
		ring.MapSmallDimensionToLargerDimensionNTT(skOutput.Value.P, keygen.poolQP.P)
		keygen.genSwitchingKey(skInput.Value.Q, keygen.poolQP, swk)
	} else { // N -> N or n -> N
		ring.MapSmallDimensionToLargerDimensionNTT(skInput.Value.Q, keygen.poolQ)

		if skInput.Value.Q.Level() < skOutput.Value.Q.Level() {

			ringQ := keygen.params.RingQ()

			ringQ.InvNTTLvl(0, keygen.poolQ, keygen.poolQP.Q)
			ringQ.InvMFormLvl(0, keygen.poolQP.Q, keygen.poolQP.Q)

			Q := ringQ.Modulus[0]
			QHalf := Q >> 1

			polQ := keygen.poolQP.Q
			polP := keygen.poolQ
			var sign uint64
			for j := 0; j < ringQ.N; j++ {

				coeff := polQ.Coeffs[0][j]

				sign = 1
				if coeff > QHalf {
					coeff = Q - coeff
					sign = 0
				}

				for i := skInput.Value.Q.Level() + 1; i < skOutput.Value.Q.Level()+1; i++ {
					polP.Coeffs[i][j] = (coeff * sign) | (ringQ.Modulus[i]-coeff)*(sign^1)
				}
			}

			for i := skInput.Value.Q.Level() + 1; i < skOutput.Value.Q.Level()+1; i++ {
				ringQ.NTTSingle(i, polP.Coeffs[i], polP.Coeffs[i])
				ring.MFormVec(polP.Coeffs[i], polP.Coeffs[i], ringQ.Modulus[i], ringQ.BredParams[i])
			}
		}

		keygen.genSwitchingKey(keygen.poolQ, skOutput.Value, swk)
	}

	return
}

// genSecretKeyFromSampler generates a new SecretKey sampled from the provided Sampler.
func (keygen *keyGenerator) genSecretKeyFromSampler(sampler ring.Sampler) *SecretKey {
	ringQP := keygen.params.RingQP()
	sk := new(SecretKey)
	sk.Value = ringQP.NewPoly()
	levelQ, levelP := keygen.params.QCount()-1, keygen.params.PCount()-1
	sampler.Read(sk.Value.Q)
	ringQP.ExtendBasisSmallNormAndCenter(sk.Value.Q, levelP, nil, sk.Value.P)
	ringQP.NTTLvl(levelQ, levelP, sk.Value, sk.Value)
	ringQP.MFormLvl(levelQ, levelP, sk.Value, sk.Value)
	return sk
}

func (keygen *keyGenerator) genSwitchingKey(skIn *ring.Poly, skOut PolyQP, swk *SwitchingKey) {

	ringQ := keygen.params.RingQ()
	ringQP := keygen.params.RingQP()

	levelQ := len(swk.Value[0][0].Q.Coeffs) - 1
	levelP := len(swk.Value[0][0].P.Coeffs) - 1

	var pBigInt *big.Int
	if levelP == keygen.params.PCount()-1 {
		pBigInt = keygen.params.RingP().ModulusBigint
	} else {
		P := keygen.params.RingP().Modulus
		pBigInt = new(big.Int).SetUint64(P[0])
		for i := 1; i < levelP+1; i++ {
			pBigInt.Mul(pBigInt, ring.NewUint(P[i]))
		}
	}

	// Computes P * skIn
	ringQ.MulScalarBigintLvl(levelQ, skIn, pBigInt, keygen.poolQ)

	alpha := levelP + 1
	beta := int(math.Ceil(float64(levelQ+1) / float64(levelP+1)))

	var index int
	for i := 0; i < beta; i++ {

		// e
		keygen.gaussianSamplerQ.ReadLvl(levelQ, swk.Value[i][0].Q)
		ringQP.ExtendBasisSmallNormAndCenter(swk.Value[i][0].Q, levelP, nil, swk.Value[i][0].P)
		ringQP.NTTLazyLvl(levelQ, levelP, swk.Value[i][0], swk.Value[i][0])
		ringQP.MFormLvl(levelQ, levelP, swk.Value[i][0], swk.Value[i][0])

		// a (since a is uniform, we consider we already sample it in the NTT and Montgomery domain)
		keygen.uniformSamplerQ.ReadLvl(levelQ, swk.Value[i][1].Q)
		keygen.uniformSamplerP.ReadLvl(levelP, swk.Value[i][1].P)

		// e + (skIn * P) * (q_star * q_tild) mod QP
		//
		// q_prod = prod(q[i*alpha+j])
		// q_star = Q/qprod
		// q_tild = q_star^-1 mod q_prod
		//
		// Therefore : (skIn * P) * (q_star * q_tild) = sk*P mod q[i*alpha+j], else 0
		for j := 0; j < alpha; j++ {

			index = i*alpha + j

			// It handles the case where nb pj does not divide nb qi
			if index >= levelQ+1 {
				break
			}

			qi := ringQ.Modulus[index]
			p0tmp := keygen.poolQ.Coeffs[index]
			p1tmp := swk.Value[i][0].Q.Coeffs[index]

			for w := 0; w < ringQ.N; w++ {
				p1tmp[w] = ring.CRed(p1tmp[w]+p0tmp[w], qi)
			}
		}

		// (skIn * P) * (q_star * q_tild) - a * skOut + e mod QP
		ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, swk.Value[i][1], skOut, swk.Value[i][0])
	}
}

func (keygen *keyGenerator) genSwitchingKeyApplyFunc(skIn *ring.Poly, skOut PolyQP, swk *SwitchingKey, preHook func(PolyQP, PolyQP), postHook func(PolyQP, PolyQP)) {

	ringQ := keygen.params.RingQ()
	ringQP := keygen.params.RingQP()

	levelQ := len(swk.Value[0][0].Q.Coeffs) - 1
	levelP := len(swk.Value[0][0].P.Coeffs) - 1

	var pBigInt *big.Int
	if levelP == keygen.params.PCount()-1 {
		pBigInt = keygen.params.RingP().ModulusBigint
	} else {
		P := keygen.params.RingP().Modulus
		pBigInt = new(big.Int).SetUint64(P[0])
		for i := 1; i < levelP+1; i++ {
			pBigInt.Mul(pBigInt, ring.NewUint(P[i]))
		}
	}

	// Computes P * skIn * M_i
	// preHook(keygen.poolQ, keygen.poolQ)
	ringQ.MulScalarBigintLvl(levelQ, skIn, pBigInt, keygen.poolQ)
	poolQP := ringQP.NewPoly()
	poolQP.Q.Copy(keygen.poolQ)
	preHook(poolQP, poolQP)
	keygen.poolQ.Copy(poolQP.Q)

	alpha := levelP + 1
	beta := int(math.Ceil(float64(levelQ+1) / float64(levelP+1)))

	var index int
	for i := 0; i < beta; i++ {

		// e
		keygen.gaussianSamplerQ.ReadLvl(levelQ, swk.Value[i][0].Q)
		for j := range swk.Value[i][0].Q.Coeffs {
			for k := range swk.Value[i][0].Q.Coeffs[j] {
				swk.Value[i][0].Q.Coeffs[j][k] = 0
			}
		}
		ringQP.ExtendBasisSmallNormAndCenter(swk.Value[i][0].Q, levelP, nil, swk.Value[i][0].P)
		ringQP.NTTLazyLvl(levelQ, levelP, swk.Value[i][0], swk.Value[i][0])
		ringQP.MFormLvl(levelQ, levelP, swk.Value[i][0], swk.Value[i][0])

		// a (since a is uniform, we consider we already sample it in the NTT and Montgomery domain)
		keygen.uniformSamplerQ.ReadLvl(levelQ, swk.Value[i][1].Q)
		keygen.uniformSamplerP.ReadLvl(levelP, swk.Value[i][1].P)
		// for _, vec := range swk.Value[i][1].Q.Coeffs {
		// 	for i := range vec {
		// 		vec[i] = 0
		// 	}
		// }
		// for _, vec := range swk.Value[i][1].P.Coeffs {
		// 	for i := range vec {
		// 		vec[i] = 0
		// 	}
		// }

		// e + (skIn * P) * (q_star * q_tild) mod QP
		//
		// q_prod = prod(q[i*alpha+j])
		// q_star = Q/qprod
		// q_tild = q_star^-1 mod q_prod
		//
		// Therefore : (skIn * P) * (q_star * q_tild) = sk*P mod q[i*alpha+j], else 0
		for j := 0; j < alpha; j++ {

			index = i*alpha + j

			// It handles the case where nb pj does not divide nb qi
			if index >= levelQ+1 {
				break
			}

			qi := ringQ.Modulus[index]
			p0tmp := keygen.poolQ.Coeffs[index]
			p1tmp := swk.Value[i][0].Q.Coeffs[index]

			for w := 0; w < ringQ.N; w++ {
				p1tmp[w] = ring.CRed(p1tmp[w]+p0tmp[w], qi)
			}
		}

		// (skIn * P) * (q_star * q_tild) - a * skOut + e mod QP
		// postHook(swk.Value[i][0], swk.Value[i][0])
		// ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, swk.Value[i][1], skOut, swk.Value[i][0])

		// f(swk.Value[i][1], swk.Value[i][1])
		// f(swk.Value[i][0], swk.Value[i][0])
	}
	for i := 0; i < beta; i++ {
		for pi := range swk.Value[i][0].P.Coeffs {
			for w := 0; w < ringQ.N; w++ {
				// fmt.Println(swk.Value[i][0].P.Coeffs[pi][w], "-->", poolQP.P.Coeffs[pi][w])
				swk.Value[i][0].P.Coeffs[pi][w] += poolQP.P.Coeffs[pi][w] // if consider err, should be added to
			}

		}
		postHook(swk.Value[i][0], swk.Value[i][0])
		ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, swk.Value[i][1], skOut, swk.Value[i][0])
	}
}

func (keygen *keyGenerator) GenCorrectionPartForRotationKey(
	skIn *ring.Poly, skOut PolyQP,
	matrix PolyQP,
	// pool *ring.Poly
) (ct0 PolyQP, ct1 PolyQP) {
	ringQ := keygen.params.RingQ()
	ringP := keygen.params.RingP()
	ringQP := keygen.params.RingQP()
	ct1 = ringQP.NewPoly()
	ct0 = ringQP.NewPoly()

	levelQ := len(ringQ.Modulus) - 1
	levelP := len(ringP.Modulus) - 1

	var pBigInt *big.Int

	P := keygen.params.RingP().Modulus
	pBigInt = new(big.Int).SetUint64(P[0])
	for i := 1; i < levelP+1; i++ { // to P_{k-1}
		pBigInt.Mul(pBigInt, ring.NewUint(P[i]))
	}

	// P_{k-1} * S
	// ringQ.MulScalarBigintLvl(levelQ, skIn, pBigInt, keygen.poolQ)

	// S * M
	ringQ.MulCoeffsMontgomeryLvl(levelQ, skIn, matrix.Q, keygen.poolQ)
	ringQ.InvMFormLvl(levelQ, keygen.poolQ, keygen.poolQ)
	ringQ.InvNTTLvl(levelQ, keygen.poolQ, keygen.poolQ)

	bigMPSQ := make([]*big.Int, keygen.params.N())
	for i := range bigMPSQ {
		bigMPSQ[i] = big.NewInt(0)
	}
	ringQ.PolyToBigintCenteredLvl(levelQ, keygen.poolQ, bigMPSQ)
	poolQP := ringQP.NewPoly()

	tmp := big.NewInt(0)
	Q := big.NewInt(1)
	for _, q := range ringQ.Modulus {
		Q.Mul(Q, ring.NewUint(q))
	}

	bigqL := ring.NewUint(ringQ.Modulus[levelQ])
	halfqL := big.NewInt(0)
	halfqL.Rsh(bigqL, 1)

	// delta := math.Log2(float64(ringP.Modulus[levelP])) - math.Log2(float64(ringQ.Modulus[levelQ]))
	for i := range bigMPSQ {
		// P_{k-1} * S * M

		// bigMPSQ[i].Mul(bigMPSQ[i], big.NewInt(72057594037538816))

		bigMPSQ[i].Mul(bigMPSQ[i], pBigInt)
		// bigMPSQ[i].Mul(bigMPSQ[i], big.NewInt(32))
		// bigMPSQ[i].Mul(bigMPSQ[i], ring.NewUint(1<<uint64(math.Round(delta))))

		// P_{k-1} * S * M * Q_L
		// bigMPSQ[i].Mul(bigMPSQ[i], Q)

		// Div q_l
		// bigMPSQ[i].Div(bigMPSQ[i], ring.NewUint(ringP.Modulus[levelP]))
		// bigMPSQ[i].Div(bigMPSQ[i], ring.NewUint(0x1000000002a0001-3141632))

		tmp.Mod(bigMPSQ[i], bigqL)
		if tmp.Cmp(halfqL) >= 0 {
			tmp.Sub(tmp, bigqL)
		}
		bigMPSQ[i].Sub(bigMPSQ[i], tmp)
		bigMPSQ[i].Div(bigMPSQ[i], bigqL)

		for qi := range poolQP.Q.Coeffs {
			tmp.Mod(bigMPSQ[i], ring.NewUint(ringQ.Modulus[qi]))
			poolQP.Q.Coeffs[qi][i] = tmp.Uint64()
		}
		for pi := range keygen.poolQP.P.Coeffs {
			// the former k-1 terms should be zeros
			tmp.Mod(bigMPSQ[i], ring.NewUint(ringP.Modulus[pi]))
			poolQP.P.Coeffs[pi][i] = tmp.Uint64()
		}
	}

	ringQP.NTTLvl(levelQ, levelP, poolQP, poolQP)
	ringQP.MFormLvl(levelQ, levelP, poolQP, poolQP)

	// e
	keygen.gaussianSamplerQ.ReadLvl(levelQ, ct0.Q)
	ringQP.ExtendBasisSmallNormAndCenter(ct0.Q, levelP, nil, ct0.P)
	ringQP.NTTLazyLvl(levelQ, levelP, ct0, ct0)
	ringQP.MFormLvl(levelQ, levelP, ct0, ct0)

	// e + M * P_{K-1} * Q_L
	for qi, vec := range ct0.Q.Coeffs {
		for i := range vec {
			vec[i] += poolQP.Q.Coeffs[qi][i]
		}
	}
	for pi, vec := range ct0.P.Coeffs {
		for i := range vec {
			vec[i] += poolQP.P.Coeffs[pi][i]
		}
	}

	// a (since a is uniform, we consider we already sample it in the NTT and Montgomery domain)
	keygen.uniformSamplerQ.ReadLvl(levelQ, ct1.Q)
	keygen.uniformSamplerP.ReadLvl(levelP, ct1.P)
	// for _, vec := range ct1.Q.Coeffs {
	// 	for i := range vec {
	// 		vec[i] = 0
	// 	}
	// }
	// for _, vec := range ct1.P.Coeffs {
	// 	for i := range vec {
	// 		vec[i] = 0
	// 	}
	// }

	ringQP.MulCoeffsMontgomeryAndSubLvl(levelQ, levelP, ct1, skOut, ct0)
	return
}
