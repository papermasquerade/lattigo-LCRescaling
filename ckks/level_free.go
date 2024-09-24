package ckks

import (
	"fmt"
	"log"
	"runtime"
	"time"

	"github.com/ldsec/lattigo/v2/ring"
	"github.com/ldsec/lattigo/v2/rlwe"
	"github.com/ldsec/lattigo/v2/utils"
)

func (eval *evaluator) MultiplyByDiagMatrixBSGS_modify(ctIn *Ciphertext, matrix LinearTransform, PoolDecompQP []rlwe.PolyQP, ctOut *Ciphertext) {

	log.Println("Modify BSGS")
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

	ring.CopyValuesLvl(levelQ, ctIn.Value[0], eval.ctxpool.Value[0])
	ring.CopyValuesLvl(levelQ, ctIn.Value[1], eval.ctxpool.Value[1])
	ctInTmp0, ctInTmp1 := eval.ctxpool.Value[0], eval.ctxpool.Value[1]

	// Pre-rotates ciphertext for the baby-step giant-step algorithm, does not divide by P yet
	ctInRotQP := eval.RotateHoistedNoModDownNew(levelQ, rotN2, ctInTmp0, eval.PoolDecompQP)

	// Accumulator inner loop
	tmp0QP := eval.Pool[1]
	tmp1QP := eval.Pool[2]

	// Accumulator outer loop
	// c0QP := eval.Pool[3]
	// c1QP := eval.Pool[4]

	// Result in QP
	c0OutQP := rlwe.PolyQP{Q: ctOut.Value[0], P: eval.Pool[5].Q}
	c1OutQP := rlwe.PolyQP{Q: ctOut.Value[1], P: eval.Pool[5].P}

	ringQ.MulScalarBigintLvl(levelQ, ctInTmp0, ringP.ModulusBigint, ctInTmp0) // P*c0
	ringQ.MulScalarBigintLvl(levelQ, ctInTmp1, ringP.ModulusBigint, ctInTmp1) // P*c1

	// OUTER LOOP
	var cnt0 int
	var countN1N2 int
	j := 0
	// for j := range index {
	log.Println("j", j)
	// INNER LOOP
	var cnt1 int
	for _, i := range index[j] {
		countN1N2++
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
	// if j != 0 {

	// // Hoisting of the ModDown of sum(sum(phi(d1) * plaintext))
	// time_inner_MD_tmp, iNTT_tmp, redu_tmp, NTT_tmp := eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, tmp1QP.Q, tmp1QP.P, tmp1QP.Q) // c1 * plaintext + sum(phi(d1) * plaintext) + phi(c1) * plaintext mod Q
	// time_inner_c1_modDown += time_inner_MD_tmp
	// time_inner_c1_modDown_iNTT += iNTT_tmp
	// time_inner_c1_modDown_redu += redu_tmp
	// time_inner_c1_modDown_NTT += NTT_tmp

	// galEl := eval.params.GaloisElementForColumnRotationBy(j)

	// rtk, generated := eval.rtks.Keys[galEl]
	// if !generated {
	// 	panic("switching key not available")
	// }

	// rotIndex := eval.permuteNTTIndex[galEl]

	// tmp1QP.Q.IsNTT = true
	// time_each_iNTT, time_each_modUp, time_each_NTT, time_each_decomp, time_eachInnerProd := eval.SwitchKeysInPlaceNoModDown(levelQ, tmp1QP.Q, rtk, c0QP.Q, c0QP.P, c1QP.Q, c1QP.P) // Switchkey(P*phi(tmpRes_1)) = (d0, d1) in base QP
	// time_n2_decomp_iNTT += time_each_iNTT
	// time_n2_decomp_modUp += time_each_modUp
	// time_n2_decomp_NTT += time_each_NTT
	// time_n2_decomp += time_each_decomp
	// time_n2_InnerProduct += time_eachInnerProd
	// t = time.Now()
	// ringQP.AddLvl(levelQ, levelP, c0QP, tmp0QP, c0QP)

	// // Outer loop rotations
	// if cnt0 == 0 {
	// 	ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, c0QP, rotIndex, c0OutQP)
	// 	ringQP.PermuteNTTWithIndexLvl(levelQ, levelP, c1QP, rotIndex, c1OutQP)
	// } else {
	// 	ringQP.PermuteNTTWithIndexAndAddNoModLvl(levelQ, levelP, c0QP, rotIndex, c0OutQP)
	// 	ringQP.PermuteNTTWithIndexAndAddNoModLvl(levelQ, levelP, c1QP, rotIndex, c1OutQP)
	// }
	// time_n2_permuteAndSum += time.Since(t)

	// Else directly adds on ((c0QP.Q, c0QP.P), (c1QP.Q, c1QP.P))
	// } else {
	if cnt0 == 0 {
		ringQP.CopyValuesLvl(levelQ, levelP, tmp0QP, c0OutQP)
		ringQP.CopyValuesLvl(levelQ, levelP, tmp1QP, c1OutQP)
	} else {
		ringQP.AddNoModLvl(levelQ, levelP, c0OutQP, tmp0QP, c0OutQP)
		ringQP.AddNoModLvl(levelQ, levelP, c1OutQP, tmp1QP, c1OutQP)
	}
	// }

	if cnt0%QiOverF == QiOverF-1 {
		ringQ.ReduceLvl(levelQ, ctOut.Value[0], ctOut.Value[0])
		ringQ.ReduceLvl(levelQ, ctOut.Value[1], ctOut.Value[1])
	}

	if cnt0%PiOverF == PiOverF-1 {
		ringP.ReduceLvl(levelP, c0OutQP.P, c0OutQP.P)
		ringP.ReduceLvl(levelP, c1OutQP.P, c1OutQP.P)
	}

	// cnt0++
	// }

	// if cnt0%QiOverF != 0 {
	// 	ringQ.ReduceLvl(levelQ, ctOut.Value[0], ctOut.Value[0])
	// 	ringQ.ReduceLvl(levelQ, ctOut.Value[1], ctOut.Value[1])
	// }

	// if cnt0%PiOverF != 0 {
	// 	ringP.ReduceLvl(levelP, c0OutQP.P, c0OutQP.P)
	// 	ringP.ReduceLvl(levelP, c1OutQP.P, c1OutQP.P)
	// }

	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, ctOut.Value[0], c0OutQP.P, ctOut.Value[0]) // sum(phi(c0 * P + d0_QP))/P
	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, ctOut.Value[1], c1OutQP.P, ctOut.Value[1]) // sum(phi(d1_QP))/P

	ctOut.Scale = matrix.Scale * ctIn.Scale

	ctInRotQP = nil
	runtime.GC()

}

func (eval *evaluator) MultiplyByDiagMatrix_modify(ctIn *Ciphertext, matrix LinearTransform, PoolDecompQP []rlwe.PolyQP, ctOut *Ciphertext) {

	log.Println("no_BSGS_modify")
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

	ring.CopyValuesLvl(levelQ, ctIn.Value[0], eval.ctxpool.Value[0])   // c0
	ring.CopyValuesLvl(levelQ, ctIn.Value[1], eval.ctxpool.Value[1])   //c1
	ctInTmp0, ctInTmp1 := eval.ctxpool.Value[0], eval.ctxpool.Value[1] //c0,c1

	t := time.Now()
	ringQ.MulScalarBigintLvl(levelQ, ctInTmp0, ringP.ModulusBigint, ct0TimesP) // P*c0 in Q, since [P*c0]_pk = 0
	time_Pmultc0 := time.Since(t)

	var state bool
	var cnt int
	var time_IP time.Duration
	var tim_multplaintext time.Duration
	var time_ModDown time.Duration
	log.Println("ringQ.NthRoot ", ringQ.NthRoot)
	for k := range matrix.Vec {

		k &= int((ringQ.NthRoot >> 2) - 1) // k&(2^15-1)

		if k == 0 {
			state = true
		} else {
			// plaintext * c0
			// ringQ.MulCoeffsMontgomeryAndAddLvl(levelQ, matrix.Vec[k].Q, ctInTmp0, c0OutQP.Q) // ctOut += c0_Q * plaintext

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

			t = time.Now()
			if cnt == 0 {
				// keyswitch(c1_Q) = (d0_QP, d1_QP)
				ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, matrix.Vec[k], tmp0QP, c0OutQP)
				ringQP.MulCoeffsMontgomeryLvl(levelQ, levelP, matrix.Vec[k], tmp1QP, c1OutQP)
			} else {
				// keyswitch(c1_Q) = (d0_QP, d1_QP)
				ringQP.MulCoeffsMontgomeryAndAddLvl(levelQ, levelP, matrix.Vec[k], tmp0QP, c0OutQP)
				ringQP.MulCoeffsMontgomeryAndAddLvl(levelQ, levelP, matrix.Vec[k], tmp1QP, c1OutQP)
			}
			tim_multplaintext += time.Since(t)

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

	t = time.Now()
	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c0OutQP.Q, c0OutQP.P, c0OutQP.Q) // sum(phi(c0 * P + d0_QP))/P
	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, c1OutQP.Q, c1OutQP.P, c1OutQP.Q) // sum(phi(d1_QP))/P
	time_ModDown += time.Since(t)

	t = time.Now()
	if state { // Rotation by zero
		ringQ.MulCoeffsMontgomeryAndAddLvl(levelQ, matrix.Vec[0].Q, ctInTmp0, c0OutQP.Q) // ctOut += c0_Q * plaintext
		ringQ.MulCoeffsMontgomeryAndAddLvl(levelQ, matrix.Vec[0].Q, ctInTmp1, c1OutQP.Q) // ctOut += c1_Q * plaintext
	}
	tim_multplaintext += time.Since(t)

	log.Println("n inner productions : ", time_IP+time_Pmultc0, " =", time_IP, "(IP) +", time_Pmultc0, "(Mul P)")
	log.Println("Mulplaintext : ", tim_multplaintext)
	log.Println("Out ModDown : ", time_ModDown)
	time_no_bsgs := time_IP + time_Pmultc0 + tim_multplaintext + time_ModDown
	log.Println("non-zero: ", len(matrix.Vec), "no-BSGStime=", time_no_bsgs)

	ctOut.Scale = matrix.Scale * ctIn.Scale
}

func (eval *evaluator) MultiplyByDiagMatrixDoublehoisting(ctIn *Ciphertext, matrix LinearTransform, PoolDecompQP []rlwe.PolyQP, ctOut *Ciphertext) {

	log.Println("double-hoisting no-bsgs")
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

	ring.CopyValuesLvl(levelQ, ctIn.Value[0], eval.ctxpool.Value[0])
	ring.CopyValuesLvl(levelQ, ctIn.Value[1], eval.ctxpool.Value[1])
	ctInTmp0, ctInTmp1 := eval.ctxpool.Value[0], eval.ctxpool.Value[1]
	ct0Q := ctInTmp0.CopyNew()

	// Pre-rotates ciphertext for the baby-step giant-step algorithm, does not divide by P yet
	var t time.Time
	ctInRotQP, ctIn0Rot, time_inner_productions, time_permuted0d1Andc0 := eval.RotateHoistedNoModDownNew_noAddPc0(levelQ, rotN2, ct0Q, eval.PoolDecompQP)

	// Accumulator inner loop
	tmp0QP := eval.Pool[1]
	tmp1QP := eval.Pool[2]

	// Accumulator outer loop
	// c0QP := eval.Pool[3]
	// c1QP := eval.Pool[4]

	// Result in QP
	c0OutQP := rlwe.PolyQP{Q: ctOut.Value[0], P: eval.Pool[5].Q}
	c1OutQP := rlwe.PolyQP{Q: ctOut.Value[1], P: eval.Pool[5].P}

	// OUTER LOOP
	var state bool
	var time_MulPT time.Duration
	var time_outer_ModDown time.Duration
	j := 0

	// INNER LOOP
	var cnt1 int
	for _, i := range index[j] {
		t := time.Now()
		if i == 0 {
			// no decomposition
			state = true
		} else {
			if cnt1 == 0 {
				ringQ.MulCoeffsMontgomeryConstantLvl(levelQ, matrix.Vec[j+i].Q, ctIn0Rot[i], ct0Q)
				ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, matrix.Vec[j+i], ctInRotQP[i][0], tmp0QP)
				ringQP.MulCoeffsMontgomeryConstantLvl(levelQ, levelP, matrix.Vec[j+i], ctInRotQP[i][1], tmp1QP)
			} else {
				ringQ.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, matrix.Vec[j+i].Q, ctIn0Rot[i], ct0Q)
				ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, matrix.Vec[j+i], ctInRotQP[i][0], tmp0QP)
				ringQP.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, levelP, matrix.Vec[j+i], ctInRotQP[i][1], tmp1QP)
			}
		}
		time_MulPT += time.Since(t)

		if cnt1%QiOverF == QiOverF-1 {
			ringQ.ReduceLvl(levelQ, tmp0QP.Q, tmp0QP.Q)
			ringQ.ReduceLvl(levelQ, tmp1QP.Q, tmp1QP.Q)
			ringQ.ReduceLvl(levelQ, ct0Q, ct0Q)
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
		ringQ.ReduceLvl(levelQ, ct0Q, ct0Q)
	}

	if cnt1%PiOverF != 0 {
		ringP.ReduceLvl(levelP, tmp0QP.P, tmp0QP.P)
		ringP.ReduceLvl(levelP, tmp1QP.P, tmp1QP.P)
	}

	ringQP.CopyValuesLvl(levelQ, levelP, tmp0QP, c0OutQP)
	ringQP.CopyValuesLvl(levelQ, levelP, tmp1QP, c1OutQP)

	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, ctOut.Value[0], c0OutQP.P, ctOut.Value[0]) // sum(phi(c0 * P + d0_QP))/P
	eval.Baseconverter.ModDownQPtoQNTT(levelQ, levelP, ctOut.Value[1], c1OutQP.P, ctOut.Value[1]) // sum(phi(d1_QP))/P

	ringQ.AddLvl(levelQ, ct0Q, ctOut.Value[0], ctOut.Value[0])

	t = time.Now()
	if state {
		ringQ.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, matrix.Vec[0].Q, ctInTmp0, ctOut.Value[0])
		ringQ.MulCoeffsMontgomeryConstantAndAddNoModLvl(levelQ, matrix.Vec[0].Q, ctInTmp1, ctOut.Value[1])
	}
	time_MulPT += time.Since(t)

	log.Println("n1 inner productions : ", time_inner_productions, " =", time_inner_productions, "(IP)")
	log.Println("n1 permute : ", time_permuted0d1Andc0)
	log.Println("Mulplaintext : ", time_MulPT)
	log.Println("Out ModDown : ", time_outer_ModDown)
	var doubleHoistingtime time.Duration
	doubleHoistingtime += time_inner_productions + time_MulPT + time_outer_ModDown
	log.Println("non-zero: ", cnt1, ", n1=", float32(cnt1)/float32(len(index)), ", n2=", len(index), ", DoubleHoistingtime=", doubleHoistingtime)

	ctOut.Scale = matrix.Scale * ctIn.Scale

	ctInRotQP = nil
	ctIn0Rot = nil
	runtime.GC()

}

func (eval *evaluator) RotateHoistedNoModDownNew_noAddPc0(level int, rotations []int, c0 *ring.Poly, c2DecompQP []rlwe.PolyQP) (cOut map[int][2]rlwe.PolyQP, c0out map[int]*ring.Poly, time_inner_productions, time_Permute time.Duration) {
	ringQ := eval.params.RingQ()
	ringP := eval.params.RingP()
	cOut = make(map[int][2]rlwe.PolyQP)
	c0out = make(map[int]*ring.Poly)
	for _, i := range rotations {

		if i != 0 {
			c0out[i] = c0.CopyNew() //initiate pointer
			cOut[i] = [2]rlwe.PolyQP{{Q: ringQ.NewPolyLvl(level), P: ringP.NewPoly()}, {Q: ringQ.NewPolyLvl(level), P: ringP.NewPoly()}}
			each_time_IP, each_time_Permute := eval.PermuteNTTHoistedNoModDown_noAddPc0(level, c0, c2DecompQP, i, cOut[i][0].Q, cOut[i][1].Q, cOut[i][0].P, cOut[i][1].P, c0out[i])
			time_inner_productions += each_time_IP
			time_Permute += each_time_Permute
		}
	}

	return
}

func (eval *evaluator) PermuteNTTHoistedNoModDown_noAddPc0(level int, c0 *ring.Poly, c2DecompQP []rlwe.PolyQP, k int, ct0OutQ, ct1OutQ, ct0OutP, ct1OutP, c0out *ring.Poly) (InnerProdTime, permutec0c1Time time.Duration) {

	pool2Q := eval.Pool[0].Q
	pool3Q := eval.Pool[1].Q

	pool2P := eval.Pool[0].P
	pool3P := eval.Pool[1].P

	levelQ := level
	levelP := eval.params.PCount() - 1

	galEl := eval.params.GaloisElementForColumnRotationBy(k)

	rtk, generated := eval.rtks.Keys[galEl]
	if !generated {
		fmt.Println(k)
		panic("switching key not available")
	}
	index := eval.permuteNTTIndex[galEl]

	eval.KeyswitchHoistedNoModDown(levelQ, c2DecompQP, rtk, pool2Q, pool3Q, pool2P, pool3P)

	ringQ := eval.params.RingQ()

	t := time.Now()
	ringQ.PermuteNTTWithIndexLvl(levelQ, pool3Q, index, ct1OutQ)
	ringQ.PermuteNTTWithIndexLvl(levelP, pool3P, index, ct1OutP)
	// permutec0c1Time += time.Since(t)

	// t = time.Now()
	// ringQ.MulScalarBigintLvl(levelQ, c0, eval.params.RingP().ModulusBigint, pool3Q)
	// time_Pc0 = time.Since(t)

	// t = time.Now()
	// ringQ.AddLvl(levelQ, pool2Q, pool3Q, pool2Q)
	ringQ.PermuteNTTWithIndexLvl(levelQ, c0, index, c0out)
	ringQ.PermuteNTTWithIndexLvl(levelQ, pool2Q, index, ct0OutQ)
	ringQ.PermuteNTTWithIndexLvl(levelP, pool2P, index, ct0OutP)
	permutec0c1Time += time.Since(t)
	return
}
