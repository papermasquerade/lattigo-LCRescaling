package drlwe

import (
	"github.com/ldsec/lattigo/v2/utils"
)

// CRS is an interface for Common Reference Strings.
// CRSs are PRNGs for which the read bits are the same for
// all parties.
type CRS interface {
	utils.PRNG
}
