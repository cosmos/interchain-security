package types

func NewCCValidator(address []byte, power int64) CrossChainValidator {
	return CrossChainValidator{
		Address: address,
		Power:   power,
	}
}
