module ccv_packets {
    import common.* from "./common"
    // contains validator updates
    type VSCPacketData =
    {
        // id of the vsc packet
        id: int,
        // validator updates
        updates: List[ValidatorUpdate],
        // downtime slash requests acknowledgements, 
        // i.e., list of validator addresses
        downtimeSlashAcks: List[string],
    }

    // contains a request to slash a validator
    type SlashPacketData = 
    {
        validator: Validator,
        validatorPower: int,
        // the id of the vsc packet that the consumer last applied
        vscId: int,
        // if it is not downtime, it is equivocation
        isDowntime: bool
    }

    type VSCMaturedPacketData = 
    {
        // the id of the VSC that reached maturity
        id: int
    }
}
