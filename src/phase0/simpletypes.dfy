include "ssz.dfy"

module SimpleTypes {
    import opened SSZ

    type Slot = uint64
    function method Slot_new(x: uint64): Slot { x }
    const Slot_default := Slot_new(0);
    type Epoch = uint64
    function method Epoch_new(x: uint64): Epoch { x }
    const Epoch_default := Epoch_new(0);
    type CommitteeIndex = uint64
    function method CommitteeIndex_new(x: uint64): CommitteeIndex { x }
    const CommitteeIndex_default := CommitteeIndex_new(0);
    type ValidatorIndex = uint64
    function method ValidatorIndex_new(x: uint64): ValidatorIndex { x }
    const ValidatorIndex_default := ValidatorIndex_new(0);
    type Gwei = uint64
    function method Gwei_new(x: uint64): Gwei { x }
    const Gwei_default := Gwei_new(0);
    type Root = Bytes32
    function method Root_new(x: Bytes32): Root { x }
    const Root_default := Root_new(0);
    type Hash32 = Bytes32
    function method Hash32_new(x: Bytes32): Hash32 { x }
    const Hash32_default := Hash32_new(0);
    type Version = Bytes4
    function method Version_new(x: Bytes4): Version { x }
    const Version_default := Version_new(0);
    type DomainType = Bytes4
    function method DomainType_new(x: Bytes4): DomainType { x }
    const DomainType_default := DomainType_new(0);
    type ForkDigest = Bytes4
    function method ForkDigest_new(x: Bytes4): ForkDigest { x }
    const ForkDigest_default := ForkDigest_new(0);
    type Domain = Bytes32
    function method Domain_new(x: Bytes32): Domain { x }
    const Domain_default := Domain_new(0);
    type BLSPubkey = Bytes48
    function method BLSPubkey_new(x: Bytes48): BLSPubkey { x }
    const BLSPubkey_default := BLSPubkey_new(0);
    type BLSSignature = Bytes96
    function method BLSSignature_new(x: Bytes96): BLSSignature { x }
    const BLSSignature_default := BLSSignature_new(0);
    type Ether = uint64
    function method Ether_new(x: uint64): Ether { x }
    const Ether_default := Ether_new(0);
}