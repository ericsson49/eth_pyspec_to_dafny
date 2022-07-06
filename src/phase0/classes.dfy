include "ssz.dfy"
include "simpletypes.dfy"

module Classes {
    import opened SSZ
    import opened SimpleTypes

    class Fork {
    constructor() {
        previous_version := Version_default;
        current_version := Version_default;
        epoch := Epoch_default;
    }
    var previous_version: Version;
    var current_version: Version;
    var epoch: Epoch;
    }
    class ForkData {
    constructor() {
        current_version := Version_default;
        genesis_validators_root := Root_default;
    }
    var current_version: Version;
    var genesis_validators_root: Root;
    }
    datatype Checkpoint = Checkpoint(epoch: Epoch, root: Root)
    function method Checkpoint_new(): Checkpoint { Checkpoint(Epoch_default, Root_default) }
    class Validator {
    constructor() {
        pubkey := BLSPubkey_default;
        withdrawal_credentials := Bytes32_default;
        effective_balance := Gwei_default;
        slashed := boolean_default;
        activation_eligibility_epoch := Epoch_default;
        activation_epoch := Epoch_default;
        exit_epoch := Epoch_default;
        withdrawable_epoch := Epoch_default;
    }
    var pubkey: BLSPubkey;
    var withdrawal_credentials: Bytes32;
    var effective_balance: Gwei;
    var slashed: boolean;
    var activation_eligibility_epoch: Epoch;
    var activation_epoch: Epoch;
    var exit_epoch: Epoch;
    var withdrawable_epoch: Epoch;
    }
    class AttestationData {
    constructor() {
        slot := Slot_default;
        index := CommitteeIndex_default;
        beacon_block_root := Root_default;
        source := Checkpoint_new();
        target := Checkpoint_new();
    }
    var slot: Slot;
    var index: CommitteeIndex;
    var beacon_block_root: Root;
    var source: Checkpoint;
    var target: Checkpoint;
    }
    class IndexedAttestation {
    constructor() {
        attesting_indices := List_new<ValidatorIndex>([]);
        data := new AttestationData();
        signature := BLSSignature_default;
    }
    var attesting_indices: ssz_List<ValidatorIndex>;
    var data: AttestationData;
    var signature: BLSSignature;
    }
    class PendingAttestation {
    constructor() {
        aggregation_bits := Bitlist_new([]);
        data := new AttestationData();
        inclusion_delay := Slot_default;
        proposer_index := ValidatorIndex_default;
    }
    var aggregation_bits: Bitlist;
    var data: AttestationData;
    var inclusion_delay: Slot;
    var proposer_index: ValidatorIndex;
    }
    class Eth1Data {
    constructor() {
        deposit_root := Root_default;
        deposit_count := 0;
        block_hash := Hash32_default;
    }
    var deposit_root: Root;
    var deposit_count: uint64;
    var block_hash: Hash32;
    }
    class HistoricalBatch {
    constructor() {
        block_roots := Vector_new<Root>();
        state_roots := Vector_new<Root>();
    }
    var block_roots: ssz_Vector<Root>;
    var state_roots: ssz_Vector<Root>;
    }
    class DepositMessage {
    constructor() {
        pubkey := BLSPubkey_default;
        withdrawal_credentials := Bytes32_default;
        amount := Gwei_default;
    }
    var pubkey: BLSPubkey;
    var withdrawal_credentials: Bytes32;
    var amount: Gwei;
    }
    class DepositData {
    constructor() {
        pubkey := BLSPubkey_default;
        withdrawal_credentials := Bytes32_default;
        amount := Gwei_default;
        signature := BLSSignature_default;
    }
    var pubkey: BLSPubkey;
    var withdrawal_credentials: Bytes32;
    var amount: Gwei;
    var signature: BLSSignature;
    }
    class BeaconBlockHeader {
    constructor() {
        slot := Slot_default;
        proposer_index := ValidatorIndex_default;
        parent_root := Root_default;
        state_root := Root_default;
        body_root := Root_default;
    }
    var slot: Slot;
    var proposer_index: ValidatorIndex;
    var parent_root: Root;
    var state_root: Root;
    var body_root: Root;
    }
    class SigningData {
    constructor() {
        object_root := Root_default;
        domain := Domain_default;
    }
    var object_root: Root;
    var domain: Domain;
    }
    class ProposerSlashing {
    constructor() {
        signed_header_1 := new SignedBeaconBlockHeader();
        signed_header_2 := new SignedBeaconBlockHeader();
    }
    var signed_header_1: SignedBeaconBlockHeader;
    var signed_header_2: SignedBeaconBlockHeader;
    }
    class AttesterSlashing {
    constructor() {
        attestation_1 := new IndexedAttestation();
        attestation_2 := new IndexedAttestation();
    }
    var attestation_1: IndexedAttestation;
    var attestation_2: IndexedAttestation;
    }
    class Attestation {
    constructor() {
        aggregation_bits := Bitlist_new([]);
        data := new AttestationData();
        signature := BLSSignature_default;
    }
    var aggregation_bits: Bitlist;
    var data: AttestationData;
    var signature: BLSSignature;
    }
    class Deposit {
    constructor() {
        proof := Vector_new<Bytes32>();
        data := new DepositData();
    }
    var proof: ssz_Vector<Bytes32>;
    var data: DepositData;
    }
    class VoluntaryExit {
    constructor() {
        epoch := Epoch_default;
        validator_index := ValidatorIndex_default;
    }
    var epoch: Epoch;
    var validator_index: ValidatorIndex;
    }
    class BeaconBlockBody {
    constructor() {
        randao_reveal := BLSSignature_default;
        eth1_data := new Eth1Data();
        graffiti := Bytes32_default;
        proposer_slashings := List_new<ProposerSlashing>([]);
        attester_slashings := List_new<AttesterSlashing>([]);
        attestations := List_new<Attestation>([]);
        deposits := List_new<Deposit>([]);
        voluntary_exits := List_new<SignedVoluntaryExit>([]);
    }
    var randao_reveal: BLSSignature;
    var eth1_data: Eth1Data;
    var graffiti: Bytes32;
    var proposer_slashings: ssz_List<ProposerSlashing>;
    var attester_slashings: ssz_List<AttesterSlashing>;
    var attestations: ssz_List<Attestation>;
    var deposits: ssz_List<Deposit>;
    var voluntary_exits: ssz_List<SignedVoluntaryExit>;
    }
    class BeaconBlock {
    constructor() {
        slot := Slot_default;
        proposer_index := ValidatorIndex_default;
        parent_root := Root_default;
        state_root := Root_default;
        body := new BeaconBlockBody();
    }
    var slot: Slot;
    var proposer_index: ValidatorIndex;
    var parent_root: Root;
    var state_root: Root;
    var body: BeaconBlockBody;
    function method copy(): BeaconBlock
    }
    class BeaconState {
    constructor() {
        genesis_time := 0;
        genesis_validators_root := Root_default;
        slot := Slot_default;
        fork := new Fork();
        latest_block_header := new BeaconBlockHeader();
        block_roots := Vector_new<Root>();
        state_roots := Vector_new<Root>();
        historical_roots := List_new<Root>([]);
        eth1_data := new Eth1Data();
        eth1_data_votes := List_new<Eth1Data>([]);
        eth1_deposit_index := 0;
        validators := List_new<Validator>([]);
        balances := List_new<Gwei>([]);
        randao_mixes := Vector_new<Bytes32>();
        slashings := Vector_new<Gwei>();
        previous_epoch_attestations := List_new<PendingAttestation>([]);
        current_epoch_attestations := List_new<PendingAttestation>([]);
        justification_bits := Bitvector_new();
        previous_justified_checkpoint := Checkpoint_new();
        current_justified_checkpoint := Checkpoint_new();
        finalized_checkpoint := Checkpoint_new();
    }
    var genesis_time: uint64;
    var genesis_validators_root: Root;
    var slot: Slot;
    var fork: Fork;
    var latest_block_header: BeaconBlockHeader;
    var block_roots: ssz_Vector<Root>;
    var state_roots: ssz_Vector<Root>;
    var historical_roots: ssz_List<Root>;
    var eth1_data: Eth1Data;
    var eth1_data_votes: ssz_List<Eth1Data>;
    var eth1_deposit_index: uint64;
    var validators: ssz_List<Validator>;
    var balances: ssz_List<Gwei>;
    var randao_mixes: ssz_Vector<Bytes32>;
    var slashings: ssz_Vector<Gwei>;
    var previous_epoch_attestations: ssz_List<PendingAttestation>;
    var current_epoch_attestations: ssz_List<PendingAttestation>;
    var justification_bits: Bitvector;
    var previous_justified_checkpoint: Checkpoint;
    var current_justified_checkpoint: Checkpoint;
    var finalized_checkpoint: Checkpoint;
    function method copy(): BeaconState
    }
    class SignedVoluntaryExit {
    constructor() {
        message := new VoluntaryExit();
        signature := BLSSignature_default;
    }
    var message: VoluntaryExit;
    var signature: BLSSignature;
    }
    class SignedBeaconBlock {
    constructor() {
        message := new BeaconBlock();
        signature := BLSSignature_default;
    }
    var message: BeaconBlock;
    var signature: BLSSignature;
    }
    class SignedBeaconBlockHeader {
    constructor() {
        message := new BeaconBlockHeader();
        signature := BLSSignature_default;
    }
    var message: BeaconBlockHeader;
    var signature: BLSSignature;
    }
    class Eth1Block {
    constructor() {
        timestamp := 0;
        deposit_root := Root_default;
        deposit_count := 0;
    }
    var timestamp: uint64;
    var deposit_root: Root;
    var deposit_count: uint64;
    }
    class AggregateAndProof {
    constructor() {
        aggregator_index := ValidatorIndex_default;
        aggregate := new Attestation();
        selection_proof := BLSSignature_default;
    }
    var aggregator_index: ValidatorIndex;
    var aggregate: Attestation;
    var selection_proof: BLSSignature;
    }
    class SignedAggregateAndProof {
    constructor() {
        message := new AggregateAndProof();
        signature := BLSSignature_default;
    }
    var message: AggregateAndProof;
    var signature: BLSSignature;
    }
    datatype LatestMessage = LatestMessage(epoch: Epoch, root: Root)
    function method LatestMessage_new(): LatestMessage
    class Store {
    constructor() {
        time := 0;
        genesis_time := 0;
        justified_checkpoint := Checkpoint_new();
        finalized_checkpoint := Checkpoint_new();
        best_justified_checkpoint := Checkpoint_new();
        proposer_boost_root := Root_default;
        equivocating_indices := Set_new([]);
        blocks := Dict_new<Root,BeaconBlock>([]);
        block_states := Dict_new<Root,BeaconState>([]);
        checkpoint_states := Dict_new<Checkpoint,BeaconState>([]);
        latest_messages := Dict_new<ValidatorIndex,LatestMessage>([]);
    }
    var time: uint64;
    var genesis_time: uint64;
    var justified_checkpoint: Checkpoint;
    var finalized_checkpoint: Checkpoint;
    var best_justified_checkpoint: Checkpoint;
    var proposer_boost_root: Root;
    var equivocating_indices: Set<ValidatorIndex>;
    var blocks: Dict<Root,BeaconBlock>;
    var block_states: Dict<Root,BeaconState>;
    var checkpoint_states: Dict<Checkpoint,BeaconState>;
    var latest_messages: Dict<ValidatorIndex,LatestMessage>;

    }
    function method Store_new(time: uint64, genesis_time: uint64, justified_checkpoint: Checkpoint, finalized_checkpoint: Checkpoint, best_justified_checkpoint: Checkpoint, proposer_boost_root: Root, equivocating_indices: Set<ValidatorIndex>, blocks: Dict<Root,BeaconBlock>, block_states: Dict<Root,BeaconState>, checkpoint_states: Dict<Checkpoint,BeaconState>, latest_messages: Dict<ValidatorIndex,LatestMessage>): Store
}