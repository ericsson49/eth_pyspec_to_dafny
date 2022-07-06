include "ssz.dfy"
include "simpletypes.dfy"

module Classes {
    import opened SSZ
    import opened SimpleTypes

    datatype Fork = Fork(
        previous_version: Version,
        current_version: Version,
        epoch: Epoch
    )
    function method Fork_new(): Fork {
        Fork(Version_default, Version_default, Epoch_default)
    }
    datatype ForkData = ForkData(
        current_version: Version,
        genesis_validators_root: Root
    )
    function method ForkData_new(): ForkData {
        ForkData(Version_default, Root_default)
    }
    datatype Checkpoint = Checkpoint(
        epoch: Epoch,
        root: Root
    )
    function method Checkpoint_new(): Checkpoint {
        Checkpoint(Epoch_default, Root_default)
    }
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
    const pubkey: BLSPubkey;
    const withdrawal_credentials: Bytes32;
    var effective_balance: Gwei;
    var slashed: boolean;
    var activation_eligibility_epoch: Epoch;
    var activation_epoch: Epoch;
    var exit_epoch: Epoch;
    var withdrawable_epoch: Epoch;
    }
    datatype AttestationData = AttestationData(
        slot: Slot,
        index: CommitteeIndex,
        beacon_block_root: Root,
        source: Checkpoint,
        target: Checkpoint
    )
    function method AttestationData_new(): AttestationData {
        AttestationData(Slot_default, CommitteeIndex_default, Root_default, Checkpoint_new(), Checkpoint_new())
    }
    datatype IndexedAttestation = IndexedAttestation(
        attesting_indices: ssz_List<ValidatorIndex>,
        data: AttestationData,
        signature: BLSSignature
    )
    function method IndexedAttestation_new(): IndexedAttestation {
        IndexedAttestation(List_new<ValidatorIndex>([]), AttestationData_new(), BLSSignature_default)
    }
    datatype PendingAttestation = PendingAttestation(
        aggregation_bits: Bitlist,
        data: AttestationData,
        inclusion_delay: Slot,
        proposer_index: ValidatorIndex
    )
    function method PendingAttestation_new(): PendingAttestation {
        PendingAttestation(Bitlist_new([]), AttestationData_new(), Slot_default, ValidatorIndex_default)
    }
    datatype Eth1Data = Eth1Data(
        deposit_root: Root,
        deposit_count: uint64,
        block_hash: Hash32
    )
    function method Eth1Data_new(): Eth1Data {
        Eth1Data(Root_default, 0, Hash32_default)
    }
    datatype HistoricalBatch = HistoricalBatch(
        block_roots: ssz_Vector<Root>,
        state_roots: ssz_Vector<Root>
    )
    function method HistoricalBatch_new(): HistoricalBatch {
        HistoricalBatch(Vector_new<Root>(), Vector_new<Root>())
    }
    datatype DepositMessage = DepositMessage(
        pubkey: BLSPubkey,
        withdrawal_credentials: Bytes32,
        amount: Gwei
    )
    function method DepositMessage_new(): DepositMessage {
        DepositMessage(BLSPubkey_default, Bytes32_default, Gwei_default)
    }
    datatype DepositData = DepositData(
        pubkey: BLSPubkey,
        withdrawal_credentials: Bytes32,
        amount: Gwei,
        signature: BLSSignature
    )
    function method DepositData_new(): DepositData {
        DepositData(BLSPubkey_default, Bytes32_default, Gwei_default, BLSSignature_default)
    }
    datatype BeaconBlockHeader = BeaconBlockHeader(
        slot: Slot,
        proposer_index: ValidatorIndex,
        parent_root: Root,
        state_root: Root,
        body_root: Root
    )
    function method BeaconBlockHeader_new(): BeaconBlockHeader {
        BeaconBlockHeader(Slot_default, ValidatorIndex_default, Root_default, Root_default, Root_default)
    }
    datatype SigningData = SigningData(
        object_root: Root,
        domain: Domain
    )
    function method SigningData_new(): SigningData {
        SigningData(Root_default, Domain_default)
    }
    datatype ProposerSlashing = ProposerSlashing(
        signed_header_1: SignedBeaconBlockHeader,
        signed_header_2: SignedBeaconBlockHeader
    )
    function method ProposerSlashing_new(): ProposerSlashing {
        ProposerSlashing(SignedBeaconBlockHeader_new(), SignedBeaconBlockHeader_new())
    }
    datatype AttesterSlashing = AttesterSlashing(
        attestation_1: IndexedAttestation,
        attestation_2: IndexedAttestation
    )
    function method AttesterSlashing_new(): AttesterSlashing {
        AttesterSlashing(IndexedAttestation_new(), IndexedAttestation_new())
    }
    datatype Attestation = Attestation(
        aggregation_bits: Bitlist,
        data: AttestationData,
        signature: BLSSignature
    )
    function method Attestation_new(): Attestation {
        Attestation(Bitlist_new([]), AttestationData_new(), BLSSignature_default)
    }
    datatype Deposit = Deposit(
        proof: ssz_Vector<Bytes32>,
        data: DepositData
    )
    function method Deposit_new(): Deposit {
        Deposit(Vector_new<Bytes32>(), DepositData_new())
    }
    datatype VoluntaryExit = VoluntaryExit(
        epoch: Epoch,
        validator_index: ValidatorIndex
    )
    function method VoluntaryExit_new(): VoluntaryExit {
        VoluntaryExit(Epoch_default, ValidatorIndex_default)
    }
    datatype BeaconBlockBody = BeaconBlockBody(
        randao_reveal: BLSSignature,
        eth1_data: Eth1Data,
        graffiti: Bytes32,
        proposer_slashings: ssz_List<ProposerSlashing>,
        attester_slashings: ssz_List<AttesterSlashing>,
        attestations: ssz_List<Attestation>,
        deposits: ssz_List<Deposit>,
        voluntary_exits: ssz_List<SignedVoluntaryExit>
    )
    function method BeaconBlockBody_new(): BeaconBlockBody {
        BeaconBlockBody(BLSSignature_default, Eth1Data_new(), Bytes32_default, List_new<ProposerSlashing>([]), List_new<AttesterSlashing>([]), List_new<Attestation>([]), List_new<Deposit>([]), List_new<SignedVoluntaryExit>([]))
    }
    datatype BeaconBlock = BeaconBlock(
        slot: Slot,
        proposer_index: ValidatorIndex,
        parent_root: Root,
        state_root: Root,
        body: BeaconBlockBody
    )
    {
        function method copy(): BeaconBlock
    }
    function method BeaconBlock_new(): BeaconBlock{
        BeaconBlock(Slot_default, ValidatorIndex_default, Root_default, Root_default, BeaconBlockBody_new())
    }
    class BeaconState {
    constructor() {
        genesis_time := 0;
        genesis_validators_root := Root_default;
        slot := Slot_default;
        fork := Fork_new();
        latest_block_header := BeaconBlockHeader_new();
        block_roots := Vector_new<Root>();
        state_roots := Vector_new<Root>();
        historical_roots := List_new<Root>([]);
        eth1_data := Eth1Data_new();
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
    datatype SignedVoluntaryExit = SignedVoluntaryExit(
        message: VoluntaryExit,
        signature: BLSSignature
    )
    function method SignedVoluntaryExit_new(): SignedVoluntaryExit {
        SignedVoluntaryExit(VoluntaryExit_new(), BLSSignature_default)
    }
    datatype SignedBeaconBlock = SignedBeaconBlock(
        message: BeaconBlock,
        signature: BLSSignature
    )
    function method SignedBeaconBlock_new(): SignedBeaconBlock {
        SignedBeaconBlock(BeaconBlock_new(), BLSSignature_default)
    }
    datatype SignedBeaconBlockHeader = SignedBeaconBlockHeader(
        message: BeaconBlockHeader,
        signature: BLSSignature
    )
    function method SignedBeaconBlockHeader_new(): SignedBeaconBlockHeader {
        SignedBeaconBlockHeader(BeaconBlockHeader_new(), BLSSignature_default)
    }
    datatype Eth1Block = Eth1Block(
        timestamp: uint64,
        deposit_root: Root,
        deposit_count: uint64
    )
    function method Eth1Block_new(): Eth1Block {
        Eth1Block(0, Root_default, 0)
    }
    datatype AggregateAndProof = AggregateAndProof(
        aggregator_index: ValidatorIndex,
        aggregate: Attestation,
        selection_proof: BLSSignature
    )
    function method AggregateAndProof_new(): AggregateAndProof {
        AggregateAndProof(ValidatorIndex_default, Attestation_new(), BLSSignature_default)
    }
    datatype SignedAggregateAndProof = SignedAggregateAndProof(
        message: AggregateAndProof,
        signature: BLSSignature
    )
    function method SignedAggregateAndProof_new(): SignedAggregateAndProof {
        SignedAggregateAndProof(AggregateAndProof_new(), BLSSignature_default)
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
        constructor Init(time: uint64, genesis_time: uint64, justified_checkpoint: Checkpoint, finalized_checkpoint: Checkpoint, best_justified_checkpoint: Checkpoint, proposer_boost_root: Root, equivocating_indices: Set<ValidatorIndex>, blocks: Dict<Root,BeaconBlock>, block_states: Dict<Root,BeaconState>, checkpoint_states: Dict<Checkpoint,BeaconState>, latest_messages: Dict<ValidatorIndex,LatestMessage>) {
            this.time := time;
            this.genesis_time := genesis_time;
            this.justified_checkpoint := justified_checkpoint;
            this.finalized_checkpoint := finalized_checkpoint;
            this.best_justified_checkpoint := best_justified_checkpoint;
            this.proposer_boost_root := proposer_boost_root;
            this.equivocating_indices := equivocating_indices;
            this.blocks := blocks;
            this.block_states := block_states;
            this.checkpoint_states := checkpoint_states;
            this.latest_messages := latest_messages;
        }
        var time: uint64;
        const genesis_time: uint64;
        var justified_checkpoint: Checkpoint;
        var finalized_checkpoint: Checkpoint;
        var best_justified_checkpoint: Checkpoint;
        var proposer_boost_root: Root;
        const equivocating_indices: Set<ValidatorIndex>;
        var blocks: Dict<Root,BeaconBlock>;
        var block_states: Dict<Root,BeaconState>;
        var checkpoint_states: Dict<Checkpoint,BeaconState>;
        const latest_messages: Dict<ValidatorIndex,LatestMessage>;
    }
}