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
    datatype Validator = Validator(
        pubkey: BLSPubkey,
        withdrawal_credentials: Bytes32,
        effective_balance: Gwei,
        slashed: boolean,
        activation_eligibility_epoch: Epoch,
        activation_epoch: Epoch,
        exit_epoch: Epoch,
        withdrawable_epoch: Epoch
    )
    function method Validator_new(): Validator {
        Validator(BLSPubkey_default, Bytes32_default, Gwei_default, boolean_default, Epoch_default, Epoch_default, Epoch_default, Epoch_default)
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
        attesting_indices: seq<ValidatorIndex>,
        data: AttestationData,
        signature: BLSSignature
    )
    function method IndexedAttestation_new(): IndexedAttestation {
        IndexedAttestation([], AttestationData_new(), BLSSignature_default)
    }
    datatype PendingAttestation = PendingAttestation(
        aggregation_bits: seq<boolean>,
        data: AttestationData,
        inclusion_delay: Slot,
        proposer_index: ValidatorIndex
    )
    function method PendingAttestation_new(): PendingAttestation {
        PendingAttestation([], AttestationData_new(), Slot_default, ValidatorIndex_default)
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
        block_roots: seq<Root>,
        state_roots: seq<Root>
    )
    function method HistoricalBatch_new(): HistoricalBatch {
        HistoricalBatch([], [])
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
        aggregation_bits: seq<boolean>,
        data: AttestationData,
        signature: BLSSignature
    )
    function method Attestation_new(): Attestation {
        Attestation([], AttestationData_new(), BLSSignature_default)
    }
    datatype Deposit = Deposit(
        proof: seq<Bytes32>,
        data: DepositData
    )
    function method Deposit_new(): Deposit {
        Deposit([], DepositData_new())
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
        proposer_slashings: seq<ProposerSlashing>,
        attester_slashings: seq<AttesterSlashing>,
        attestations: seq<Attestation>,
        deposits: seq<Deposit>,
        voluntary_exits: seq<SignedVoluntaryExit>
    )
    function method BeaconBlockBody_new(): BeaconBlockBody {
        BeaconBlockBody(BLSSignature_default, Eth1Data_new(), Bytes32_default, [], [], [], [], [])
    }
    datatype BeaconBlock = BeaconBlock(
        slot: Slot,
        proposer_index: ValidatorIndex,
        parent_root: Root,
        state_root: Root,
        body: BeaconBlockBody
    )
    {
        function method copy(): BeaconBlock {
            this
        }
    }
    function method BeaconBlock_new(): BeaconBlock{
        BeaconBlock(Slot_default, ValidatorIndex_default, Root_default, Root_default, BeaconBlockBody_new())
    }
    datatype BeaconState = BeaconState(
        genesis_time: uint64,
        genesis_validators_root: Root,
        slot: Slot,
        fork: Fork,
        latest_block_header: BeaconBlockHeader,
        block_roots: seq<Root>,
        state_roots: seq<Root>,
        historical_roots: seq<Root>,
        eth1_data: Eth1Data,
        eth1_data_votes: seq<Eth1Data>,
        eth1_deposit_index: uint64,
        validators: seq<Validator>,
        balances: seq<Gwei>,
        randao_mixes: seq<Bytes32>,
        slashings: seq<Gwei>,
        previous_epoch_attestations: seq<PendingAttestation>,
        current_epoch_attestations: seq<PendingAttestation>,
        justification_bits: seq<boolean>,
        previous_justified_checkpoint: Checkpoint,
        current_justified_checkpoint: Checkpoint,
        finalized_checkpoint: Checkpoint
    ) {
        function method copy(): BeaconState {
            this
        }
    }
    function method BeaconState_new(): BeaconState {
        BeaconState(0, Root_default, Slot_default, Fork_new(), BeaconBlockHeader_new(), [], [], [], Eth1Data_new(), [], 0, [], [], [], [], [], [], [], Checkpoint_new(), Checkpoint_new(), Checkpoint_new())
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
    constructor empty() {
        time := 0;
        genesis_time := 0;
        justified_checkpoint := Checkpoint_new();
        finalized_checkpoint := Checkpoint_new();
        best_justified_checkpoint := Checkpoint_new();
        proposer_boost_root := Root_default;
        equivocating_indices := new Set.empty();
        blocks := new Dict.empty();
        block_states := new Dict.empty();
        checkpoint_states := new Dict.empty();
        latest_messages := new Dict.empty();
    }
    constructor Init(time: uint64, genesis_time: uint64, justified_checkpoint: Checkpoint, finalized_checkpoint: Checkpoint, best_justified_checkpoint: Checkpoint, proposer_boost_root: Root, equivocating_indices: Set<ValidatorIndex>, blocks: Dict<Root,BeaconBlock>, block_states: Dict<Root,BeaconState>, checkpoint_states: Dict<Checkpoint,BeaconState>, latest_messages: Dict<ValidatorIndex,LatestMessage>)
    ensures this.time == time && this.genesis_time == genesis_time && this.justified_checkpoint == justified_checkpoint
    && this.finalized_checkpoint == finalized_checkpoint && this.best_justified_checkpoint == best_justified_checkpoint
    && this.proposer_boost_root == proposer_boost_root && this.equivocating_indices == equivocating_indices
    && this.blocks == blocks && this.block_states == block_states && this.checkpoint_states == checkpoint_states
    && this.latest_messages == latest_messages
    {
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
    function method toPure(): Store_dt
    reads this, this.equivocating_indices, this.blocks, this.block_states, this.checkpoint_states, this.latest_messages
    {
        Store_dt(
            time, genesis_time, justified_checkpoint, finalized_checkpoint,
            best_justified_checkpoint, proposer_boost_root, equivocating_indices.repr,
            blocks.repr, block_states.repr, checkpoint_states.repr, latest_messages.repr
        )
    }
    }
    datatype Store_dt = Store_dt(
        time: uint64,
        genesis_time: uint64,
        justified_checkpoint: Checkpoint,
        finalized_checkpoint: Checkpoint,
        best_justified_checkpoint: Checkpoint,
        proposer_boost_root: Root,
        equivocating_indices: set<ValidatorIndex>,
        blocks: map<Root,BeaconBlock>,
        block_states: map<Root,BeaconState>,
        checkpoint_states: map<Checkpoint,BeaconState>,
        latest_messages: map<ValidatorIndex,LatestMessage>
    ) {
        method toImpure() returns (ret_: Store)
        ensures ret_.toPure() == this
        ensures fresh(ret_) && fresh(ret_.blocks) && fresh(ret_.block_states)
        && fresh(ret_.checkpoint_states) && fresh(ret_.latest_messages)
        && fresh(ret_.equivocating_indices)
        {
            var equivocating_indices := Set_new(equivocating_indices);
            var blocks := Dict_new(blocks);
            var block_states := Dict_new(block_states);
            var checkpoint_states := Dict_new(checkpoint_states);
            var latest_messages := Dict_new(latest_messages);
            ret_ := new Store.Init(
                time, genesis_time, justified_checkpoint, finalized_checkpoint,
                best_justified_checkpoint, proposer_boost_root, equivocating_indices,
                blocks, block_states, checkpoint_states, latest_messages
            );
        }
    }
}