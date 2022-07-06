include "ssz.dfy"
include "simpletypes.dfy"

module Consts {
    import opened SSZ
    import opened SimpleTypes

    const GENESIS_SLOT := Slot_new(0);
    const GENESIS_EPOCH := Epoch_new(0);
    const FAR_FUTURE_EPOCH := Epoch_new(0);
    const BASE_REWARDS_PER_EPOCH := uint64_new(4);
    const DEPOSIT_CONTRACT_TREE_DEPTH := uint64_new(pow(2, 5));
    const JUSTIFICATION_BITS_LENGTH := uint64_new(4);
    const ENDIANNESS := "little";
    const BLS_WITHDRAWAL_PREFIX := Bytes1_new(0x00);
    const ETH1_ADDRESS_WITHDRAWAL_PREFIX := Bytes1_new(0x01);
    const DOMAIN_BEACON_PROPOSER := DomainType_new(0x00000000);
    const DOMAIN_BEACON_ATTESTER := DomainType_new(0x01000000);
    const DOMAIN_RANDAO := DomainType_new(0x02000000);
    const DOMAIN_DEPOSIT := DomainType_new(0x03000000);
    const DOMAIN_VOLUNTARY_EXIT := DomainType_new(0x04000000);
    const DOMAIN_SELECTION_PROOF := DomainType_new(0x05000000);
    const DOMAIN_AGGREGATE_AND_PROOF := DomainType_new(0x06000000);
    const MAX_COMMITTEES_PER_SLOT := uint64_new(pow(2, 6));
    const TARGET_COMMITTEE_SIZE := uint64_new(pow(2, 7));
    const MAX_VALIDATORS_PER_COMMITTEE := uint64_new(pow(2, 11));
    const SHUFFLE_ROUND_COUNT := uint64_new(90);
    const HYSTERESIS_QUOTIENT := uint64_new(4);
    const HYSTERESIS_DOWNWARD_MULTIPLIER := uint64_new(1);
    const HYSTERESIS_UPWARD_MULTIPLIER := uint64_new(5);
    const MIN_DEPOSIT_AMOUNT := Gwei_new(pow(2, 0) * pow(10, 9));
    const MAX_EFFECTIVE_BALANCE := Gwei_new(pow(2, 5) * pow(10, 9));
    const EFFECTIVE_BALANCE_INCREMENT := Gwei_new(pow(2, 0) * pow(10, 9));
    const MIN_ATTESTATION_INCLUSION_DELAY := uint64_new(pow(2, 0));
    const SLOTS_PER_EPOCH := uint64_new(pow(2, 5));
    const MIN_SEED_LOOKAHEAD := uint64_new(pow(2, 0));
    const MAX_SEED_LOOKAHEAD := uint64_new(pow(2, 2));
    const MIN_EPOCHS_TO_INACTIVITY_PENALTY := uint64_new(pow(2, 2));
    const EPOCHS_PER_ETH1_VOTING_PERIOD := uint64_new(pow(2, 6));
    const SLOTS_PER_HISTORICAL_ROOT := uint64_new(pow(2, 13));
    const EPOCHS_PER_HISTORICAL_VECTOR := uint64_new(pow(2, 16));
    const EPOCHS_PER_SLASHINGS_VECTOR := uint64_new(pow(2, 13));
    const HISTORICAL_ROOTS_LIMIT := uint64_new(pow(2, 24));
    const VALIDATOR_REGISTRY_LIMIT := uint64_new(pow(2, 40));
    const BASE_REWARD_FACTOR := uint64_new(pow(2, 6));
    const WHISTLEBLOWER_REWARD_QUOTIENT := uint64_new(pow(2, 9));
    const PROPOSER_REWARD_QUOTIENT := uint64_new(pow(2, 3));
    const INACTIVITY_PENALTY_QUOTIENT := uint64_new(pow(2, 26));
    const MIN_SLASHING_PENALTY_QUOTIENT := uint64_new(pow(2, 7));
    const PROPORTIONAL_SLASHING_MULTIPLIER := uint64_new(1);
    const MAX_PROPOSER_SLASHINGS := pow(2, 4);
    const MAX_ATTESTER_SLASHINGS := pow(2, 1);
    const MAX_ATTESTATIONS := pow(2, 7);
    const MAX_DEPOSITS := pow(2, 4);
    const MAX_VOLUNTARY_EXITS := pow(2, 4);
    const MIN_GENESIS_ACTIVE_VALIDATOR_COUNT := uint64_new(pow(2, 14));
    const MIN_GENESIS_TIME := uint64_new(1606824000);
    const GENESIS_FORK_VERSION := Version_new(0x00000000);
    const GENESIS_DELAY := uint64_new(604800);
    const SECONDS_PER_SLOT := uint64_new(12);
    const SECONDS_PER_ETH1_BLOCK := uint64_new(14);
    const MIN_VALIDATOR_WITHDRAWABILITY_DELAY := uint64_new(pow(2, 8));
    const SHARD_COMMITTEE_PERIOD := uint64_new(pow(2, 8));
    const ETH1_FOLLOW_DISTANCE := uint64_new(pow(2, 11));
    const EJECTION_BALANCE := Gwei_new(pow(2, 4) * pow(10, 9));
    const MIN_PER_EPOCH_CHURN_LIMIT := uint64_new(pow(2, 2));
    const CHURN_LIMIT_QUOTIENT := uint64_new(pow(2, 16));
    const INTERVALS_PER_SLOT := uint64_new(3);
    const SAFE_SLOTS_TO_UPDATE_JUSTIFIED := pow(2, 3);
    const PROPOSER_SCORE_BOOST := uint64_new(70);
    const TARGET_AGGREGATORS_PER_COMMITTEE := pow(2, 4);
    const RANDOM_SUBNETS_PER_VALIDATOR := pow(2, 0);
    const EPOCHS_PER_RANDOM_SUBNET_SUBSCRIPTION := pow(2, 8);
    const ATTESTATION_SUBNET_COUNT := 64;
    const ETH_TO_GWEI := uint64_new(pow(10, 9));
    const SAFETY_DECAY := uint64_new(10);
}
