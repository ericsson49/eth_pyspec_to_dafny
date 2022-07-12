include "ssz.dfy"
include "simpletypes.dfy"
include "classes_datatypes.dfy"
include "consts.dfy"

import opened SSZ
import opened SimpleTypes
import opened Classes
import opened Consts

function method get_current_epoch(state: BeaconState): Epoch
function method is_slashable_attestation_data(data1: AttestationData, data2: AttestationData): bool
function method is_valid_indexed_attestation(state: BeaconState, attestation: IndexedAttestation): bool
function method get_indexed_attestation(state: BeaconState, attestation: Attestation): IndexedAttestation
function method get_active_validator_indices(state: BeaconState, epoch: Epoch): Sequence<ValidatorIndex>
function method get_total_active_balance(state: BeaconState): Gwei
method process_slots(state_: BeaconState, slot: Slot) returns (status_: Outcome<()>, state: BeaconState)
method state_transition(state_: BeaconState, block: SignedBeaconBlock, check: bool) returns (status_: Outcome<()>, state: BeaconState)

/*
    Return the epoch number at ``slot``.
    */
function method compute_epoch_at_slot(slot: Slot): Epoch
requires SLOTS_PER_EPOCH != 0
{
  Epoch_new(slot / SLOTS_PER_EPOCH)
}

/*
    Return the start slot of ``epoch``.
    */
function method compute_start_slot_at_epoch(epoch: Epoch): Slot
{
  Slot_new(epoch * SLOTS_PER_EPOCH)
}

method get_forkchoice_store(anchor_state: BeaconState, anchor_block: BeaconBlock)
returns (status_: Outcome<Store_dt>)
{
  var _ :- pyassert(anchor_block.state_root == hash_tree_root(anchor_state));
  var anchor_root: Root := Root_new(hash_tree_root(anchor_block));
  var anchor_epoch: Epoch := get_current_epoch(anchor_state);
  var justified_checkpoint: Checkpoint := Checkpoint(anchor_epoch, anchor_root);
  var finalized_checkpoint: Checkpoint := Checkpoint(anchor_epoch, anchor_root);
  var proposer_boost_root: Root := Root_new(0);
  return Result(Store_dt(uint64_new(anchor_state.genesis_time + (SECONDS_PER_SLOT * anchor_state.slot)), anchor_state.genesis_time, justified_checkpoint, finalized_checkpoint, justified_checkpoint, proposer_boost_root, {}, map[anchor_root := anchor_block.copy()], map[anchor_root := anchor_state.copy()], map[justified_checkpoint := anchor_state.copy()], map[]));
}

function method get_slots_since_genesis(store: Store_dt): int
{
  (store.time - store.genesis_time) / SECONDS_PER_SLOT
}

function method get_current_slot(store: Store_dt): Slot
{
  Slot_new(GENESIS_SLOT + get_slots_since_genesis(store))
}

function method compute_slots_since_epoch_start(slot: Slot): int
{
  slot - compute_start_slot_at_epoch(compute_epoch_at_slot(slot))
}

function method get_ancestor(store: Store_dt, root: Root, slot: Slot): Outcome<Root>
{
  var block: BeaconBlock :- map_get(store.blocks, root);
  if block.slot > slot then
    get_ancestor(store, block.parent_root, slot)
  else
    if block.slot == slot then
      Result(root)
    else
      Result(root)
}

function method get_latest_attesting_balance(store: Store_dt, root: Root): Outcome<Gwei>
{
  var state: BeaconState :- map_get(store.checkpoint_states, store.justified_checkpoint);
  var active_indices: Sequence<ValidatorIndex> := get_active_validator_indices(state, get_current_epoch(state));
  var tmp_0 :- filter_f((i) =>
      if i in store.latest_messages && i !in store.equivocating_indices then
        var tmp_0 :- map_get(store.latest_messages, i);
        var tmp_1 :- map_get(store.blocks, root);
        var tmp_2 :- get_ancestor(store, tmp_0.root, tmp_1.slot);
        Result(tmp_2 == root)
      else Result(false),
    active_indices);
  var tmp_1 :- pymap_f((i) => var tmp_0 :- seq_get(state.validators, i); Result(tmp_0.effective_balance), tmp_0);
  var attestation_score: Gwei := Gwei_new(sum(tmp_1));
  if store.proposer_boost_root == Root_new(0) then
    Result(attestation_score)
  else
    var proposer_score: Gwei := Gwei_new(0);
    var tmp_1 :- map_get(store.blocks, root);
    var tmp_2 :- get_ancestor(store, store.proposer_boost_root, tmp_1.slot);
    var proposer_score_2: Gwei :=
      if tmp_2 == root then
        var num_validators: int := len(get_active_validator_indices(state, get_current_epoch(state)));
        var avg_balance: Gwei := get_total_active_balance(state) / num_validators;
        var committee_size: uint64 := num_validators / SLOTS_PER_EPOCH;
        var committee_weight: Gwei := committee_size * avg_balance;
        var proposer_score_1: Gwei := committee_weight * PROPOSER_SCORE_BOOST / 100;
        proposer_score_1
      else
        proposer_score;
  Result(attestation_score + proposer_score_2)
}

method filter_block_tree(store: Store_dt, block_root: Root, blocks_: map<Root,BeaconBlock>)
returns (status_: Outcome<bool>, blocks: map<Root, BeaconBlock>)
{
  blocks := blocks_;
  var block: BeaconBlock :- map_get(store.blocks, block_root);
  var tmp_0 := store.blocks.Keys;
  var children: seq<Root> := set_to_seq(set_filter((root) => store.blocks[root].parent_root == block_root, tmp_0));
  if seq_any(children) {
    var tmp_0 := children;
    var tmp_1 := [];
    while tmp_0 != [] decreases tmp_0 {
      var child := tmp_0[0];
      tmp_0 := tmp_0[1..];
      var tmp_2, ret_ :- filter_block_tree(store, child, blocks);
      tmp_1 := tmp_1 + [tmp_2];
    }
    var filter_block_tree_result: seq<bool> := tmp_1;
    if seq_any(filter_block_tree_result) {
      blocks := blocks[block_root := block];
      return Result(true), blocks;
    }
    return Result(false), blocks;
  }
  var head_state: BeaconState :- map_get(store.block_states, block_root);
  var correct_justified: bool := store.justified_checkpoint.epoch == GENESIS_EPOCH || head_state.current_justified_checkpoint == store.justified_checkpoint;
  var correct_finalized: bool := store.finalized_checkpoint.epoch == GENESIS_EPOCH || head_state.finalized_checkpoint == store.finalized_checkpoint;
  if correct_justified && correct_finalized {
    blocks := blocks[block_root := block];
    return Result(true), blocks;
  }
  return Result(false), blocks;
}

/*
    Retrieve a filtered block tree from ``store``, only returning branches
    whose leaf state's justified/finalized info agrees with that in ``store``.
    */
method get_filtered_block_tree(store: Store_dt) returns (status_: Outcome<map<Root,BeaconBlock>>)
{
  var base: Root := store.justified_checkpoint.root;
  var blocks: map<Root,BeaconBlock> := map[];
  var tmp_0;
  tmp_0, blocks := filter_block_tree(store, base, blocks);
  return Result(blocks);
}

method get_head(store: Store_dt) returns (status_: Outcome<Root>)
{
  var blocks: map<Root,BeaconBlock> :- get_filtered_block_tree(store);
  var head: Root := store.justified_checkpoint.root;
  var head_2 := head;
  while true {
    var tmp_0 := blocks.Keys;
    var children: seq<Root> := set_to_seq(set_filter((root) => blocks[root].parent_root == head_2, tmp_0));
    if |children| == 0 {
      return Result(head_2);
    }
    var head_1: Root :- seq_max_f(children, (root: Root) => var tmp_0 :- get_latest_attesting_balance(store, root); Result((tmp_0, root)));
    head_2 := head_1;
  }
}

/*
    To address the bouncing attack, only update conflicting justified
    checkpoints in the fork choice if in the early slots of the epoch.
    Otherwise, delay incorporation of new justified checkpoint until next epoch boundary.

    See https://ethresear.ch/t/prevention-of-bouncing-attack-on-ffg/6114 for more detailed analysis and discussion.
    */
function method should_update_justified_checkpoint(store: Store_dt, new_justified_checkpoint: Checkpoint): Outcome<bool>
{
  if compute_slots_since_epoch_start(get_current_slot(store)) < SAFE_SLOTS_TO_UPDATE_JUSTIFIED then
    Result(true)
  else
    var justified_slot: Slot := compute_start_slot_at_epoch(store.justified_checkpoint.epoch);
    var tmp_0 :- get_ancestor(store, new_justified_checkpoint.root, justified_slot);
    if !(tmp_0 == store.justified_checkpoint.root) then
      Result(false)
    else
      Result(true)
}

function method validate_target_epoch_against_current_time(store: Store_dt, attestation: Attestation): Outcome<()>
{
  var target: Checkpoint := attestation.data.target;
  var current_epoch: Epoch := compute_epoch_at_slot(get_current_slot(store));
  var previous_epoch: Epoch := if (current_epoch > GENESIS_EPOCH) then current_epoch - 1 else GENESIS_EPOCH;
  var _ :- pyassert(target.epoch in [current_epoch, previous_epoch]);
  Result(())
}

function method validate_on_attestation(store: Store_dt, attestation: Attestation, is_from_block: bool): Outcome<()>
{
  var target: Checkpoint := attestation.data.target;
  if !is_from_block then
    var _ :- validate_target_epoch_against_current_time(store, attestation);
    Result(())
  else
  var _ :- pyassert(target.epoch == compute_epoch_at_slot(attestation.data.slot));
  var _ :- pyassert(target.root in store.blocks);
  var _ :- pyassert(attestation.data.beacon_block_root in store.blocks);
  var _ :- pyassert(store.blocks[attestation.data.beacon_block_root].slot <= attestation.data.slot);
  var target_slot: Slot := compute_start_slot_at_epoch(target.epoch);
  var tmp_0 :- get_ancestor(store, attestation.data.beacon_block_root, target_slot);
  var _ :- pyassert(target.root == tmp_0);
  var _ :- pyassert(get_current_slot(store) >= (attestation.data.slot + 1));
  Result(())
}

method store_target_checkpoint_state(store_: Store_dt, target: Checkpoint)
returns (status_: Outcome<()>, store: Store_dt) 
{
  var unused_: ();
  status_, store := Result(()), store_;
  if target !in store.checkpoint_states {
    var tmp_0 :- map_get(store.block_states, target.root);
    var base_state: BeaconState := tmp_0.copy();
    if base_state.slot < compute_start_slot_at_epoch(target.epoch) {
      unused_, base_state :- process_slots(base_state, compute_start_slot_at_epoch(target.epoch));
    }
    store := store.(checkpoint_states := store.checkpoint_states[target := base_state]);
  }
}

method update_latest_messages(store_: Store_dt, attesting_indices: seq<ValidatorIndex>, attestation: Attestation)
returns (store: Store_dt)
{
  store := store_;
  var target: Checkpoint := attestation.data.target;
  var beacon_block_root: Root := attestation.data.beacon_block_root;
  var non_equivocating_attesting_indices: seq<ValidatorIndex> := seq_filter((i) => i !in store.equivocating_indices, attesting_indices);
  var tmp_for_0: seq<ValidatorIndex> := non_equivocating_attesting_indices;
  while tmp_for_0 != [] decreases tmp_for_0 {
    var i: ValidatorIndex := tmp_for_0[0];
    tmp_for_0 := tmp_for_0[1..];
    if i !in store.latest_messages || target.epoch > store.latest_messages[i].epoch {
      store := store.(latest_messages := store.latest_messages[i := LatestMessage(target.epoch, beacon_block_root)]);
    }
  }
}

method on_tick(store_: Store_dt, time: uint64)
returns (status_: Outcome<()>, store: Store_dt) 
{
  status_, store := Result(()), store_;
  var previous_slot: Slot := get_current_slot(store);
  store := store.(time := time);
  var current_slot: Slot := get_current_slot(store);
  if current_slot > previous_slot {
    store := store.(proposer_boost_root := Root_new(0));
  }
  if !(current_slot > previous_slot && compute_slots_since_epoch_start(current_slot) == 0) {
    return;
  }
  if store.best_justified_checkpoint.epoch > store.justified_checkpoint.epoch {
    var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
    var ancestor_at_finalized_slot: Root :- get_ancestor(store, store.best_justified_checkpoint.root, finalized_slot);
    if ancestor_at_finalized_slot == store.finalized_checkpoint.root {
      store := store.(justified_checkpoint := store.best_justified_checkpoint);
    }
  }
}

method on_block(store_: Store_dt, signed_block: SignedBeaconBlock)
returns (status_: Outcome<()>, store: Store_dt) 
{
  var unused_: ();
  status_, store := Result(()), store_;
  var block: BeaconBlock := signed_block.message;
  var _ :- pyassert(block.parent_root in store.block_states);
  var tmp_0 :- map_get(store.block_states, block.parent_root);
  var pre_state: BeaconState := tmp_0.copy();
  var _ :- pyassert(get_current_slot(store) >= block.slot);
  var finalized_slot: Slot := compute_start_slot_at_epoch(store.finalized_checkpoint.epoch);
  var _ :- pyassert(block.slot > finalized_slot);
  var tmp_1 :- get_ancestor(store, block.parent_root, finalized_slot);
  var _ :- pyassert(tmp_1 == store.finalized_checkpoint.root);
  var state: BeaconState := pre_state.copy();
  unused_, state :- state_transition(state, signed_block, true);
  store := store.(blocks := store.blocks[hash_tree_root(block) := block]);
  store := store.(block_states := store.block_states[hash_tree_root(block) := state]);
  var time_into_slot: uint64 := (store.time - store.genesis_time) % SECONDS_PER_SLOT;
  var is_before_attesting_interval: bool := time_into_slot < (SECONDS_PER_SLOT / INTERVALS_PER_SLOT);
  if get_current_slot(store) == block.slot && is_before_attesting_interval {
    store := store.(proposer_boost_root := Root_new(hash_tree_root(block)));
  }
  if state.current_justified_checkpoint.epoch > store.justified_checkpoint.epoch {
    if state.current_justified_checkpoint.epoch > store.best_justified_checkpoint.epoch {
      store := store.(best_justified_checkpoint := state.current_justified_checkpoint);
    }
    var tmp_2 :- should_update_justified_checkpoint(store, state.current_justified_checkpoint);
    if tmp_2 {
      store := store.(justified_checkpoint := state.current_justified_checkpoint);
    }
  }
  if state.finalized_checkpoint.epoch > store.finalized_checkpoint.epoch {
    store := store.(finalized_checkpoint := state.finalized_checkpoint);
    store := store.(justified_checkpoint := state.current_justified_checkpoint);
  }
}

/*
    Run ``on_attestation`` upon receiving a new ``attestation`` from either within a block or directly on the wire.

    An ``attestation`` that is asserted as invalid may be valid at a later time,
    consider scheduling it for later processing in such case.
    */
method on_attestation(store_: Store_dt, attestation: Attestation, is_from_block: bool)
returns (status_: Outcome<()>, store: Store_dt) 
{
  var unused_: ();
  status_, store := Result(()), store_;
  var _ :- validate_on_attestation(store, attestation, is_from_block);
  unused_, store :- store_target_checkpoint_state(store, attestation.data.target);
  var target_state: BeaconState :- map_get(store.checkpoint_states, attestation.data.target);
  var indexed_attestation: IndexedAttestation := get_indexed_attestation(target_state, attestation);
  var _ :- pyassert(is_valid_indexed_attestation(target_state, indexed_attestation));
  store := update_latest_messages(store, indexed_attestation.attesting_indices, attestation);
}

/*
    Run ``on_attester_slashing`` immediately upon receiving a new ``AttesterSlashing``
    from either within a block or directly on the wire.
    */
method on_attester_slashing(store_: Store_dt, attester_slashing: AttesterSlashing)
returns (status_: Outcome<()>, store: Store_dt) 
{
  status_, store := Result(()), store_;
  var attestation_1: IndexedAttestation := attester_slashing.attestation_1;
  var attestation_2: IndexedAttestation := attester_slashing.attestation_2;
  var _ :- pyassert(is_slashable_attestation_data(attestation_1.data, attestation_2.data));
  var state: BeaconState :- map_get(store.block_states, store.justified_checkpoint.root);
  var _ :- pyassert(is_valid_indexed_attestation(state, attestation_1));
  var _ :- pyassert(is_valid_indexed_attestation(state, attestation_2));
  var indices: set<ValidatorIndex> := seq_to_set(attestation_1.attesting_indices) * seq_to_set(attestation_2.attesting_indices);
  var tmp_for_0: set<ValidatorIndex> := indices;
  while tmp_for_0 != {} decreases tmp_for_0 {
    var index: ValidatorIndex :| index in tmp_for_0;
    tmp_for_0 := tmp_for_0 - {index};
    store := store.(equivocating_indices := store.equivocating_indices + {index});
  }
}
